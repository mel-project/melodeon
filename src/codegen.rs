use std::sync::Arc;

use crate::{
    typed_ast::{BinOp, Expr, ExprInner, Program, UniOp},
    typesys::Type,
};
use ethnum::U256;

use mil2::Mil;

use smol_str::ToSmolStr;

/// Generates Mil code (in s-expression format) by traversing a fully monomorphized Program.
pub fn codegen_program(prog: Program) -> Mil {
    tracing::debug!(
        "generating code for program with {} monomorphized definitions",
        prog.fun_defs.len()
    );
    let toplevel_bindings = prog
        .fun_defs
        .iter()
        .map(|fdef| {
            let body = codegen_expr(&fdef.body);
            (
                fdef.name.to_smolstr(),
                Mil::Lambda(
                    fdef.args.iter().map(|sym| sym.to_smolstr()).collect(),
                    Arc::new(body),
                ),
            )
        })
        .fold(imbl::HashMap::new(), |mut h, (k, v)| {
            h.insert(k, v);
            h
        });
    Mil::Letrec(toplevel_bindings, codegen_expr(&prog.body).into())
}

fn codegen_expr(expr: &Expr) -> Mil {
    match &expr.inner {
        ExprInner::BinOp(op, x, y) => {
            let x = codegen_expr(x);
            let y = codegen_expr(y);
            let op = match op {
                BinOp::Add => mil2::BinOp::Add,
                BinOp::Sub => mil2::BinOp::Sub,
                BinOp::Mul => mil2::BinOp::Mul,
                BinOp::Div => mil2::BinOp::Div,
                BinOp::Mod => mil2::BinOp::Rem,
                BinOp::Expt => mil2::BinOp::Exp,
                BinOp::Vappend => mil2::BinOp::Vappend,
                BinOp::Bappend => mil2::BinOp::Bappend,
                BinOp::Append => {
                    return Mil::Call(Mil::Var("__dyn_append".into()).into(), vec![x, y].into())
                }
                BinOp::Eq => {
                    return Mil::Call(Mil::Var("__dyn_equal".into()).into(), vec![x, y].into())
                }
                BinOp::Lt => mil2::BinOp::Lt,
                BinOp::Le => {
                    return Mil::Call(Mil::Var("__dyn_leq".into()).into(), vec![x, y].into())
                }
                BinOp::Gt => mil2::BinOp::Gt,
                BinOp::Ge => {
                    return Mil::Call(Mil::Var("__dyn_geq".into()).into(), vec![x, y].into())
                }
                BinOp::Bor => mil2::BinOp::Bor,
                BinOp::Band => mil2::BinOp::Band,
                BinOp::Bxor => mil2::BinOp::Bxor,
                BinOp::Lshift => mil2::BinOp::Lshift,
                BinOp::Rshift => mil2::BinOp::Rshift,
                BinOp::NumEq => mil2::BinOp::Eql,
            };
            Mil::BinOp(op, x.into(), y.into())
        }
        ExprInner::UniOp(op, inner) => {
            let op = match op {
                UniOp::Bnot => mil2::UniOp::Bnot,
                UniOp::TypeQ => mil2::UniOp::TypeQ,
                UniOp::Vlen => mil2::UniOp::Vlen,
                UniOp::Blen => mil2::UniOp::Blen,
            };
            Mil::UniOp(op, codegen_expr(inner).into())
        }

        ExprInner::If(condition, then_case, else_case) => {
            let condition = codegen_expr(condition);
            let then_case = codegen_expr(then_case);
            let else_case = codegen_expr(else_case);
            Mil::IfThenElse(condition.into(), then_case.into(), else_case.into())
        }
        ExprInner::Let(bindings, inner) => {
            bindings
                .iter()
                .rev()
                .fold(codegen_expr(inner), |inner, (var_name, var_value)| {
                    let var_value = codegen_expr(var_value);
                    Mil::Let(var_name.to_smolstr(), var_value.into(), inner.into())
                })
        }
        ExprInner::Apply(_, _) => todo!(),
        ExprInner::ApplyGeneric(f, _, args) => Mil::Call(
            codegen_expr(f).into(),
            args.iter().map(codegen_expr).collect(),
        ),
        ExprInner::LitNum(num) => Mil::Number(*num),
        ExprInner::LitBytes(_) => todo!(),
        ExprInner::LitBVec(_) => todo!(),
        ExprInner::LitVec(vec) => Mil::List(vec.iter().map(codegen_expr).collect()),
        ExprInner::Var(x) => Mil::Var(x.to_smolstr()),
        ExprInner::IsType(x, t) => {
            // recurse through the type
            let checker = is_type_checker(t);
            Mil::Call(checker.into(), vec![Mil::Var(x.to_smolstr())].into())
        }
        ExprInner::VectorRef(vec, idx) => Mil::BinOp(
            mil2::BinOp::Vref,
            codegen_expr(vec).into(),
            codegen_expr(idx).into(),
        ),
        ExprInner::VectorUpdate(vec, i, val) => Mil::TriOp(
            mil2::TriOp::Vupdate,
            codegen_expr(vec).into(),
            codegen_expr(i).into(),
            codegen_expr(val).into(),
        ),
        ExprInner::VectorSlice(vec, i, j) => Mil::TriOp(
            mil2::TriOp::Vslice,
            codegen_expr(vec).into(),
            codegen_expr(i).into(),
            codegen_expr(j).into(),
        ),
        ExprInner::Fail => todo!(),
        ExprInner::Lambda(args, body) => Mil::Lambda(
            args.iter().map(|s| s.0.to_smolstr()).collect(),
            codegen_expr(body).into(),
        ),
    }
}

fn is_type_checker(t: &Type) -> Mil {
    match t {
        Type::Nothing => Mil::Lambda(vec!["_".into()].into(), Mil::Number(U256::ZERO).into()),
        Type::Any => Mil::Lambda(vec!["_".into()].into(), Mil::Number(U256::ONE).into()),
        Type::Var(_) => Mil::Lambda(vec!["_".into()].into(), Mil::Number(U256::ZERO).into()),
        Type::Nat => Mil::Var("__istype_nat".into()),
        Type::Vector(inner) => Mil::Call(
            Mil::Var("__istype_vector_by_idx".into()).into(),
            vec![Mil::List(inner.iter().map(is_type_checker).collect())].into(),
        ),
        Type::Vectorof(inner) => Mil::Call(
            Mil::Var("__istype_vectorof".into()).into(),
            vec![is_type_checker(inner)].into(),
        ),
        Type::Bytes => Mil::Var("__istype_bytes".into()),
        Type::Struct(_, _) => todo!(),
        Type::Union(t, u) => Mil::Call(
            Mil::Var("__istype_union".into()).into(),
            vec![is_type_checker(t), is_type_checker(u)].into(),
        ),
        Type::Lambda {
            free_vars: _,
            args: _,
            result: _,
        } => todo!(),
    }
}

#[cfg(test)]
mod tests {
    use std::path::Path;

    use crate::{context::ModuleId, grammar::parse_program, typesys::typecheck_program};

    use super::*;

    #[test]
    fn simple_test() {
        let module = ModuleId::from_path(Path::new("whatever.melo"));
        eprintln!(
            "{:?}",
            codegen_program(
                typecheck_program(
                    parse_program(
                        r"
                        1 + 2
                        ",
                        module,
                        &std::path::PathBuf::from(""),
                    )
                    .unwrap()
                )
                .unwrap()
            )
        );
    }

    #[test]
    fn expt_codegen() {
        let module = ModuleId::from_path(Path::new("whatever.melo"));
        eprintln!(
            "{:?}",
            codegen_program(
                typecheck_program(
                    parse_program(
                        r"
                        let x = 5 in (2**5) + x
                        ",
                        module,
                        &std::path::PathBuf::from(""),
                    )
                    .unwrap()
                )
                .unwrap()
            )
        );
    }

    #[test]
    fn tricky_codegen() {
        let module = ModuleId::from_path(Path::new("whatever.melo"));
        eprintln!(
            "{:?}",
            codegen_program(
                typecheck_program(
                    parse_program(
                        r"
                        def dol(x: Nat) = if x % 2 == 0 then [x] else x
                        def foo(x: Nat) =
                            let y = dol(x) in
                            if y is [Nat] then
                                y[0]
                            else
                                [y, 2][0 => 2]
                        
                        ---
                        
                        foo(3)
                        ",
                        module,
                        &std::path::PathBuf::from(""),
                    )
                    .unwrap()
                )
                .unwrap()
            )
        );
    }

    #[test]
    fn empty_byte_string() {
        let module = ModuleId::from_path(Path::new("whatever.melo"));
        eprintln!(
            "{:?}",
            codegen_program(
                typecheck_program(
                    parse_program(
                        r#"
                        "test" ++ ""
                        "#,
                        module,
                        &std::path::PathBuf::from(""),
                    )
                    .unwrap()
                )
                .unwrap()
            )
        );
    }
}
