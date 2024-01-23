use std::sync::Arc;

use crate::{
    containers::Symbol,
    typed_ast::{BinOp, Expr, ExprInner, Program, UniOp},
    typesys::Type,
};
use ethnum::U256;

use mil2::Mil;
use serde::{Deserialize, Serialize};
use smol_str::ToSmolStr;

/// Generates Mil code (in s-expression format) by traversing a fully monomorphized Program.
pub fn codegen_program(prog: Program) -> Mil {
    log::debug!(
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
                BinOp::Append => mil2::BinOp::Vappend,
                BinOp::Eq => mil2::BinOp::Eql,
                BinOp::Lt => todo!(),
                BinOp::Le => todo!(),
                BinOp::Gt => todo!(),
                BinOp::Ge => todo!(),
                BinOp::Bor => todo!(),
                BinOp::Band => todo!(),
                BinOp::Bxor => todo!(),
                BinOp::Lshift => todo!(),
                BinOp::Rshift => todo!(),
            };
            Mil::BinOp(op, x.into(), y.into())
        }
        ExprInner::UniOp(_, _) => todo!(),

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
        ExprInner::ApplyGeneric(_, _, _) => todo!(),
        ExprInner::LitNum(num) => Mil::Number(*num),
        ExprInner::LitBytes(_) => todo!(),
        ExprInner::LitBVec(_) => todo!(),
        ExprInner::LitVec(_) => todo!(),
        ExprInner::Var(x) => Mil::Var(x.to_smolstr()),
        ExprInner::IsType(_, _) => todo!(),
        ExprInner::VectorRef(_, _) => todo!(),
        ExprInner::VectorUpdate(_, _, _) => todo!(),
        ExprInner::VectorSlice(_, _, _) => todo!(),
        ExprInner::Fail => todo!(),
    }
}

#[cfg(test)]
mod tests {
    use std::path::Path;

    use log::LevelFilter;

    use crate::{context::ModuleId, grammar::parse_program, typesys::typecheck_program};

    use super::*;

    fn init_logs() {
        let _ = env_logger::builder()
            .is_test(true)
            .format_timestamp(None)
            .filter_level(LevelFilter::Trace)
            .try_init();
    }

    #[test]
    fn simple_test() {
        init_logs();
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
        init_logs();
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
        init_logs();
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
                                [y, 2]
                        
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
    fn simple_codegen() {
        init_logs();
        let module = ModuleId::from_path(Path::new("whatever.melo"));
        eprintln!(
            "{:?}",
            codegen_program(
                typecheck_program(
                    parse_program(
                        r"
                        def succ<$n>(x: {$n..$n}) = $n + 1
                        def peel<$n>(x : {$n+1..$n+1}) = $n
                        --- 
                        let res = (let x = 0 :: Nat in
                        loop 100 do
                            x <- x + 1
                        return x) in
                        res is Nat | [Nat, Nat]
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
        init_logs();
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

    #[test]
    fn vref_stuff() {
        init_logs();
        let module = ModuleId::from_path(Path::new("whatever.melo"));
        eprintln!(
            "{:?}",
            codegen_program(
                typecheck_program(
                    parse_program(
                        r#"
                        let nested = [[0,1], [2,3], [4,5]] in for val in vref(nested, 1) collect val + 1
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
