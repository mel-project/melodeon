use std::ops::Deref;

use crate::{
    containers::Symbol,
    typed_ast::{BinOp, Expr, ExprInner, FunDefn, Program, UniOp},
    typesys::Type,
};
use ethnum::U256;
use lexpr::Value;

/// Generates Mil code (in s-expression format) by traversing a fully monomorphized Program.
pub fn codegen_program(prog: Program) -> String {
    log::debug!(
        "generating code for program with {} monomorphized definitions",
        prog.fun_defs.len()
    );
    prog.fun_defs
        .iter()
        .map(codegen_fundef)
        .chain(std::iter::once(codegen_expr(&prog.body)))
        .fold(String::new(), |mut a, b| {
            a.push_str(&sexpr_pretty(&b));
            a.push('\n');
            a
        })
}

/// Trivial pretty-printer for an s-expression
fn sexpr_pretty(v: &Value) -> String {
    let unpretty = v.to_string();
    if unpretty.len() < 50 {
        return unpretty;
    }
    if let Some(mut inner) = v.list_iter() {
        let form_name = inner.next().unwrap().to_string();
        let mut accum = format!("({}", form_name);
        for inner in inner {
            let inner_str = sexpr_pretty(inner);
            for line in inner_str.lines() {
                if accum.len() > 10 {
                    accum.push('\n');
                }
                accum.push(' ');
                accum.push_str(line)
            }
        }
        accum.push(')');
        accum
    } else {
        unpretty
    }
}

fn codegen_fundef(fdef: &FunDefn) -> Value {
    [
        Value::symbol("fn"),
        Value::symbol(fdef.name.to_string()),
        fdef.args
            .iter()
            .map(|s| Value::symbol(s.to_string()))
            .sexpr(),
        codegen_expr(&fdef.body),
    ]
    .sexpr()
}

fn codegen_expr(expr: &Expr) -> Value {
    match &expr.inner {
        ExprInner::BinOp(BinOp::Eq, x, y) => {
            let x_temp = Symbol::generate("@if");
            let y_temp = Symbol::generate("@if");
            [
                Value::symbol("let"),
                [
                    Value::symbol(x_temp.to_string()),
                    codegen_expr(x),
                    Value::symbol(y_temp.to_string()),
                    codegen_expr(y),
                ]
                .sexpr(),
                generate_eq_check(
                    if x.itype.subtype_of(&y.itype) {
                        &y.itype
                    } else {
                        &x.itype
                    },
                    Value::symbol(x_temp.to_string()),
                    Value::symbol(y_temp.to_string()),
                ),
            ]
            .sexpr()
        }
        ExprInner::UniOp(op, x) => {
            let op = match op {
                UniOp::Bnot => Value::symbol("not"),
            };
            let x = codegen_expr(x);
            [op, x].sexpr()
        }
        ExprInner::BinOp(op, x, y) => {
            let op = match op {
                BinOp::Add => Value::symbol("+"),
                BinOp::Sub => Value::symbol("-"),
                BinOp::Mul => Value::symbol("*"),
                BinOp::Div => Value::symbol("/"),
                BinOp::Mod => Value::symbol("%"),
                BinOp::Append => {
                    if x.itype
                        .deunionize()
                        .any(|f| matches!(f, Type::Bytes(_) | Type::DynBytes))
                    {
                        Value::symbol("b-concat")
                    } else {
                        Value::symbol("v-concat")
                    }
                }
                BinOp::Eq => unreachable!(),
                BinOp::Lt => Value::symbol("<"),
                BinOp::Le => Value::symbol("<="),
                BinOp::Gt => Value::symbol(">"),
                BinOp::Ge => Value::symbol(">="),
                BinOp::Bor => Value::symbol("or"),
                BinOp::Band => Value::symbol("and"),
                BinOp::Bxor => Value::symbol("xor"),
                BinOp::Lshift => Value::symbol("<<"),
                BinOp::Rshift => Value::symbol(">>"),
            };
            let x = codegen_expr(x);
            let y = codegen_expr(y);
            [op, x, y].sexpr()
        }
        ExprInner::Exp(k, base, exp) => [
            Value::symbol("**"),
            // TODO do something a little more intelligent here
            Value::Number(255.into()),
            codegen_expr(base),
            codegen_expr(exp),
        ]
        .sexpr(),
        ExprInner::If(a, b, c) => [
            Value::symbol("if"),
            codegen_expr(a),
            codegen_expr(b),
            codegen_expr(c),
        ]
        .sexpr(),
        ExprInner::Let(binds, i) => [
            Value::symbol("let"),
            binds
                .iter()
                .fold(vec![], |acc, (var, val)| {
                    [acc, vec![Value::symbol(var.to_string()), codegen_expr(val)]].concat()
                })
                .sexpr(),
            codegen_expr(i),
        ]
        .sexpr(),
        ExprInner::Apply(f, vec) => std::iter::once(Value::symbol(f.to_string()))
            .chain(vec.iter().map(codegen_expr))
            .sexpr(),
        ExprInner::ApplyGeneric(_, _, _, _) => todo!(),
        ExprInner::LitNum(num) => {
            // lexpr does not support u64, so we desugar to smaller numbers
            u256_to_sexpr(*num)
        }
        ExprInner::LitVec(vec) => std::iter::once(Value::symbol("vector"))
            .chain(vec.iter().map(codegen_expr))
            .sexpr(),
        ExprInner::LitBVec(vec) => std::iter::once(Value::symbol("bytes"))
            .chain(vec.iter().map(codegen_expr))
            .sexpr(),
        ExprInner::LitConst(_) => unreachable!(),
        ExprInner::Var(v) => Value::symbol(v.to_string()),
        ExprInner::IsType(a, t) => generate_type_check(t, Value::symbol(a.to_string())),
        ExprInner::VectorRef(v, i) => [
            if v.itype
                .deunionize()
                .any(|f| matches!(f, Type::Bytes(_) | Type::DynBytes))
            {
                Value::symbol("b-get")
            } else {
                Value::symbol("v-get")
            },
            codegen_expr(v),
            codegen_expr(i),
        ]
        .sexpr(),
        ExprInner::VectorUpdate(v, i, n) => [
            Value::symbol("v-from"),
            codegen_expr(v),
            codegen_expr(i),
            codegen_expr(n),
        ]
        .sexpr(),
        ExprInner::VectorSlice(v, i, j) => [
            Value::symbol("v-slice"),
            codegen_expr(v),
            codegen_expr(i),
            codegen_expr(j),
        ]
        .sexpr(),
        ExprInner::Loop(n, bod, res) => [
            Value::symbol("let"),
            [].sexpr(),
            [
                Value::symbol("loop"),
                Value::Number(n.eval().as_u64().into()),
                [Value::symbol("set-let"), [].sexpr()]
                    .into_iter()
                    .chain(bod.iter().map(|(s, x)| {
                        [
                            Value::symbol("set!"),
                            Value::symbol(s.to_string()),
                            codegen_expr(x),
                        ]
                        .sexpr()
                    }))
                    .sexpr(),
            ]
            .sexpr(),
            codegen_expr(res),
        ]
        .sexpr(),
        ExprInner::Fail => Value::symbol("fail!"),
        ExprInner::LitBytes(b) => {
            if b.is_empty() {
                Value::symbol("\"\"")
            } else {
                Value::symbol(format!("0x{}", hex::encode(&b)))
            }
        }
        ExprInner::ExternApply(f, args) => std::iter::once(Value::symbol(f.as_str()))
            .chain(args.iter().map(codegen_expr))
            .sexpr(),
        ExprInner::Extern(s) => Value::symbol(s.clone()),
    }
}

fn generate_eq_check(t: &Type, left_expr: Value, right_expr: Value) -> Value {
    match t {
        Type::Nothing => Value::Number(1.into()),
        Type::Any => Value::Number(0.into()),
        Type::Var(_) => unreachable!(),
        Type::NatRange(_, _) => [Value::symbol("="), left_expr, right_expr].sexpr(),
        Type::Vector(v) => v
            .iter()
            .enumerate()
            .map(|(i, t)| {
                generate_eq_check(
                    t,
                    [
                        Value::symbol("v-get"),
                        left_expr.clone(),
                        Value::Number((i as u64).into()),
                    ]
                    .sexpr(),
                    [
                        Value::symbol("v-get"),
                        right_expr.clone(),
                        Value::Number((i as u64).into()),
                    ]
                    .sexpr(),
                )
            })
            .fold(Value::Number(1_u64.into()), |a, b| {
                [Value::symbol("and"), a, b].sexpr()
            }),
        Type::Bytes(b) => (0..b.eval().as_u64().saturating_sub(1))
            .map(|i| {
                generate_eq_check(
                    &Type::NatRange(0_u32.into(), 1_u32.into()),
                    [
                        Value::symbol("b-get"),
                        left_expr.clone(),
                        Value::Number((i as u64).into()),
                    ]
                    .sexpr(),
                    [
                        Value::symbol("b-get"),
                        right_expr.clone(),
                        Value::Number((i as u64).into()),
                    ]
                    .sexpr(),
                )
            })
            .fold(Value::Number(1_u64.into()), |a, b| {
                [Value::symbol("and"), a, b].sexpr()
            }),
        Type::Vectorof(t, n) => generate_eq_check(
            &Type::Vector(
                std::iter::repeat(t.deref().clone())
                    .take(n.eval().as_usize())
                    .collect(),
            ),
            left_expr,
            right_expr,
        ),
        Type::Struct(_, _) => todo!(),
        Type::Union(t, u) => {
            let both_t = [
                Value::symbol("and"),
                generate_type_check(t, left_expr.clone()),
                generate_type_check(t, right_expr.clone()),
            ]
            .sexpr();
            let both_u = [
                Value::symbol("and"),
                generate_type_check(u, left_expr.clone()),
                generate_type_check(u, right_expr.clone()),
            ]
            .sexpr();
            [
                Value::symbol("or"),
                [
                    Value::symbol("and"),
                    both_t,
                    generate_eq_check(t, left_expr.clone(), right_expr.clone()),
                ]
                .sexpr(),
                [
                    Value::symbol("and"),
                    both_u,
                    generate_eq_check(t, left_expr, right_expr),
                ]
                .sexpr(),
            ]
            .sexpr()
        }
        Type::DynVectorof(_) => todo!(),
        Type::DynBytes => todo!(),
    }
}

fn u256_to_sexpr(num: U256) -> Value {
    // lexpr does not support u64, so we desugar to smaller numbers
    if num > U256::from(u64::MAX) {
        let divisor = U256::from(1u64 << 32);
        let inner = codegen_expr(&Expr {
            itype: Type::Any,
            inner: ExprInner::LitNum(num / divisor),
        });
        [
            Value::symbol("+"),
            Value::Number((num % divisor).as_u64().into()),
            [
                Value::symbol("*"),
                Value::Number(divisor.as_u64().into()),
                inner,
            ]
            .sexpr(),
        ]
        .sexpr()
    } else {
        Value::Number(num.as_u64().into())
    }
}

fn generate_type_check(t: &Type, inner: Value) -> Value {
    match t {
        Type::Nothing => Value::Number(0.into()),
        Type::Any => Value::Number(1.into()),
        Type::Var(_) => unreachable!(),
        Type::NatRange(a, b) => {
            let is_number_expr = [
                Value::symbol("="),
                Value::Number(0.into()),
                [Value::symbol("typeof"), inner.clone()].sexpr(),
            ]
            .sexpr();
            if a.eval() == U256::MIN && b.eval() == U256::MAX {
                is_number_expr
            } else {
                [
                    Value::symbol("if"),
                    is_number_expr,
                    [
                        Value::symbol("and"),
                        [Value::symbol(">="), inner.clone(), u256_to_sexpr(a.eval())].sexpr(),
                        [Value::symbol("<="), inner, u256_to_sexpr(b.eval())].sexpr(),
                    ]
                    .sexpr(),
                    Value::Number(0i32.into()),
                ]
                .sexpr()
            }
        }
        Type::Vector(inners) => {
            let is_vector_expr = [
                Value::symbol("="),
                Value::Number(2.into()),
                [Value::symbol("typeof"), inner.clone()].sexpr(),
            ]
            .sexpr();
            let length_correct_expr = [
                Value::symbol("="),
                Value::Number((inners.len() as u64).into()),
                [Value::symbol("v-len"), inner.clone()].sexpr(),
            ]
            .sexpr();
            inners
                .iter()
                .enumerate()
                .map(|(idx, t)| {
                    generate_type_check(
                        t,
                        [
                            Value::symbol("v-get"),
                            inner.clone(),
                            Value::Number((idx as u64).into()),
                        ]
                        .sexpr(),
                    )
                })
                .fold(
                    [
                        Value::symbol("if"),
                        is_vector_expr,
                        length_correct_expr,
                        Value::Number(0.into()),
                    ]
                    .sexpr(),
                    |a, b| [Value::symbol("if"), a, b, Value::Number(0.into())].sexpr(),
                )
        }
        Type::Vectorof(v, n) => generate_type_check(
            &Type::Vector(
                std::iter::repeat(v.deref().clone())
                    .take(n.eval().as_usize())
                    .collect(),
            ),
            inner,
        ),
        Type::Struct(_, v) => generate_type_check(
            &Type::Vector(v.iter().map(|t| t.1.clone()).collect()),
            inner,
        ),
        Type::Union(t, u) => {
            let t_check = generate_type_check(t, inner.clone());
            let u_check = generate_type_check(u, inner);
            [Value::symbol("or"), t_check, u_check].sexpr()
        }
        Type::DynVectorof(_) => panic!("is expressions on dynamic vectors not yet supported"),
        Type::Bytes(n) => {
            let is_bytes_expr = [
                Value::symbol("="),
                Value::Number(1.into()),
                [Value::symbol("typeof"), inner.clone()].sexpr(),
            ]
            .sexpr();
            let length_correct_expr = [
                Value::symbol("="),
                Value::Number((n.eval().as_u64()).into()),
                [Value::symbol("b-len"), inner].sexpr(),
            ]
            .sexpr();
            [
                Value::symbol("if"),
                is_bytes_expr,
                length_correct_expr,
                Value::Number(0.into()),
            ]
            .sexpr()
        }
        Type::DynBytes => [
            Value::symbol("="),
            Value::Number(1.into()),
            [Value::symbol("typeof"), inner].sexpr(),
        ]
        .sexpr(),
    }
}

trait ToSexpr {
    fn sexpr(self) -> Value;
}

impl<T: IntoIterator<Item = lexpr::Value>> ToSexpr for T {
    fn sexpr(self) -> Value {
        collect_sexpr(self.into_iter())
    }
}

fn collect_sexpr(mut i: impl Iterator<Item = lexpr::Value>) -> lexpr::Value {
    match i.next() {
        Some(head) => {
            let tail = collect_sexpr(i);
            lexpr::Cons::new(head, tail).into()
        }
        None => lexpr::Value::Null,
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
    fn vector_slice() {
        init_logs();
        let module = ModuleId::from_path(Path::new("whatever.melo"));
        eprintln!(
            "{}",
            codegen_program(
                typecheck_program(
                    parse_program(
                        r"
                        [1, 2, 3][0..3]
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
            "{}",
            codegen_program(
                typecheck_program(
                    parse_program(
                        r"
                        2**5
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
            "{}",
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
            "{}",
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
            "{}",
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
            "{}",
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
