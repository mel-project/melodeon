use std::ops::Deref;

use crate::{
    containers::Symbol,
    typed_ast::{BinOp, Expr, ExprInner, FunDefn, Program},
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
            a.push_str(&b.to_string());
            a.push('\n');
            a
        })
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
            let x_temp = Symbol::generate("-if");
            let y_temp = Symbol::generate("-if");
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
        ExprInner::BinOp(op, x, y) => {
            let x = codegen_expr(x);
            let y = codegen_expr(y);
            let op = match op {
                BinOp::Add => Value::symbol("+"),
                BinOp::Sub => Value::symbol("-"),
                BinOp::Mul => Value::symbol("*"),
                BinOp::Div => Value::symbol("/"),
                BinOp::Append => Value::symbol("v-concat"),
                BinOp::Eq => unreachable!(),
            };
            [op, x, y].sexpr()
        }
        ExprInner::If(a, b, c) => [
            Value::symbol("if"),
            codegen_expr(a),
            codegen_expr(b),
            codegen_expr(c),
        ]
        .sexpr(),
        ExprInner::Let(v, b, i) => [
            Value::symbol("let"),
            [Value::symbol(v.to_string()), codegen_expr(b)].sexpr(),
            codegen_expr(i),
        ]
        .sexpr(),
        ExprInner::Apply(f, vec) => std::iter::once(Value::symbol(f.to_string()))
            .chain(vec.iter().map(|i| codegen_expr(i)))
            .sexpr(),
        ExprInner::ApplyGeneric(_, _, _, _) => todo!(),
        ExprInner::LitNum(num) => {
            // lexpr does not support u64, so we desugar to smaller numbers
            u256_to_sexpr(*num)
        }
        ExprInner::LitVec(vec) => {
            Value::vector(vec.iter().map(|i| codegen_expr(i)).collect::<Vec<_>>())
        }
        ExprInner::LitConst(_) => unreachable!(),
        ExprInner::Var(v) => Value::symbol(v.to_string()),
        ExprInner::IsType(a, t) => generate_type_check(t, Value::symbol(a.to_string())),
        ExprInner::VectorRef(v, i) => {
            [Value::symbol("v-get"), codegen_expr(v), codegen_expr(i)].sexpr()
        }
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
            ]
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
            codegen_expr(res),
        ]
        .sexpr(),
    }
}

fn generate_eq_check(t: &Type, left_expr: Value, right_expr: Value) -> Value {
    match t {
        Type::None => Value::Number(1.into()),
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
            .fold(Value::Number(1.into()), |a, b| {
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
        Type::None => Value::Number(0.into()),
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
                    Value::symbol("and"),
                    is_number_expr,
                    [
                        Value::symbol("and"),
                        [Value::symbol(">="), inner.clone(), u256_to_sexpr(a.eval())].sexpr(),
                        [Value::symbol("<="), inner, u256_to_sexpr(b.eval())].sexpr(),
                    ]
                    .sexpr(),
                ]
                .sexpr()
            }
        }
        Type::Vector(_) => todo!(),
        Type::Vectorof(_, _) => todo!(),
        Type::Struct(_, _) => todo!(),
        Type::Union(_, _) => todo!(),
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
                        let x = 0 in
                        loop 100 do
                            set! x = x + 1
                        done with x
                ",
                        module
                    )
                    .unwrap()
                )
                .unwrap()
            )
        );
    }
}
