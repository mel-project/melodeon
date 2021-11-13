use crate::typesys::{BinOp, Expr, ExprInner, FunDefn, Program, Type};
use ethnum::U256;
use lexpr::Value;

/// Generates Mil code (in s-expression format) by traversing a fully monomorphized Program.
pub fn codegen_program(prog: Program) -> String {
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
    let itype = expr.itype.clone();
    match &expr.inner {
        ExprInner::BinOp(op, x, y) => {
            let x = codegen_expr(x);
            let y = codegen_expr(y);
            let op = match op {
                BinOp::Add => Value::symbol("+"),
                BinOp::Sub => Value::symbol("-"),
                BinOp::Mul => Value::symbol("*"),
                BinOp::Div => Value::symbol("/"),
                BinOp::Append => Value::symbol("vappend"),
                BinOp::Eq => todo!(),
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
            if num > &U256::from(u64::MAX) {
                let divisor = U256::from(1u64 << 32);
                let inner = codegen_expr(&Expr {
                    itype: Type::Any,
                    inner: ExprInner::LitNum(*num / divisor),
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
        ExprInner::LitVec(vec) => {
            Value::vector(vec.iter().map(|i| codegen_expr(i)).collect::<Vec<_>>())
        }
        ExprInner::LitConst(_) => todo!(),
        ExprInner::Var(v) => Value::symbol(v.to_string()),
        ExprInner::IsType(_, _) => todo!(),
        ExprInner::VectorRef(_, _) => todo!(),
        ExprInner::VectorUpdate(_, _, _) => todo!(),
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
    use log::LevelFilter;

    use crate::{
        containers::Symbol, context::ModuleId, grammar::parse_program, typesys::typecheck_program,
    };

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
        let module = ModuleId(Symbol::from("whatever.melo"));
        eprintln!(
            "{}",
            codegen_program(
                typecheck_program(
                    parse_program(
                        r"
                        def succ<$n>(x: {$n..$n}) = $n + 1
                        def peel<$n>(x : {$n+1..$n+1}) = $n
                        ---
                        [peel(succ(succ(0))*1000), [2, 3, 4, 5], 6]
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
