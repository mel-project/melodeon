use std::sync::Arc;

use crate::{
    containers::Symbol,
    typed_ast::{BinOp, Expr, ExprInner, Program, UniOp},
    typesys::Type,
};
use ethnum::U256;

use melvm::opcode::OpCode;
use serde::{Deserialize, Serialize};

/// The final intermediate representation that can be quickly translated into MelVM instructions.
#[derive(Clone, PartialEq, Eq, Debug, Serialize, Deserialize)]
pub enum Ir {
    Op(OpCode, Arc<Vec<Ir>>),
    Call(Arc<Ir>, Arc<Vec<Ir>>),
    Bind(imbl::HashMap<Symbol, Ir>, Arc<Ir>),
    LitNum(U256),
    Lambda(Vec<Symbol>, Arc<Ir>),
    LitVar(Symbol),
    VEmpty,
    BEmpty,
}

/// Generates Mil code (in s-expression format) by traversing a fully monomorphized Program.
pub fn codegen_program(prog: Program) -> Ir {
    log::debug!(
        "generating code for program with {} monomorphized definitions",
        prog.fun_defs.len()
    );
    let toplevel_bindings = prog
        .fun_defs
        .iter()
        .map(|fdef| {
            let body = codegen_expr(&fdef.body);
            (fdef.name, Ir::Lambda(fdef.args.clone(), Arc::new(body)))
        })
        .fold(imbl::HashMap::new(), |mut h, (k, v)| {
            h.insert(k, v);
            h
        });
    Ir::Bind(toplevel_bindings, codegen_expr(&prog.body).into())
}

fn codegen_expr(expr: &Expr) -> Ir {
    match &expr.inner {
        ExprInner::BinOp(BinOp::Eq, _x, _y) => {
            todo!()
        }
        ExprInner::UniOp(op, x) => {
            let op = match op {
                UniOp::Bnot => OpCode::Not,
            };
            let x = codegen_expr(x);
            Ir::Op(op, vec![x].into())
        }
        ExprInner::BinOp(op, x, y) => {
            let op = match op {
                BinOp::Add => OpCode::Add,
                BinOp::Sub => OpCode::Sub,
                BinOp::Mul => OpCode::Mul,
                BinOp::Div => OpCode::Div,
                BinOp::Mod => OpCode::Rem,
                BinOp::Append => {
                    if x.itype.deunionize().any(|f| matches!(f, Type::DynBytes)) {
                        OpCode::BAppend
                    } else if x
                        .itype
                        .deunionize()
                        .any(|f| matches!(f, Type::DynVectorof(_)))
                    {
                        OpCode::VAppend
                    } else {
                        todo!("dynamic dispatch for appends")
                    }
                }
                BinOp::Eq => todo!("dynamic dispatch for equality"),
                BinOp::Lt => OpCode::Lt,
                BinOp::Le => todo!("dynamic dispatch for <="),
                BinOp::Gt => OpCode::Gt,
                BinOp::Ge => todo!("dynamic dispatch for >="),
                BinOp::Bor => OpCode::Or,
                BinOp::Band => OpCode::And,
                BinOp::Bxor => OpCode::Xor,
                BinOp::Lshift => OpCode::Shl,
                BinOp::Rshift => OpCode::Shr,
            };
            let x = codegen_expr(x);
            let y = codegen_expr(y);
            Ir::Op(op, vec![x, y].into())
        }
        ExprInner::Exp(_k, base, exp) => {
            let x = codegen_expr(base);
            let y = codegen_expr(exp);
            Ir::Op(OpCode::Exp(255), vec![x, y].into())
        }
        ExprInner::If(_a, _b, _c) => todo!("if expression not impl"),
        ExprInner::Let(binds, inner) => {
            let inner = codegen_expr(inner);
            Ir::Bind(
                binds
                    .iter()
                    .map(|(sym, expr)| (*sym, codegen_expr(expr)))
                    .collect(),
                Arc::new(inner),
            )
        }
        ExprInner::Apply(f, vec) => Ir::Call(
            Arc::new(codegen_expr(f)),
            Arc::new(vec.iter().map(codegen_expr).collect()),
        ),
        ExprInner::ApplyGeneric(_, _, _) => unreachable!(),
        ExprInner::LitNum(num) => Ir::LitNum(*num),
        ExprInner::LitVec(vec) => vec.iter().fold(Ir::VEmpty, |v, a| {
            Ir::Op(OpCode::VPush, vec![v, codegen_expr(a)].into())
        }),
        ExprInner::LitBVec(_vec) => todo!("byte strings not supported yet"),

        ExprInner::Var(v) => Ir::LitVar(*v),
        ExprInner::IsType(_a, _t) => todo!("is not supported yet"),
        ExprInner::VectorRef(v, i) => Ir::Op(
            if v.itype.deunionize().any(|f| matches!(f, Type::DynBytes)) {
                OpCode::BRef
            } else if v
                .itype
                .deunionize()
                .any(|f| matches!(f, Type::DynVectorof(_)))
            {
                OpCode::VRef
            } else {
                todo!("dynamic dispatch for vector ref")
            },
            vec![codegen_expr(v), codegen_expr(i)].into(),
        ),
        ExprInner::VectorUpdate(_v, i, n) => {
            Ir::Op(OpCode::VSet, vec![codegen_expr(i), codegen_expr(n)].into())
        }
        ExprInner::VectorSlice(_v, i, j) => Ir::Op(
            OpCode::VSlice,
            vec![codegen_expr(i), codegen_expr(j)].into(),
        ),

        ExprInner::Fail => todo!("fail not implemented"),
        ExprInner::LitBytes(b) => b.iter().fold(Ir::BEmpty, |v, a| {
            Ir::Op(
                OpCode::BPush,
                vec![v, Ir::LitNum((*a as u64).into())].into(),
            )
        }),
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
            "{:?}",
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
