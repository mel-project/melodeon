// use crate::typesys::{Expr, FunDefn, Program, BinOp};
// use lexpr::sexp;

// /// Generates Mil code (in s-expression format) by traversing a fully monomorphized Program.
// pub fn codegen_program(prog: Program) -> lexpr::Value {
//     let definitions = collect_sexpr(prog.fun_defs.into_iter().map(codegen_fundef));
//     let body = codegen_expr(prog.body);
//     todo!()
// }

// fn codegen_fundef(fdef: FunDefn) -> lexpr::Value {
//     todo!()
// }

// fn codegen_expr(expr: Expr) -> lexpr::Value {
//     let itype = expr.itype;
//     match expr.inner {
//         crate::typesys::ExprInner::BinOp(op, x, y) => {
//             let x = codegen_expr(x);
//             let y = codegen_expr(y);
//             match op {
//                 BinOp::Add => sexp!(#"+"),
//                 BinOp::Sub => sexp!(#"-"),
//                 BinO
//             }
//         },
//         crate::typesys::ExprInner::If(_, _, _) => todo!(),
//         crate::typesys::ExprInner::Let(_, _, _) => todo!(),
//         crate::typesys::ExprInner::Apply(_, _) => todo!(),
//         crate::typesys::ExprInner::ApplyGeneric(_, _, _, _) => todo!(),
//         crate::typesys::ExprInner::LitNum(_) => todo!(),
//         crate::typesys::ExprInner::LitVec(_) => todo!(),
//         crate::typesys::ExprInner::LitConst(_) => todo!(),
//         crate::typesys::ExprInner::Var(_) => todo!(),
//         crate::typesys::ExprInner::IsType(_, _) => todo!(),
//         crate::typesys::ExprInner::VectorRef(_, _) => todo!(),
//         crate::typesys::ExprInner::VectorUpdate(_, _, _) => todo!(),
//     }
// }

// fn collect_sexpr(mut i: impl Iterator<Item = lexpr::Value>) -> lexpr::Value {
//     match i.next() {
//         Some(head) => {
//             let tail = collect_sexpr(i);
//             sexp!((head.tail))
//         }
//         None => sexp!(()),
//     }
// }
