use std::ops::Deref;

use ethnum::U256;

use crate::{
    containers::{Symbol, Void},
    context::{Ctx, CtxLocation, CtxResult, ToCtx},
    grammar::RawExpr,
    typesys::{BinOp, ConstExpr, ExprInner, Type},
};

use self::state::TypecheckState;

use super::{Expr, Variable};

mod state;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct TypeParam(Symbol);

impl Variable for TypeParam {}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct CgParam(Symbol);

impl Variable for CgParam {}

impl Variable for i32 {}

fn assert_subtype<Tv: Variable, Cv: Variable>(
    ctx: Option<CtxLocation>,
    a: &Type<Tv, Cv>,
    b: &Type<Tv, Cv>,
) -> CtxResult<()> {
    if !a.subtype_of(b) {
        Err(anyhow::anyhow!("expected a subtype of {:?}, got {:?} instead", b, a).with_ctx(ctx))
    } else {
        Ok(())
    }
}

/// Typechecks a single expression, returning a single typed ast node.
pub fn typecheck_expr<Tv: Variable, Cv: Variable>(
    state: TypecheckState<Tv, Cv>,
    raw: Ctx<RawExpr>,
) -> CtxResult<Expr<Tv, Cv>> {
    let recurse = |c| typecheck_expr(state.clone(), c);
    let ctx = raw.ctx();
    match raw.deref().clone() {
        RawExpr::Let(_, _, _) => todo!(),
        RawExpr::If(_, _, _) => todo!(),
        RawExpr::BinOp(op, a, b) => {
            let a = recurse(a)?;
            let b = recurse(b)?;
            // both must be numbers
            assert_subtype(ctx, &a.itype, &Type::all_nat())?;
            assert_subtype(ctx, &b.itype, &Type::all_nat())?;
            let template: Type<Void, i32> = Type::NatRange(ConstExpr::Var(0), ConstExpr::Var(1));
            let a_range = template.unify_cvars(&a.itype).unwrap();
            let b_range = template.unify_cvars(&b.itype).unwrap();
            match op.deref() {
                crate::grammar::BinOp::Add => {
                    // if the bounds are numbers, we can actually compute the range
                    let lower_bound =
                        ConstExpr::Plus(a_range[&0].clone().into(), b_range[&0].clone().into())
                            .simplify();
                    let upper_bound =
                        ConstExpr::Plus(a_range[&1].clone().into(), b_range[&1].clone().into())
                            .simplify();
                    Ok(Expr {
                        itype: Type::NatRange(lower_bound, upper_bound),
                        inner: ExprInner::BinOp(BinOp::Add, a.into(), b.into()),
                    })
                }
                crate::grammar::BinOp::Sub => todo!(),
                crate::grammar::BinOp::Mul => todo!(),
                crate::grammar::BinOp::Div => todo!(),
                crate::grammar::BinOp::Eq => todo!(),
            }
        }
        RawExpr::LitNum(num) => Ok(Expr {
            itype: Type::NatRange(num.into(), num.into()),
            inner: ExprInner::LitNum(num),
        }),
        RawExpr::Var(_) => todo!(),
        RawExpr::Apply(_, _) => todo!(),
        RawExpr::Field(_, _) => todo!(),
        RawExpr::VectorRef(_, _) => todo!(),
        RawExpr::VectorUpdate(_, _) => todo!(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{containers::Void, context::ModuleId, grammar::parse_program};

    #[test]
    fn typecheck_simple() {
        let state: TypecheckState<Void, Void> = TypecheckState::new();
        let module = ModuleId(Symbol::from("whatever.melo"));
        eprintln!(
            "{:?}",
            typecheck_expr(state, parse_program("1 + 2", module).unwrap().body.clone()).unwrap()
        );
    }
}
