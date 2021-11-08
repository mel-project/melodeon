use std::ops::Deref;

use anyhow::Context;

use crate::{
    containers::{Symbol, Void},
    context::{Ctx, CtxErr, CtxLocation, CtxResult, ToCtx, ToCtxErr},
    grammar::RawExpr,
    typesys::{BinOp, ConstExpr, Expr, ExprInner, Type, Variable},
    typesys::typecheck::state::TypecheckState,
};

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
        RawExpr::Let(var, value, body) => {
            let value = recurse(value)?;
            let body = typecheck_expr(state.clone().bind_var(*var, value.itype.clone()), body)?;
            Ok(Expr {
                itype: body.itype.clone(),
                inner: ExprInner::Let(*var, value.into(), body.into()),
            })
        }
        RawExpr::If(_, _, _) => todo!(),
        RawExpr::BinOp(op, a, b) => {
            let a = recurse(a)?;
            let b = recurse(b)?;
            let op = *op.deref();
            // both must be numbers
            let check_nats = || {
                assert_subtype(ctx, &a.itype, &Type::all_nat())?;
                assert_subtype(ctx, &b.itype, &Type::all_nat())?;
                let template: Type<Void, i32> =
                    Type::NatRange(ConstExpr::Var(0), ConstExpr::Var(1));
                let a_range = template.unify_cvars(&a.itype).unwrap();
                let b_range = template.unify_cvars(&b.itype).unwrap();
                Ok::<_, CtxErr>((a_range, b_range))
            };
            match op {
                crate::grammar::BinOp::Add => {
                    let (a_range, b_range) = check_nats()?;
                    // add the two ranges
                    let lower_bound =
                        ConstExpr::Plus(a_range[&0].clone().into(), b_range[&0].clone().into())
                            .simplify();
                    let upper_bound =
                        ConstExpr::Plus(a_range[&1].clone().into(), b_range[&1].clone().into())
                            .simplify();
                    Ok(Expr {
                        itype: Type::NatRange(lower_bound, upper_bound).fix_natrange(),
                        inner: ExprInner::BinOp(BinOp::Add, a.into(), b.into()),
                    })
                }
                crate::grammar::BinOp::Sub => {
                    check_nats()?;
                    // cannot subtract CGs correctly at the moment
                    Ok(Expr {
                        itype: Type::all_nat(),
                        inner: ExprInner::BinOp(BinOp::Sub, a.into(), b.into()),
                    })
                }
                crate::grammar::BinOp::Mul => {
                    let (a_range, b_range) = check_nats()?;
                    // add the two ranges
                    let lower_bound =
                        ConstExpr::Mult(a_range[&0].clone().into(), b_range[&0].clone().into())
                            .simplify();
                    let upper_bound =
                        ConstExpr::Mult(a_range[&1].clone().into(), b_range[&1].clone().into())
                            .simplify();
                    Ok(Expr {
                        itype: Type::NatRange(lower_bound, upper_bound).fix_natrange(),
                        inner: ExprInner::BinOp(BinOp::Mul, a.into(), b.into()),
                    })
                }
                // cannot divide CGs correctly at the moment
                crate::grammar::BinOp::Div => {
                    check_nats()?;
                    Ok(Expr {
                        itype: Type::all_nat(),
                        inner: ExprInner::BinOp(BinOp::Div, a.into(), b.into()),
                    })
                }
                // don't check for nats
                crate::grammar::BinOp::Eq => Ok(Expr {
                    itype: Type::NatRange(0.into(), 1.into()),
                    inner: ExprInner::BinOp(BinOp::Eq, a.into(), b.into()),
                }),
            }
        }
        RawExpr::LitNum(num) => Ok(Expr {
            itype: Type::NatRange(num.into(), num.into()),
            inner: ExprInner::LitNum(num),
        }),
        RawExpr::Var(v) => {
            let itype = state
                .lookup_var(v)
                .context("undefined variable")
                .err_ctx(ctx)?;
            Ok(Expr {
                itype,
                inner: ExprInner::Var(v),
            })
        }
        RawExpr::Apply(_, _) => todo!(),
        RawExpr::Field(_, _) => todo!(),
        RawExpr::VectorRef(_, _) => todo!(),
        RawExpr::VectorUpdate(_, _) => todo!(),
    }
}

#[cfg(test)]
mod tests {
    use ethnum::U256;

    use crate::{containers::Void, context::ModuleId, grammar::parse_program};
    use crate::typesys::typecheck_expr;
    use crate::typesys::typecheck::{Symbol, TypecheckState};

    #[test]
    fn typecheck_simple() {
        let state: TypecheckState<Void, Void> = TypecheckState::new();
        let module = ModuleId(Symbol::from("whatever.melo"));
        eprintln!(
            "{:?}",
            typecheck_expr(
                state,
                parse_program(&format!("let x = 0 in {} + 1 == x", U256::MAX), module)
                    .unwrap()
                    .body
                    .clone()
            )
            .unwrap()
        );
    }
}