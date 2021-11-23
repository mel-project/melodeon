use anyhow::Context;

use crate::typesys::{ConstExpr, Variable};

/// Solves a recurrence. Given an initial const-expression, a pre-step expression, a post-step expression, and a number of iterations, compute the total sum
pub fn solve_recurrence<C: Variable>(
    initial: ConstExpr<C>,
    pre_step: C,
    post_step: ConstExpr<C>,
    iterations: ConstExpr<C>,
) -> anyhow::Result<ConstExpr<C>> {
    // First, we ensure that the post_step only has this one variable, and it is of the form n + c
    let diff = post_step
        .checked_sub(&ConstExpr::Var(pre_step))
        .context("pre_step cannot be subtracted from post_step")?
        .try_eval()
        .context("per-step change in constant-generic variable is not constant")?;
    // Then we add iterations * diff to initial
    Ok(ConstExpr::Add(
        initial.into(),
        ConstExpr::Mul(ConstExpr::Lit(diff).into(), iterations.into()).into(),
    ))
}
