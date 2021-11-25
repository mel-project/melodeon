use anyhow::Context;

use crate::typesys::{ConstExpr, Type, Variable};

/// *Partially erase* const-generic variables within a type, given a function that determines whether or not a particular variable should be erased. Numeric bounds become Nat, and vector-length bounds become dynamic-length vectors.
pub fn partially_erase_cg<T: Variable, C: Variable>(
    t: &Type<T, C>,
    erase: impl Fn(&C) -> bool + Copy,
) -> Type<T, C> {
    let recurse = |v| partially_erase_cg(v, erase);
    match t {
        Type::None => Type::None,
        Type::Any => Type::Any,
        Type::Var(v) => Type::Var(v.clone()),
        Type::NatRange(n, m) => Type::NatRange(
            if n.cvars().iter().any(erase) {
                0.into()
            } else {
                n.clone()
            },
            if m.cvars().iter().any(erase) {
                0.into()
            } else {
                m.clone()
            },
        ),
        Type::Vector(v) => Type::Vector(v.iter().map(recurse).collect()),
        Type::Vectorof(a, n) => {
            if n.cvars().iter().any(erase) {
                Type::DynVectorof(recurse(a).into())
            } else {
                Type::Vectorof(recurse(a).into(), n.clone())
            }
        }
        Type::Struct(s, b) => Type::Struct(*s, b.iter().map(|(a, b)| (*a, recurse(b))).collect()),
        Type::Union(t, u) => Type::Union(recurse(t).into(), recurse(u).into()),
        Type::DynVectorof(t) => Type::DynVectorof(recurse(t).into()),
        Type::Bytes(m) => {
            if m.cvars().iter().any(erase) {
                Type::DynBytes
            } else {
                Type::Bytes(m.clone())
            }
        }
        Type::DynBytes => Type::DynBytes,
    }
}

/// Replaces all the possible slots within a type with const-generic parameters.
pub fn cgify_all_slots<T: Variable, C: Variable>(
    t: &Type<T, C>,
    gensym: impl Fn() -> C + Copy,
) -> Type<T, C> {
    match &t {
        Type::Vector(v) => Type::Vector(v.iter().map(|t| cgify_all_slots(t, gensym)).collect()),
        Type::Vectorof(v, _) => Type::Vectorof(v.clone(), ConstExpr::Var(gensym())),
        Type::Struct(_, _) => todo!(),
        Type::Union(_, _) => todo!(),
        _ => t.clone(),
    }
}

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
        .context("pre_step cannot be subtracted from post_step")?;
    let diff = diff.try_eval().context(format!(
        "per-step change in constant-generic variable is not constant: {:?}",
        diff
    ))?;
    // Then we add iterations * diff to initial
    Ok(ConstExpr::Add(
        initial.into(),
        ConstExpr::Mul(ConstExpr::Lit(diff).into(), iterations.into()).into(),
    ))
}
