use std::{fmt::Debug, ops::Deref, sync::atomic::AtomicUsize};

use anyhow::Context;
use dashmap::{DashMap, DashSet};
use ethnum::U256;
use rustc_hash::FxHashSet;
use tap::Tap;

use crate::{
    containers::{List, Map, Set, Symbol, Void},
    context::{Ctx, CtxErr, CtxLocation, CtxResult, ToCtx, ToCtxErr},
    grammar::{sort_defs, RawConstExpr, RawExpr, RawProgram, RawTypeExpr},
    typed_ast::{BinOp, Expr, ExprInner, FunDefn, Program, UniOp},
    typesys::{
        typecheck::fold::{cgify_all_slots, partially_erase_cg, solve_recurrence},
        ConstExpr, Type, Variable,
    },
};

use self::{
    facts::TypeFacts,
    state::{FunctionType, TypecheckState},
};

mod facts;
mod fold;
mod state;

#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct TypeParam(Symbol);

impl Debug for TypeParam {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

impl Variable for TypeParam {}

#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct CgParam(Symbol);

impl Debug for CgParam {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

impl Variable for CgParam {
    fn try_from_sym(s: Symbol) -> Option<Self> {
        Some(Self(s))
    }
}

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

/// Typechecks a whole program, resolving free variables fully.
pub fn typecheck_program(raw: Ctx<RawProgram>) -> CtxResult<Program> {
    log::debug!(
        "typechecking whole program rooted at {:?} with {} defs",
        raw.ctx().map(|ctx| ctx.source.to_string()),
        raw.definitions.len()
    );
    // Check for duplicate definitions
    let mut seen = FxHashSet::default();
    for defn in raw.definitions.iter() {
        if !seen.insert(defn.name()) {
            return Err(
                anyhow::anyhow!("duplicated definition of {:?}", defn.name()).with_ctx(defn.ctx()),
            );
        }
    }
    // Topologically sort definitions
    let sorted = sort_defs(raw.definitions.clone());

    // build the typecheck state
    let mut state = TypecheckState::new();
    let mut fun_defs: List<FunDefn<TypeParam, CgParam>> = List::new();
    //for definition in raw.definitions.iter() {
    for definition in sorted.iter() {
        match definition.deref() {
            crate::grammar::RawDefn::Function {
                name,
                cgvars,
                genvars,
                args,
                rettype,
                body,
            } => {
                // bind the type variables, then the CG-variables
                let istate: TypecheckState<TypeParam, CgParam> =
                    genvars.iter().fold(state.clone(), |state, sym| {
                        state.bind_type_alias(**sym, Type::Var(TypeParam(**sym)))
                    });
                let istate = cgvars.iter().fold(istate, |state, sym| {
                    state.bind_cgvar(**sym, ConstExpr::Var(CgParam(**sym)))
                });
                // now also bind the argument types
                let state_no_args = istate.clone();
                let istate = args.iter().fold(Ok::<_, CtxErr>(istate), |state, arg| {
                    let state = state?;
                    let arg_tc = typecheck_type_expr(&state_no_args, arg.bind.clone())?;
                    Ok(state.bind_var(*arg.name, arg_tc))
                })?;
                // we calculate the body type
                let (body, _) = typecheck_expr(istate.clone(), body.clone())?;
                let rettype = if let Some(rettype) = rettype {
                    let ctx = rettype.ctx();
                    let rettype = typecheck_type_expr(&state_no_args, rettype.clone())?;
                    if !body.itype.subtype_of(&rettype) {
                        return Err(anyhow::anyhow!(
                            "return type of {:?} is {:?}, contradicting annotated type {:?}",
                            name,
                            body.itype,
                            rettype
                        )
                        .with_ctx(ctx));
                    }
                    rettype
                } else {
                    body.itype.clone()
                };
                let fun_info = FunctionType {
                    free_cgvars: cgvars.iter().map(|c| CgParam(**c)).collect(),
                    free_vars: genvars.iter().map(|c| TypeParam(**c)).collect(),
                    args: args
                        .iter()
                        .map(|s| istate.lookup_var(*s.name).unwrap())
                        .collect(),
                    result: rettype,
                };
                state = state.bind_fun(**name, fun_info);
                fun_defs.push(FunDefn {
                    name: **name,
                    args: args.iter().map(|s| *s.name).collect(),
                    body,
                });
            }
            crate::grammar::RawDefn::Constant(_, _) => todo!(),
            crate::grammar::RawDefn::Struct { name, fields } => {
                let tstate = state.clone();
                state = state.bind_type_alias(
                    **name,
                    Type::Struct(
                        **name,
                        fields
                            .iter()
                            .map(|rtb| {
                                Ok((*rtb.name, typecheck_type_expr(&tstate, rtb.bind.clone())?))
                            })
                            .collect::<CtxResult<List<_>>>()?,
                    ),
                );
            }
            crate::grammar::RawDefn::Require(_) => {
                panic!("non-demodularized AST passed into typechecker")
            }
            crate::grammar::RawDefn::Provide(_) => {
                panic!("non-demodularized AST passed into typechecker")
            }
            crate::grammar::RawDefn::TypeAlias(a, b) => {
                let b = typecheck_type_expr(&state, b.clone())?;
                state = state.bind_type_alias(**a, b);
            }
        }
    }
    log::trace!("initial definitions created: {:?}", fun_defs);
    // time to typecheck the expression preliminarily
    let (prelim_body, _) = typecheck_expr(state, raw.body.clone())?;
    log::trace!("preliminary body created: {:?}", prelim_body);

    // MONOMORPHIZE!
    Ok(monomorphize(fun_defs, prelim_body))
}

/*
pub fn typecheck_bindings<Tv: Variable, Cv: Variable>(binds: Vec<(Ctx<Symbol>, Ctx<RawExpr>)>)
-> CtxResult<Vec<(Ctx<Symbol>, (Expr<Tv,Cv>, TypeFacts<Tv,Cv>))>> {
    let recurse = |c| typecheck_expr(state.clone(), c);
    binds.into_iter().map(|(v,e)| (v, recurse(e))).collect()
}
*/

/// Typechecks a single expression, returning a single typed ast node.
pub fn typecheck_expr<Tv: Variable, Cv: Variable>(
    state: TypecheckState<Tv, Cv>,
    raw: Ctx<RawExpr>,
) -> CtxResult<(Expr<Tv, Cv>, TypeFacts<Tv, Cv>)> {
    let recurse = |c| typecheck_expr(state.clone(), c);
    let ctx = raw.ctx();
    match raw.deref().clone() {
        RawExpr::Let(binds, body) => {
            let mut checked_binds: List<(Symbol, Expr<Tv, Cv>)> = List::new();
            let mut final_state = state.clone();
            for (var, val) in binds.into_iter() {
                let checked_val = typecheck_expr(final_state.clone(), val)?;
                final_state = final_state.bind_var(*var, checked_val.0.itype.clone());
                checked_binds.push((*var.deref(), checked_val.0));
            }

            let body = typecheck_expr(final_state, body)?;
            let type_facts = checked_binds
                .iter()
                .map(|t| t.0)
                .fold(body.1, |acc, var| acc.clear_mapping(var));

            Ok((
                Expr {
                    itype: body.0.itype.clone(),
                    inner: ExprInner::Let(
                        checked_binds
                            .into_iter()
                            .map(|(v, e)| (v, e.into()))
                            .collect(),
                        body.0.into(),
                    ),
                },
                type_facts,
            ))
        }
        RawExpr::If(c, x, y) => {
            let (c, c_facts) = recurse(c)?;
            let not_c_facts = c_facts.clone().negate_against(&state);
            let (x, x_facts) = typecheck_expr(state.clone().with_facts(&c_facts), x)?;
            let (y, y_facts) = typecheck_expr(state.clone().with_facts(&not_c_facts), y)?;
            // okay, so here's the deal.
            // "if c then x else y" is true implies either "c && x" is true, or "!c && y" is true.
            // unfortunately, we cannot really express "or" in typefacts form.
            // thus, we check if one of the branches is totally false (this is the case when this "if" is autogenerated from && or ||)
            // then we take the other branch.
            let result_facts = if x.itype.always_falsy() {
                not_c_facts.union(y_facts)
            } else if y.itype.always_falsy() {
                c_facts.union(x_facts)
            } else {
                TypeFacts::empty()
            };
            Ok((
                Expr {
                    itype: x.itype.smart_union(&y.itype),
                    inner: ExprInner::If(c.into(), x.into(), y.into()),
                },
                result_facts,
            ))
        }
        RawExpr::BinOp(op, a, b) => {
            let a_expr = recurse(a.clone()).map(|a| a.0);
            let b_expr = recurse(b.clone()).map(|a| a.0);
            let op = *op.deref();
            // both must be numbers
            let check_nats = || {
                let a_expr = a_expr.as_ref().map_err(|e| e.clone())?;
                let b_expr = b_expr.as_ref().map_err(|e| e.clone())?;
                assert_subtype(ctx, &a_expr.itype, &Type::all_nat())?;
                assert_subtype(ctx, &b_expr.itype, &Type::all_nat())?;
                let template: Type<Void, i32> =
                    Type::NatRange(ConstExpr::Var(0), ConstExpr::Var(1));
                let mut a_range = template.unify_cvars(&a_expr.itype).unwrap();
                let mut b_range = template.unify_cvars(&b_expr.itype).unwrap();

                // TODO figure out why this happens at all
                if !a_range.contains_key(&0) || !a_range.contains_key(&1) {
                    a_range.insert(0, ConstExpr::Lit(U256::ZERO));
                    a_range.insert(1, ConstExpr::Lit(U256::MAX));
                }
                if !b_range.contains_key(&0) || !b_range.contains_key(&1) {
                    b_range.insert(0, ConstExpr::Lit(U256::ZERO));
                    b_range.insert(1, ConstExpr::Lit(U256::MAX));
                }

                Ok::<_, CtxErr>((a_range, b_range))
            };
            match op {
                crate::grammar::BinOp::Add => {
                    let (a_range, b_range) = check_nats()?;
                    if a_range.len() == 2 && b_range.len() == 2 {
                        log::trace!("a_range = {:?}, b_range = {:?}", a_range, b_range);
                        // add the two ranges
                        let lower_bound =
                            ConstExpr::Add(a_range[&0].clone().into(), b_range[&0].clone().into())
                                .simplify();
                        let upper_bound =
                            ConstExpr::Add(a_range[&1].clone().into(), b_range[&1].clone().into())
                                .simplify();
                        Ok((
                            Expr {
                                itype: Type::NatRange(lower_bound, upper_bound).fix_natrange(),
                                inner: ExprInner::BinOp(BinOp::Add, a_expr?.into(), b_expr?.into()),
                            },
                            TypeFacts::empty(),
                        ))
                    } else {
                        Ok((
                            Expr {
                                itype: Type::all_nat(),
                                inner: ExprInner::BinOp(BinOp::Add, a_expr?.into(), b_expr?.into()),
                            },
                            TypeFacts::empty(),
                        ))
                    }
                }
                crate::grammar::BinOp::Sub => {
                    check_nats()?;
                    // cannot subtract CGs correctly at the moment
                    Ok((
                        Expr {
                            itype: Type::all_nat(),
                            inner: ExprInner::BinOp(BinOp::Sub, a_expr?.into(), b_expr?.into()),
                        },
                        TypeFacts::empty(),
                    ))
                }
                crate::grammar::BinOp::Mul => {
                    let (a_range, b_range) = check_nats()?;
                    // add the two ranges
                    let lower_bound =
                        ConstExpr::Mul(a_range[&0].clone().into(), b_range[&0].clone().into())
                            .simplify();
                    let upper_bound =
                        ConstExpr::Mul(a_range[&1].clone().into(), b_range[&1].clone().into())
                            .simplify();
                    Ok((
                        Expr {
                            itype: Type::NatRange(lower_bound, upper_bound).fix_natrange(),
                            inner: ExprInner::BinOp(BinOp::Mul, a_expr?.into(), b_expr?.into()),
                        },
                        TypeFacts::empty(),
                    ))
                }
                // cannot divide CGs correctly at the moment
                crate::grammar::BinOp::Div => {
                    check_nats()?;
                    Ok((
                        Expr {
                            itype: Type::all_nat(),
                            inner: ExprInner::BinOp(BinOp::Div, a_expr?.into(), b_expr?.into()),
                        },
                        TypeFacts::empty(),
                    ))
                }
                crate::grammar::BinOp::Mod => {
                    check_nats()?;
                    Ok((
                        Expr {
                            itype: Type::all_nat(),
                            inner: ExprInner::BinOp(BinOp::Mod, a_expr?.into(), b_expr?.into()),
                        },
                        TypeFacts::empty(),
                    ))
                }
                crate::grammar::BinOp::Eq => {
                    check_nats()?;
                    Ok((
                        Expr {
                            itype: Type::NatRange(0u32.into(), 1u32.into()),
                            inner: ExprInner::BinOp(BinOp::Eq, a_expr?.into(), b_expr?.into()),
                        },
                        TypeFacts::empty(),
                    ))
                }
                crate::grammar::BinOp::Lt => {
                    check_nats()?;
                    Ok((
                        Expr {
                            itype: Type::NatRange(0u32.into(), 1u32.into()),
                            inner: ExprInner::BinOp(BinOp::Lt, a_expr?.into(), b_expr?.into()),
                        },
                        TypeFacts::empty(),
                    ))
                }
                crate::grammar::BinOp::Le => {
                    check_nats()?;
                    Ok((
                        Expr {
                            itype: Type::NatRange(0u32.into(), 1u32.into()),
                            inner: ExprInner::BinOp(BinOp::Le, a_expr?.into(), b_expr?.into()),
                        },
                        TypeFacts::empty(),
                    ))
                }
                crate::grammar::BinOp::Gt => {
                    check_nats()?;
                    Ok((
                        Expr {
                            itype: Type::NatRange(0u32.into(), 1u32.into()),
                            inner: ExprInner::BinOp(BinOp::Gt, a_expr?.into(), b_expr?.into()),
                        },
                        TypeFacts::empty(),
                    ))
                }
                crate::grammar::BinOp::Ge => {
                    check_nats()?;
                    Ok((
                        Expr {
                            itype: Type::NatRange(0u32.into(), 1u32.into()),
                            inner: ExprInner::BinOp(BinOp::Ge, a_expr?.into(), b_expr?.into()),
                        },
                        TypeFacts::empty(),
                    ))
                }
                crate::grammar::BinOp::Append => {
                    // vector append
                    let a_expr = a_expr?;
                    let b_expr = b_expr?;
                    Ok((
                        Expr {
                            itype: a_expr
                                .itype
                                .append(&b_expr.itype)
                                .context(format!(
                                    "cannot append values of types {:?} and {:?}",
                                    a_expr.itype, b_expr.itype
                                ))
                                .err_ctx(ctx)?,
                            inner: ExprInner::BinOp(BinOp::Append, a_expr.into(), b_expr.into()),
                        },
                        TypeFacts::empty(),
                    ))
                }
                crate::grammar::BinOp::Lor => {
                    // Desugar!
                    let desugared =
                        RawExpr::If(a, RawExpr::LitNum(1u32.into()).into(), b).with_ctx(ctx);
                    recurse(desugared)
                }
                crate::grammar::BinOp::Land => {
                    // Desugar!
                    let desugared =
                        RawExpr::If(a, b, RawExpr::LitNum(0u32.into()).into()).with_ctx(ctx);
                    recurse(desugared)
                }
                crate::grammar::BinOp::Lshift => {
                    check_nats()?;
                    Ok((
                        Expr {
                            itype: Type::all_nat(),
                            inner: ExprInner::BinOp(BinOp::Lshift, a_expr?.into(), b_expr?.into()),
                        },
                        TypeFacts::empty(),
                    ))
                }
                crate::grammar::BinOp::Rshift => {
                    check_nats()?;
                    Ok((
                        Expr {
                            itype: Type::all_nat(),
                            inner: ExprInner::BinOp(BinOp::Rshift, a_expr?.into(), b_expr?.into()),
                        },
                        TypeFacts::empty(),
                    ))
                }
                crate::grammar::BinOp::Bor => {
                    check_nats()?;
                    Ok((
                        Expr {
                            itype: Type::all_nat(),
                            inner: ExprInner::BinOp(BinOp::Bor, a_expr?.into(), b_expr?.into()),
                        },
                        TypeFacts::empty(),
                    ))
                }
                crate::grammar::BinOp::Band => {
                    check_nats()?;
                    Ok((
                        Expr {
                            itype: Type::all_nat(),
                            inner: ExprInner::BinOp(BinOp::Band, a_expr?.into(), b_expr?.into()),
                        },
                        TypeFacts::empty(),
                    ))
                }
                crate::grammar::BinOp::Bxor => {
                    check_nats()?;
                    Ok((
                        Expr {
                            itype: Type::all_nat(),
                            inner: ExprInner::BinOp(BinOp::Bxor, a_expr?.into(), b_expr?.into()),
                        },
                        TypeFacts::empty(),
                    ))
                }
            }
        }
        RawExpr::UniOp(op, a) => {
            let a_expr = recurse(a.clone()).map(|a| a.0);
            let op = *op.deref();

            // expr must be a number
            let check_nat = || {
                let a_expr = a_expr.as_ref().map_err(|e| e.clone())?;
                assert_subtype(ctx, &a_expr.itype, &Type::all_nat())?;
                let template: Type<Void, i32> =
                    Type::NatRange(ConstExpr::Var(0), ConstExpr::Var(1));
                let a_range = template.unify_cvars(&a_expr.itype).unwrap();
                Ok::<_, CtxErr>(a_range)
            };
            match op {
                crate::grammar::UniOp::Bnot => {
                    check_nat()?;
                    Ok((
                        Expr {
                            itype: Type::all_nat(),
                            inner: ExprInner::UniOp(UniOp::Bnot, a_expr?.into()),
                        },
                        TypeFacts::empty(),
                    ))
                }
                crate::grammar::UniOp::Lnot => {
                    let desugared = RawExpr::If(
                        a,
                        RawExpr::LitNum(0u32.into()).into(),
                        RawExpr::LitNum(1u32.into()).into(),
                    )
                    .with_ctx(ctx);
                    recurse(desugared)
                }
            }
        }
        RawExpr::LitNum(num) => Ok((
            Expr {
                itype: Type::NatRange(num.into(), num.into()),
                inner: ExprInner::LitNum(num),
            },
            TypeFacts::empty(),
        )),
        RawExpr::Var(v) => {
            let itype = state
                .lookup_var(v)
                .context("undefined variable")
                .err_ctx(ctx)?;
            // Here we at least know that the variable is *NOT* false if expression is true.
            Ok((
                Expr {
                    itype: itype.clone(),
                    inner: ExprInner::Var(v),
                },
                TypeFacts::empty().with_mapping(
                    v,
                    itype
                        .subtract(&Type::NatRange(0u32.into(), 0u32.into()))
                        .into_owned(),
                ),
            ))
        }
        RawExpr::Apply(f, args) => {
            if let RawExpr::Var(f) = f.deref() {
                let ftype = state
                    .lookup_fun(*f)
                    .context(format!("undefined function: {:?}", f))
                    .err_ctx(ctx)?;
                if ftype.args.len() != args.len() {
                    Err(anyhow::anyhow!(
                        "calling function {} with the wrong arity (expected {}, got {})",
                        f,
                        ftype.args.len(),
                        args.len()
                    )
                    .with_ctx(ctx))
                } else {
                    // create a mapping for the CG-vars
                    let typechecked_args = args
                        .iter()
                        .map(|a| Ok(recurse(a.clone())?.0))
                        .collect::<CtxResult<List<_>>>()?;
                    let generic_mapping = ftype
                        .args
                        .iter()
                        .zip(typechecked_args.iter())
                        .map(|(arg_type, arg)| {
                            let actual_arg_type = arg.itype.clone();
                            arg_type.unify_tvars(&actual_arg_type).unwrap_or_default()
                        })
                        .reduce(|a, b| a.union_with(b, |a, b| a.smart_union(&b)))
                        .unwrap_or_default();
                    let cg_mapping = ftype
                        .args
                        .iter()
                        .zip(typechecked_args.iter())
                        .map(|(arg_type, arg)| {
                            let actual_arg_type = arg.itype.clone();
                            arg_type.unify_cvars(&actual_arg_type).unwrap_or_default()
                        })
                        .reduce(|a, b| a.union_with(b, |a, _| a))
                        .unwrap_or_default();
                    for (arg, required_type) in typechecked_args.iter().zip(ftype.args.iter()) {
                        let required_type = required_type
                            .try_fill_tvars(|tv| generic_mapping.get(tv).cloned())
                            .and_then(|t| t.try_fill_cvars(|cv| cg_mapping.get(cv).cloned()))
                            .context(format!(
                                "cannot fill type variables in argument type {:?}, given concrete {:?}",
                                required_type,
                                arg.itype
                            ))
                            .err_ctx(ctx)?;
                        if !arg.itype.subtype_of(&required_type) {
                            return Err(anyhow::anyhow!(
                                "argument of type {:?} instead of required {:?}",
                                arg.itype,
                                required_type
                            )
                            .with_ctx(ctx));
                        }
                    }
                    Ok((
                        Expr {
                            itype: ftype
                                .result
                                .try_fill_tvars(|tv| generic_mapping.get(tv).cloned())
                                .and_then(|t| t.try_fill_cvars(|cv| cg_mapping.get(cv).cloned()))
                                .context(format!(
                                    "cannot fill type variables in result type {:?}",
                                    ftype.result
                                ))
                                .err_ctx(ctx)?,
                            inner: if generic_mapping.is_empty() && cg_mapping.is_empty() {
                                ExprInner::Apply(*f, typechecked_args)
                            } else {
                                ExprInner::ApplyGeneric(
                                    *f,
                                    generic_mapping,
                                    cg_mapping,
                                    typechecked_args,
                                )
                            },
                        },
                        TypeFacts::empty(),
                    ))
                }
            } else {
                Err(
                    anyhow::anyhow!("cannot call anything other than a function literal")
                        .with_ctx(ctx),
                )
            }
        }
        RawExpr::Field(a, f) => {
            let a = recurse(a)?.0;
            if let Type::Struct(_, fields) = a.itype.clone() {
                let idx = fields
                    .iter()
                    .enumerate()
                    .find(|(_, (s, _))| *s == *f)
                    .map(|a| (a.0, a.1 .1.clone()));
                if let Some((idx, t)) = idx {
                    return Ok((
                        Expr {
                            itype: t,
                            inner: ExprInner::VectorRef(
                                a.into(),
                                Expr {
                                    itype: Type::all_nat(),
                                    inner: ExprInner::LitNum((idx as u64).into()),
                                }
                                .into(),
                            ),
                        },
                        TypeFacts::empty(),
                    ));
                }
            }
            Err(
                anyhow::anyhow!("value of type {:?} has no field named {:?}", a.itype, f)
                    .with_ctx(f.ctx()),
            )
        }
        RawExpr::VectorRef(v, i) => {
            let (v, _) = recurse(v)?;
            let (i, _) = recurse(i)?;
            let restype = type_vector_ref(&v.itype, &i.itype)
                .or_else(|_| type_bytes_ref(&v.itype, &i.itype))
                .err_ctx(ctx)?;
            Ok((
                Expr {
                    itype: restype,
                    inner: ExprInner::VectorRef(v.into(), i.into()),
                },
                TypeFacts::empty(),
            ))
        }
        RawExpr::VectorUpdate(v, i, x) => {
            let (v, _) = recurse(v)?;
            let (i, _) = recurse(i)?;
            let (x, _) = recurse(x)?;
            // "pretend" to index to ensure the vector is of the right length
            let at_i = type_vector_ref(&v.itype, &i.itype)?;
            if !x.itype.subtype_of(&at_i) {
                Err(anyhow::anyhow!("cannot update vector of type {:?} at position of type {:?} with incompatible type {:?}", v.itype, i.itype, x.itype).with_ctx(ctx))
            } else {
                Ok((
                    Expr {
                        itype: v.itype.clone(),
                        inner: ExprInner::VectorUpdate(v.into(), i.into(), x.into()),
                    },
                    TypeFacts::empty(),
                ))
            }
        }
        RawExpr::IsType(x, y) => {
            let orig_type = state
                .lookup_var(x)
                .context("undefined variable")
                .err_ctx(ctx)?;
            let t = typecheck_type_expr(&state, y)?;
            if !t.subtype_of(&orig_type) {
                return Err(anyhow::anyhow!(
                    "type check always fails because {:?} is not a subtype of {:?}",
                    t,
                    orig_type
                )
                .with_ctx(ctx));
            }
            Ok((
                Expr {
                    itype: Type::NatRange(0_i32.into(), 1_i32.into()),
                    inner: ExprInner::IsType(x, t.clone()),
                },
                TypeFacts::empty().with_mapping(x, t),
            ))
        }
        RawExpr::AsType(inner, t) => {
            let (inner, inner_facts) = recurse(inner)?;
            let t = typecheck_type_expr(&state, t)?;
            if !inner.itype.subtype_of(&t) {
                Err(anyhow::anyhow!(
                    "cannot cast type {:?} to non-supertype {:?}",
                    inner.itype,
                    t
                )
                .with_ctx(ctx))
            } else {
                Ok((
                    Expr {
                        itype: t,
                        inner: inner.inner,
                    },
                    inner_facts,
                ))
            }
        }
        RawExpr::LitVec(vv) => {
            let vv: CtxResult<List<_>> = vv.into_iter().map(|a| Ok(recurse(a)?.0)).collect();
            let vv = vv?;
            Ok((
                Expr {
                    itype: Type::Vector(vv.iter().map(|v| v.itype.clone()).collect()),
                    inner: ExprInner::LitVec(vv),
                },
                TypeFacts::empty(),
            ))
        }
        RawExpr::CgVar(cgv) => {
            let maps_to = state
                .lookup_cgvar(cgv)
                .context(format!("undefined constant-generic variable {:?}", cgv))
                .err_ctx(ctx)?;
            Ok((
                Expr {
                    itype: Type::NatRange(maps_to.clone(), maps_to.clone()),
                    inner: ExprInner::LitConst(maps_to),
                },
                TypeFacts::empty(),
            ))
        }
        RawExpr::VectorSlice(v, l, r) => {
            // TODO: producing vectors with uncertain lengths
            // TODO: special-case when v is a written-out vector and l and r are both constants
            let v = recurse(v)?.0;
            let v_length =
                Type::<Void, Symbol>::Vectorof(Type::Any.into(), ConstExpr::Var(Symbol::from("n")))
                    .unify_cvars(&v.itype)
                    .and_then(|h| h.get(&Symbol::from("n")).cloned())
                    .context(format!("type {:?} cannot be sliced into", &v.itype))?;
            let l = recurse(l)?.0;
            let r = recurse(r)?.0;
            let l_num = Type::NatRange::<Void, Symbol>(
                ConstExpr::Var(Symbol::from("a")),
                ConstExpr::Var(Symbol::from("a")),
            )
            .unify_cvars(&l.itype)
            .and_then(|h| h.get(&Symbol::from("a")).cloned());
            let r_num = Type::NatRange::<Void, Symbol>(
                ConstExpr::Var(Symbol::from("a")),
                ConstExpr::Var(Symbol::from("a")),
            )
            .unify_cvars(&r.itype)
            .and_then(|h| h.get(&Symbol::from("a")).cloned());
            if let (Some(l_num), Some(r_num)) = (l_num, r_num) {
                if !l_num.leq(&r_num) {
                    Err(anyhow::anyhow!(
                        "left bound of vector slice {:?} is bigger than right bound {:?}",
                        l_num,
                        r_num
                    )
                    .with_ctx(ctx))
                } else if !r_num.leq(&v_length) {
                    Err(anyhow::anyhow!(
                        "right bound of vector slice {:?} is too big for vector of length {:?}",
                        r_num,
                        v_length
                    )
                    .with_ctx(ctx))
                } else {
                    let new_length = r_num
                        .checked_sub(&l_num)
                        .context(format!(
                            "cannot subtract {:?} - {:?} to compute length of sliced vector",
                            r_num, l_num
                        ))
                        .err_ctx(ctx)?;
                    Ok((
                        Expr {
                            itype: Type::Vectorof(
                                v.itype.index(None).unwrap().into_owned().into(),
                                new_length,
                            ),
                            inner: ExprInner::VectorSlice(v.into(), l.into(), r.into()),
                        },
                        TypeFacts::empty(),
                    ))
                }
            } else {
                Err(anyhow::anyhow!(
                    "cannot resolve slice indices (of types {:?} and {:?}) to single numbers",
                    l.itype,
                    r.itype
                )
                .with_ctx(ctx))
            }
        }
        RawExpr::LitStruct(name, fields) => {
            let stype = state
                .lookup_type_alias(name)
                .context(format!("undefined struct type {:?}", name))
                .err_ctx(ctx)?;
            if let Type::Struct(_, ifields) = &stype {
                if fields.len() != ifields.len() {
                    Err(anyhow::anyhow!(
                        "struct {:?} needs {} fields, got {} instead",
                        name,
                        ifields.len(),
                        fields.len()
                    )
                    .with_ctx(ctx))
                } else {
                    let args = ifields.iter().map(|(fname, correct_t)| {
                        let actual = recurse(fields[fname].clone())?.0;
                        if !actual.itype.subtype_of(correct_t) {
                            Err(anyhow::anyhow!("field {:?}.{:?} must be of type {:?}, but given a value of type {:?}", name, fname, correct_t, actual.itype).with_ctx(fields[fname].ctx()))
                        } else {
                            Ok(actual)
                        }
                    }).collect::<CtxResult<List<_>>>()?;
                    Ok((
                        Expr {
                            itype: stype.clone(),
                            inner: ExprInner::LitVec(args),
                        },
                        TypeFacts::empty(),
                    ))
                }
            } else {
                Err(anyhow::anyhow!(
                    "type {:?} is not a struct and can't be instantiated like one",
                    name
                )
                .with_ctx(ctx))
            }
        }
        RawExpr::Exp(a, b) => {
            // TODO infer this from b
            let k = ConstExpr::Lit(255_u32.into());
            let a: std::sync::Arc<Expr<Tv, Cv>> = recurse(a)?.0.into();
            let b = typecheck_const_expr(&state, b)?;

            // Check that a is Nat
            assert_subtype(ctx, &a.itype, &Type::all_nat())?;
            /*
            let template: Type<Void, i32> =
                Type::NatRange(ConstExpr::Var(0), ConstExpr::Var(1));
            let a_range = template.unify_cvars(&a_expr.itype).unwrap();
            */

            Ok((
                Expr {
                    itype: a.itype.clone(),
                    inner: ExprInner::Exp(k, a, b),
                },
                TypeFacts::empty(),
            ))
        }
        RawExpr::Loop(iterations, body, end) => {
            let iterations = typecheck_const_expr(&state, iterations)?;
            //let free_vars = body.iter().map(|(sym, val)| val.free_variables(state.var_scope()));
            let var_scope = state.var_scope();
            let free_vars = body.iter().fold(Set::new(), |acc, (sym, val)| {
                acc.union(val.free_variables(&var_scope).update(*sym))
            });

            let body = body
                .into_iter()
                .map(|(s, v)| {
                    let ctx = v.ctx();
                    let v = recurse(v)?.0;
                    let s_type = state
                        .lookup_var(s)
                        .context(format!("assigning to undefined variable {:?}", s))
                        .err_ctx(ctx)?;
                    if !v.itype.subtype_of(&s_type) {
                        Err(anyhow::anyhow!("assigning value of incompatible type {:?} to variable {:?} of type {:?}", v.itype, s, s_type).with_ctx(ctx))
                    } else {
                        Ok((s, v))
                    }
                })
                .collect::<CtxResult<List<_>>>()?;
            let end = recurse(end)?.0;
            Ok((
                Expr {
                    itype: end.itype.clone(),
                    //inner: ExprInner::Loop(iterations, body, end.into()),
                    inner: ExprInner::Let(
                        free_vars
                            .into_iter()
                            .map(|sym| {
                                (
                                    sym,
                                    Expr {
                                        itype: state.lookup_var(sym).expect(
                                            "Expected binding to be available, this is a bug.",
                                        ),
                                        inner: ExprInner::Var(sym),
                                    }
                                    .into(),
                                )
                            })
                            .collect(),
                        Expr {
                            itype: end.itype.clone(),
                            inner: ExprInner::Loop(iterations, body, end.into()),
                        }
                        .into(),
                    ),
                },
                TypeFacts::empty(),
            ))
        }
        RawExpr::Fail => Ok((
            Expr {
                inner: ExprInner::Fail,
                itype: Type::Nothing,
            },
            TypeFacts::empty(),
        )),
        RawExpr::For(sym, val, body) => {
            let val = recurse(val)?.0;
            let (val_inner_length, val_inner_type) = vector_info(&val).err_ctx(ctx)?;
            log::debug!(
                "recursing inside for expression while binding {:?}={:?}",
                sym,
                val_inner_type
            );
            let body = typecheck_expr(state.bind_var(*sym, val_inner_type.clone()), body)?.0;
            let temp_counter = Symbol::generate("@for-counter");
            let temp_result = Symbol::generate("@for-result");
            let result_type = Type::Vectorof(body.itype.clone().into(), val_inner_length.clone());
            // desugar into a loop
            // let counter = 0 in
            // let result = $val in
            // loop $val_length
            //   set! result = let $sym = result[counter] in result[counter => $body]
            //   set! counter = counter + 1
            // done with result
            Ok((
                Expr {
                    inner: ExprInner::Let(
                        [(
                            temp_counter,
                            ExprInner::LitNum(0u32.into()).wrap(Type::all_nat()).into(),
                        )]
                        .into(),
                        ExprInner::Let(
                            [(temp_result, val.clone().into())].into(),
                            ExprInner::Loop(
                                val_inner_length,
                                [
                                    (
                                        temp_result,
                                        ExprInner::Let(
                                            [(
                                                *sym,
                                                ExprInner::VectorRef(
                                                    ExprInner::Var(temp_result)
                                                        .wrap(val.itype.clone())
                                                        .into(),
                                                    ExprInner::Var(temp_counter)
                                                        .wrap(Type::all_nat())
                                                        .into(),
                                                )
                                                .wrap(val_inner_type)
                                                .into(),
                                            )]
                                            .into(),
                                            ExprInner::VectorUpdate(
                                                ExprInner::Var(temp_result).wrap(val.itype).into(),
                                                ExprInner::Var(temp_counter)
                                                    .wrap(Type::all_nat())
                                                    .into(),
                                                body.into(),
                                            )
                                            .wrap(result_type.clone())
                                            .into(),
                                        )
                                        .wrap(result_type.clone()),
                                    ),
                                    (
                                        temp_counter,
                                        ExprInner::BinOp(
                                            BinOp::Add,
                                            ExprInner::Var(temp_counter)
                                                .wrap(Type::all_nat())
                                                .into(),
                                            ExprInner::LitNum(1u32.into())
                                                .wrap(Type::all_nat())
                                                .into(),
                                        )
                                        .wrap(Type::all_nat()),
                                    ),
                                ]
                                .into_iter()
                                .collect(),
                                ExprInner::Var(temp_result).wrap(result_type.clone()).into(),
                            )
                            .wrap(result_type.clone())
                            .into(),
                        )
                        .wrap(result_type.clone())
                        .into(),
                    ),
                    itype: result_type,
                },
                TypeFacts::empty(),
            ))
        }
        RawExpr::Transmute(inner, t) => {
            if state.lookup_safety() {
                Err(anyhow::anyhow!("cannot transmute without unsafe").with_ctx(ctx))
            } else {
                let mut inner = recurse(inner)?;
                let t = typecheck_type_expr(&state, t)?;
                inner.0.itype = t;
                Ok(inner)
            }
        }
        RawExpr::ForFold(var_name, var_binding, accum_name, accum_binding, body) => {
            // First, we try the "easy" case, where the body has, straightforwardly, the same type as the accum
            let init_accum = recurse(accum_binding)?.0;
            let iterating_list = recurse(var_binding)?.0;
            let (list_length, list_inner_type) = vector_info(&iterating_list)?;
            let body_easy_case = typecheck_expr(
                state
                    .clone()
                    .bind_var(*var_name, list_inner_type.clone())
                    .bind_var(*accum_name, init_accum.itype.clone()),
                body.clone(),
            )?
            .0;
            let loop_body: Expr<Tv, Cv>;
            let result_type: Type<Tv, Cv>;
            if body_easy_case.itype.subtype_of(&init_accum.itype) {
                log::trace!("**EASY** case for folds");
                loop_body = body_easy_case;
                result_type = init_accum.itype.clone();
            } else {
                log::trace!("**HARD** case for folds");
                // Then, the tricky, "inference" case. We "const-genericize" the accumulator, replacing every position where we *can* place a const-generic parameter with a const-generic parameter. For example, [Nat; 0] becomes [{$n..$m}; $q].
                let new_cgvars = DashSet::new();
                let init_accum_cgified = cgify_all_slots(&init_accum.itype, || {
                    let v = Cv::try_from_sym(Symbol::generate("@g")).unwrap();
                    new_cgvars.insert(v.clone());
                    v
                });
                let cgification_mapping =
                    init_accum_cgified.unify_cvars(&init_accum.itype).unwrap();
                // Then, we typecheck the body, binding the accumulator variable to the const-genericized type above.
                let cgified_body = typecheck_expr(
                    state
                        .bind_var(*var_name, list_inner_type.clone())
                        .bind_var(*accum_name, init_accum_cgified.clone()),
                    body,
                )?
                .0;
                // We then unify the body with the const-genericized accumulator type. For example, we may get [{$n+1..$m+1}; $q+1]
                let pre_post_mapping = init_accum_cgified.unify_cvars(&cgified_body.itype).context(format!("cannot unify pre-iteration accumulator type {:?} with post-iteration accumulator type {:?}", init_accum_cgified, cgified_body.itype))?;
                log::trace!(
                    "pre-iteration {:?}, post-iteration {:?}, mapping {:?}",
                    init_accum_cgified,
                    cgified_body.itype,
                    pre_post_mapping
                );
                if !cgified_body
                    .itype
                    .subtype_of(&init_accum_cgified.fill_cvars(|c| {
                        pre_post_mapping
                            .get(c)
                            .cloned()
                            .unwrap_or_else(|| ConstExpr::Var(c.clone()))
                    }))
                {
                    return Err(anyhow::anyhow!(
                        "post-iteration type {:?} fundamentally incompatible wth pre-iteration type {:?}",
                        cgified_body.itype,
                        init_accum_cgified
                    )
                    .with_ctx(ctx));
                }
                let all_the_way_mapping = pre_post_mapping
                    .into_iter()
                    .map(|(k, v)| {
                        Ok((
                            k.clone(),
                            solve_recurrence(
                                cgification_mapping[&k].clone(),
                                k,
                                v,
                                list_length.clone(),
                            )
                            .err_ctx(ctx)?,
                        ))
                    })
                    .collect::<CtxResult<Map<_, _>>>()?;
                // Each unification binding then lets us calculate the final type. Each binding is of the form
                //    $n => (some expression that contains $n, say 2*$n+1)
                // if the RHS contains any variable other than $n, we fail.
                // The "diff" each time is then RHS - LHS. If this fails, we fail too.
                let erased_body = cgified_body.recursive_map(|mut x| {
                    x.itype = partially_erase_cg(&x.itype, |c| new_cgvars.contains(c));
                    x
                });
                loop_body = erased_body;
                result_type = init_accum_cgified.fill_cvars(|c| {
                    if let Some(r) = all_the_way_mapping.get(c) {
                        r.clone()
                    } else {
                        ConstExpr::Var(c.clone())
                    }
                });
                log::trace!("result_type is {:?}", result_type);
            }
            // desugar into a loop
            // let input = $val in
            // let counter = 0 in
            // let accum = $init_accum in
            // loop $val_length
            //   set! accum = let $sym = input[counter] in $body
            //   set! counter = counter + 1
            // done with accum
            use ExprInner::*;
            let temp_counter = Symbol::generate("@fold-counter");
            let temp_input = Symbol::generate("@fold-input");
            let loop_inner: List<(Symbol, Expr<Tv, Cv>)> = [
                (
                    *accum_name,
                    ExprInner::Let(
                        [(
                            *var_name,
                            ExprInner::VectorRef(
                                ExprInner::Var(temp_input)
                                    .wrap(iterating_list.itype.clone())
                                    .into(),
                                ExprInner::Var(temp_counter).wrap(Type::all_nat()).into(),
                            )
                            .wrap(list_inner_type)
                            .into(),
                        )]
                        .into(),
                        loop_body.into(),
                    )
                    .wrap_any(),
                ),
                (
                    temp_counter,
                    ExprInner::BinOp(
                        crate::typed_ast::BinOp::Add,
                        Var(temp_counter).wrap(Type::all_nat()).into(),
                        LitNum(1u32.into()).wrap(Type::all_nat()).into(),
                    )
                    .wrap(Type::all_nat()),
                ),
            ]
            .into_iter()
            .collect();
            Ok((
                Let(
                    [
                        (temp_input, iterating_list.into()),
                        //Let(
                        (
                            temp_counter,
                            LitNum(0u32.into()).wrap(Type::all_nat()).into(),
                        ),
                        //Let(
                        (*accum_name, init_accum.into()),
                    ]
                    .into(),
                    Loop(
                        list_length,
                        loop_inner,
                        Var(*accum_name).wrap(result_type.clone()).into(),
                    )
                    .wrap(result_type.clone())
                    .into(),
                )
                .wrap(result_type),
                TypeFacts::empty(),
            ))
        }
        RawExpr::LitBytes(b) => {
            let blen = b.len().into();
            Ok((
                ExprInner::LitBytes(b).wrap(Type::Bytes(blen)),
                TypeFacts::empty(),
            ))
        }
        RawExpr::LitBVec(vv) => {
            let args = vv
                .into_iter()
                .map(|arg| {
                    let ctx = arg.ctx();
                    let arg = recurse(arg)?.0;
                    if !arg
                        .itype
                        .subtype_of(&Type::NatRange(0_i32.into(), 255_i32.into()))
                    {
                        Err(anyhow::anyhow!(
                            "element in bytes must be byte-valued, got {:?} instead",
                            arg.itype
                        )
                        .with_ctx(ctx))
                    } else {
                        Ok(arg)
                    }
                })
                .collect::<CtxResult<List<_>>>()?;
            let itype = Type::Bytes(args.len().into());
            Ok((ExprInner::LitBVec(args).wrap(itype), TypeFacts::empty()))
        }
        RawExpr::Unsafe(s) => typecheck_expr(state.bind_safety(false), s),
        RawExpr::Extern(ext) => {
            if state.lookup_safety() {
                return Err(
                    anyhow::anyhow!("cannot use an external variable without unsafe").with_ctx(ctx),
                );
            }
            Ok((
                ExprInner::Extern(ext.deref().clone()).wrap_any(),
                TypeFacts::empty(),
            ))
        }
        RawExpr::ExternApply(f, args) => {
            if state.lookup_safety() {
                return Err(
                    anyhow::anyhow!("cannot call an external function without unsafe")
                        .with_ctx(ctx),
                );
            }
            let args = args
                .into_iter()
                .map(|f| Ok(recurse(f)?.0))
                .collect::<CtxResult<List<_>>>()?;
            Ok((
                ExprInner::ExternApply(f.deref().clone(), args).wrap_any(),
                TypeFacts::empty(),
            ))
        }
    }
}

fn vector_info<Tv: Variable, Cv: Variable>(
    val: &Expr<Tv, Cv>,
) -> anyhow::Result<(ConstExpr<Cv>, Type<Tv, Cv>)> {
    let val_lengths = val.itype.lengths();
    if val_lengths.len() == 1 {
        Ok((
            val_lengths.into_iter().next().unwrap(),
            val.itype.index(None).unwrap().into_owned(),
        ))
    } else {
        return Err(anyhow::anyhow!(
            "list comprehension needs a list with a definite length, got {:?} instead",
            val.itype
        ));
    }
}

fn type_bytes_ref<Tv: Variable, Cv: Variable>(
    vtype: &Type<Tv, Cv>,
    itype: &Type<Tv, Cv>,
) -> anyhow::Result<Type<Tv, Cv>> {
    // first, we unify the vector to [Any; n] in order to get the length
    let v_length = Type::<Void, Symbol>::Bytes(ConstExpr::Var(Symbol::from("n")))
        .unify_cvars(vtype)
        .and_then(|h| h.get(&Symbol::from("n")).cloned())
        .context(format!("type {:?} cannot be indexed into", vtype))?;
    log::trace!("indexing into bytes of length {:?}", v_length);
    // then, we unify the index into a range to see whether it's correct.
    let i_params = Type::<Void, Symbol>::NatRange(
        ConstExpr::Var(Symbol::from("a")),
        ConstExpr::Var(Symbol::from("b")),
    )
    .unify_cvars(itype)
    .unwrap_or_default();
    let i_upper_bound = i_params.get(&Symbol::from("b")).cloned().context(format!(
        "bytes index of type {:?} has no upper bound",
        itype
    ))?;
    if !i_upper_bound.lt(&v_length) {
        Err(anyhow::anyhow!(
            "cannot index into vector {:?} of length {:?} with something of type {:?}",
            vtype,
            v_length,
            itype
        ))
    } else {
        Ok(Type::NatRange(0u32.into(), 255u32.into()))
    }
}

fn type_vector_ref<Tv: Variable, Cv: Variable>(
    vtype: &Type<Tv, Cv>,
    itype: &Type<Tv, Cv>,
) -> anyhow::Result<Type<Tv, Cv>> {
    // first, we unify the vector to [Any; n] in order to get the length
    let v_length =
        Type::<Void, Symbol>::Vectorof(Type::Any.into(), ConstExpr::Var(Symbol::from("n")))
            .unify_cvars(vtype)
            .and_then(|h| h.get(&Symbol::from("n")).cloned())
            .context(format!("type {:?} cannot be indexed into", vtype))?;
    log::trace!("indexing into vector of length {:?}", v_length);
    // then, we unify the index into a range to see whether it's correct.
    let i_params = Type::<Void, Symbol>::NatRange(
        ConstExpr::Var(Symbol::from("a")),
        ConstExpr::Var(Symbol::from("b")),
    )
    .unify_cvars(itype)
    .unwrap_or_default();
    let i_lower_bound = i_params.get(&Symbol::from("a")).cloned().context(format!(
        "vector index of type {:?} has no lower bound",
        itype
    ))?;
    let i_upper_bound = i_params.get(&Symbol::from("b")).cloned().context(format!(
        "vector index of type {:?} has no upper bound",
        itype
    ))?;
    log::debug!(
        "comparing upper bound {:?} to v_length {:?}",
        i_upper_bound,
        v_length
    );
    if !i_upper_bound.lt(&v_length) {
        Err(anyhow::anyhow!(
            "cannot index into vector {:?} of length {:?} with something of type {:?}",
            vtype,
            v_length,
            itype
        ))
    } else {
        Ok(if i_upper_bound.leq(&i_lower_bound) {
            vtype.index(Some(&i_upper_bound)).unwrap().into_owned()
        } else {
            vtype.index(None).unwrap().into_owned()
        })
    }
}

fn typecheck_type_expr<Tv: Variable, Cv: Variable>(
    state: &TypecheckState<Tv, Cv>,
    raw: Ctx<RawTypeExpr>,
) -> CtxResult<Type<Tv, Cv>> {
    match raw.deref().clone() {
        RawTypeExpr::Sym(s) => {
            if s == Symbol::from("Nat") {
                Ok(Type::all_nat())
            } else if s == Symbol::from("Any") {
                Ok(Type::Any)
            } else if s == Symbol::from("Nothing") {
                Ok(Type::Nothing)
            } else {
                state
                    .lookup_type_alias(s)
                    .context(format!("undefined type {}", s))
                    .err_ctx(raw.ctx())
            }
        }
        RawTypeExpr::Union(a, b) => {
            Ok(typecheck_type_expr(state, a)?.smart_union(&typecheck_type_expr(state, b)?))
        }
        RawTypeExpr::Vector(tt) => {
            let processed_tt: CtxResult<List<_>> = tt
                .into_iter()
                .map(|t| typecheck_type_expr(state, t))
                .collect();
            Ok(Type::Vector(processed_tt?))
        }
        RawTypeExpr::Vectorof(t, n) => {
            let t = typecheck_type_expr(state, t)?;
            let n = typecheck_const_expr(state, n)?;
            Ok(Type::Vectorof(t.into(), n))
        }
        RawTypeExpr::NatRange(a, b) => {
            let a = typecheck_const_expr(state, a)?;
            let b = typecheck_const_expr(state, b)?;
            Ok(Type::NatRange(a, b))
        }
        RawTypeExpr::DynVectorof(v) => {
            let v = typecheck_type_expr(state, v)?;
            Ok(Type::DynVectorof(v.into()))
        }
        RawTypeExpr::Bytes(c) => Ok(Type::Bytes(typecheck_const_expr(state, c)?)),
        RawTypeExpr::DynBytes => Ok(Type::DynBytes),
    }
}

fn typecheck_const_expr<Tv: Variable, Cv: Variable>(
    state: &TypecheckState<Tv, Cv>,
    raw: Ctx<RawConstExpr>,
) -> CtxResult<ConstExpr<Cv>> {
    match raw.deref() {
        RawConstExpr::Sym(s) => Ok(state
            .lookup_cgvar(*s)
            .context("no cgvar")
            .err_ctx(raw.ctx())?),
        RawConstExpr::Lit(a) => Ok(ConstExpr::Lit(*a)),
        RawConstExpr::Plus(a, b) => Ok(ConstExpr::Add(
            typecheck_const_expr(state, a.clone())?.into(),
            typecheck_const_expr(state, b.clone())?.into(),
        )),
        RawConstExpr::Mult(a, b) => Ok(ConstExpr::Mul(
            typecheck_const_expr(state, a.clone())?.into(),
            typecheck_const_expr(state, b.clone())?.into(),
        )),
    }
}

/// Monomorphizes a set of function definitions and a "preliminary" body into a fully degenericized version.
///
/// Uses monomorphization for const-generics and type erasure for "normal" generics. But that's unspecified.
pub fn monomorphize(
    fun_defs: List<FunDefn<TypeParam, CgParam>>,
    body: Expr<TypeParam, CgParam>,
) -> Program {
    // The basic idea is to identify all calls to generic functions, replacing them with non-generic calls to generated functions.
    let monomorph_collector = DashMap::new();
    let body = monomorphize_inner(
        &fun_defs.into_iter().map(|fd| (fd.name, fd)).collect(),
        &body,
        &monomorph_collector,
        &Map::new(),
        &Map::new(),
    );
    Program {
        fun_defs: monomorph_collector.into_iter().map(|x| x.1).collect(),
        body,
    }
}

fn monomorphize_inner(
    fun_defs: &Map<Symbol, FunDefn<TypeParam, CgParam>>,
    body: &Expr<TypeParam, CgParam>,
    mangled: &DashMap<Symbol, FunDefn>,
    tvar_scope: &Map<TypeParam, Type>,
    cvar_scope: &Map<CgParam, ConstExpr<Void>>,
) -> Expr {
    let recurse = |b| monomorphize_inner(fun_defs, b, mangled, tvar_scope, cvar_scope);
    Expr {
        inner: match body.inner.clone() {
            ExprInner::UniOp(op, a) => ExprInner::UniOp(op, recurse(&a).into()),
            ExprInner::BinOp(op, a, b) => {
                ExprInner::BinOp(op, recurse(&a).into(), recurse(&b).into())
            }
            ExprInner::If(cond, a, b) => ExprInner::If(
                recurse(&cond).into(),
                recurse(&a).into(),
                recurse(&b).into(),
            ),
            ExprInner::Exp(k, a, b) => ExprInner::Exp(
                k.fill(|c| cvar_scope.get(c).cloned().unwrap()),
                recurse(&a).into(),
                b.fill(|c| cvar_scope.get(c).cloned().unwrap()),
            ),
            ExprInner::Let(binds, i) => ExprInner::Let(
                binds
                    .iter()
                    .map(|(var, val)| (*var, recurse(val).into()))
                    .collect(),
                recurse(&i).into(),
            ),
            ExprInner::Apply(f, args) => {
                // we must monomorphize the function too
                if mangled.get(&f).is_none() {
                    let noo = recurse(&fun_defs.get(&f).unwrap().body);
                    mangled.insert(
                        f,
                        FunDefn {
                            name: f,
                            args: fun_defs.get(&f).unwrap().args.clone(),
                            body: noo,
                        },
                    );
                }
                ExprInner::Apply(f, args.iter().map(recurse).collect())
            }
            ExprInner::ApplyGeneric(f, tvars, cvars, args) => {
                // generate a monomorphized version
                let mangled_name = if tvars.is_empty() && cvars.is_empty() {
                    f
                } else {
                    static MANGLE_COUNT: AtomicUsize = AtomicUsize::new(0);
                    Symbol::from(
                        format!(
                            "{:?}-mm{}",
                            f,
                            MANGLE_COUNT.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
                        )
                        .as_str(),
                    )
                };
                log::trace!("making up a mangled name {:?}!", mangled_name);
                // if we have a monomorphized version already, we just call that.
                // otherwise, we must populate the table now
                if mangled.get(&mangled_name).is_none() {
                    let unmangled_fundef = fun_defs.get(&f).cloned().unwrap();
                    let noo = monomorphize_inner(
                        fun_defs,
                        &unmangled_fundef.body,
                        mangled,
                        &tvar_scope.clone().tap_mut(|tvs| {
                            for (k, v) in tvars.iter() {
                                tvs.insert(
                                    *k,
                                    v.fill_cvars(|c| cvar_scope.get(c).cloned().unwrap())
                                        .fill_tvars(|t| tvar_scope.get(t).cloned().unwrap()),
                                );
                            }
                        }),
                        &cvar_scope.clone().tap_mut(|cvs| {
                            for (k, v) in cvars.iter() {
                                cvs.insert(*k, v.fill(|cv| cvar_scope.get(cv).cloned().unwrap()));
                            }
                        }),
                    );
                    mangled.insert(
                        mangled_name,
                        FunDefn {
                            name: mangled_name,
                            args: unmangled_fundef.args,
                            body: noo,
                        },
                    );
                }
                ExprInner::Apply(mangled_name, args.iter().map(recurse).collect())
            }
            ExprInner::LitNum(v) => ExprInner::LitNum(v),
            ExprInner::LitVec(lv) => ExprInner::LitVec(lv.iter().map(recurse).collect()),
            ExprInner::Var(v) => ExprInner::Var(v),
            ExprInner::IsType(a, b) => ExprInner::IsType(
                a,
                b.fill_cvars(|c| cvar_scope.get(c).cloned().unwrap())
                    .fill_tvars(|t| tvar_scope.get(t).cloned().unwrap()),
            ),
            ExprInner::VectorRef(v, i) => {
                ExprInner::VectorRef(recurse(&v).into(), recurse(&i).into())
            }
            ExprInner::VectorUpdate(v, i, n) => {
                ExprInner::VectorUpdate(recurse(&v).into(), recurse(&i).into(), recurse(&n).into())
            }
            ExprInner::LitConst(cexpr) => ExprInner::LitNum(
                cexpr
                    .fill(|c| cvar_scope.get(c).cloned().unwrap())
                    .try_eval()
                    .unwrap(),
            ),
            ExprInner::VectorSlice(v, i, j) => {
                ExprInner::VectorSlice(recurse(&v).into(), recurse(&i).into(), recurse(&j).into())
            }
            ExprInner::Loop(n, body, res) => ExprInner::Loop(
                n.fill(|c| cvar_scope.get(c).cloned().unwrap()),
                body.iter().map(|(s, v)| (*s, recurse(v))).collect(),
                recurse(&res).into(),
            ),
            ExprInner::Fail => ExprInner::Fail,
            ExprInner::LitBytes(b) => ExprInner::LitBytes(b),
            ExprInner::LitBVec(v) => ExprInner::LitBVec(v.iter().map(recurse).collect()),
            ExprInner::ExternApply(x, args) => {
                ExprInner::ExternApply(x, args.iter().map(recurse).collect())
            }
            ExprInner::Extern(x) => ExprInner::Extern(x),
        },
        itype: body
            .itype
            .fill_cvars(|c| cvar_scope.get(c).cloned().unwrap())
            .fill_tvars(|t| tvar_scope.get(t).cloned().unwrap()),
    }
}

#[cfg(test)]
mod tests {

    use std::path::Path;

    use log::LevelFilter;

    use super::*;
    use crate::{containers::Void, context::ModuleId, grammar::parse_program};

    #[test]
    fn typecheck_simple() {
        init_logs();
        let state: TypecheckState<Void, Void> = TypecheckState::new();
        let module = ModuleId::from_path(Path::new("whatever.melo"));
        eprintln!(
            "{:#?}",
            typecheck_expr(
                state,
                parse_program("1 :: Nat", module, &std::path::PathBuf::from(""))
                    .unwrap()
                    .body
                    .clone()
            )
            .unwrap()
        );
    }

    #[test]
    fn typecheck_tricky() {
        init_logs();
        let module = ModuleId::from_path(Path::new("whatever.melo"));
        eprintln!(
            "{:?}",
            typecheck_program(
                parse_program(
                    r"
def foo<$n>() = succ(0)
def succ<$n>(x: {$n..$n}) = $n + 1
def peel<$n>(x : {$n+1..$n+1}) = $n
--- 
let x = 0 :: Nat in
loop 100 do
set! x = x + 1
return x
                ",
                    module,
                    &std::path::PathBuf::from(""),
                )
                .unwrap()
            )
            .unwrap()
        );
    }

    #[test]
    fn typecheck_issue4() {
        init_logs();
        let module = ModuleId::from_path(Path::new("whatever.melo"));
        assert!(typecheck_program(
            parse_program(
                r"
        def head<$n, T>(t: [T; $n]) = t[0]
    ",
                module,
                &std::path::PathBuf::from(""),
            )
            .unwrap(),
        )
        .unwrap_err()
        .to_string()
        .contains("index"));
    }

    #[test]
    fn typecheck_whole() {
        init_logs();
        let module = ModuleId::from_path(Path::new("whatever.melo"));
        eprintln!(
            "{:?}",
            typecheck_program(
                parse_program(
                    r"
def foo<$n>() = succ(0)
def succ<$n>(x: {$n..$n}) = $n + 1
def peel<$n>(x : {$n+1..$n+1}) = $n
--- 
let x = 0 :: Nat in
loop 100 do
set! x = x + 1
return 
for x in [1, 2, 3] collect x*2
                ",
                    module,
                    &std::path::PathBuf::from(""),
                )
                .unwrap()
            )
            .unwrap()
        );
    }

    fn init_logs() {
        let _ = env_logger::builder()
            .is_test(true)
            .format_timestamp(None)
            .filter_level(LevelFilter::Trace)
            .try_init();
    }
}
