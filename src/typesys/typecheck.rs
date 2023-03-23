use std::{fmt::Debug, ops::Deref, sync::atomic::AtomicUsize};

use anyhow::Context;
use dashmap::{DashMap, DashSet};
use ethnum::U256;
use rustc_hash::FxHashSet;
use tap::Tap;

use crate::{
    containers::{List, Map, Set, Symbol, Void},
    context::{Ctx, CtxErr, CtxLocation, CtxResult, ToCtx, ToCtxErr},
    grammar::{sort_defs, RawExpr, RawProgram, RawTypeExpr},
    typed_ast::{BinOp, Expr, ExprInner, FunDefn, Program, UniOp},
    typesys::{Type, Variable},
};

use self::{
    facts::TypeFacts,
    state::{FunctionType, TypecheckState},
};

mod facts;

mod state;

#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct TypeParam(Symbol);

impl Debug for TypeParam {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

impl Variable for TypeParam {
    fn try_from_sym(sym: Symbol) -> Option<Self> {
        Some(Self(sym))
    }
}

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

impl Variable for i32 {
    fn try_from_sym(_: Symbol) -> Option<Self> {
        panic!("cannot work")
    }
}

fn assert_subtype<Tv: Variable>(
    ctx: Option<CtxLocation>,
    a: &Type<Tv>,
    b: &Type<Tv>,
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
    let mut fun_defs: List<FunDefn<TypeParam>> = List::new();
    //for definition in raw.definitions.iter() {
    for definition in sorted.iter() {
        match definition.deref() {
            crate::grammar::RawDefn::Function {
                name,
                genvars,
                args,
                rettype,
                body,
            } => {
                // bind the type variables, then the CG-variables
                let istate: TypecheckState<TypeParam> =
                    genvars.iter().fold(state.clone(), |state, sym| {
                        state.bind_type_alias(**sym, Type::Var(TypeParam(**sym)))
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
pub fn typecheck_expr<Tv: Variable>(
    state: TypecheckState<Tv>,
    raw: Ctx<RawExpr>,
) -> CtxResult<(Expr<Tv>, TypeFacts<Tv>)> {
    let recurse = |c| typecheck_expr(state.clone(), c);
    let ctx = raw.ctx();
    match raw.deref().clone() {
        RawExpr::Let(binds, body) => {
            let mut checked_binds: List<(Symbol, Expr<Tv>)> = List::new();
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
                assert_subtype(ctx, &a_expr.itype, &Type::Nat)?;
                assert_subtype(ctx, &b_expr.itype, &Type::Nat)?;

                Ok::<_, CtxErr>(())
            };
            match op {
                crate::grammar::BinOp::Add => {
                    check_nats()?;
                    Ok((
                        Expr {
                            itype: Type::Nat,
                            inner: ExprInner::BinOp(BinOp::Add, a_expr?.into(), b_expr?.into()),
                        },
                        TypeFacts::empty(),
                    ))
                }
                crate::grammar::BinOp::Sub => {
                    check_nats()?;
                    // cannot subtract CGs correctly at the moment
                    Ok((
                        Expr {
                            itype: Type::Nat,
                            inner: ExprInner::BinOp(BinOp::Sub, a_expr?.into(), b_expr?.into()),
                        },
                        TypeFacts::empty(),
                    ))
                }

                crate::grammar::BinOp::Exp => {
                    check_nats()?;
                    // cannot subtract CGs correctly at the moment
                    Ok((
                        Expr {
                            itype: Type::Nat,
                            inner: ExprInner::Exp(U256::MAX, a_expr?.into(), b_expr?.into()),
                        },
                        TypeFacts::empty(),
                    ))
                }
                crate::grammar::BinOp::Mul => {
                    check_nats()?;
                    Ok((
                        Expr {
                            itype: Type::Nat,
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
                            itype: Type::Nat,
                            inner: ExprInner::BinOp(BinOp::Div, a_expr?.into(), b_expr?.into()),
                        },
                        TypeFacts::empty(),
                    ))
                }
                crate::grammar::BinOp::Mod => {
                    check_nats()?;
                    Ok((
                        Expr {
                            itype: Type::Nat,
                            inner: ExprInner::BinOp(BinOp::Mod, a_expr?.into(), b_expr?.into()),
                        },
                        TypeFacts::empty(),
                    ))
                }
                crate::grammar::BinOp::Eq => {
                    check_nats()?;
                    Ok((
                        Expr {
                            itype: Type::Nat,
                            inner: ExprInner::BinOp(BinOp::Eq, a_expr?.into(), b_expr?.into()),
                        },
                        TypeFacts::empty(),
                    ))
                }
                crate::grammar::BinOp::Lt => {
                    check_nats()?;
                    Ok((
                        Expr {
                            itype: Type::Nat,
                            inner: ExprInner::BinOp(BinOp::Lt, a_expr?.into(), b_expr?.into()),
                        },
                        TypeFacts::empty(),
                    ))
                }
                crate::grammar::BinOp::Le => {
                    check_nats()?;
                    Ok((
                        Expr {
                            itype: Type::Nat,
                            inner: ExprInner::BinOp(BinOp::Le, a_expr?.into(), b_expr?.into()),
                        },
                        TypeFacts::empty(),
                    ))
                }
                crate::grammar::BinOp::Gt => {
                    check_nats()?;
                    Ok((
                        Expr {
                            itype: Type::Nat,
                            inner: ExprInner::BinOp(BinOp::Gt, a_expr?.into(), b_expr?.into()),
                        },
                        TypeFacts::empty(),
                    ))
                }
                crate::grammar::BinOp::Ge => {
                    check_nats()?;
                    Ok((
                        Expr {
                            itype: Type::Nat,
                            inner: ExprInner::BinOp(BinOp::Ge, a_expr?.into(), b_expr?.into()),
                        },
                        TypeFacts::empty(),
                    ))
                }
                crate::grammar::BinOp::Append => {
                    // vector append
                    let a_expr = a_expr?;
                    let b_expr = b_expr?;
                    todo!()
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
                            itype: Type::Nat,
                            inner: ExprInner::BinOp(BinOp::Lshift, a_expr?.into(), b_expr?.into()),
                        },
                        TypeFacts::empty(),
                    ))
                }
                crate::grammar::BinOp::Rshift => {
                    check_nats()?;
                    Ok((
                        Expr {
                            itype: Type::Nat,
                            inner: ExprInner::BinOp(BinOp::Rshift, a_expr?.into(), b_expr?.into()),
                        },
                        TypeFacts::empty(),
                    ))
                }
                crate::grammar::BinOp::Bor => {
                    check_nats()?;
                    Ok((
                        Expr {
                            itype: Type::Nat,
                            inner: ExprInner::BinOp(BinOp::Bor, a_expr?.into(), b_expr?.into()),
                        },
                        TypeFacts::empty(),
                    ))
                }
                crate::grammar::BinOp::Band => {
                    check_nats()?;
                    Ok((
                        Expr {
                            itype: Type::Nat,
                            inner: ExprInner::BinOp(BinOp::Band, a_expr?.into(), b_expr?.into()),
                        },
                        TypeFacts::empty(),
                    ))
                }
                crate::grammar::BinOp::Bxor => {
                    check_nats()?;
                    Ok((
                        Expr {
                            itype: Type::Nat,
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
                assert_subtype(ctx, &a_expr.itype, &Type::Nat)?;
                Ok::<_, CtxErr>(())
            };
            match op {
                crate::grammar::UniOp::Bnot => {
                    check_nat()?;
                    Ok((
                        Expr {
                            itype: Type::Nat,
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
                itype: Type::Nat,
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
            // TODO impl this
            Ok((
                Expr {
                    itype: itype.clone(),
                    inner: ExprInner::Var(v),
                },
                TypeFacts::empty(),
            ))
        }
        RawExpr::Apply(f, tvars, args) => {
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
                    let mut generic_mapping = ftype
                        .args
                        .iter()
                        .zip(typechecked_args.iter())
                        .map(|(arg_type, arg)| {
                            let actual_arg_type = arg.itype.clone();
                            arg_type.unify_tvars(&actual_arg_type).unwrap_or_default()
                        })
                        .reduce(|a, b| a.union_with(b, |a, b| a.smart_union(&b)))
                        .unwrap_or_default();

                    // override with the things in the explicit turbofish
                    for (k, v) in tvars {
                        let k = Tv::try_from_sym(k).expect("wtf");
                        let v = typecheck_type_expr(&state, v)?;
                        generic_mapping.insert(k, v);
                    }

                    for (arg, required_type) in typechecked_args.iter().zip(ftype.args.iter()) {
                        let required_type = required_type
                            .try_fill_tvars(|tv| generic_mapping.get(tv).cloned())
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
                                .context(format!(
                                    "cannot fill type variables in result type {:?}",
                                    ftype.result
                                ))
                                .err_ctx(ctx)?,
                            inner: if generic_mapping.is_empty() {
                                ExprInner::Apply(*f, typechecked_args)
                            } else {
                                ExprInner::ApplyGeneric(*f, generic_mapping, typechecked_args)
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
                                    itype: Type::Nat,
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
            todo!()
            // let (v, _) = recurse(v)?;
            // let (i, _) = recurse(i)?;
            // let restype = type_vector_ref(&v.itype, &i.itype)
            //     .or_else(|_| type_bytes_ref(&v.itype, &i.itype))
            //     .err_ctx(ctx)?;
            // Ok((
            //     Expr {
            //         itype: restype,
            //         inner: ExprInner::VectorRef(v.into(), i.into()),
            //     },
            //     TypeFacts::empty(),
            // ))
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
            // let orig_type = state
            //     .lookup_var(x)
            //     .context("undefined variable")
            //     .err_ctx(ctx)?;
            let t = typecheck_type_expr(&state, y)?;
            // if !t.subtype_of(&orig_type) {
            //     return Err(anyhow::anyhow!(
            //         "type check always fails because {:?} is not a subtype of {:?}",
            //         t,
            //         orig_type
            //     )
            //     .with_ctx(ctx));
            // }
            Ok((
                Expr {
                    itype: Type::Nat,
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

        RawExpr::VectorSlice(v, l, r) => {
            todo!()
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

        RawExpr::Fail => Ok((
            Expr {
                inner: ExprInner::Fail,
                itype: Type::Nothing,
            },
            TypeFacts::empty(),
        )),

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

        RawExpr::LitBytes(b) => Ok((
            ExprInner::LitBytes(b).wrap(Type::DynBytes),
            TypeFacts::empty(),
        )),
        RawExpr::LitBVec(vv) => {
            let args = vv
                .into_iter()
                .map(|arg| {
                    let ctx = arg.ctx();
                    let arg = recurse(arg)?.0;
                    if !arg.itype.subtype_of(&Type::Nat) {
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
            let itype = Type::DynBytes;
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

fn type_vector_ref<Tv: Variable>(vtype: &Type<Tv>, itype: &Type<Tv>) -> anyhow::Result<Type<Tv>> {
    todo!()
}

fn typecheck_type_expr<Tv: Variable>(
    state: &TypecheckState<Tv>,
    raw: Ctx<RawTypeExpr>,
) -> CtxResult<Type<Tv>> {
    match raw.deref().clone() {
        RawTypeExpr::Sym(s) => {
            if s == Symbol::from("Nat") {
                Ok(Type::Nat)
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

        RawTypeExpr::DynVectorof(v) => {
            let v = typecheck_type_expr(state, v)?;
            Ok(Type::DynVectorof(v.into()))
        }

        RawTypeExpr::DynBytes => Ok(Type::DynBytes),
    }
}

/// Monomorphizes a set of function definitions and a "preliminary" body into a fully degenericized version.
///
/// Uses monomorphization for const-generics and type erasure for "normal" generics. But that's unspecified.
pub fn monomorphize(fun_defs: List<FunDefn<TypeParam>>, body: Expr<TypeParam>) -> Program {
    // The basic idea is to identify all calls to generic functions, replacing them with non-generic calls to generated functions.
    let monomorph_collector = DashMap::new();
    let body = monomorphize_inner(
        &fun_defs.into_iter().map(|fd| (fd.name, fd)).collect(),
        &body,
        &monomorph_collector,
        &Map::new(),
    );
    Program {
        fun_defs: monomorph_collector.into_iter().map(|x| x.1).collect(),
        body,
    }
}

fn monomorphize_inner(
    fun_defs: &Map<Symbol, FunDefn<TypeParam>>,
    body: &Expr<TypeParam>,
    mangled: &DashMap<Symbol, FunDefn>,
    tvar_scope: &Map<TypeParam, Type>,
) -> Expr {
    let recurse = |b| monomorphize_inner(fun_defs, b, mangled, tvar_scope);
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
            ExprInner::Exp(k, a, b) => ExprInner::Exp(k, recurse(&a).into(), recurse(&b).into()),
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
            ExprInner::ApplyGeneric(f, tvars, args) => {
                // generate a monomorphized version
                let mangled_name = if tvars.is_empty() {
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
                                    v.fill_tvars(|t| tvar_scope.get(t).cloned().unwrap()),
                                );
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
            ExprInner::IsType(a, b) => {
                ExprInner::IsType(a, b.fill_tvars(|t| tvar_scope.get(t).cloned().unwrap()))
            }
            ExprInner::VectorRef(v, i) => {
                ExprInner::VectorRef(recurse(&v).into(), recurse(&i).into())
            }
            ExprInner::VectorUpdate(v, i, n) => {
                ExprInner::VectorUpdate(recurse(&v).into(), recurse(&i).into(), recurse(&n).into())
            }
            ExprInner::VectorSlice(v, i, j) => {
                ExprInner::VectorSlice(recurse(&v).into(), recurse(&i).into(), recurse(&j).into())
            }
            ExprInner::Loop(n, body, res) => todo!(),
            ExprInner::Fail => ExprInner::Fail,
            ExprInner::LitBytes(b) => ExprInner::LitBytes(b),
            ExprInner::LitBVec(v) => ExprInner::LitBVec(v.iter().map(recurse).collect()),
            ExprInner::ExternApply(x, args) => {
                ExprInner::ExternApply(x, args.iter().map(recurse).collect())
            }
            ExprInner::Extern(x) => ExprInner::Extern(x),
            ExprInner::LitConst(_) => todo!(),
        },
        itype: body
            .itype
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
        let state: TypecheckState<Void> = TypecheckState::new();
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
    x <- x + 1
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
    fn typecheck_issue15() {
        init_logs();
        let module = ModuleId::from_path(Path::new("whatever.melo"));
        dbg!(typecheck_program(
            parse_program(
                r"
        2 ** 3 + 1
    ",
                module,
                &std::path::PathBuf::from(""),
            )
            .unwrap(),
        )
        .unwrap());
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
x <- x + 1
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
