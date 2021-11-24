use std::{fmt::Debug, ops::Deref};

use anyhow::Context;
use dashmap::{DashMap, DashSet};
use tap::Tap;

use crate::{
    containers::{List, Map, Symbol, Void},
    context::{Ctx, CtxErr, CtxLocation, CtxResult, ToCtx, ToCtxErr},
    grammar::{sort_defs, RawConstExpr, RawExpr, RawProgram, RawTypeExpr},
    typed_ast::{BinOp, Expr, ExprInner, FunDefn, Program},
    typesys::{
        struct_uniqid,
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
                fun_defs.push_back(FunDefn {
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
        }
    }
    log::trace!("initial definitions created: {:?}", fun_defs);
    // time to typecheck the expression preliminarily
    let (prelim_body, _) = typecheck_expr(state, raw.body.clone())?;
    log::trace!("preliminary body created: {:?}", prelim_body);

    // MONOMORPHIZE!
    Ok(monomorphize(fun_defs, prelim_body))
}

/// Typechecks a single expression, returning a single typed ast node.
pub fn typecheck_expr<Tv: Variable, Cv: Variable>(
    state: TypecheckState<Tv, Cv>,
    raw: Ctx<RawExpr>,
) -> CtxResult<(Expr<Tv, Cv>, TypeFacts<Tv, Cv>)> {
    let recurse = |c| typecheck_expr(state.clone(), c);
    let ctx = raw.ctx();
    match raw.deref().clone() {
        RawExpr::Let(var, value, body) => {
            let value = recurse(value)?;
            let body = typecheck_expr(state.clone().bind_var(*var, value.0.itype.clone()), body)?;
            Ok((
                Expr {
                    itype: body.0.itype.clone(),
                    inner: ExprInner::Let(*var, value.0.into(), body.0.into()),
                },
                body.1.clear_mapping(*var),
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
            let (a_expr, _) = recurse(a.clone())?;
            let (b_expr, _) = recurse(b.clone())?;
            let op = *op.deref();
            // both must be numbers
            let check_nats = || {
                assert_subtype(ctx, &a_expr.itype, &Type::all_nat())?;
                assert_subtype(ctx, &b_expr.itype, &Type::all_nat())?;
                let template: Type<Void, i32> =
                    Type::NatRange(ConstExpr::Var(0), ConstExpr::Var(1));
                let a_range = template.unify_cvars(&a_expr.itype).unwrap();
                let b_range = template.unify_cvars(&b_expr.itype).unwrap();
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
                                inner: ExprInner::BinOp(BinOp::Add, a_expr.into(), b_expr.into()),
                            },
                            TypeFacts::empty(),
                        ))
                    } else {
                        Ok((
                            Expr {
                                itype: Type::all_nat(),
                                inner: ExprInner::BinOp(BinOp::Add, a_expr.into(), b_expr.into()),
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
                            inner: ExprInner::BinOp(BinOp::Sub, a_expr.into(), b_expr.into()),
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
                            inner: ExprInner::BinOp(BinOp::Mul, a_expr.into(), b_expr.into()),
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
                            inner: ExprInner::BinOp(BinOp::Div, a_expr.into(), b_expr.into()),
                        },
                        TypeFacts::empty(),
                    ))
                }
                // don't check for nats
                crate::grammar::BinOp::Eq => {
                    if !a_expr.itype.subtype_of(&b_expr.itype)
                        && !b_expr.itype.subtype_of(&a_expr.itype)
                    {
                        Err(anyhow::anyhow!(
                            "cannot compare equality for incomparable types {:?} and {:?}",
                            a_expr.itype,
                            b_expr.itype
                        )
                        .with_ctx(ctx))
                    } else {
                        Ok((
                            Expr {
                                itype: Type::NatRange(0.into(), 1.into()),
                                inner: ExprInner::BinOp(BinOp::Eq, a_expr.into(), b_expr.into()),
                            },
                            TypeFacts::empty(),
                        ))
                    }
                }
                crate::grammar::BinOp::Append => {
                    // vector append
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
                        RawExpr::If(a, RawExpr::LitNum(1u8.into()).into(), b).with_ctx(ctx);
                    recurse(desugared)
                }
                crate::grammar::BinOp::Land => {
                    // Desugar!
                    let desugared =
                        RawExpr::If(a, b, RawExpr::LitNum(0u8.into()).into()).with_ctx(ctx);
                    recurse(desugared)
                }
                crate::grammar::BinOp::Lnot => todo!(),
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
            Ok((
                Expr {
                    itype,
                    inner: ExprInner::Var(v),
                },
                TypeFacts::empty(),
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
                                    inner: ExprInner::LitNum(((idx + 1) as u64).into()),
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
            let restype = type_vector_ref(&v.itype, &i.itype).err_ctx(ctx)?;
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
            state
                .lookup_var(x)
                .context("undefined variable")
                .err_ctx(ctx)?;
            let t = typecheck_type_expr(&state, y)?;
            Ok((
                Expr {
                    itype: Type::NatRange(0.into(), 1.into()),
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
                    let mut args = ifields.iter().map(|(fname, correct_t)| {
                        let actual = recurse(fields[fname].clone())?.0;
                        if !actual.itype.subtype_of(correct_t) {
                            Err(anyhow::anyhow!("field {:?}.{:?} must be of type {:?}, but given a value of type {:?}", name, fname, correct_t, actual.itype).with_ctx(fields[fname].ctx()))
                        } else {
                            Ok(actual)
                        }
                    }).collect::<CtxResult<List<_>>>()?;
                    let sid = struct_uniqid(name);
                    args.insert(
                        0,
                        Expr {
                            itype: Type::all_nat(),
                            inner: ExprInner::LitNum(sid),
                        },
                    );
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
        RawExpr::Loop(iterations, body, end) => {
            let iterations = typecheck_const_expr(&state, iterations)?;
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
                    inner: ExprInner::Loop(iterations, body, end.into()),
                },
                TypeFacts::empty(),
            ))
        }
        RawExpr::Fail => Ok((
            Expr {
                inner: ExprInner::Fail,
                itype: Type::None,
            },
            TypeFacts::empty(),
        )),
        RawExpr::For(sym, val, body) => {
            let val = recurse(val)?.0;
            let (val_inner_length, val_inner_type) = vector_info(&val).err_ctx(ctx)?;
            let body = typecheck_expr(state.bind_var(*sym, val_inner_type.clone()), body)?.0;
            let temp_counter = Symbol::generate("-for-counter");
            let temp_result = Symbol::generate("-for-result");
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
                        temp_counter,
                        ExprInner::LitNum(0u8.into()).wrap(Type::all_nat()).into(),
                        ExprInner::Let(
                            temp_result,
                            val.clone().into(),
                            ExprInner::Loop(
                                val_inner_length,
                                [
                                    (
                                        temp_result,
                                        ExprInner::Let(
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
                                            ExprInner::LitNum(1u8.into())
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
            let mut inner = recurse(inner)?;
            let t = typecheck_type_expr(&state, t)?;
            inner.0.itype = t;
            Ok(inner)
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
                    let v = Cv::try_from_sym(Symbol::generate("g")).unwrap();
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
            let temp_counter = Symbol::generate("-fold-counter");
            let temp_input = Symbol::generate("-fold-input");
            let loop_inner: List<(Symbol, Expr<Tv, Cv>)> = [
                (
                    *accum_name,
                    ExprInner::Let(
                        *var_name,
                        ExprInner::VectorRef(
                            ExprInner::Var(temp_input)
                                .wrap(iterating_list.itype.clone())
                                .into(),
                            ExprInner::Var(temp_counter).wrap(Type::all_nat()).into(),
                        )
                        .wrap(list_inner_type)
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
                        LitNum(1u8.into()).wrap(Type::all_nat()).into(),
                    )
                    .wrap(Type::all_nat())
                    .into(),
                ),
            ]
            .into_iter()
            .collect();
            Ok((
                Let(
                    temp_input,
                    iterating_list.into(),
                    Let(
                        temp_counter,
                        LitNum(0u8.into()).wrap(Type::all_nat()).into(),
                        Let(
                            *accum_name,
                            init_accum.into(),
                            Loop(
                                list_length,
                                loop_inner,
                                Var(*accum_name).wrap(result_type.clone()).into(),
                            )
                            .wrap(result_type.clone())
                            .into(),
                        )
                        .wrap(result_type.clone())
                        .into(),
                    )
                    .wrap(result_type.clone())
                    .into(),
                )
                .wrap(result_type.clone()),
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
    if !i_upper_bound.add1().leq(&v_length) {
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
            ExprInner::BinOp(op, a, b) => {
                ExprInner::BinOp(op, recurse(&a).into(), recurse(&b).into())
            }
            ExprInner::If(cond, a, b) => ExprInner::If(
                recurse(&cond).into(),
                recurse(&a).into(),
                recurse(&b).into(),
            ),
            ExprInner::Let(s, b, i) => ExprInner::Let(s, recurse(&b).into(), recurse(&i).into()),
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
                ExprInner::Apply(f, args.iter().map(|a| recurse(a)).collect())
            }
            ExprInner::ApplyGeneric(f, tvars, cvars, args) => {
                // generate a monomorphized version
                let mangler = blake3::hash(format!("{:?}_{:?}", tvars, cvars).as_bytes()).to_hex()
                    [..16]
                    .to_string();
                let mangled_name = if tvars.is_empty() && cvars.is_empty() {
                    f
                } else {
                    Symbol::from(format!("{:?}_{}", f, mangler).as_str())
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
                ExprInner::Apply(mangled_name, args.iter().map(|a| recurse(a)).collect())
            }
            ExprInner::LitNum(v) => ExprInner::LitNum(v),
            ExprInner::LitVec(lv) => ExprInner::LitVec(lv.iter().map(|a| recurse(a)).collect()),
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
                parse_program("1 as Nat", module).unwrap().body.clone()
            )
            .unwrap()
        );
    }

    #[test]
    fn typecheck_whole() {
        init_logs();
        let module = ModuleId::from_path(Path::new("whatever.melo"));
        eprintln!(
            "{:#?}",
            typecheck_program(
                parse_program(
                    r"
def foo<$n>() = succ(0)
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
