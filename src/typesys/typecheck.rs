use std::{fmt::Debug, ops::Deref};

use anyhow::Context;
use dashmap::DashMap;
use ethnum::U256;
use tap::Tap;

use crate::{
    containers::{List, Map, Symbol, Void},
    context::{Ctx, CtxErr, CtxLocation, CtxResult, ToCtx, ToCtxErr},
    grammar::{RawConstExpr, RawExpr, RawProgram, RawTypeExpr},
    typesys::{typecheck::state::FunctionType, BinOp, ConstExpr, ExprInner, FunDefn, Type},
};

use self::{facts::TypeFacts, state::TypecheckState};

use super::{Expr, Program, Variable};

mod facts;
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

/// Typechecks a whole program, resolving free variables fully.
pub fn typecheck_program(raw: Ctx<RawProgram>) -> CtxResult<Program> {
    // build the typecheck state
    // TODO: sort the definitions
    let mut state = TypecheckState::new();
    let mut fun_defs: List<FunDefn<TypeParam, CgParam>> = List::new();
    for definition in raw.definitions.iter() {
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
                c_facts.union(y_facts)
            } else if y.itype.always_falsy() {
                not_c_facts.union(x_facts)
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
            let (a, _) = recurse(a)?;
            let (b, _) = recurse(b)?;
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
                    Ok((
                        Expr {
                            itype: Type::NatRange(lower_bound, upper_bound).fix_natrange(),
                            inner: ExprInner::BinOp(BinOp::Add, a.into(), b.into()),
                        },
                        TypeFacts::empty(),
                    ))
                }
                crate::grammar::BinOp::Sub => {
                    check_nats()?;
                    // cannot subtract CGs correctly at the moment
                    Ok((
                        Expr {
                            itype: Type::all_nat(),
                            inner: ExprInner::BinOp(BinOp::Sub, a.into(), b.into()),
                        },
                        TypeFacts::empty(),
                    ))
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
                    Ok((
                        Expr {
                            itype: Type::NatRange(lower_bound, upper_bound).fix_natrange(),
                            inner: ExprInner::BinOp(BinOp::Mul, a.into(), b.into()),
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
                            inner: ExprInner::BinOp(BinOp::Div, a.into(), b.into()),
                        },
                        TypeFacts::empty(),
                    ))
                }
                // don't check for nats
                crate::grammar::BinOp::Eq => Ok((
                    Expr {
                        itype: Type::NatRange(0.into(), 1.into()),
                        inner: ExprInner::BinOp(BinOp::Eq, a.into(), b.into()),
                    },
                    TypeFacts::empty(),
                )),
                crate::grammar::BinOp::Append => {
                    // vector append
                    Ok((
                        Expr {
                            itype: a
                                .itype
                                .append(&b.itype)
                                .context(format!(
                                    "cannot append values of types {:?} and {:?}",
                                    a.itype, b.itype
                                ))
                                .err_ctx(ctx)?,
                            inner: ExprInner::BinOp(BinOp::Append, a.into(), b.into()),
                        },
                        TypeFacts::empty(),
                    ))
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
                        .reduce(|a, b| a.union_with(b, |a, b| a))
                        .unwrap_or_default();
                    for (arg, required_type) in typechecked_args.iter().zip(ftype.args.iter()) {
                        let required_type = required_type
                            .try_fill_tvars(|tv| generic_mapping.get(tv).cloned())
                            .and_then(|t| t.try_fill_cvars(|cv| cg_mapping.get(cv).cloned()))
                            .context(format!(
                                "cannot fill type variables in argument type {:?}",
                                required_type
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
        RawExpr::Field(_, _) => todo!(),
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
                Ok(Type::NatRange(0.into(), U256::MAX.into()))
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
        RawConstExpr::Lit(a) => Ok(ConstExpr::Literal(*a)),
        RawConstExpr::Plus(a, b) => Ok(ConstExpr::Plus(
            typecheck_const_expr(state, a.clone())?.into(),
            typecheck_const_expr(state, b.clone())?.into(),
        )),
        RawConstExpr::Mult(a, b) => Ok(ConstExpr::Mult(
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
        },
        itype: body
            .itype
            .fill_cvars(|c| cvar_scope.get(c).cloned().unwrap())
            .fill_tvars(|t| tvar_scope.get(t).cloned().unwrap()),
    }
}

#[cfg(test)]
mod tests {

    use log::LevelFilter;

    use super::*;
    use crate::{containers::Void, context::ModuleId, grammar::parse_program};

    #[test]
    fn typecheck_simple() {
        init_logs();
        let state: TypecheckState<Void, Void> = TypecheckState::new();
        let module = ModuleId(Symbol::from("whatever.melo"));
        eprintln!(
            "{:#?}",
            typecheck_expr(
                state,
                parse_program("1 as Noonoo", module).unwrap().body.clone()
            )
            .unwrap()
        );
    }

    #[test]
    fn typecheck_whole() {
        init_logs();
        let module = ModuleId(Symbol::from("whatever.melo"));
        eprintln!(
            "{:#?}",
            typecheck_program(
                parse_program(
                    r"
def bar<$n, T>(x: [T; $n]) = x ++ [0]
def foo<$n, T>(x: [T; $n]) = bar(x ++ x)
---
foo([1, 2, 3, 4, 5])[0]
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
