use std::ops::Deref;

use anyhow::Context;

use ethnum::U256;
use rustc_hash::FxHashSet;

use crate::{
    containers::{List, Symbol},
    context::{Ctx, CtxErr, CtxLocation, CtxResult, ToCtx, ToCtxErr},
    grammar::{RawDefn, RawExpr, RawProgram, RawTypeExpr},
    typed_ast::{BinOp, Expr, ExprInner, FunDefn, Program, UniOp},
    typesys::Type,
};

use self::{facts::TypeFacts, scope::Scope};

mod facts;

mod scope;

fn assert_subtype(ctx: Option<CtxLocation>, a: &Type, b: &Type) -> CtxResult<()> {
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

    // We build a *provisional* typecheck state for the top-level functions, which is used to typecheck their bodies only. This allows us to typecheck recursive functions correctly.
    let provisional_toplevel_scope =
        raw.definitions
            .iter()
            .try_fold(Scope::new(), |state, defn| {
                if let RawDefn::Function {
                    name,
                    genvars,
                    args,
                    rettype,
                    body: _,
                } = defn.deref()
                {
                    let istate: Scope = genvars.iter().fold(state.clone(), |state, sym| {
                        state.bind_type_alias(**sym, Type::Var(**sym))
                    });
                    let rettype = typecheck_type_expr(
                        &istate,
                        rettype
                            .clone()
                            .unwrap_or(RawTypeExpr::Sym("Any".into()).with_ctx(name.ctx())),
                    )?;

                    let funtype = Type::Lambda {
                        free_vars: genvars.iter().map(|gv| **gv).collect(),
                        args: args
                            .iter()
                            .map(|bind| typecheck_type_expr(&istate, bind.bind.clone()))
                            .collect::<Result<Vec<_>, _>>()?,
                        result: rettype.into(),
                    };

                    Ok::<_, CtxErr>(state.bind_var(**name, funtype))
                } else {
                    Ok::<_, CtxErr>(state)
                }
            })?;

    // build the typecheck scope
    let mut scope = provisional_toplevel_scope;
    let mut fun_defs: List<FunDefn> = List::new();
    for definition in raw.definitions.iter() {
        match definition.deref() {
            crate::grammar::RawDefn::Function {
                name,
                genvars,
                args,
                rettype,
                body,
            } => {
                // bind the type variables, then the CG-variables
                let istate: Scope = genvars.iter().fold(scope.clone(), |state, sym| {
                    state.bind_type_alias(**sym, Type::Var(**sym))
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
                let fun_info = Type::Lambda {
                    free_vars: genvars.iter().map(|c| **c).collect(),
                    args: args
                        .iter()
                        .map(|s| istate.lookup_var(*s.name).unwrap())
                        .collect(),
                    result: rettype.into(),
                };
                scope = scope.bind_var(**name, fun_info);
                fun_defs.push(FunDefn {
                    name: **name,
                    args: args.iter().map(|s| *s.name).collect(),
                    body,
                });
            }
            crate::grammar::RawDefn::Constant(_, _) => todo!(),
            crate::grammar::RawDefn::Struct { name, fields } => {
                let tstate = scope.clone();
                scope = scope.bind_type_alias(
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
                let b = typecheck_type_expr(&scope, b.clone())?;
                scope = scope.bind_type_alias(**a, b);
            }
        }
    }
    log::trace!("initial definitions created: {:?}", fun_defs);
    // time to typecheck the expression preliminarily
    let (body, _) = typecheck_expr(scope, raw.body.clone())?;

    Ok(Program { fun_defs, body })
}

/// Typechecks a single expression, returning a single typed ast node.
pub fn typecheck_expr(state: Scope, raw: Ctx<RawExpr>) -> CtxResult<(Expr, TypeFacts)> {
    let recurse = |c| typecheck_expr(state.clone(), c);
    let ctx = raw.ctx();
    match raw.deref().clone() {
        RawExpr::Let(binds, body) => {
            let mut checked_binds: List<(Symbol, Expr)> = List::new();
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
            let (x, _x_facts) = typecheck_expr(state.clone().with_facts(&c_facts), x)?;
            let (y, _y_facts) = typecheck_expr(state.clone().with_facts(&not_c_facts), y)?;
            Ok((
                Expr {
                    itype: x.itype.smart_union(&y.itype),
                    inner: ExprInner::If(c.into(), x.into(), y.into()),
                },
                TypeFacts::empty(),
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
                            inner: ExprInner::BinOp(BinOp::Expt, a_expr?.into(), b_expr?.into()),
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
                    let _a_expr = a_expr?;
                    let _b_expr = b_expr?;
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
                .context(format!("undefined variable {v}"))
                .err_ctx(ctx)?;
            // Here we at least know that the variable is *NOT* false if expression is true.
            // TODO impl this
            Ok((
                Expr {
                    itype,
                    inner: ExprInner::Var(v),
                },
                TypeFacts::empty(),
            ))
        }
        RawExpr::Apply(f, tvars, call_args) => {
            let (fval, _) = recurse(f.clone())?;
            if let Type::Lambda {
                free_vars: _,
                args,
                result,
            } = fval.itype.clone()
            {
                if args.len() != call_args.len() {
                    Err(anyhow::anyhow!(
                        "calling function with the wrong arity (expected {}, got {})",
                        args.len(),
                        call_args.len()
                    )
                    .with_ctx(ctx))
                } else {
                    // create a mapping for the CG-vars
                    let typechecked_args = call_args
                        .iter()
                        .map(|a| Ok(recurse(a.clone())?.0))
                        .collect::<CtxResult<List<_>>>()?;
                    let mut generic_mapping = args
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
                        let v = typecheck_type_expr(&state, v)?;
                        generic_mapping.insert(k, v);
                    }

                    for (arg, required_type) in typechecked_args.iter().zip(args.iter()) {
                        let required_type = required_type
                            .try_fill_tvars(|tv| generic_mapping.get(&tv).cloned())
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
                            itype: result
                                .try_fill_tvars(|tv| generic_mapping.get(&tv).cloned())
                                .context(format!(
                                    "cannot fill type variables in result type {:?}",
                                    result
                                ))
                                .err_ctx(ctx)?,
                            inner: ExprInner::ApplyGeneric(
                                fval.into(),
                                generic_mapping,
                                typechecked_args,
                            ),
                        },
                        TypeFacts::empty(),
                    ))
                }
            } else {
                Err(
                    anyhow::anyhow!("trying to call a non-function value: {:?}", fval)
                        .with_ctx(f.ctx()),
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

        RawExpr::VectorSlice(_v, _l, _r) => {
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

        RawExpr::LitBytes(b) => Ok((ExprInner::LitBytes(b).wrap(Type::Bytes), TypeFacts::empty())),
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
            let itype = Type::Bytes;
            Ok((ExprInner::LitBVec(args).wrap(itype), TypeFacts::empty()))
        }
        RawExpr::Unsafe(s) => typecheck_expr(state.bind_safety(false), s),
    }
}

fn type_vector_ref(vtype: &Type, itype: &Type) -> anyhow::Result<Type> {
    if !itype.subtype_of(&Type::Nat) {
        anyhow::bail!("vector index not a Nat")
    }
    // we go through the type recursively, building up a union
    match vtype {
        Type::Vectorof(t) => Ok(t.as_ref().clone()),
        Type::Vector(lst) => Ok(lst.iter().fold(Type::Nothing, |a, b| a.smart_union(b))),
        Type::Union(t, u) => Ok(Type::Union(
            type_vector_ref(t, itype)?.into(),
            type_vector_ref(u, itype)?.into(),
        )),
        t => anyhow::bail!("type {:?} cannot be index into", t),
    }
}

fn typecheck_type_expr(state: &Scope, raw: Ctx<RawTypeExpr>) -> CtxResult<Type> {
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
            Ok(Type::Vectorof(v.into()))
        }

        RawTypeExpr::DynBytes => Ok(Type::Bytes),
    }
}

#[cfg(test)]
mod tests {

    use std::path::Path;

    use log::LevelFilter;

    use super::*;
    use crate::{context::ModuleId, grammar::parse_program};

    #[test]
    fn typecheck_simple() {
        init_logs();
        let state = Scope::new();
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
def identity<T>(x: T): T = x
def foo(): Nat = succ(0)
def succ(x: Nat): Nat = x + 1
--- 
foo()
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
    fn typecheck_whole() {
        init_logs();
        let module = ModuleId::from_path(Path::new("whatever.melo"));
        eprintln!(
            "{:?}",
            typecheck_program(
                parse_program(
                    r"
def even(n: Nat): Nat = if n == 0 then 1 else !odd(n - 1)
def odd (n: Nat): Nat = if n == 1 then 1 else !even(n - 1)

---

even(200)
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
