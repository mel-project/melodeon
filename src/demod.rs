use std::{ops::Deref, path::Path, sync::Arc};

use dashmap::DashMap;
use rayon::iter::{IntoParallelRefIterator, ParallelIterator};

use crate::{
    containers::{List, Set, Symbol},
    context::{Ctx, CtxErr, CtxResult, ModuleId, ToCtx, ToCtxErr},
    grammar::{parse_program, RawDefn, RawExpr, RawProgram, RawTypeBind, RawTypeExpr},
};

/// A struct that encapsulates a parallel demodularizer that eliminates "require" and "provide" in a raw AST.
pub struct Demodularizer {
    cache: DashMap<ModuleId, Ctx<RawProgram>>,
    fallback: Arc<dyn Fn(ModuleId) -> anyhow::Result<String> + Send + Sync + 'static>,
}

impl Demodularizer {
    /// Overrides a particular path in the demodularization cache.
    pub fn module_override(&mut self, id: ModuleId, content: String) {
        let fallback = self.fallback.clone();
        self.fallback = Arc::new(move |i| {
            if i == id {
                Ok(content.clone())
            } else {
                fallback(i)
            }
        })
    }

    /// Creates a new demodularizer, rooted at some filesystem.
    pub fn new_at_fs(root: &Path, global_root: &Path) -> Self {
        let root = root.to_owned();
        let global_root = global_root.to_owned();
        let fallback =
            move |mid: ModuleId| {
                let mid = mid.to_string();
                if let Some(stripped) = mid.strip_prefix('$') {
                    let mut root = global_root.clone();
                    root.push(&stripped);
                    log::debug!("reading library {:?}", root);
                    Ok(std::fs::read_to_string(&Path::new(&format!(
                        "{}.melo",
                        root.to_string_lossy()
                    )))
                    .or_else(|_| {
                        std::fs::read_to_string(&Path::new(&format!(
                            "{}/main.melo",
                            root.to_string_lossy()
                        )))
                    })?)
                } else {
                    let mut root = root.clone();
                    root.push(&mid);
                    Ok(std::fs::read_to_string(&root)?)
                }
            };
        Self {
            cache: DashMap::new(),
            fallback: Arc::new(fallback),
        }
    }

    /// Return the demodularized version of some module ID.
    pub fn demod(&self, id: ModuleId, root: &Path) -> CtxResult<Ctx<RawProgram>> {
        if let Some(res) = self.cache.get(&id) {
            log::debug!("demod {} HIT!", id);
            Ok(res.deref().clone())
        } else {
            log::debug!("demod {} MISS!", id);
            // populate the cache
            let raw_string = (self.fallback)(id).err_ctx(None)?;
            let parsed = parse_program(&raw_string, id, root)?;
            // go through the dependencies in parallel, demodularizing as we go

            #[cfg(target_arch = "wasm32")]
            let mut new_defs =
                parsed
                    .definitions
                    .iter()
                    .fold(Ok::<_, CtxErr>(List::new()), |accum, def| {
                        let mut accum = accum?;
                        match def.deref() {
                            RawDefn::Require(other) => {
                                let other_demodularized = self.demod(*other, root)?;
                                accum.append(&mut mangle(
                                    other_demodularized.definitions.clone(),
                                    *other,
                                ));
                            }
                            //_ => accum.push_back(def.clone()),
                            _ => accum.push(def.clone()),
                        }
                        Ok(accum)
                    })?;

            #[cfg(not(target_arch = "wasm32"))]
            let mut new_defs = parsed
                .definitions
                .par_iter()
                .fold(
                    || Ok::<_, CtxErr>(List::new()),
                    |accum, def| {
                        let mut accum = accum?;
                        match def.deref() {
                            RawDefn::Require(other) => {
                                let other_demodularized = self.demod(*other, root)?;
                                accum.append(&mut mangle(
                                    other_demodularized.definitions.clone(),
                                    *other,
                                ));
                            }
                            //_ => accum.push_back(def.clone()),
                            _ => accum.push(def.clone()),
                        }
                        Ok(accum)
                    },
                )
                .reduce(
                    || Ok::<_, CtxErr>(List::new()),
                    |a, b| {
                        let mut a = a?;
                        a.append(&mut b?);
                        Ok(a)
                    },
                )?;

            // INJECT the stdlib
            let stdlib = parse_program(
                include_str!("stdlib.melo"),
                ModuleId::from_path(Path::new("STDLIB")),
                root,
            )
            .unwrap();
            new_defs.append(&mut stdlib.definitions.clone());
            Ok(RawProgram {
                definitions: new_defs,
                body: parsed.body.clone(),
            }
            .with_ctx(parsed.ctx()))
        }
    }
}

fn mangle(defs: List<Ctx<RawDefn>>, source: ModuleId) -> List<Ctx<RawDefn>> {
    let no_mangle: Set<Symbol> = defs
        .iter()
        .filter_map(|a| {
            if let RawDefn::Provide(a) = a.deref() {
                Some(*a)
            } else {
                None
            }
        })
        .collect();
    log::debug!("no_mangle for {}: {:?}", source, no_mangle);
    defs.into_iter()
        .filter_map(|defn| {
            match defn.deref().clone() {
                RawDefn::Function {
                    name,
                    genvars,
                    args,
                    rettype,
                    body,
                } => {
                    let inner_nomangle = genvars
                        .iter()
                        .map(|a| **a)
                        .chain(args.iter().map(|a| *a.name))
                        .fold(no_mangle.clone(), |mut acc, s| {
                            acc.insert(s);
                            acc
                        });
                    Some(RawDefn::Function {
                        name: mangle_ctx_sym(name, source, &no_mangle),

                        genvars,
                        args: args
                            .into_iter()
                            .map(|arg| {
                                let ctx = arg.ctx();
                                let mut arg = arg.deref().clone();
                                let new_bind =
                                    mangle_type_expr(arg.bind.clone(), source, &inner_nomangle);
                                arg.bind = new_bind;
                                arg.with_ctx(ctx)
                            })
                            .collect(),
                        rettype: rettype.map(|rt| mangle_type_expr(rt, source, &inner_nomangle)),
                        body: mangle_expr(body, source, &inner_nomangle),
                    })
                }
                RawDefn::Struct { name, fields } => Some(RawDefn::Struct {
                    name: mangle_ctx_sym(name, source, &no_mangle),
                    fields: fields
                        .into_iter()
                        .map(|rtb| {
                            RawTypeBind {
                                name: rtb.name.clone(),
                                bind: mangle_type_expr(rtb.bind.clone(), source, &no_mangle),
                            }
                            .with_ctx(rtb.ctx())
                        })
                        .collect(),
                }),
                RawDefn::Constant(_, _) => todo!(),
                RawDefn::Require(_) => None,
                RawDefn::Provide(_) => None,
                RawDefn::TypeAlias(t, a) => Some(RawDefn::TypeAlias(
                    mangle_ctx_sym(t, source, &no_mangle),
                    mangle_type_expr(a, source, &no_mangle),
                )),
            }
            .map(|c| c.with_ctx(defn.ctx()))
        })
        .collect()
}

fn mangle_expr(expr: Ctx<RawExpr>, source: ModuleId, no_mangle: &Set<Symbol>) -> Ctx<RawExpr> {
    let recurse = |expr| mangle_expr(expr, source, no_mangle);
    let ctx = expr.ctx();
    match expr.deref().clone() {
        RawExpr::Let(binds, body) => {
            let mut inner_no_mangle = no_mangle.clone();
            for (sym, _) in binds.iter() {
                inner_no_mangle.insert(*sym.deref());
            }

            RawExpr::Let(
                binds.into_iter().map(|(s, v)| (s, recurse(v))).collect(),
                mangle_expr(body, source, &inner_no_mangle),
            )
        }
        RawExpr::If(cond, a, b) => RawExpr::If(recurse(cond), recurse(a), recurse(b)),
        RawExpr::UniOp(op, a) => RawExpr::UniOp(op, recurse(a)),
        RawExpr::BinOp(op, a, b) => RawExpr::BinOp(op, recurse(a), recurse(b)),
        RawExpr::LitNum(a) => RawExpr::LitNum(a),
        RawExpr::LitVec(v) => RawExpr::LitVec(v.into_iter().map(recurse).collect()),
        RawExpr::LitStruct(a, fields) => RawExpr::LitStruct(
            mangle_sym(a, source, no_mangle),
            fields.into_iter().map(|(k, b)| (k, recurse(b))).collect(),
        ),
        RawExpr::Var(v) => RawExpr::Var(mangle_sym(v, source, no_mangle)),

        RawExpr::Apply(f, t, args) => RawExpr::Apply(
            recurse(f),
            t.into_iter()
                .map(|(k, v)| {
                    (
                        mangle_sym(k, source, no_mangle),
                        mangle_type_expr(v, source, no_mangle),
                    )
                })
                .collect(),
            args.into_iter().map(recurse).collect(),
        ),
        RawExpr::Field(a, b) => RawExpr::Field(recurse(a), b),
        RawExpr::VectorRef(v, i) => RawExpr::VectorRef(recurse(v), recurse(i)),
        RawExpr::VectorSlice(v, i, j) => RawExpr::VectorSlice(recurse(v), recurse(i), recurse(j)),
        RawExpr::VectorUpdate(v, i, x) => RawExpr::VectorUpdate(recurse(v), recurse(i), recurse(x)),

        RawExpr::IsType(a, t) => RawExpr::IsType(
            mangle_sym(a, source, no_mangle),
            mangle_type_expr(t, source, no_mangle),
        ),
        RawExpr::AsType(a, t) => {
            RawExpr::AsType(recurse(a), mangle_type_expr(t, source, no_mangle))
        }
        RawExpr::Fail => RawExpr::Fail,
        RawExpr::For(sym, bind, body) => {
            let mut inner_no_mangle = no_mangle.clone();
            inner_no_mangle.insert(*sym);
            RawExpr::For(
                sym,
                recurse(bind),
                mangle_expr(body, source, &inner_no_mangle),
            )
        }
        RawExpr::Transmute(a, t) => {
            RawExpr::Transmute(recurse(a), mangle_type_expr(t, source, no_mangle))
        }
        RawExpr::ForFold(loop_sym, loop_bind, accum_sym, accum_bind, body) => {
            let mut inner_no_mangle = no_mangle.clone();
            inner_no_mangle.insert(*loop_sym);
            inner_no_mangle.insert(*accum_sym);
            RawExpr::ForFold(
                loop_sym,
                recurse(loop_bind),
                accum_sym,
                recurse(accum_bind),
                mangle_expr(body, source, &inner_no_mangle),
            )
        }
        RawExpr::LitBytes(b) => RawExpr::LitBytes(b),
        RawExpr::LitBVec(vv) => RawExpr::LitBVec(vv.into_iter().map(recurse).collect()),
        RawExpr::Unsafe(s) => RawExpr::Unsafe(recurse(s)),
        RawExpr::Extern(s) => RawExpr::Extern(s),
        RawExpr::ExternApply(f, args) => {
            RawExpr::ExternApply(f, args.into_iter().map(recurse).collect())
        }
    }
    .with_ctx(ctx)
}

fn mangle_ctx_sym(sym: Ctx<Symbol>, source: ModuleId, no_mangle: &Set<Symbol>) -> Ctx<Symbol> {
    mangle_sym(*sym, source, no_mangle).with_ctx(sym.ctx())
}

fn mangle_sym(sym: Symbol, source: ModuleId, no_mangle: &Set<Symbol>) -> Symbol {
    if no_mangle.contains(&sym)
        || sym == Symbol::from("Nat")
        || sym == Symbol::from("Any")
        || sym == Symbol::from("None")
    {
        sym
    } else {
        Symbol::from(format!("{:?}-{}", sym, source.uniqid()).as_str())
    }
}

fn mangle_type_expr(
    bind: Ctx<RawTypeExpr>,
    source: ModuleId,
    no_mangle: &Set<Symbol>,
) -> Ctx<RawTypeExpr> {
    let recurse = |bind| mangle_type_expr(bind, source, no_mangle);
    match bind.deref().clone() {
        RawTypeExpr::Sym(s) => RawTypeExpr::Sym(mangle_sym(s, source, no_mangle)),
        RawTypeExpr::Union(a, b) => RawTypeExpr::Union(recurse(a), recurse(b)),
        RawTypeExpr::Vector(v) => RawTypeExpr::Vector(v.into_iter().map(recurse).collect()),

        RawTypeExpr::DynVectorof(v) => RawTypeExpr::DynVectorof(recurse(v)),

        RawTypeExpr::DynBytes => RawTypeExpr::DynBytes,
    }
    .with_ctx(bind.ctx())
}
