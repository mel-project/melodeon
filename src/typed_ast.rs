use std::sync::Arc;

use bytes::Bytes;
use ethnum::U256;

use crate::containers::{List, Map, Symbol};

use crate::typesys::Type;

#[derive(Debug, Clone)]
pub struct Program {
    pub fun_defs: List<FunDefn>,
    pub body: Expr,
}

#[derive(Debug, Clone)]
pub struct FunDefn {
    pub name: Symbol,
    pub args: List<Symbol>,
    pub body: Expr,
}

#[derive(Debug, Clone)]
pub struct Expr {
    pub itype: Type,
    pub inner: ExprInner,
}

impl Expr {
    pub fn new(itype: Type, inner: ExprInner) -> Self {
        Self { itype, inner }
    }

    /// Unconditionally structure-preserving map.
    pub fn recursive_map(&self, f: impl Fn(Self) -> Self + Copy) -> Self {
        let recurse = |o: &Self| o.recursive_map(f);
        let new_inner = match &self.inner {
            ExprInner::BinOp(o, a, b) => ExprInner::BinOp(*o, recurse(a).into(), recurse(b).into()),
            ExprInner::If(c, a, b) => {
                ExprInner::If(recurse(c).into(), recurse(a).into(), recurse(b).into())
            }
            //ExprInner::Let(s, b, i) => ExprInner::Let(*s, recurse(b).into(), recurse(i).into()),
            ExprInner::Let(binds, i) => ExprInner::Let(
                binds.iter().map(|(s, b)| (*s, recurse(b).into())).collect(),
                recurse(i).into(),
            ),
            ExprInner::Apply(f, args) => {
                ExprInner::Apply(recurse(f).into(), args.iter().map(recurse).collect())
            }
            ExprInner::ApplyGeneric(f, tg, args) => ExprInner::ApplyGeneric(
                recurse(f).into(),
                tg.clone(),
                args.iter().map(recurse).collect(),
            ),
            ExprInner::VectorRef(v, i) => {
                ExprInner::VectorRef(recurse(v).into(), recurse(i).into())
            }
            ExprInner::VectorUpdate(v, i, x) => {
                ExprInner::VectorUpdate(recurse(v).into(), recurse(i).into(), recurse(x).into())
            }
            ExprInner::VectorSlice(v, i, j) => {
                ExprInner::VectorSlice(recurse(v).into(), recurse(i).into(), recurse(j).into())
            }

            _ => self.inner.clone(),
        };
        let nova = Self {
            inner: new_inner,
            itype: self.itype.clone(),
        };
        f(nova)
    }
}

#[derive(Debug, Clone)]
pub enum ExprInner {
    BinOp(BinOp, Arc<Expr>, Arc<Expr>),
    UniOp(UniOp, Arc<Expr>),

    If(Arc<Expr>, Arc<Expr>, Arc<Expr>),
    //Let(Symbol, Arc<Expr<TVar, CVar>>, Arc<Expr<TVar, CVar>>),
    Let(List<(Symbol, Arc<Expr>)>, Arc<Expr>),
    ExternCall(Symbol, List<Expr>),
    Apply(Arc<Expr>, List<Expr>),

    ApplyGeneric(Arc<Expr>, Map<Symbol, Type>, List<Expr>),
    LitNum(U256),
    LitBytes(Bytes),
    LitBVec(List<Expr>),
    LitVec(List<Expr>),

    Var(Symbol),
    IsType(Symbol, Type),
    VectorRef(Arc<Expr>, Arc<Expr>),
    VectorUpdate(Arc<Expr>, Arc<Expr>, Arc<Expr>),
    VectorSlice(Arc<Expr>, Arc<Expr>, Arc<Expr>),

    Lambda(List<(Symbol, Type)>, Arc<Expr>),

    Fail,
}

impl ExprInner {
    /// Convenience type to wrap in an Expr with the any type
    pub fn wrap_any(self) -> Expr {
        Expr {
            inner: self,
            itype: Type::Any,
        }
    }

    /// Convenience type to wrap in an Expr with the given type
    pub fn wrap(self, t: Type) -> Expr {
        Expr {
            inner: self,
            itype: t,
        }
    }
}

/// Unary operator
#[derive(Clone, Copy, Debug)]
pub enum UniOp {
    Bnot,
    TypeQ,
    Vlen,
    Blen,
}

/// Binary operator
#[derive(Clone, Copy, Debug)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    Expt,

    Append,

    Vappend,
    Bappend,

    Eq,
    NumEq,
    Lt,
    Le,
    Gt,
    Ge,

    Bor,
    Band,
    Bxor,

    Lshift,
    Rshift,
}

/// Ternary operator
#[derive(Clone, Copy, Debug)]
pub enum TriOp {
    Exp,
}
