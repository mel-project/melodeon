use std::sync::Arc;

use bytes::Bytes;
use ethnum::U256;

use crate::containers::{List, Map, Symbol, Void};

use crate::typesys::{Type, Variable};

#[derive(Debug, Clone)]
pub struct Program {
    pub fun_defs: List<FunDefn>,
    pub body: Expr,
}

#[derive(Debug, Clone)]
pub struct FunDefn<TVar: Variable = Void> {
    pub name: Symbol,
    pub args: List<Symbol>,
    pub body: Expr<TVar>,
}

#[derive(Debug, Clone)]
pub struct Expr<TVar: Variable = Void> {
    pub itype: Type<TVar>,
    pub inner: ExprInner<TVar>,
}

impl<TVar: Variable> Expr<TVar> {
    pub fn new(itype: Type<TVar>, inner: ExprInner<TVar>) -> Self {
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
pub enum ExprInner<TVar: Variable> {
    BinOp(BinOp, Arc<Expr<TVar>>, Arc<Expr<TVar>>),
    UniOp(UniOp, Arc<Expr<TVar>>),
    /// The first one is an **upper bound** for how big the exponent is
    Exp(U256, Arc<Expr<TVar>>, Arc<Expr<TVar>>),
    If(Arc<Expr<TVar>>, Arc<Expr<TVar>>, Arc<Expr<TVar>>),
    //Let(Symbol, Arc<Expr<TVar, CVar>>, Arc<Expr<TVar, CVar>>),
    Let(List<(Symbol, Arc<Expr<TVar>>)>, Arc<Expr<TVar>>),
    Apply(Arc<Expr<TVar>>, List<Expr<TVar>>),

    ApplyGeneric(Arc<Expr<TVar>>, Map<TVar, Type<TVar>>, List<Expr<TVar>>),
    LitNum(U256),
    LitBytes(Bytes),
    LitBVec(List<Expr<TVar>>),
    LitVec(List<Expr<TVar>>),

    Var(Symbol),
    IsType(Symbol, Type<TVar>),
    VectorRef(Arc<Expr<TVar>>, Arc<Expr<TVar>>),
    VectorUpdate(Arc<Expr<TVar>>, Arc<Expr<TVar>>, Arc<Expr<TVar>>),
    VectorSlice(Arc<Expr<TVar>>, Arc<Expr<TVar>>, Arc<Expr<TVar>>),

    Fail,
}

impl<TVar: Variable> ExprInner<TVar> {
    /// Convenience type to wrap in an Expr with the any type
    pub fn wrap_any(self) -> Expr<TVar> {
        Expr {
            inner: self,
            itype: Type::Any,
        }
    }

    /// Convenience type to wrap in an Expr with the given type
    pub fn wrap(self, t: Type<TVar>) -> Expr<TVar> {
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
}

/// Binary operator
#[derive(Clone, Copy, Debug)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod,

    Append,

    Eq,
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
