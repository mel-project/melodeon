use std::sync::Arc;

use bytes::Bytes;
use ethnum::U256;

use crate::containers::{List, Map, Symbol, Void};

use crate::typesys::{ConstExpr, Type, Variable};

#[derive(Debug, Clone)]
pub struct Program {
    pub fun_defs: List<FunDefn>,
    pub body: Expr,
}

#[derive(Debug, Clone)]
pub struct FunDefn<TVar: Variable = Void, CVar: Variable = Void> {
    pub name: Symbol,
    pub args: List<Symbol>,
    pub body: Expr<TVar, CVar>,
}

#[derive(Debug, Clone)]
pub struct Expr<TVar: Variable = Void, CVar: Variable = Void> {
    pub itype: Type<TVar, CVar>,
    pub inner: ExprInner<TVar, CVar>,
}

impl<TVar: Variable, CVar: Variable> Expr<TVar, CVar> {
    pub fn new(itype: Type<TVar, CVar>, inner: ExprInner<TVar, CVar>) -> Self {
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
            ExprInner::Let(s, b, i) => ExprInner::Let(*s, recurse(b).into(), recurse(i).into()),
            ExprInner::Apply(f, args) => ExprInner::Apply(*f, args.iter().map(recurse).collect()),
            ExprInner::ApplyGeneric(f, tg, cg, args) => ExprInner::ApplyGeneric(
                *f,
                tg.clone(),
                cg.clone(),
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
            ExprInner::Loop(count, sets, end) => ExprInner::Loop(
                count.clone(),
                sets.iter().map(|(a, b)| (*a, recurse(b))).collect(),
                recurse(end).into(),
            ),
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
pub enum ExprInner<TVar: Variable, CVar: Variable> {
    BinOp(BinOp, Arc<Expr<TVar, CVar>>, Arc<Expr<TVar, CVar>>),
    UniOp(UniOp, Arc<Expr<TVar, CVar>>),
    Exp(ConstExpr<CVar>, Arc<Expr<TVar, CVar>>, ConstExpr<CVar>),
    If(
        Arc<Expr<TVar, CVar>>,
        Arc<Expr<TVar, CVar>>,
        Arc<Expr<TVar, CVar>>,
    ),
    Let(Symbol, Arc<Expr<TVar, CVar>>, Arc<Expr<TVar, CVar>>),
    Apply(Symbol, List<Expr<TVar, CVar>>),
    ExternApply(String, List<Expr<TVar, CVar>>),
    Extern(String),
    ApplyGeneric(
        Symbol,
        Map<TVar, Type<TVar, CVar>>,
        Map<CVar, ConstExpr<CVar>>,
        List<Expr<TVar, CVar>>,
    ),
    LitNum(U256),
    LitBytes(Bytes),
    LitBVec(List<Expr<TVar, CVar>>),
    LitVec(List<Expr<TVar, CVar>>),
    LitConst(ConstExpr<CVar>),
    Var(Symbol),
    IsType(Symbol, Type<TVar, CVar>),
    VectorRef(Arc<Expr<TVar, CVar>>, Arc<Expr<TVar, CVar>>),
    VectorUpdate(
        Arc<Expr<TVar, CVar>>,
        Arc<Expr<TVar, CVar>>,
        Arc<Expr<TVar, CVar>>,
    ),
    VectorSlice(
        Arc<Expr<TVar, CVar>>,
        Arc<Expr<TVar, CVar>>,
        Arc<Expr<TVar, CVar>>,
    ),
    Loop(
        ConstExpr<CVar>,
        List<(Symbol, Expr<TVar, CVar>)>,
        Arc<Expr<TVar, CVar>>,
    ),
    Fail,
}

impl<TVar: Variable, CVar: Variable> ExprInner<TVar, CVar> {
    /// Convenience type to wrap in an Expr with the any type
    pub fn wrap_any(self) -> Expr<TVar, CVar> {
        Expr {
            inner: self,
            itype: Type::Any,
        }
    }

    /// Convenience type to wrap in an Expr with the given type
    pub fn wrap(self, t: Type<TVar, CVar>) -> Expr<TVar, CVar> {
        Expr {
            inner: self,
            itype: t,
        }
    }
}

/// Unary operator
#[derive(Clone, Copy, Debug)]
pub enum UniOp {
    Bnot
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
