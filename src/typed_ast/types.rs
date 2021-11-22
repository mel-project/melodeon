use std::sync::Arc;

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
}

#[derive(Debug, Clone)]
pub enum ExprInner<TVar: Variable, CVar: Variable> {
    BinOp(BinOp, Arc<Expr<TVar, CVar>>, Arc<Expr<TVar, CVar>>),
    If(
        Arc<Expr<TVar, CVar>>,
        Arc<Expr<TVar, CVar>>,
        Arc<Expr<TVar, CVar>>,
    ),
    Let(Symbol, Arc<Expr<TVar, CVar>>, Arc<Expr<TVar, CVar>>),
    Apply(Symbol, List<Expr<TVar, CVar>>),
    ApplyGeneric(
        Symbol,
        Map<TVar, Type<TVar, CVar>>,
        Map<CVar, ConstExpr<CVar>>,
        List<Expr<TVar, CVar>>,
    ),
    LitNum(U256),
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

/// Binary operator
#[derive(Clone, Copy, Debug)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,

    Append,

    Eq,
}
