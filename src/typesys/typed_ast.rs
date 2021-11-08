use std::sync::Arc;

use ethnum::U256;

use crate::containers::{List, Symbol, Void};

use super::{Type, Variable};

#[derive(Debug, Clone)]
pub struct Program {
    pub fun_defs: List<FunDefn>,
    pub body: Expr,
}

#[derive(Debug, Clone)]
pub struct FunDefn<TVar: Variable = Void, CVar: Variable = Void> {
    pub name: Symbol,
    pub args: List<(Symbol, Type<TVar, CVar>)>,
    pub body: Expr<TVar, CVar>,
}

#[derive(Debug, Clone)]
pub struct Expr<TVar: Variable = Void, CVar: Variable = Void> {
    pub itype: Type<TVar, CVar>,
    pub inner: ExprInner<TVar, CVar>,
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
    Apply(Arc<Expr<TVar, CVar>>, List<Arc<Expr<TVar, CVar>>>),
    LitNum(U256),
    Var(Symbol),
}

/// Binary operator
#[derive(Clone, Copy, Debug)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,

    Eq,
}
