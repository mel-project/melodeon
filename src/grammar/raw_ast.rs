use ethnum::U256;

use crate::{
    containers::{List, Symbol},
    context::Ctx,
};

/// A whole program.
#[derive(Clone, Debug)]
pub struct RawProgram {
    pub definitions: List<Ctx<RawDefn>>,
    pub body: Ctx<RawExpr>,
}

/// A definition.
#[derive(Clone, Debug)]
pub enum RawDefn {
    Function {
        name: Ctx<Symbol>,
        cgvars: List<Ctx<Symbol>>,
        genvars: List<Ctx<Symbol>>,
        args: List<Ctx<RawTypeBind>>,
        rettype: Option<Ctx<RawTypeExpr>>,
        body: Ctx<RawExpr>,
    },
    Constant(Ctx<Symbol>, Ctx<RawExpr>),
}

/// A type binding
#[derive(Clone, Debug)]
pub struct RawTypeBind {
    pub name: Ctx<Symbol>,
    pub bind: Ctx<RawTypeExpr>,
}

/// A raw type expression
#[derive(Clone, Debug)]
pub enum RawTypeExpr {
    Sym(Symbol),
    Union(Ctx<Self>, Ctx<Self>),
    Vector(List<Ctx<Self>>),
    Vectorof(Ctx<Self>, Ctx<RawConstExpr>),
}

/// A raw constant expression.
#[derive(Clone, Debug)]
pub enum RawConstExpr {
    Sym(Symbol),
    Lit(U256),
    Plus(Ctx<Self>, Ctx<Self>),
    Mult(Ctx<Self>, Ctx<Self>),
}

/// A raw expression.
#[derive(Clone, Debug)]
pub enum RawExpr {
    Let(Ctx<Symbol>, Ctx<Self>, Ctx<Self>),
    If(Ctx<Self>, Ctx<Self>, Ctx<Self>),

    BinOp(Ctx<BinOp>, Ctx<RawExpr>, Ctx<RawExpr>),
    LitNum(U256),
    Var(Symbol),

    Apply(Ctx<Self>, List<Ctx<Self>>),
    Field(Ctx<Self>, Ctx<Symbol>),
    VectorRef(Ctx<Self>, Ctx<Self>),
    VectorUpdate(Ctx<Self>, Ctx<Self>),
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
