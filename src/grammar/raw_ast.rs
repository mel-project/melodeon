use bytes::Bytes;
use ethnum::U256;
use tap::Pipe;

use crate::{
    containers::{List, Map, Set, Symbol},
    context::{Ctx, ModuleId},
    typesys::{Type, Variable},
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
        genvars: List<Ctx<Symbol>>,
        args: List<Ctx<RawTypeBind>>,
        rettype: Option<Ctx<RawTypeExpr>>,
        body: Ctx<RawExpr>,
    },
    Struct {
        name: Ctx<Symbol>,
        fields: List<Ctx<RawTypeBind>>,
    },

    Constant(Ctx<Symbol>, Ctx<RawExpr>),
    Require(ModuleId),
    Provide(Symbol),
    TypeAlias(Ctx<Symbol>, Ctx<RawTypeExpr>),
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
    DynVectorof(Ctx<Self>),
    Bytes(Ctx<RawConstExpr>),
    DynBytes,
    NatRange(Ctx<RawConstExpr>, Ctx<RawConstExpr>),
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
    //Let(Ctx<Symbol>, Ctx<Self>, Ctx<Self>),
    Let(List<(Ctx<Symbol>, Ctx<Self>)>, Ctx<Self>),
    For(Ctx<Symbol>, Ctx<Self>, Ctx<Self>),
    ForFold(Ctx<Symbol>, Ctx<Self>, Ctx<Symbol>, Ctx<Self>, Ctx<Self>),
    If(Ctx<Self>, Ctx<Self>, Ctx<Self>),
    Fail,

    BinOp(Ctx<BinOp>, Ctx<RawExpr>, Ctx<RawExpr>),
    UniOp(Ctx<UniOp>, Ctx<RawExpr>),
    LitNum(U256),
    LitBytes(Bytes),
    LitBVec(List<Ctx<Self>>),
    LitVec(List<Ctx<Self>>),
    LitStruct(Symbol, Map<Symbol, Ctx<RawExpr>>),
    Var(Symbol),

    Apply(
        Ctx<Self>,
        Map<Symbol, Ctx<RawTypeExpr>>,
        Map<Symbol, Ctx<RawConstExpr>>,
        List<Ctx<Self>>,
    ),

    Field(Ctx<Self>, Ctx<Symbol>),
    VectorRef(Ctx<Self>, Ctx<Self>),
    VectorSlice(Ctx<Self>, Ctx<Self>, Ctx<Self>),
    VectorUpdate(Ctx<Self>, Ctx<Self>, Ctx<Self>),

    Loop(Ctx<RawConstExpr>, List<(Symbol, Ctx<Self>)>, Ctx<Self>),

    IsType(Symbol, Ctx<RawTypeExpr>),
    AsType(Ctx<Self>, Ctx<RawTypeExpr>),

    Transmute(Ctx<Self>, Ctx<RawTypeExpr>),

    Unsafe(Ctx<Self>),
    Extern(Ctx<String>),
    ExternApply(Ctx<String>, List<Ctx<Self>>),
}

/// Unary operator
#[derive(Clone, Copy, Debug)]
pub enum UniOp {
    Bnot,
    Lnot,
}

/// Binary operator
#[derive(Clone, Copy, Debug)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod,

    Lor,
    Land,

    Bor,
    Band,
    Bxor,

    Lshift,
    Rshift,

    Append,

    Eq,
    Le,
    Lt,
    Ge,
    Gt,

    Exp,
}

pub fn sort_defs(defs: List<Ctx<RawDefn>>) -> List<Ctx<RawDefn>> {
    let mut sorted = List::new();
    let mut visited = Set::new();

    for def in defs.iter() {
        visit(def.name(), &defs, &mut sorted, &mut visited);
    }

    log::debug!(
        "definitions sorted: {:?}",
        sorted.iter().map(|d| d.name()).collect::<Vec<_>>()
    );

    sorted
}

fn visit(
    def: Symbol,
    defs: &List<Ctx<RawDefn>>,
    sorted: &mut List<Ctx<RawDefn>>,
    visited: &mut Set<Symbol>,
) {
    if !visited.contains(&def) {
        visited.insert(def);
        log::trace!("visiting {:?}", def);

        let def = find_by_name(defs, def);
        if let Some(def) = def {
            for parent in def.parents() {
                log::trace!("{:?} depends on {:?}", def.name(), parent);
                visit(parent, defs, sorted, visited);
            }
            sorted.push(def.clone());
        }
    }
}

pub fn find_by_name(defs: &List<Ctx<RawDefn>>, name: Symbol) -> Option<&Ctx<RawDefn>> {
    defs.iter().find(|def| def.name() == name)
}

impl RawDefn {
    /// Get the name of a definition
    pub fn name(&self) -> Symbol {
        match self {
            RawDefn::Function { name, .. } => **name,
            RawDefn::Struct { name, .. } => **name,
            RawDefn::Constant(name, _) => **name,
            RawDefn::TypeAlias(name, _) => **name,
            _ => Symbol::from("undefined"),
        }
    }

    /// Get a list of all definition names referenced in a definition's body.
    pub fn parents(&self) -> Set<Symbol> {
        match self {
            RawDefn::Function {
                args,
                body,
                genvars,
                rettype,
                ..
            } => expr_parents(body)
                .relative_complement(
                    args.iter()
                        .map(|a| *a.name)
                        .chain(genvars.iter().map(|a| **a))
                        .collect(),
                )
                .pipe(|s| {
                    if let Some(rettype) = rettype.as_ref() {
                        s.union(typebind_parents(rettype))
                    } else {
                        s
                    }
                }),
            RawDefn::Struct { name: _, fields } => fields.iter().fold(Set::new(), |acc, field| {
                acc.union(typebind_parents(&field.bind))
            }),
            RawDefn::Constant(_, body) => expr_parents(body),
            RawDefn::Require(_) => Set::new(),
            RawDefn::Provide(_) => Set::new(),
            RawDefn::TypeAlias(_, a) => typebind_parents(a),
        }
    }
}

fn typebind_parents(tb: &RawTypeExpr) -> Set<Symbol> {
    let rec = typebind_parents;

    match tb {
        RawTypeExpr::Sym(sym) => {
            if sym == &Symbol::from("Nat")
                || sym == &Symbol::from("Any")
                || sym == &Symbol::from("None")
            {
                Set::new()
            } else {
                Set::unit(*sym)
            }
        }
        RawTypeExpr::Union(l, r) => rec(l).union(rec(r)),
        RawTypeExpr::Vector(l) => l.iter().fold(Set::new(), |acc, t| acc.union(rec(t))),
        RawTypeExpr::Vectorof(t, _) => rec(t),
        RawTypeExpr::NatRange(_, _) => Set::new(),
        RawTypeExpr::DynVectorof(v) => rec(v),
        RawTypeExpr::Bytes(_) => Set::new(),
        RawTypeExpr::DynBytes => Set::new(),
    }
}

impl RawExpr {
    pub fn free_variables<Tv: Variable>(&self, var_set: &Map<Symbol, Type<Tv>>) -> Set<Symbol> {
        let vars = expr_parents(self);
        vars.into_iter()
            .filter(|sym| var_set.contains_key(sym))
            .collect()
    }
}

fn expr_parents(expr: &RawExpr) -> Set<Symbol> {
    let rec = expr_parents;

    match expr {
        // Important cases
        RawExpr::Var(var) => Set::unit(*var),
        //RawExpr::Let(var, val, body) => rec(val).union(rec(body)).without(var),
        RawExpr::Let(binds, body) => {
            let vars: Vec<Ctx<Symbol>> = binds.iter().map(|(v, _)| v.clone()).collect();
            let vals: Vec<Ctx<RawExpr>> = binds.iter().map(|(_, v)| v.clone()).collect();
            vars.iter().fold(
                vals.iter()
                    .fold(Set::new(), |acc, v| acc.union(rec(v)))
                    .union(rec(body)),
                |acc, var| acc.without(var),
            )
        }
        RawExpr::Apply(fn_name, _, _, args) => args
            .iter()
            .fold(rec(fn_name), |acc, arg| acc.union(rec(arg))),
        RawExpr::LitStruct(s_name, fields) => fields
            .values()
            .fold(Set::unit(*s_name), |acc, field| acc.union(rec(field))),

        // Trivial cases
        RawExpr::VectorRef(v, idx) => rec(v).union(rec(idx)),
        RawExpr::VectorUpdate(v, old, new) => rec(v).union(rec(old)).union(rec(new)),
        RawExpr::VectorSlice(v, from, to) => rec(v).union(rec(from)).union(rec(to)),
        RawExpr::If(p, t, f) => rec(p).union(rec(t)).union(rec(f)),
        RawExpr::UniOp(_, a) => rec(a),
        RawExpr::BinOp(_, a, b) => rec(a).union(rec(b)),
        RawExpr::Field(strct, _) => rec(strct),
        RawExpr::LitVec(v) | RawExpr::LitBVec(v) => {
            v.iter().fold(Set::new(), |acc, e| acc.union(rec(e)))
        }
        RawExpr::For(var, val, body) => rec(val).union(rec(body)).without(var),
        RawExpr::ForFold(var, val, avar, aval, body) => rec(val)
            .union(rec(aval))
            .union(rec(body))
            .without(var)
            .without(avar),
        RawExpr::Fail => Set::new(),
        RawExpr::LitNum(_) => Set::new(),
        RawExpr::Loop(_, body, inner) => body
            .iter()
            .map(|a| rec(&a.1))
            .fold(Set::new(), |a, b| a.union(b))
            .union(rec(inner)),
        RawExpr::IsType(v, t) => Set::unit(*v).union(typebind_parents(t)),
        RawExpr::AsType(a, t) | RawExpr::Transmute(a, t) => rec(a).union(typebind_parents(t)),
        RawExpr::LitBytes(_) => Set::new(),
        RawExpr::Unsafe(s) => rec(s),
        RawExpr::Extern(_) => Set::new(),
        RawExpr::ExternApply(_, args) => {
            args.iter().fold(Set::new(), |acc, arg| acc.union(rec(arg)))
        }
    }
}
