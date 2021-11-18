use ethnum::U256;
use imbl::hashset;

use crate::{
    containers::{Set, List, Map, Symbol},
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
    Struct {
        name: Ctx<Symbol>,
        fields: List<Ctx<RawTypeBind>>,
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
    Let(Ctx<Symbol>, Ctx<Self>, Ctx<Self>),
    If(Ctx<Self>, Ctx<Self>, Ctx<Self>),

    BinOp(Ctx<BinOp>, Ctx<RawExpr>, Ctx<RawExpr>),
    LitNum(U256),
    LitVec(List<Ctx<Self>>),
    LitStruct(Symbol, Map<Symbol, Ctx<RawExpr>>),
    Var(Symbol),
    CgVar(Symbol),

    Apply(Ctx<Self>, List<Ctx<Self>>),
    Field(Ctx<Self>, Ctx<Symbol>),
    VectorRef(Ctx<Self>, Ctx<Self>),
    VectorSlice(Ctx<Self>, Ctx<Self>, Ctx<Self>),
    VectorUpdate(Ctx<Self>, Ctx<Self>, Ctx<Self>),

    IsType(Symbol, Ctx<RawTypeExpr>),
    AsType(Ctx<Self>, Ctx<RawTypeExpr>),
}

/// Binary operator
#[derive(Clone, Copy, Debug)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,

    Lor,
    Land,
    Lnot,

    Append,

    Eq,
}

pub fn sort_defs(defs: List<Ctx<RawDefn>>)
-> List<Ctx<RawDefn>> {
    let mut sorted  = List::new();
    let mut visited = Set::new();

    for def in defs.iter() {
        visit(*def.name(), &defs, &mut sorted, &mut visited);
    }

    sorted
}

fn visit(
    def: Symbol,
    defs: &List<Ctx<RawDefn>>,
    mut sorted: &mut List<Ctx<RawDefn>>,
    mut visited: &mut Set<Symbol>) {

    if !visited.contains(&def) {
        visited.insert(def);

        let def = find_by_name(defs, &def)
            .expect("A parent reference should always be in the definitions list, this is a bug");

        for parent in def.parents() {
            visit(parent, defs, &mut sorted, &mut visited);
        }

        sorted.push(def.clone());
    }
}


pub fn sort_defsx(defs: List<Ctx<RawDefn>>)
-> List<Ctx<RawDefn>> {
    // TODO assumes no cycles, will not halt if there are cycles
    defs.clone().into_iter().fold(
        (List::new(), Set::new()),
        |(sorted, visited), def| sort_single_def(def, defs.clone(), sorted, visited)).0
}

fn sort_single_def(
    def: Ctx<RawDefn>,
    defs: List<Ctx<RawDefn>>,
    sorted: List<Ctx<RawDefn>>,
    visited: Set<Symbol>)
-> (List<Ctx<RawDefn>>, Set<Symbol>) {
    let name = def.name();
    if !visited.contains(name) {
        let (mut sorted, visited) = def.parents().iter().fold(
            (sorted, visited.update(*name)),
            |(sorted, visited), parent|
                sort_single_def(
                    find_by_name(&defs, parent)
                        .expect("A parent reference should always be in the definitions list, this is a bug").clone(),
                    defs.clone(),
                    sorted.clone(),
                    visited));

        sorted.push(def);
        (sorted, visited)
    } else {
        (defs, visited)
    }
}

pub fn find_by_name<'a>(defs: &'a List<Ctx<RawDefn>>, name: &Symbol) -> Option<&'a Ctx<RawDefn>> {
    defs.iter().find(|def| def.name() == name)
}

impl RawDefn {
    /// Get the name of a definition
    pub fn name(&self) -> &Symbol {
        match self {
            RawDefn::Function{name, ..} => name,
            RawDefn::Struct{name, ..} => name,
            RawDefn::Constant(name, _) => name,
        }
    }

    /// Get a list of all definition names referenced in a definition's body.
    pub fn parents(&self) -> Set<Symbol> {
        match self {
            RawDefn::Function{body, ..} => expr_parents(body),
            RawDefn::Struct{name: _, fields} =>
                fields.iter().fold(Set::new(), |acc, field| acc.union(typebind_parents(&field.bind))),
            RawDefn::Constant(_, body) => expr_parents(body),
        }
    }
}

fn typebind_parents(tb: &RawTypeExpr) -> Set<Symbol> {
    let rec = typebind_parents;

    match tb {
        RawTypeExpr::Sym(sym) => Set::unit(*sym),
        RawTypeExpr::Union(l, r) => rec(l).union(rec(&r)),
        RawTypeExpr::Vector(l) => l.iter().fold(Set::new(), |acc, t| acc.union(rec(t))),
        RawTypeExpr::Vectorof(t, _) => rec(&t),
        RawTypeExpr::NatRange(_,_) => Set::new(),
    }
}

fn expr_parents(expr: &RawExpr) -> Set<Symbol> {
    let rec = expr_parents;

    match expr {
        // Important cases
        RawExpr::Var(var) => Set::unit(*var),
        RawExpr::Let(var, val, body) =>
            rec(val).union(rec(body)).without(var),
        RawExpr::Apply(fn_name, args) =>
            args.into_iter().fold(rec(fn_name), |acc, arg| acc.union(rec(arg))),
        RawExpr::LitStruct(s_name, fields) =>
            fields.values().fold(Set::unit(*s_name), |acc, field| acc.union(rec(field))),

        // Trivial cases
        RawExpr::VectorRef(v, idx) => rec(v).union(rec(idx)),
        RawExpr::VectorUpdate(v, old, new) => rec(v).union(rec(old)).union(rec(new)),
        RawExpr::VectorSlice(v, from, to) => rec(v).union(rec(from)).union(rec(to)),
        RawExpr::If(p,t,f) => rec(p).union(rec(t)).union(rec(f)),
        RawExpr::BinOp(_, a, b) => rec(a).union(rec(b)),
        RawExpr::Field(strct, _) => rec(strct),
        RawExpr::LitVec(v) => v.iter().fold(Set::new(), |acc, e| acc.union(rec(e))),
        // TODO traverse type-defs in IsType
        _ => Set::new(),
    }
}
