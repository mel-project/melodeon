use ethnum::U256;

use crate::{
    containers::{List, Map, Set, Symbol},
    context::{Ctx, ModuleId},
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
    Require(ModuleId),
    Provide(Symbol),
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
    For(Ctx<Symbol>, Ctx<Self>, Ctx<Self>),
    ForFold(Ctx<Symbol>, Ctx<Self>, Ctx<Symbol>, Ctx<Self>, Ctx<Self>),
    If(Ctx<Self>, Ctx<Self>, Ctx<Self>),
    Fail,

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

    Loop(Ctx<RawConstExpr>, List<(Symbol, Ctx<Self>)>, Ctx<Self>),

    IsType(Symbol, Ctx<RawTypeExpr>),
    AsType(Ctx<Self>, Ctx<RawTypeExpr>),

    Transmute(Ctx<Self>, Ctx<RawTypeExpr>),
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
    mut sorted: &mut List<Ctx<RawDefn>>,
    mut visited: &mut Set<Symbol>,
) {
    if !visited.contains(&def) {
        visited.insert(def);
        log::trace!("visiting {:?}", def);

        let def = find_by_name(defs, def)
            .expect(&format!("A parent reference should always be in the definitions list, this is a bug. defs {:?}, trying to find {:?}", defs.iter().map(|d| d.name()).collect::<Vec<_>>(), def));

        for parent in def.parents() {
            log::trace!("{:?} depends on {:?}", def.name(), parent);
            visit(parent, defs, &mut sorted, &mut visited);
        }

        sorted.push_back(def.clone());
    }
}

// pub fn sort_defsx(defs: List<Ctx<RawDefn>>) -> List<Ctx<RawDefn>> {
//     // TODO assumes no cycles, will not halt if there are cycles
//     defs.clone()
//         .into_iter()
//         .fold((List::new(), Set::new()), |(sorted, visited), def| {
//             sort_single_def(def, defs.clone(), sorted, visited)
//         })
//         .0
// }

// fn sort_single_def(
//     def: Ctx<RawDefn>,
//     defs: List<Ctx<RawDefn>>,
//     sorted: List<Ctx<RawDefn>>,
//     visited: Set<Symbol>,
// ) -> (List<Ctx<RawDefn>>, Set<Symbol>) {
//     let name = def.name();
//     if !visited.contains(&name) {
//         let (mut sorted, visited) = def.parents().iter().fold(
//             (sorted, visited.update(name)),
//             |(sorted, visited), parent|
//                 sort_single_def(
//                     find_by_name(&defs, *parent)
//                         .expect("A parent reference should always be in the definitions list, this is a bug").clone(),
//                     defs.clone(),
//                     sorted,
//                     visited));

//         sorted.push_back(def);
//         (sorted, visited)
//     } else {
//         (defs, visited)
//     }
// }

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
                ..
            } => expr_parents(body).relative_complement(
                args.iter()
                    .map(|a| *a.name)
                    .chain(genvars.iter().map(|a| **a))
                    .collect(),
            ),
            RawDefn::Struct { name: _, fields } => fields.iter().fold(Set::new(), |acc, field| {
                acc.union(typebind_parents(&field.bind))
            }),
            RawDefn::Constant(_, body) => expr_parents(body),
            RawDefn::Require(_) => Set::new(),
            RawDefn::Provide(_) => Set::new(),
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
    }
}

fn expr_parents(expr: &RawExpr) -> Set<Symbol> {
    let rec = expr_parents;

    match expr {
        // Important cases
        RawExpr::Var(var) => Set::unit(*var),
        RawExpr::Let(var, val, body) => rec(val).union(rec(body)).without(var),
        RawExpr::Apply(fn_name, args) => args
            .into_iter()
            .fold(rec(fn_name), |acc, arg| acc.union(rec(arg))),
        RawExpr::LitStruct(s_name, fields) => fields
            .values()
            .fold(Set::unit(*s_name), |acc, field| acc.union(rec(field))),

        // Trivial cases
        RawExpr::VectorRef(v, idx) => rec(v).union(rec(idx)),
        RawExpr::VectorUpdate(v, old, new) => rec(v).union(rec(old)).union(rec(new)),
        RawExpr::VectorSlice(v, from, to) => rec(v).union(rec(from)).union(rec(to)),
        RawExpr::If(p, t, f) => rec(p).union(rec(t)).union(rec(f)),
        RawExpr::BinOp(_, a, b) => rec(a).union(rec(b)),
        RawExpr::Field(strct, _) => rec(strct),
        RawExpr::LitVec(v) => v.iter().fold(Set::new(), |acc, e| acc.union(rec(e))),
        RawExpr::For(var, val, body) => rec(val).union(rec(body)).without(var),
        RawExpr::ForFold(var, val, avar, aval, body) => rec(val)
            .union(rec(aval))
            .union(rec(body))
            .without(var)
            .without(avar),
        RawExpr::Fail => Set::new(),
        RawExpr::LitNum(_) => Set::new(),
        RawExpr::CgVar(_) => Set::new(),
        RawExpr::Loop(_, body, inner) => body
            .iter()
            .map(|a| rec(&a.1))
            .fold(Set::new(), |a, b| a.union(b))
            .union(rec(inner)),
        RawExpr::IsType(v, t) => Set::unit(*v).union(typebind_parents(t)),
        RawExpr::AsType(a, t) | RawExpr::Transmute(a, t) => rec(a).union(typebind_parents(t)),
    }
}
