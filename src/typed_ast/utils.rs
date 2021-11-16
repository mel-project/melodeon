use imbl::hashset;
use crate::{
    containers::{Set, Symbol, List},
    typesys::{TypeParam, CgParam, Variable},
    typed_ast::{Expr, ExprInner, FunDefn},
};

/*
pub fn foldr<A,Tp,Cg,F>(f: F, ast: Expr<Tp,Cg>) -> Expr<Tp,Cg> {
    where F: Fn<A,Tp,Cg>(a: A, b: Expr<Tp,Cg>>) -> Expr<Tp,CG>,
}
*/

pub fn sort_defs(defs: List<FunDefn<TypeParam, CgParam>>)
-> List<FunDefn<TypeParam, CgParam>> {
    // TODO assumes no cycles, will not halt if there are cycles
    defs.clone().into_iter().fold(
        (defs, Set::new()),
        |(defs, visited), def| sort_single_def(def, defs, visited)).0
}

fn sort_single_def<T: Variable,C: Variable>(
    def: FunDefn<T,C>,
    defs: List<FunDefn<T, C>>,
    visited: Set<Symbol>)
-> (List<FunDefn<T, C>>, Set<Symbol>) {
    if !visited.contains(&def.name) {
        defs.clone().into_iter().fold(
            (defs, visited.update(def.name)),
            |(defs, visited), parent| sort_single_def(parent, defs, visited))
    } else {
        (defs, visited)
    }
}

impl<T: Variable, C: Variable> FunDefn<T,C> {
    /// Get a list of all definition names referenced in a definition's body.
    pub fn parents(self) -> Set<Symbol> {
        FunDefn::get_defn_parents_aux(&self.body)
    }

    fn get_defn_parents_aux(expr: &Expr<T, C>) -> Set<Symbol> {
        let rec = FunDefn::get_defn_parents_aux;

        match &expr.inner {
            // Important cases
            ExprInner::Var(var) => Set::unit(*var),
            ExprInner::Let(var, val, body) =>
                rec(&val).union(rec(&body)).without(&var),
            ExprInner::Apply(fn_name, args) =>
                args.into_iter().fold(hashset!{*fn_name}, |acc, arg| acc.union(rec(&arg))),
            ExprInner::ApplyGeneric(fn_name, _, _, args) =>
                args.into_iter().fold(hashset!{*fn_name}, |acc, arg| acc.union(rec(&arg))),

            // Trivial cases
            ExprInner::VectorRef(v, idx) => rec(&v).union(rec(&idx)),
            ExprInner::VectorUpdate(v, old, new) => rec(&v).union(rec(&old)).union(rec(&new)),
            ExprInner::VectorSlice(v, from, to) => rec(&v).union(rec(&from)).union(rec(&to)),
            ExprInner::If(p,t,f) => rec(&p).union(rec(&t)).union(rec(&f)),
            ExprInner::BinOp(_, a, b) => rec(&a).union(rec(&b)),
            ExprInner::LitVec(v) => v.iter().fold(hashset!{}, |acc, e| acc.union(rec(e))),
            // TODO traverse type-defs in IsType
            _ => Set::new(),
        }
    }
}
