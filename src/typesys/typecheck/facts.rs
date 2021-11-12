use crate::{
    containers::{Map, Symbol},
    typesys::{Type, Variable},
};

use super::state::TypecheckState;

/// A carrier of information gleaned about the types of variables through occurrence-typing operators (`is` and such).
#[derive(Clone, Debug)]
pub struct TypeFacts<Tv: Variable, Cv: Variable> {
    mapping: Map<Symbol, Type<Tv, Cv>>,
}

impl<Tv: Variable, Cv: Variable> TypeFacts<Tv, Cv> {
    /// Creates a new empty set.
    pub fn empty() -> Self {
        Self {
            mapping: Map::new(),
        }
    }

    /// Adds a mapping to the type facts. If a mapping already exists, replaces it.
    pub fn with_mapping(mut self, sym: Symbol, t: Type<Tv, Cv>) -> Self {
        self.mapping.insert(sym, t);
        self
    }

    /// Removes a mapping to the type facts. If a mapping already exists, replaces it.
    pub fn clear_mapping(mut self, sym: Symbol) -> Self {
        self.mapping.remove(&sym);
        self
    }

    /// Union with another type facts. Duplicates are handled by computing the *intersection* of the two types.
    pub fn union(mut self, other: Self) -> Self {
        //  A best-effort attempt at intersecting the types is done (T & U is transformed into (T | U) - (T - U) - (U - T)
        self.mapping = self.mapping.union_with(other.mapping, |a, b| {
            a.smart_union(&b)
                .subtract(&a.subtract(&b))
                .subtract(&b.subtract(&a))
                .into_owned()
        });
        self
    }

    /// Negates the type facts, with respect to some type state.
    pub fn negate_against(mut self, universe: &TypecheckState<Tv, Cv>) -> Self {
        self.mapping.iter_mut().for_each(|(k, b)| {
            if let Some(u) = universe.lookup_var(*k) {
                let new = u.subtract(b).into_owned();
                *b = new;
            }
        });
        self
    }

    /// Iterates through the bindings
    pub fn iter(&self) -> impl Iterator<Item = (&Symbol, &Type<Tv, Cv>)> {
        self.mapping.iter()
    }
}
