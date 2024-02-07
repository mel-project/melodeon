use crate::{
    containers::{List, Map, Symbol},
    typesys::Type,
};

use super::facts::TypeFacts;

/// A purely-functional typechecking scope.
#[derive(Debug, Clone, Default)]
pub struct Scope {
    variable_scope: Map<Symbol, Type>,
    type_scope: Map<Symbol, Type>,
    safety: bool,
}

impl Scope {
    /// Creates an empty
    pub fn new() -> Self {
        Self {
            variable_scope: Map::new(),
            type_scope: Map::new(),

            safety: true,
        }
    }

    /// Binds a variable.
    pub fn bind_var(mut self, s: Symbol, t: Type) -> Self {
        self.variable_scope.insert(s, t);
        self
    }

    /// Binds a list of variables.
    pub fn bind_vars(mut self, binds: List<(Symbol, Type)>) -> Self {
        for (s, t) in binds.into_iter() {
            self.variable_scope.insert(s, t);
        }
        self
    }

    /// Binds a type name
    pub fn bind_type_alias(mut self, alias: Symbol, t: Type) -> Self {
        self.type_scope.insert(alias, t);
        self
    }

    /// Binds safety mode.
    pub fn bind_safety(mut self, safety: bool) -> Self {
        self.safety = safety;
        self
    }

    /// Gets safety
    pub fn lookup_safety(&self) -> bool {
        self.safety
    }

    /// Looks up the type of a variable
    pub fn lookup_var(&self, s: Symbol) -> Option<Type> {
        self.variable_scope.get(&s).cloned()
    }

    /// Looks up a type alias
    pub fn lookup_type_alias(&self, alias: Symbol) -> Option<Type> {
        self.type_scope.get(&alias).cloned()
    }

    pub fn var_scope(&self) -> Map<Symbol, Type> {
        self.variable_scope.clone()
    }

    /// Applies some type facts
    pub fn with_facts(mut self, facts: &TypeFacts) -> Self {
        tracing::trace!("with facts {:?}", facts);
        for (k, v) in facts.iter() {
            if let Some(t) = self.variable_scope.get_mut(k) {
                tracing::trace!("applying fact type {:?} to existing {:?}", v, t);
                let new_t = if t.subtype_of(v) {
                    t.clone()
                } else {
                    v.clone()
                };
                *t = new_t;
            }
        }
        self
    }
}
