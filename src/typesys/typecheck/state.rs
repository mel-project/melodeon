use crate::{
    containers::{List, Map, Symbol},
    typesys::{ConstExpr, Type, Variable},
};

use super::facts::TypeFacts;

/// A purely-functional typechecking state.
#[derive(Debug, Clone, Default)]
pub struct TypecheckState<TVar: Variable, CVar: Variable> {
    variable_scope: Map<Symbol, Type<TVar, CVar>>,
    type_scope: Map<Symbol, Type<TVar, CVar>>,
    cg_scope: Map<Symbol, ConstExpr<CVar>>,
    function_scope: Map<Symbol, FunctionType<TVar, CVar>>,
    safety: bool,
}

impl<TVar: Variable, CVar: Variable> TypecheckState<TVar, CVar> {
    /// Creates an empty
    pub fn new() -> Self {
        Self {
            variable_scope: Map::new(),
            type_scope: Map::new(),
            cg_scope: Map::new(),
            function_scope: Map::new(),
            safety: true,
        }
    }

    /// Binds a variable.
    pub fn bind_var(mut self, s: Symbol, t: Type<TVar, CVar>) -> Self {
        self.variable_scope.insert(s, t);
        self
    }

    /// Binds a const-generic variable.
    pub fn bind_cgvar(mut self, s: Symbol, v: ConstExpr<CVar>) -> Self {
        self.cg_scope.insert(s, v);
        self
    }

    /// Binds a type name
    pub fn bind_type_alias(mut self, alias: Symbol, t: Type<TVar, CVar>) -> Self {
        self.type_scope.insert(alias, t);
        self
    }

    /// Binds a function name.
    pub fn bind_fun(mut self, name: Symbol, funtype: FunctionType<TVar, CVar>) -> Self {
        self.function_scope.insert(name, funtype);
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
    pub fn lookup_var(&self, s: Symbol) -> Option<Type<TVar, CVar>> {
        self.variable_scope.get(&s).cloned()
    }

    /// Looks up a bound const-generic variable
    pub fn lookup_cgvar(&self, s: Symbol) -> Option<ConstExpr<CVar>> {
        self.cg_scope.get(&s).cloned()
    }

    /// Looks up a type alias
    pub fn lookup_type_alias(&self, alias: Symbol) -> Option<Type<TVar, CVar>> {
        self.type_scope.get(&alias).cloned()
    }

    /// Looks up a function
    pub fn lookup_fun(&self, name: Symbol) -> Option<FunctionType<TVar, CVar>> {
        self.function_scope.get(&name).cloned()
    }

    /// Applies some type facts
    pub fn with_facts(mut self, facts: &TypeFacts<TVar, CVar>) -> Self {
        log::trace!("with facts {:?}", facts);
        for (k, v) in facts.iter() {
            if let Some(t) = self.variable_scope.get_mut(k) {
                log::trace!("applying fact type {:?} to existing {:?}", v, t);
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

#[derive(Debug, Clone)]
pub struct FunctionType<TVar: Variable, CVar: Variable> {
    pub free_cgvars: List<CVar>,
    pub free_vars: List<TVar>,
    pub args: List<Type<TVar, CVar>>,
    pub result: Type<TVar, CVar>,
}
