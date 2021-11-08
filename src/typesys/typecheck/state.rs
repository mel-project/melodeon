use crate::{
    containers::{List, Map, Symbol},
    typesys::{Type, Variable},
};

/// A purely-functional typechecking state.
#[derive(Debug, Clone, Default)]
pub struct TypecheckState<TVar: Variable, CVar: Variable> {
    variable_scope: Map<Symbol, Type<TVar, CVar>>,
    type_scope: Map<TVar, Type<TVar, CVar>>,
    function_scope: Map<Symbol, FunctionType<TVar, CVar>>,
}

impl<TVar: Variable, CVar: Variable> TypecheckState<TVar, CVar> {
    /// Creates an empty
    pub fn new() -> Self {
        Self {
            variable_scope: Map::new(),
            type_scope: Map::new(),
            function_scope: Map::new(),
        }
    }

    /// Binds a variable.
    pub fn bind_var(mut self, s: Symbol, t: Type<TVar, CVar>) -> Self {
        self.variable_scope.insert(s, t);
        self
    }

    /// Binds a type name
    pub fn bind_type_alias(mut self, alias: TVar, t: Type<TVar, CVar>) -> Self {
        // First, we resolve any aliases in t
        let t = t.fill_tvars(|tv| {
            self.lookup_type_alias(tv.clone())
                .unwrap_or_else(|| Type::Var(tv.clone()))
        });
        self.type_scope.insert(alias, t);
        self
    }

    /// Binds a function name.
    pub fn bind_fun(mut self, name: Symbol, funtype: FunctionType<TVar, CVar>) -> Self {
        self.function_scope.insert(name, funtype);
        self
    }

    /// Looks up the type of a variable
    pub fn lookup_var(&self, s: Symbol) -> Option<Type<TVar, CVar>> {
        self.variable_scope.get(&s).cloned()
    }

    /// Looks up a type alias
    pub fn lookup_type_alias(&self, alias: TVar) -> Option<Type<TVar, CVar>> {
        self.type_scope.get(&alias).cloned()
    }

    /// Looks up a function
    pub fn lookup_fun(&self, name: Symbol) -> Option<FunctionType<TVar, CVar>> {
        self.function_scope.get(&name).cloned()
    }
}

#[derive(Debug, Clone)]
pub struct FunctionType<TVar: Variable, CVar: Variable> {
    pub free_cgvars: List<CVar>,
    pub free_vars: List<TVar>,
    pub args: List<Type<TVar, CVar>>,
    pub result: Type<TVar, CVar>,
}
