use std::sync::Arc;

use ethnum::U256;

use crate::containers::{IStr, List, Map};

/// A Melodeon type. Generic over a "placeholder" type that represents type variables, "holes", etc.
#[derive(Clone, Debug)]
pub enum Type<TVar: Clone = ()> {
    None,
    Any,
    Var(TVar),
    NatRange(U256, U256),
    Vector(List<Type>),
    Vectorof(Arc<Type>, u16),
    Struct(IStr, Map<IStr, Type>),
}
