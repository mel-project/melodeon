use std::fmt::{Debug, Display};

use internment::Intern;

/// List type.
///
/// TODO: replace with some good immutable vector
pub type List<T> = Vec<T>;

/// Set type
pub type Set<T> = imbl::HashSet<T>;

/// Map type
pub type Map<K, V> = imbl::HashMap<K, V>;

/// Interned string with O(1) equality and hashing.
#[derive(Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Symbol(Intern<String>);

impl Debug for Symbol {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(&self.0, f)
    }
}

impl Display for Symbol {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(&self.0, f)
    }
}

impl From<&str> for Symbol {
    fn from(s: &str) -> Self {
        Symbol(Intern::from(s))
    }
}

/// A type that cannot have elements.
#[derive(Clone, Hash, PartialEq, Eq, Debug)]
pub enum Void {}
