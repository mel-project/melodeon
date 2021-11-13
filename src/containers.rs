use std::{
    fmt::{Debug, Display},
    sync::atomic::{AtomicBool, AtomicU64},
};

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
#[derive(Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord, Default)]
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

impl Symbol {
    /// Gensym.
    pub fn generate(prefix: &str) -> Self {
        static COUNTER: AtomicU64 = AtomicU64::new(0);
        Symbol::from(
            format!(
                "{}{}",
                prefix,
                COUNTER.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
            )
            .as_str(),
        )
    }
}

/// A type that cannot have elements.
#[derive(Clone, Hash, PartialEq, Eq, Debug, PartialOrd, Ord)]
pub enum Void {}
