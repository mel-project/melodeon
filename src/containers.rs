use internment::Intern;
use smallvec::SmallVec;

/// List type
/// TODO: replace with some good immutable vector
pub type List<T> = Vec<T>;

/// Set type
pub type Set<T> = imbl::HashSet<T>;

/// Map type
pub type Map<K, V> = imbl::HashMap<K, V>;

/// Interned string
pub type IStr = Intern<String>;

/// A type that cannot have elements.
#[derive(Clone, Hash, PartialEq, Eq, Debug)]
pub enum Void {}
