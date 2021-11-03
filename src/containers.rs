use catvec::CatVec;
use internment::Intern;

/// List type
pub type List<T> = CatVec<T, 64>;

/// Map type
pub type Map<K, V> = imbl::HashMap<K, V>;

/// Interned string
pub type IStr = Intern<String>;
