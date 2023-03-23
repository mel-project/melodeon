use ethnum::U256;
use std::hash::Hash;
use std::sync::Arc;
use std::{borrow::Cow, fmt::Debug};
use tap::Tap;

use crate::containers::{List, Map, Set, Symbol, Void};

pub trait Variable: Clone + Hash + Eq + Debug + Ord {
    /// Possibly convert from a symbol. By default, just fails mercilessly.
    fn try_from_sym(_: Symbol) -> Option<Self>;
}

impl Variable for Void {
    fn try_from_sym(_: Symbol) -> Option<Self> {
        panic!("cannot make a Void from a symbol")
    }
}

impl Variable for Symbol {
    fn try_from_sym(s: Symbol) -> Option<Self> {
        Some(s)
    }
}

/// A Melodeon type. [`Type`] is generic over one parameter, `T`, which represents the type for type-variables.
/// This is a generic type in order to statically guarantee the status of free variables. For example, one may start
/// with `Type<RawT>`, turn that into `Type<MangledT>`, and resolve that into [`Type`].
///
/// [`Type`] is an alias for [`Type<Void>`], representing a type with *no* free variables. [`Void`] is a special
/// type that cannot be constructed, so a value of [`Type<Void>`] *statically* guarantees a lack of free variables.
///
/// In general, typechecking code should not directly match against [`Type`]. Instead, use the subtyping and unification methods as needed.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Type<T = Void> {
    Nothing,
    Any,
    Var(T),
    Nat,
    Vector(List<Self>),
    DynVectorof(Arc<Self>),
    DynBytes,
    Struct(Symbol, List<(Symbol, Self)>),
    Union(Arc<Self>, Arc<Self>),
}

impl<T: Variable> Debug for Type<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Type::Nothing => std::fmt::Display::fmt("Nothing", f),
            Type::Any => std::fmt::Display::fmt("Any", f),
            Type::Var(t) => t.fmt(f),
            Type::Nat => "Nat".fmt(f),
            Type::Vector(vec) => vec.fmt(f),

            Type::Struct(s, _) => std::fmt::Display::fmt(&format!("{}", s), f),
            Type::Union(t, u) => std::fmt::Display::fmt(&format!("{:?} | {:?}", t, u), f),
            Type::DynVectorof(t) => std::fmt::Display::fmt(&format!("[{:?};]", t), f),

            Type::DynBytes => std::fmt::Display::fmt("%[]", f),
        }
    }
}

impl<TVar: Variable> Type<TVar> {
    /// Checks whether this type is always "falsy".
    pub fn always_falsy(&self) -> bool {
        todo!()
    }

    /// Equivalence relation. Returns true iff `self` and `other` are subtypes of each other.
    pub fn equiv_to(&self, other: &Self) -> bool {
        self.subtype_of(other) && other.subtype_of(other)
    }

    /// "Deunionizes" the type, returning an iterator over non-union types.
    pub fn deunionize(&self) -> impl Iterator<Item = &Self> {
        let res: Box<dyn Iterator<Item = &Self>> = if let Type::Union(t, u) = self {
            Box::new(t.deunionize().chain(u.deunionize()))
        } else {
            Box::new(std::iter::once(self))
        };
        res
    }

    // /// Checks whether or not a value of this type can be compared with another value of another type.
    // pub fn comparable_with(&self, other: &Self) -> bool {
    //     log::trace!("checking {:?} comparable? {:?}", self, other);
    //     match (self, other) {
    //         (Type::Any, _) => false,
    //         (Type::NatRange(_, _), Type::NatRange(_, _)) => true,
    //         (Type::Struct(_, _), Type::Struct(_, _)) =>
    //         (Type::Union(t, u), _) => t.comparable_with(other) && u.comparable_with(other),
    //         _ => other.comparable_with(self),
    //     }
    // }

    /// Subtype relation. Returns true iff `self` is a subtype of `other`.
    pub fn subtype_of(&self, other: &Self) -> bool {
        log::trace!("checking {:?} <:? {:?}", self, other);
        match (self, other) {
            (Type::Nothing, _) => true,
            (_, Type::Any) => true,
            (Type::Any, _) => false,
            // structs desugar to vectors
            (Type::Struct(_, v), _) => {
                Type::Vector(v.iter().map(|a| a.1.clone()).collect()).subtype_of(other)
            }
            (_, Type::Struct(_, v)) => {
                self.subtype_of(&Type::Vector(v.iter().map(|a| a.1.clone()).collect()))
            }
            (Type::Union(t, u), anything) => t.subtype_of(anything) && u.subtype_of(anything),
            (Type::Var(x), Type::Var(y)) => x == y,
            (Type::Var(_), Type::Union(t, u)) => {
                // This is the "union rule". It is conservative and sound, but imprecise, because the left-hand type might be a *combination* of some subtype of T and some subtype of U, while not a subtype of either.
                // But because the LHS here is just a single variable, we cannot further investigate, so we do the best we can.
                self.subtype_of(t) || self.subtype_of(u)
            }
            (Type::Var(_), _) => false,

            (Type::Vector(v1), Type::Vector(v2)) => {
                // pairwise comparison
                v1.len() == v2.len() && v1.iter().zip(v2.iter()).all(|(v1, v2)| v1.subtype_of(v2))
            }
            (Type::Vector(v1), Type::DynVectorof(t)) => v1.iter().all(|t1| t1.subtype_of(t)),

            (Type::Vector(v1), Type::Union(t, u)) => {
                // We "look into" the RHS vector. This is more precise than the union rule.
                // We still apply the union rule first because that's faster and doesn't allocate.
                // Because the union rule is conservative, it never gives us false positives, so we can always use it as a first try.
                self.subtype_of(t)
                    || self.subtype_of(u)
                    || other
                        .try_to_vector()
                        .map(|other| {
                            v1.len() == other.len()
                                && v1
                                    .iter()
                                    .zip(other.iter())
                                    .all(|(v1, v2)| v1.subtype_of(v2))
                        })
                        .unwrap_or(false)
            }
            (Type::Vector(_), _) => false,

            (Type::DynVectorof(v1_all), Type::DynVectorof(v2_all)) => v1_all.subtype_of(v2_all),
            (Type::DynVectorof(_), Type::Union(t, u)) => {
                // conservatively deal with this
                self.subtype_of(t) || self.subtype_of(u)
            }
            (Type::DynVectorof(_), _) => false,

            (Type::DynBytes, Type::DynBytes) => true,
            (Type::DynBytes, Type::Union(t, u)) => self.subtype_of(t) || self.subtype_of(u),
            (Type::DynBytes, _) => false,
            (Type::Nat, Type::Nat) => true,
            (Type::Nat, Type::Union(a, b)) => self.subtype_of(a) || self.subtype_of(b),
            (Type::Nat, _) => false,
        }
    }

    /// Subtracts another type, *conservatively*. That is, it produces a type that includes *at least* all the values that are in `self` but not in `other`, but it may include more in difficult-to-calculate cases.
    pub fn subtract(&self, other: &Self) -> Cow<Self> {
        log::trace!("subtracting {:?} - {:?}", self, other);
        // if we're a subtype of other, we're done
        if self.subtype_of(other) {
            return Cow::Owned(Type::Nothing);
        }
        if let Type::Union(t, u) = other {
            return Cow::Owned(self.subtract(t).subtract(u).into_owned());
        }
        match self {
            Type::Union(x, y) => {
                if x.subtype_of(other) {
                    y.subtract(other)
                } else if y.subtype_of(other) {
                    x.subtract(other)
                } else {
                    Cow::Owned(Type::Union(
                        x.subtract(other).into_owned().into(),
                        y.subtract(other).into_owned().into(),
                    ))
                }
            }
            Type::Vector(elems) => {
                if let Some(other) = other.try_to_vector() {
                    // we subtract elements from the other side, pairwise
                    if other.len() != elems.len() {
                        // disjoint
                        Cow::Borrowed(self)
                    } else {
                        let new_elems = elems
                            .iter()
                            .zip(other.iter())
                            .map(|(a, b)| a.subtract(b).into_owned())
                            .collect();
                        Cow::Owned(Type::Vector(new_elems))
                    }
                } else {
                    Cow::Borrowed(self)
                }
            }

            Type::Nothing => Cow::Borrowed(self),
            Type::Any => Cow::Borrowed(self),
            Type::Var(_) => Cow::Borrowed(self),

            Type::Struct(_, _) => Cow::Borrowed(self),
            Type::DynVectorof(t) => {
                if let Type::DynVectorof(their_t) = other {
                    Cow::Owned(Type::DynVectorof(t.subtract(their_t).into_owned().into()))
                } else {
                    Cow::Borrowed(self)
                }
            }

            Type::DynBytes => Cow::Borrowed(self),
            Type::Nat => todo!(),
        }
    }

    /// Using the current type (which contains typevars of type TVar) as a template, as well as a different type where the "holes" formed by these typevars are filled, derive a mapping between the free typevars of [self] and types.
    pub fn unify_tvars<TVar2: Variable>(
        &self,
        other: &Type<TVar2>,
    ) -> Option<Map<TVar, Type<TVar2>>> {
        log::trace!("unify_tvars {:?} with {:?}", self, other);
        // First, we find out exactly *where* in self do the typevars appear.
        let locations = self.tvar_locations();
        log::trace!("found locations: {:?}", locations);
        // Then, we index into other to find out what concrete types those tvars represent
        let res = locations
            .into_iter()
            .map(|(var, locations)| {
                locations
                    .into_iter()
                    .fold(Some(Type::Nothing), |accum, elem| {
                        let accum = accum?;
                        let mut ptr = other.clone();
                        for elem in elem {
                            todo!()
                        }
                        Some(accum.smart_union(&ptr))
                    })
                    .map(|other_piece| (var, other_piece))
            })
            .collect();
        log::trace!("post unify: {:?}", res);
        res
    }

    /// "Smart" union that is a no-op if one of the types is actually a subtype of another
    pub fn smart_union(&self, other: &Self) -> Self {
        if self.subtype_of(other) {
            other.clone()
        } else if other.subtype_of(self) {
            self.clone()
        } else {
            Type::Union(self.clone().into(), other.clone().into())
        }
    }

    /// Returns the set of all locations where constant-generic parameters appear.
    fn cvar_locations(&self) -> Set<List<Option<usize>>> {
        match self {
            Type::Nothing => Set::new(),
            Type::Any => Set::new(),
            Type::Var(_) => Set::new(),

            Type::Vector(elems) => elems
                .iter()
                .map(|elem| elem.cvar_locations())
                .enumerate()
                .fold(Set::new(), |accum, (idx, inner_locations)| {
                    accum.union(
                        inner_locations
                            .into_iter()
                            .map(|mut v| {
                                v.insert(0, Some(idx));
                                v
                            })
                            .collect(),
                    )
                }),

            Type::Struct(_, i) => {
                Type::Vector(i.iter().map(|a| a.1.clone()).collect()).cvar_locations()
            }
            Type::Union(t, u) => t.cvar_locations().union(u.cvar_locations()),
            Type::DynVectorof(t) => t
                .cvar_locations()
                .into_iter()
                .map(|mut loc| {
                    loc.insert(0, None);
                    loc
                })
                .collect(),

            Type::DynBytes => Set::new(),
            Type::Nat => todo!(),
        }
    }

    /// Creates a mapping of free type variables and their locations in the type. Locations are represented as indexes. An index is either a number, or None, which represents "all".
    fn tvar_locations(&self) -> Map<TVar, Set<List<Option<usize>>>> {
        match self {
            Type::Var(tvar) => Map::new().tap_mut(|map| {
                map.insert(tvar.clone(), [List::new()].into_iter().collect());
            }),
            Type::Vector(vec) => {
                let mut mapping = Map::new();
                for (idx, v) in vec.iter().enumerate() {
                    let child_map: Map<TVar, Set<List<Option<usize>>>> = v
                        .tvar_locations()
                        .into_iter()
                        .map(|(k, v)| {
                            (
                                k,
                                v.into_iter()
                                    .map(|v| v.tap_mut(|v| v.insert(0, Some(idx))))
                                    .collect(),
                            )
                        })
                        .collect();
                    mapping = mapping.union_with(child_map, |a, b| a.union(b));
                }
                mapping
            }

            Type::Struct(_, inner) => {
                Type::Vector(inner.iter().map(|a| a.1.clone()).collect()).tvar_locations()
            }
            Type::Union(a, b) => {
                let a = a.tvar_locations();
                let b = b.tvar_locations();
                a.union_with(b, |a, b| a.union(b))
            }
            _ => Map::new(),
        }
    }

    /// Fills in all type-variables, given a fallible function that resolves type-variables. If the resolution fails at any step, returns [None].
    pub fn try_fill_tvars<NewTVar: Variable>(
        &self,
        mapping: impl Fn(&TVar) -> Option<Type<NewTVar>>,
    ) -> Option<Type<NewTVar>> {
        self.try_fill_tvars_inner(&mapping)
    }

    /// Fills in all type-variables, except infallibly.
    pub fn fill_tvars<NewTVar: Variable>(
        &self,
        mapping: impl Fn(&TVar) -> Type<NewTVar>,
    ) -> Type<NewTVar> {
        self.try_fill_tvars(|tv| Some(mapping(tv))).unwrap()
    }

    // separate out for recursion
    fn try_fill_tvars_inner<NewTVar: Variable>(
        &self,
        mapping: &impl Fn(&TVar) -> Option<Type<NewTVar>>,
    ) -> Option<Type<NewTVar>> {
        match self {
            Type::Nothing => Some(Type::Nothing),
            Type::Any => Some(Type::Any),
            Type::Var(tvar) => mapping(tvar),
            Type::Nat => Some(Type::Nat),
            Type::Vector(elems) => {
                let elems: Option<List<_>> = elems
                    .iter()
                    .map(|e| e.try_fill_tvars_inner(mapping))
                    .collect();
                Some(Type::Vector(elems?))
            }

            Type::Struct(name, b) => Some(Type::Struct(
                *name,
                b.iter()
                    .map(|(a, b)| Some((*a, b.try_fill_tvars_inner(mapping)?)))
                    .collect::<Option<List<_>>>()?,
            )),
            Type::Union(a, b) => Some(Type::Union(
                a.try_fill_tvars_inner(mapping)?.into(),
                b.try_fill_tvars_inner(mapping)?.into(),
            )),
            Type::DynVectorof(t) => {
                Some(Type::DynVectorof(t.try_fill_tvars_inner(mapping)?.into()))
            }

            Type::DynBytes => Some(Type::DynBytes),
        }
    }

    /// Interpret a vector type into a list of types. Returns [None] if this is not a vector type, or if the vector type has an indeterminate length.
    pub fn try_to_vector(&self) -> Option<Cow<List<Self>>> {
        match self {
            Type::Vector(inner) => Some(Cow::Borrowed(inner)),
            Type::Union(x, y) => {
                let x = x.try_to_vector()?;
                let y = y.try_to_vector()?;
                if x.len() != y.len() {
                    return None;
                }
                Some(Cow::Owned(
                    x.iter()
                        .cloned()
                        .zip(y.iter().cloned())
                        .map(|(x, y)| Type::Union(x.into(), y.into()))
                        .collect(),
                ))
            }
            _ => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use log::LevelFilter;

    use super::*;
    #[test]

    fn init_logs() {
        let _ = env_logger::builder()
            .is_test(true)
            .format_timestamp(None)
            .filter_level(LevelFilter::Trace)
            .try_init();
    }
}
