use std::{borrow::Cow, fmt::Debug};
use std::{ops::Deref, sync::Arc};
use tap::Tap;

use crate::containers::{List, Map, Set, Symbol};

/// A Melodeon type.
///
/// In general, typechecking code should not directly match against [`Type`]. Instead, use the subtyping and unification methods as needed.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Type {
    Nothing,
    Any,
    Var(Symbol),
    Nat,
    Vector(List<Self>),
    Vectorof(Arc<Self>),
    Bytes,
    Struct(Symbol, List<(Symbol, Self)>),
    Union(Arc<Self>, Arc<Self>),
    Lambda {
        free_vars: List<Symbol>,
        args: List<Self>,
        result: Arc<Self>,
    },
}

impl Debug for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Type::Nothing => std::fmt::Display::fmt("Nothing", f),
            Type::Any => std::fmt::Display::fmt("Any", f),
            Type::Var(t) => t.fmt(f),
            Type::Nat => std::fmt::Display::fmt("Nat", f),
            Type::Vector(vec) => vec.fmt(f),

            Type::Struct(s, _) => std::fmt::Display::fmt(&format!("{}", s), f),
            Type::Union(t, u) => std::fmt::Display::fmt(&format!("{:?} | {:?}", t, u), f),
            Type::Vectorof(t) => std::fmt::Display::fmt(&format!("[{:?}..]", t), f),

            Type::Bytes => std::fmt::Display::fmt("Bytes", f),

            Type::Lambda {
                free_vars: _,
                args,
                result,
            } => {
                let free_vars = args
                    .iter()
                    .map(|a| format!("{:?}", a))
                    .collect::<Vec<_>>()
                    .join(", ");
                let arg_frag = args
                    .iter()
                    .map(|a| format!("{:?}", a))
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("<{free_vars}>({arg_frag}) -> {:?}", result).fmt(f)
            }
        }
    }
}

impl Type {
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

    /// Subtype relation. Returns true iff `self` is a subtype of `other`.
    pub fn subtype_of(&self, other: &Self) -> bool {
        tracing::trace!("checking {:?} <:? {:?}", self, other);
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
            (Type::Vector(v1), Type::Vectorof(t)) => v1.iter().all(|t1| t1.subtype_of(t)),

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

            (Type::Vectorof(v1_all), Type::Vectorof(v2_all)) => v1_all.subtype_of(v2_all),
            (Type::Vectorof(_), Type::Union(t, u)) => {
                // conservatively deal with this
                self.subtype_of(t) || self.subtype_of(u)
            }
            (Type::Vectorof(_), _) => false,

            (Type::Bytes, Type::Bytes) => true,
            (Type::Bytes, Type::Union(t, u)) => self.subtype_of(t) || self.subtype_of(u),
            (Type::Bytes, _) => false,
            (Type::Nat, Type::Nat) => true,
            (Type::Nat, Type::Union(a, b)) => self.subtype_of(a) || self.subtype_of(b),
            (Type::Nat, _) => false,
            (
                Type::Lambda {
                    free_vars: _fv1,
                    args: a1,
                    result: r1,
                },
                Type::Lambda {
                    free_vars: _fv2,
                    args: a2,
                    result: r2,
                },
            ) => {
                // the arity is the same, the arguments are looser, and the result is tighter
                a1.len() == a2.len()
                    && a1.iter().zip(a2.iter()).all(|(a, b)| b.subtype_of(a))
                    && r1.subtype_of(r2)
            }
            (Type::Lambda { .. }, _) => false,
        }
    }

    /// Subtracts another type, *conservatively*. That is, it produces a type that includes *at least* all the values that are in `self` but not in `other`, but it may include more in difficult-to-calculate cases.
    pub fn subtract(&self, other: &Self) -> Cow<Self> {
        tracing::trace!("subtracting {:?} - {:?}", self, other);
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
            Type::Vectorof(t) => {
                if let Type::Vectorof(their_t) = other {
                    Cow::Owned(Type::Vectorof(t.subtract(their_t).into_owned().into()))
                } else {
                    Cow::Borrowed(self)
                }
            }

            Type::Bytes => Cow::Borrowed(self),
            Type::Nat => Cow::Borrowed(self),
            Type::Lambda {
                free_vars: _,
                args: _,
                result: _,
            } => Cow::Borrowed(self),
        }
    }

    /// Using the current type (which contains typevars of type TVar) as a template, as well as a different type where the "holes" formed by these typevars are filled, derive a mapping between the free typevars of [self] and types.
    pub fn unify_tvars(&self, other: &Type) -> Option<Map<Symbol, Type>> {
        tracing::trace!("unify_tvars {:?} with {:?}", self, other);
        // First, we find out exactly *where* in self do the typevars appear.
        let locations = self.tvar_locations();
        tracing::trace!("found locations: {:?}", locations);
        // Then, we index into other to find out what concrete types those tvars represent
        let res = locations
            .into_iter()
            .map(|(var, locations)| {
                locations
                    .into_iter()
                    .fold(Some(Type::Nothing), |accum, elem| {
                        let accum = accum?;
                        let ptr = other.clone();
                        for _elem in elem {
                            todo!()
                        }
                        Some(accum.smart_union(&ptr))
                    })
                    .map(|other_piece| (var, other_piece))
            })
            .collect();
        tracing::trace!("post unify: {:?}", res);
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

    /// Creates a mapping of free type variables and their locations in the type. Locations are represented as indexes. An index is either a number, or None, which represents "all".
    fn tvar_locations(&self) -> Map<Symbol, Set<List<Option<usize>>>> {
        match self {
            Type::Var(tvar) => Map::new().tap_mut(|map| {
                map.insert(*tvar, [List::new()].into_iter().collect());
            }),
            Type::Vector(vec) => {
                let mut mapping = Map::new();
                for (idx, v) in vec.iter().enumerate() {
                    let child_map: Map<Symbol, Set<List<Option<usize>>>> = v
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
    pub fn try_fill_tvars(&self, mapping: impl Fn(Symbol) -> Option<Type>) -> Option<Type> {
        self.try_fill_tvars_inner(&mapping)
    }

    /// Fills in all type-variables, except infallibly.
    pub fn fill_tvars(&self, mapping: impl Fn(Symbol) -> Type) -> Type {
        self.try_fill_tvars(|tv| Some(mapping(tv))).unwrap()
    }

    // separate out for recursion
    fn try_fill_tvars_inner(&self, mapping: &impl Fn(Symbol) -> Option<Type>) -> Option<Type> {
        match self {
            Type::Nothing => Some(Type::Nothing),
            Type::Any => Some(Type::Any),
            Type::Var(tvar) => mapping(*tvar),
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
            Type::Vectorof(t) => Some(Type::Vectorof(t.try_fill_tvars_inner(mapping)?.into())),

            Type::Bytes => Some(Type::Bytes),
            Type::Lambda {
                free_vars: _,
                args,
                result,
            } => {
                // this is *not* really correct in the general case, but we only fill type-vars to 1. type erase or 2. on non-lambdas
                Some(Type::Lambda {
                    free_vars: vec![],
                    args: args
                        .iter()
                        .map(|a| a.try_fill_tvars_inner(mapping))
                        .collect::<Option<List<_>>>()?,
                    result: result.try_fill_tvars_inner(mapping)?.into(),
                })
            }
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

    /// Interpret a vector type as a dynamic vector, returning
    pub fn try_vectorof_inner(&self) -> Option<Self> {
        match self {
            Type::Vectorof(t) => Some(t.deref().clone()),
            Type::Vector(inner) => {
                if inner.is_empty() {
                    Some(Type::Nothing)
                } else {
                    let u = inner.iter().fold(Type::Nothing, |a, b| a.smart_union(b));
                    Some(u)
                }
            }
            Type::Union(x, y) => {
                let x = x.try_vectorof_inner()?;
                let y = y.try_vectorof_inner()?;
                Some(x.smart_union(&y))
            }
            _ => None,
        }
    }
}
