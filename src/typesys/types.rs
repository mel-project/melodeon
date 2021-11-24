use ethnum::U256;
use std::hash::Hash;
use std::sync::Arc;
use std::{borrow::Cow, fmt::Debug};
use tap::Tap;

use crate::containers::{List, Map, Set, Symbol, Void};

use super::poly::Polynomial;

pub trait Variable: Clone + Hash + Eq + Debug + Ord {
    /// Possibly convert from a symbol. By default, just fails mercilessly.
    fn try_from_sym(_: Symbol) -> Option<Self> {
        None
    }
}

impl Variable for Void {}

impl Variable for Symbol {
    fn try_from_sym(s: Symbol) -> Option<Self> {
        Some(s)
    }
}

/// A Melodeon type. [`Type`] is generic over two parameters, `TVar` and `CVar`, which represent the type for
/// type-variables as well as the type for constant-generic variables.
/// These are generic types in order to statically guarantee the status of free variables. For example, one may start
/// with `Type<RawTVar, RawCVar>`, turn that into `Type<MangledTVar, MangledCVar>`, and resolve that into [`Type`].
///
/// [`Type`] is an alias for [`Type<Void, Void>`], representing a type with *no* free variables. [`Void`] is a special
/// type that cannot be constructed, so a value of [`Type<Void, Void>`] *statically* guarantees a lack of free variables.
///
/// In general, typechecking code should not directly match against [`Type`]. Instead, use the subtyping and unification methods as needed.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Type<TVar: Variable = Void, CVar: Variable = Void> {
    None,
    Any,
    Var(TVar),
    NatRange(ConstExpr<CVar>, ConstExpr<CVar>),
    Vector(List<Self>),
    Vectorof(Arc<Self>, ConstExpr<CVar>),
    DynVectorof(Arc<Self>),
    Struct(Symbol, List<(Symbol, Self)>),
    Union(Arc<Self>, Arc<Self>),
}

impl<TVar: Variable, CVar: Variable> Debug for Type<TVar, CVar> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self == &Type::all_nat() {
            return std::fmt::Display::fmt("Nat", f);
        }
        match self {
            Type::None => std::fmt::Display::fmt("None", f),
            Type::Any => std::fmt::Display::fmt("Any", f),
            Type::Var(t) => t.fmt(f),
            Type::NatRange(a, b) => {
                if a == b {
                    std::fmt::Display::fmt(&format!("{{{:?}}}", a), f)
                } else {
                    std::fmt::Display::fmt(&format!("{{{:?}..{:?}}}", a, b), f)
                }
            }
            Type::Vector(vec) => vec.fmt(f),
            Type::Vectorof(a, b) => std::fmt::Display::fmt(&format!("[{:?}; {:?}]", a, b), f),
            Type::Struct(s, v) => std::fmt::Display::fmt(&format!("!struct({}){:?}", s, v), f),
            Type::Union(t, u) => std::fmt::Display::fmt(&format!("{:?} | {:?}", t, u), f),
            Type::DynVectorof(t) => std::fmt::Display::fmt(&format!("[{:?};]", t), f),
        }
    }
}

impl<TVar: Variable, CVar: Variable> Type<TVar, CVar> {
    /// Checks whether this type is always "falsy".
    pub fn always_falsy(&self) -> bool {
        // that means it needs to be just zero.
        self.subtype_of(&Type::NatRange(0.into(), 0.into()))
    }
    /// Convenience function that creates a NatRange covering all numbers
    pub fn all_nat() -> Self {
        Self::NatRange(0.into(), U256::MAX.into())
    }
    /// Equivalence relation. Returns true iff `self` and `other` are subtypes of each other.
    pub fn equiv_to(&self, other: &Self) -> bool {
        self.subtype_of(other) && other.subtype_of(other)
    }
    /// Subtype relation. Returns true iff `self` is a subtype of `other`.
    pub fn subtype_of(&self, other: &Self) -> bool {
        log::trace!("checking {:?} <:? {:?}", self, other);
        match (self, other) {
            (Type::None, _) => true,
            (_, Type::Any) => true,
            (Type::Union(t, u), anything) => t.subtype_of(anything) && u.subtype_of(anything),
            (Type::Var(x), Type::Var(y)) => x == y,
            (Type::Var(_), Type::Union(t, u)) => {
                // This is the "union rule". It is conservative and sound, but imprecise, because the left-hand type might be a *combination* of some subtype of T and some subtype of U, while not a subtype of either.
                // But because the LHS here is just a single variable, we cannot further investigate, so we do the best we can.
                self.subtype_of(t) || self.subtype_of(u)
            }
            (Type::NatRange(ax, ay), Type::NatRange(bx, by)) => {
                (bx.try_eval() == Some(0u8.into()) && by.try_eval() == Some(U256::MAX))
                    || (bx.leq(ax) && ay.leq(by))
            }
            (Type::NatRange(a, b), Type::Union(t, u)) => {
                // we only apply the union rule in two cases:
                // - both sides of the range are the same number. This means that this is literally a single number. In this case, the union rule is actually precise: a single number being a subtype of T | U means that it must be a subtype of at least one of T or U.
                // - the range has const-generic parameters. we cannot investigate further, so the "union rule" is the best we can do.
                // otherwise, we can do better than apply the union rule. We try the union rule because in most cases it works, but if it does not, we break the range down into two halves and handle them separately. This eventually "bottoms out" as either a simple number or some other thing where the union rule works.
                if let Some((a, b)) = a.try_eval().and_then(|a| Some((a, b.try_eval()?))) {
                    if a == b {
                        self.subtype_of(t) || self.subtype_of(u)
                    } else {
                        self.subtype_of(t) || self.subtype_of(u) || {
                            // break down
                            let midpoint = a + (b - a) / 2;
                            let left_half = Type::NatRange(a.into(), midpoint.into());
                            let right_half = Type::NatRange((midpoint + 1).min(b).into(), b.into());
                            left_half.subtype_of(other) && right_half.subtype_of(other)
                        }
                    }
                } else {
                    self.subtype_of(t) || self.subtype_of(u)
                }
            }
            (Type::Vector(v1), Type::Vector(v2)) => {
                // pairwise comparison
                v1.len() == v2.len() && v1.iter().zip(v2.iter()).all(|(v1, v2)| v1.subtype_of(v2))
            }
            (Type::Vector(v1), Type::DynVectorof(t)) => v1.iter().all(|t1| t1.subtype_of(t)),
            (Type::Vector(v1), Type::Vectorof(v2_all, v2_len)) => v2_len
                .try_eval()
                .map(|v2_len| {
                    v2_len == U256::from(v1.len() as u64) && v1.iter().all(|i| i.subtype_of(v2_all))
                })
                .unwrap_or(false),
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
            (Type::Vectorof(v1_all, v1_len), Type::Vector(v2)) => v1_len
                .try_eval()
                .map(|v1_len| {
                    v1_len.as_usize() == v2.len() && v2.iter().all(|v2| v1_all.subtype_of(v2))
                })
                .unwrap_or(false),
            (Type::Vectorof(v1_all, v1_len), Type::Vectorof(v2_all, v2_len)) => {
                // equal lengths
                v1_len.leq(v2_len) && v2_len.leq(v1_len) && v1_all.subtype_of(v2_all)
            }
            (Type::Vectorof(v1_all, _), Type::DynVectorof(v2_all)) => v1_all.subtype_of(v2_all),
            (Type::Vectorof(v1_all, v1_len), Type::Union(t, u)) => {
                // Similar to elementwise vectors
                self.subtype_of(t)
                    || self.subtype_of(u)
                    || v1_len
                        .try_eval()
                        .and_then(|v1_len| {
                            let other = other.try_to_vector()?;
                            Some(
                                other.len() == v1_len.as_usize()
                                    && other.iter().all(|o| v1_all.subtype_of(o)),
                            )
                        })
                        .unwrap_or(false)
            }
            (Type::Struct(a, _), Type::Struct(b, _)) => a == b,
            // Structs are "atomic", just like individual numbers, so the union rule is in fact precise.
            (Type::Struct(_, _), Type::Union(t, u)) => self.subtype_of(t) || self.subtype_of(u),
            (Type::DynVectorof(v1_all), Type::DynVectorof(v2_all)) => v1_all.subtype_of(v2_all),
            _ => false,
        }
    }

    /// Subtracts another type, *conservatively*. That is, it produces a type that includes *at least* all the values that are in `self` but not in `other`, but it may include more in difficult-to-calculate cases.
    pub fn subtract(&self, other: &Self) -> Cow<Self> {
        log::trace!("subtracting {:?} - {:?}", self, other);
        // if we're a subtype of other, we're done
        if self.subtype_of(other) {
            return Cow::Owned(Type::None);
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
            Type::Vectorof(t, n) => {
                // since the other side cannot possibly be a union (that's handled earlier), the only case where we subtract is if they're also a vectorof.
                match other {
                    Type::Vectorof(their_t, their_n) => {
                        if n != their_n {
                            Cow::Borrowed(self)
                        } else {
                            Cow::Owned(Type::Vectorof(
                                t.subtract(their_t).into_owned().into(),
                                n.clone(),
                            ))
                        }
                    }
                    Type::DynVectorof(their_t) => Cow::Owned(Type::Vectorof(
                        t.subtract(their_t).into_owned().into(),
                        n.clone(),
                    )),
                    _ => Cow::Borrowed(self),
                }
            }
            Type::None => Cow::Borrowed(self),
            Type::Any => Cow::Borrowed(self),
            Type::Var(_) => Cow::Borrowed(self),
            Type::NatRange(ax, ay) => {
                if let Type::NatRange(bx, by) = other {
                    // four cases: no overlap, shrink to left, shrink to right, or punch a hole in the middle.
                    if !bx.leq(ay) || !ax.leq(by) {
                        Cow::Borrowed(self)
                    } else if ay.leq(by) {
                        // this means the overlap is to the right,
                        Cow::Owned(Type::NatRange(
                            ax.clone(),
                            bx.sub1().unwrap_or_else(|| bx.clone()),
                        ))
                    } else if bx.leq(ax) {
                        // the overlap is to the left
                        Cow::Owned(Type::NatRange(by.clone().add1(), ay.clone()))
                    } else {
                        // punch a hole
                        Cow::Owned(Type::Union(
                            Type::NatRange(ax.clone(), bx.sub1().unwrap_or_else(|| bx.clone()))
                                .into(),
                            Type::NatRange(by.add1(), ay.clone()).into(),
                        ))
                    }
                } else {
                    Cow::Borrowed(self)
                }
            }
            Type::Struct(_, _) => Cow::Borrowed(self),
            Type::DynVectorof(t) => {
                if let Type::DynVectorof(their_t) = other {
                    Cow::Owned(Type::DynVectorof(t.subtract(their_t).into_owned().into()))
                } else {
                    Cow::Borrowed(self)
                }
            }
        }
    }

    /// Using the current type (which contains typevars of type TVar) as a template, as well as a different type where the "holes" formed by these typevars are filled, derive a mapping between the free typevars of [self] and types.
    pub fn unify_tvars<TVar2: Variable, CVar2: Variable>(
        &self,
        other: &Type<TVar2, CVar2>,
    ) -> Option<Map<TVar, Type<TVar2, CVar2>>> {
        log::trace!("unify_tvars {:?} with {:?}", self, other);
        // First, we find out exactly *where* in self do the typevars appear.
        let locations = self.tvar_locations();
        log::trace!("found locations: {:?}", locations);
        // Then, we index into other to find out what concrete types those tvars represent
        locations
            .into_iter()
            .map(|(var, locations)| {
                locations
                    .into_iter()
                    .fold(Some(Type::None), |accum, elem| {
                        let accum = accum?;
                        let mut ptr = other.clone();
                        for elem in elem {
                            ptr = ptr.index(elem.map(ConstExpr::from).as_ref())?.into_owned();
                        }
                        Some(accum.smart_union(&ptr))
                    })
                    .map(|other_piece| (var, other_piece))
            })
            .collect()
    }

    /// Similar to [`Type::unify_tvars`], but for const-generic variables instead.
    pub fn unify_cvars<TVar2: Variable, CVar2: Variable>(
        &self,
        other: &Type<TVar2, CVar2>,
    ) -> Option<Map<CVar, ConstExpr<CVar2>>> {
        log::trace!("unify_cvars {:?} with {:?}", self, other);
        // First, we find all the locations where const-generic parameters appear. This is actually just a list of locations where if we index there, we will find a type containing a const-generic parameter.
        let locations = self.cvar_locations();
        // Then, we establish a bunch of equations by indexing into those locations in both sides and creating equations.
        let mut accum = Map::new();
        for location in locations {
            let this_elem =
                self.index_iterated(location.iter().cloned().map(|f| f.map(ConstExpr::from)))?;
            let other_elem =
                other.index_iterated(location.iter().cloned().map(|f| f.map(ConstExpr::from)))?;
            match (this_elem, other_elem) {
                (
                    Type::NatRange(ConstExpr::Var(ax), ConstExpr::Var(ay)),
                    Type::NatRange(bx, by),
                ) => {
                    accum.insert(ax, bx);
                    accum.insert(ay, by);
                }
                (
                    Type::NatRange(ax, ay),
                    Type::NatRange(bx, by),
                ) => {
                    if let Some((bx, by)) = bx.try_eval().and_then(|bx| Some((bx, by.try_eval()?))) {
                        // solve the polynomials
                        let t  = Polynomial::from(&ax).solve(bx);
                        if t.len() == 1 {
                            accum.insert(ax.cvars()[0].clone(), t[0].into());
                        }
                        let t  = Polynomial::from(&ay).solve(by);
                        if t.len() == 1 {
                            accum.insert(ay.cvars()[0].clone(), t[0].into());
                        }
                    }
                }
                (Type::Vectorof(_, ConstExpr::Var(var)), Type::Vectorof(_, real)) => {
                    accum.insert(var, real);
                },
                (Type::Vectorof(_, var), Type::Vectorof(_, real)) => {
                    if let Some(real) = real.try_eval() {
                        let t = Polynomial::from(&var).solve(real);
                        if t.len() == 1 {
                            accum.insert(var.cvars()[0].clone(), t[0].into());
                        }
                    }
                },
                (Type::Vectorof(_, var), Type::Vector(v)) => {
                    let solns = Polynomial::from(&var).solve((v.len() as u64).into());
                    if solns.len() == 1 {
                        accum.insert(var.cvars()[0].clone(), solns[0].into());
                    }
                }
                 (a, b) => log::warn!(
                    "does not yet support nontrivial const-generic variables (matching {:?} with {:?})",
                    a, b
                ),
            }
        }
        // 19:13 98.5
        Some(accum)
    }

    // /// Unifies "into" a template
    // pub fn unify_into(&self, template: &Self) -> Option<Self> {
    //     let cvar_tab = template.unify_cvars(self)?;
    //     let tvar_tab = template.unify_tvars(self)?;
    //     template
    //         .try_fill_cvars(|c| cvar_tab.get(c).cloned())?
    //         .try_fill_tvars(|c| tvar_tab.get(c).cloned())
    // }

    /// Returns a set of possible lengths of this type.
    pub fn lengths(&self) -> Set<ConstExpr<CVar>> {
        match self {
            Type::Vector(v) => std::iter::once(ConstExpr::from(v.len())).collect(),
            Type::Vectorof(_, n) => std::iter::once(n.clone()).collect(),
            Type::Union(t, u) => t.lengths().union(u.lengths()),
            _ => Set::new(),
        }
    }

    /// Indexes into this type. None indicates a generalized index.
    pub fn index(&self, idx: Option<&ConstExpr<CVar>>) -> Option<Cow<Self>> {
        match self {
            Type::Vector(elems) => {
                if let Some(idx) = idx {
                    let idx = idx.try_eval()?.as_usize();
                    Some(Cow::Borrowed(elems.get(idx)?))
                } else {
                    Some(Cow::Owned(
                        elems.iter().fold(Type::None, |a, b| a.smart_union(b)),
                    ))
                }
            }
            Type::Vectorof(t, n) => {
                if let Some(idx) = idx {
                    if idx.add1().leq(n) {
                        Some(Cow::Owned(t.as_ref().clone()))
                    } else {
                        None
                    }
                } else {
                    Some(Cow::Owned(t.as_ref().clone()))
                }
            }
            Type::Struct(_, b) => Some(Cow::Owned(
                Type::Vector(b.iter().map(|a| a.1.clone()).collect())
                    .index(idx)?
                    .into_owned(),
            )),
            Type::Union(a, b) => Some(Cow::Owned(Type::Union(
                a.index(idx)?.into_owned().into(),
                b.index(idx)?.into_owned().into(),
            ))),
            _ => None,
        }
    }

    /// Append this vector type to another vector type. Returns None if the two types cannot be appended.
    pub fn append(&self, other: &Self) -> Option<Self> {
        match (self, other) {
            (Type::Union(t, u), v) => Some(Type::Union(t.append(v)?.into(), u.append(v)?.into())),
            (v, Type::Union(t, u)) => Some(Type::Union(v.append(t)?.into(), u.append(t)?.into())),
            (Type::Vector(v1), Type::Vector(v2)) => Some(Type::Vector(
                v1.iter().cloned().chain(v2.iter().cloned()).collect(),
            )),
            (Type::Vector(v1), Type::Vectorof(t, n)) => Some(Type::Vectorof(
                t.smart_union(&v1.iter().fold(Type::None, |a, b| a.smart_union(b)))
                    .into(),
                ConstExpr::Add(n.clone().into(), Arc::new(v1.len().into())),
            )),
            (Type::Vectorof(t, n), Type::Vector(v)) => Some(Type::Vectorof(
                t.smart_union(&v.iter().fold(Type::None, |a, b| a.smart_union(b)))
                    .into(),
                ConstExpr::Add(n.clone().into(), Arc::new(v.len().into())),
            )),
            (Type::Vectorof(t1, n1), Type::Vectorof(t2, n2)) => Some(Type::Vectorof(
                t1.smart_union(t2).into(),
                ConstExpr::Add(n1.clone().into(), n2.clone().into()),
            )),
            _ => None,
        }
    }

    /// Helper function that indexes into an iterator of locations.
    pub fn index_iterated(
        &self,
        indices: impl Iterator<Item = Option<ConstExpr<CVar>>>,
    ) -> Option<Self> {
        let mut ptr = self.clone();
        for index in indices {
            ptr = ptr.index(index.as_ref())?.into_owned();
        }
        Some(ptr)
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

    /// Fixes an illegal NatRange by turning it into a full-range Nat instead.
    ///
    /// TODO: is this sound?
    pub fn fix_natrange(self) -> Self {
        if let Type::NatRange(a, b) = &self {
            if !a.leq(b) {
                Type::all_nat()
            } else {
                self
            }
        } else {
            self
        }
    }

    /// Returns the set of all locations where constant-generic parameters appear.
    fn cvar_locations(&self) -> Set<List<Option<usize>>> {
        match self {
            Type::None => Set::new(),
            Type::Any => Set::new(),
            Type::Var(_) => Set::new(),
            Type::NatRange(_, _) => [List::new()].into_iter().collect(),
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
            Type::Vectorof(inner, _) => inner
                .cvar_locations()
                .into_iter()
                .map(|mut loc| {
                    loc.insert(0, None);
                    loc
                })
                .chain(std::iter::once(List::new()))
                .collect(),
            Type::Struct(_, i) => {
                Type::Vector(i.iter().map(|a| a.1.clone()).collect()).cvar_locations()
            }
            Type::Union(t, u) => t.cvar_locations().union(u.cvar_locations()),
            Type::DynVectorof(t) => t
                .cvar_locations()
                .into_iter()
                .map(|mut loc| {
                    loc.push_front(None);
                    loc
                })
                .collect(),
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
            Type::Vectorof(t, _) => {
                let inner_map = t.tvar_locations();
                inner_map
                    .into_iter()
                    .map(|(k, v)| {
                        (
                            k,
                            v.into_iter()
                                .map(|mut v| {
                                    v.insert(0, None);
                                    v
                                })
                                .collect(),
                        )
                    })
                    .collect()
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
        mapping: impl Fn(&TVar) -> Option<Type<NewTVar, CVar>>,
    ) -> Option<Type<NewTVar, CVar>> {
        self.try_fill_tvars_inner(&mapping)
    }

    /// Fills in all type-variables, except infallibly.
    pub fn fill_tvars<NewTVar: Variable>(
        &self,
        mapping: impl Fn(&TVar) -> Type<NewTVar, CVar>,
    ) -> Type<NewTVar, CVar> {
        self.try_fill_tvars(|tv| Some(mapping(tv))).unwrap()
    }

    // separate out for recursion
    fn try_fill_tvars_inner<NewTVar: Variable>(
        &self,
        mapping: &impl Fn(&TVar) -> Option<Type<NewTVar, CVar>>,
    ) -> Option<Type<NewTVar, CVar>> {
        match self {
            Type::None => Some(Type::None),
            Type::Any => Some(Type::Any),
            Type::Var(tvar) => mapping(tvar),
            Type::NatRange(a, b) => Some(Type::NatRange(a.clone(), b.clone())),
            Type::Vector(elems) => {
                let elems: Option<List<_>> = elems
                    .iter()
                    .map(|e| e.try_fill_tvars_inner(mapping))
                    .collect();
                Some(Type::Vector(elems?))
            }
            Type::Vectorof(t, n) => Some(Type::Vectorof(
                t.try_fill_tvars_inner(mapping)?.into(),
                n.clone(),
            )),
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
        }
    }

    /// Fills in all const-generic variables. If the resolution fails at any step, returns [None].
    pub fn try_fill_cvars<NewCVar: Variable>(
        &self,
        mut mapping: impl FnMut(&CVar) -> Option<ConstExpr<NewCVar>>,
    ) -> Option<Type<TVar, NewCVar>> {
        self.try_fill_cvars_inner(&mut mapping)
    }

    /// Fills in all const-generic variables. But infallible.
    pub fn fill_cvars<NewCVar: Variable>(
        &self,
        mapping: impl Fn(&CVar) -> ConstExpr<NewCVar>,
    ) -> Type<TVar, NewCVar> {
        self.try_fill_cvars(|a| Some(mapping(a))).unwrap()
    }

    fn try_fill_cvars_inner<NewCVar: Variable>(
        &self,
        mapping: &mut impl FnMut(&CVar) -> Option<ConstExpr<NewCVar>>,
    ) -> Option<Type<TVar, NewCVar>> {
        match self {
            Type::None => Some(Type::None),
            Type::Any => Some(Type::Any),
            Type::Var(tvar) => Some(Type::Var(tvar.clone())),
            Type::NatRange(a, b) => Some(Type::NatRange(
                a.try_fill_inner(mapping)?,
                b.try_fill_inner(mapping)?,
            )),
            Type::Vector(elems) => {
                let elems: Option<List<_>> = elems
                    .iter()
                    .map(|e| e.try_fill_cvars_inner(mapping))
                    .collect();
                Some(Type::Vector(elems?))
            }
            Type::Vectorof(t, n) => Some(Type::Vectorof(
                t.try_fill_cvars_inner(mapping)?.into(),
                n.try_fill_inner(mapping)?,
            )),
            Type::Struct(name, b) => Some(Type::Struct(
                *name,
                b.iter()
                    .map(|(a, b)| Some((*a, b.try_fill_cvars_inner(mapping)?)))
                    .collect::<Option<List<_>>>()?,
            )),
            Type::Union(a, b) => Some(Type::Union(
                a.try_fill_cvars_inner(mapping)?.into(),
                b.try_fill_cvars_inner(mapping)?.into(),
            )),
            Type::DynVectorof(t) => {
                Some(Type::DynVectorof(t.try_fill_cvars_inner(mapping)?.into()))
            }
        }
    }

    /// Interpret a vector type into a list of types. Returns [None] if this is not a vector type, or if the vector type has an indeterminate length.
    pub fn try_to_vector(&self) -> Option<Cow<List<Self>>> {
        match self {
            Type::Vectorof(inner, v) => {
                let len = v.try_eval()?.as_usize();
                Some(Cow::Owned(
                    std::iter::repeat(inner.as_ref().clone())
                        .take(len)
                        .collect(),
                ))
            }
            Type::Vector(inner) => Some(Cow::Borrowed(inner)),
            Type::Union(x, y) => {
                let x = x.try_to_vector()?;
                let y = y.try_to_vector()?;
                if x.len() != y.len() {
                    return None;
                }
                Some(Cow::Owned(
                    x.into_owned()
                        .into_iter()
                        .zip(y.into_owned().into_iter())
                        .map(|(x, y)| Type::Union(x.into(), y.into()))
                        .collect(),
                ))
            }
            _ => None,
        }
    }
}

/// Represents a rather surface-level const-expression. Polynomial-based canonicalization is not yet here.
#[derive(Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum ConstExpr<CVar: Variable> {
    Lit(U256),
    Var(CVar),
    Add(Arc<Self>, Arc<Self>),
    Mul(Arc<Self>, Arc<Self>),
}

impl<CVar: Variable> Debug for ConstExpr<CVar> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ConstExpr::Lit(lit) => lit.fmt(f),
            ConstExpr::Var(v) => v.fmt(f),
            ConstExpr::Add(a, b) => std::fmt::Display::fmt(&format!("({:?} + {:?})", a, b), f),
            ConstExpr::Mul(a, b) => std::fmt::Display::fmt(&format!("({:?} * {:?})", a, b), f),
        }
    }
}

impl<CVar: Variable> ConstExpr<CVar> {
    /// Find all the cvars.
    pub fn cvars(&self) -> List<CVar> {
        let mut accum = List::new();
        self.fill(|v| {
            accum.push_back(v.clone());
            Self::Var(v.clone())
        });
        accum
    }

    /// Partial order relation
    pub fn leq(&self, other: &Self) -> bool {
        self == other || Polynomial::from(self) <= Polynomial::from(other)
    }

    /// Fills in the free variables fallibly, given a mapping.
    pub fn try_fill<NewCVar: Variable>(
        &self,
        mut mapping: impl FnMut(&CVar) -> Option<ConstExpr<NewCVar>>,
    ) -> Option<ConstExpr<NewCVar>> {
        self.try_fill_inner(&mut mapping)
    }

    /// Fills in the free variables infallibly, given a mapping.
    pub fn fill<NewCVar: Variable>(
        &self,
        mut mapping: impl FnMut(&CVar) -> ConstExpr<NewCVar>,
    ) -> ConstExpr<NewCVar> {
        self.try_fill(|a| Some(mapping(a))).unwrap()
    }

    fn try_fill_inner<NewCVar: Variable>(
        &self,
        mapping: &mut impl FnMut(&CVar) -> Option<ConstExpr<NewCVar>>,
    ) -> Option<ConstExpr<NewCVar>> {
        match self {
            ConstExpr::Lit(lit) => Some(ConstExpr::Lit(*lit)),
            ConstExpr::Var(cvar) => mapping(cvar),
            ConstExpr::Add(a, b) => Some(ConstExpr::Add(
                a.try_fill_inner(mapping)?.into(),
                b.try_fill_inner(mapping)?.into(),
            )),
            ConstExpr::Mul(a, b) => Some(ConstExpr::Mul(
                a.try_fill_inner(mapping)?.into(),
                b.try_fill_inner(mapping)?.into(),
            )),
        }
    }

    /// Simplifies the const-expr to an equivalent form.
    pub fn simplify(self) -> Self {
        if let Some(num) = self.try_eval() {
            Self::Lit(num)
        } else {
            self
        }
    }

    /// Reduces the const-expr down to a single number if possible
    pub fn try_eval(&self) -> Option<U256> {
        match self {
            ConstExpr::Var(_) => None,
            ConstExpr::Add(x, y) => Some(x.try_eval()?.wrapping_add(y.try_eval()?)),
            ConstExpr::Lit(x) => Some(*x),
            ConstExpr::Mul(x, y) => Some(x.try_eval()?.wrapping_mul(y.try_eval()?)),
        }
    }

    /// Adds 1
    pub fn add1(&self) -> Self {
        ConstExpr::Add(self.clone().into(), Arc::new(1.into()))
    }

    /// Subtract 1, if possible.
    pub fn sub1(&self) -> Option<Self> {
        let val = self.try_eval()?;
        Some(ConstExpr::Lit(val.checked_sub(U256::from(1u8))?))
    }

    /// Tries to subtract another const-expression.
    pub fn checked_sub(&self, other: &Self) -> Option<Self> {
        let my_poly = Polynomial::from(self);
        let their_poly = Polynomial::from(other);
        Some(my_poly.checked_sub(their_poly)?.into())
    }
}

impl ConstExpr<Void> {
    /// Reduces the const-expr down to a single number. Always possible for unparameterized cexprs.
    pub fn eval(&self) -> U256 {
        self.try_eval().unwrap()
    }
}

impl<CVar: Variable> From<i32> for ConstExpr<CVar> {
    fn from(i: i32) -> Self {
        ConstExpr::Lit((i as u64).into())
    }
}

impl<CVar: Variable> From<usize> for ConstExpr<CVar> {
    fn from(i: usize) -> Self {
        ConstExpr::Lit((i as u64).into())
    }
}

impl<CVar: Variable> From<U256> for ConstExpr<CVar> {
    fn from(i: U256) -> Self {
        ConstExpr::Lit(i)
    }
}

#[cfg(test)]
mod tests {
    use log::LevelFilter;

    use super::*;
    #[test]
    fn tricky_range() {
        init_logs();
        let r1: Type = Type::NatRange(0.into(), 500.into());
        let r2: Type = Type::NatRange(501.into(), 1000.into());
        let middle: Type = Type::NatRange(499.into(), 501.into());
        assert!(middle.subtype_of(&Type::Union(r1.clone().into(), r2.clone().into())));
        let middle: Type = Type::NatRange(499.into(), 1001.into());
        assert!(!middle.subtype_of(&Type::Union(r1.into(), r2.into())));
    }

    #[test]
    fn simple_fill() {
        init_logs();
        let r1: Type<Symbol, Symbol> = Type::Vector(
            [
                Type::NatRange(0.into(), 10.into()),
                Type::NatRange(10.into(), 20.into()),
                Type::Var(Symbol::from("T")),
                Type::Vectorof(
                    Type::Var(Symbol::from("T")).into(),
                    ConstExpr::Var(Symbol::from("n")),
                ),
                Type::Vectorof(
                    Type::Var(Symbol::from("U")).into(),
                    ConstExpr::Add(Arc::new(1.into()), ConstExpr::Var(Symbol::from("n")).into()),
                ),
            ]
            .into_iter()
            .collect(),
        );
        let resolved: Type = r1
            .fill_tvars(|sym| {
                if sym == &Symbol::from("T") {
                    Type::NatRange(0.into(), 1000.into())
                } else {
                    Type::NatRange(1000.into(), 2000.into())
                }
            })
            .fill_cvars(|_| 100.into());
        log::info!("before substitution: {:?}", r1);
        log::info!("after substitution: {:?}", resolved);
        log::info!("tvar unification: {:?}", r1.unify_tvars(&resolved));
        log::info!("cvar unification: {:?}", r1.unify_cvars(&resolved));
    }

    #[test]
    fn tricky_unification() {
        init_logs();
        let r1: Type<Symbol, Symbol> = Type::Vectorof(
            Type::Var(Symbol::from("T")).into(),
            ConstExpr::Add(
                ConstExpr::Var(Symbol::from("n")).into(),
                ConstExpr::Mul(
                    ConstExpr::Var(Symbol::from("n")).into(),
                    ConstExpr::Var(Symbol::from("n")).into(),
                )
                .into(),
            ),
        );
        log::info!("before unification: {:?}", r1);
        let r2: Type<Symbol, Void> =
            Type::Vectorof(Type::Var(Symbol::from("T")).into(), 392614410.into());
        let map = r1.unify_cvars(&r2);
        log::info!("after unification: {:?}", map);
    }

    #[test]
    fn sub_hole_punching() {
        init_logs();
        let r1: Type = Type::NatRange(0.into(), 500.into());
        assert!(r1
            .subtract(&Type::NatRange(0.into(), 500.into()))
            .equiv_to(&Type::None));
        assert!(r1
            .subtract(&Type::NatRange(0.into(), 400.into()))
            .equiv_to(&Type::NatRange(401.into(), 500.into())));
        assert!(r1
            .subtract(&Type::NatRange(400.into(), 501.into()))
            .equiv_to(&Type::NatRange(0.into(), 399.into())));
        assert!(r1
            .subtract(&Type::NatRange(100.into(), 400.into()))
            .equiv_to(&Type::Union(
                Type::NatRange(0.into(), 99.into()).into(),
                Type::NatRange(401.into(), 500.into()).into()
            )));
    }

    fn init_logs() {
        let _ = env_logger::builder()
            .is_test(true)
            .format_timestamp(None)
            .filter_level(LevelFilter::Trace)
            .try_init();
    }
}

// def get<T, $n>(vec: [T; $n + 1], idx: {0..$n}) : T = vec[idx]

/// Struct name to unique ID.
pub fn struct_uniqid(name: Symbol) -> U256 {
    U256::from_be_bytes(
        *blake3::keyed_hash(
            b"__________melodeon_struct_uniqid",
            name.to_string().as_bytes(),
        )
        .as_bytes(),
    )
    .as_u64()
    .into()
}
