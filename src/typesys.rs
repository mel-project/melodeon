use ethnum::U256;
use std::hash::Hash;
use std::sync::Arc;
use std::{borrow::Cow, fmt::Debug};

use crate::containers::{IStr, List, Void};

pub trait Variable: Clone + Hash + Eq + Debug {}

impl Variable for Void {}

/// A Melodeon type. Generic over a "placeholder" type that represents type variables.
///
/// In general, typechecking code should not directly match against Type. Instead, use the subtyping and unification methods as needed.
#[derive(Clone)]
pub enum Type<TVar: Variable = Void, CVar: Variable = Void> {
    None,
    Any,
    Var(TVar),
    NatRange(ConstExpr<CVar>, ConstExpr<CVar>),
    Vector(List<Self>),
    Vectorof(Arc<Self>, ConstExpr<CVar>),
    Struct(IStr, List<Self>),
    Union(Arc<Self>, Arc<Self>),
}

impl<TVar: Variable, CVar: Variable> Debug for Type<TVar, CVar> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Type::None => std::fmt::Display::fmt("None", f),
            Type::Any => std::fmt::Display::fmt("Any", f),
            Type::Var(t) => t.fmt(f),
            Type::NatRange(a, b) => std::fmt::Display::fmt(&format!("{{{:?}:{:?}}}", a, b), f),
            Type::Vector(vec) => vec.fmt(f),
            Type::Vectorof(a, b) => std::fmt::Display::fmt(&format!("[{:?}; {:?}]", a, b), f),
            Type::Struct(s, v) => std::fmt::Display::fmt(&format!("!struct({}){:?}", s, v), f),
            Type::Union(t, u) => std::fmt::Display::fmt(&format!("{:?} | {:?}", t, u), f),
        }
    }
}

impl<TVar: Variable, CVar: Variable> Type<TVar, CVar> {
    /// Subtype relation. Returns true iff `self` is a subtype of `other`.
    pub fn subtype_of(&self, other: &Self) -> bool {
        log::debug!("checking {:?} <:? {:?}", self, other);
        match (self, other) {
            (Type::None, _) => true,
            (_, Type::None) => false,
            (_, Type::Any) => true,
            (Type::Any, _) => false,
            (Type::Union(t, u), anything) => t.subtype_of(anything) && u.subtype_of(anything),
            (Type::Var(x), Type::Var(y)) => x == y,
            (Type::Var(_), Type::Union(t, u)) => {
                // conservatively
                self.subtype_of(t) || self.subtype_of(u)
            }
            (Type::Var(_), _) => false,
            (_, Type::Var(_)) => false,
            (Type::NatRange(ax, ay), Type::NatRange(bx, by)) => bx.leq(ax) && ay.leq(by),
            (Type::NatRange(a, b), Type::Union(t, u)) => {
                // we only apply the union rule if either both sides of the range are the same number, or they cannot  be evaluated down to numbers. otherwise, we break down the LHS too.
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
            (Type::NatRange(_, _), _) => false,
            (Type::Vector(_), Type::NatRange(_, _)) => false,
            (Type::Vector(v1), Type::Vector(v2)) => {
                // pairwise comparison
                v1.len() == v2.len() && v1.iter().zip(v2.iter()).all(|(v1, v2)| v1.subtype_of(v2))
            }
            (Type::Vector(v1), Type::Vectorof(v2_all, v2_len)) => v2_len
                .try_eval()
                .map(|v2_len| {
                    v2_len == U256::from(v1.len() as u64) && v1.iter().all(|i| i.subtype_of(v2_all))
                })
                .unwrap_or(false),
            (Type::Vector(_), Type::Struct(_, _)) => false,
            (Type::Vector(v1), Type::Union(t, u)) => {
                // We "look into" the RHS vector. This is more precise than the union rule.
                // We still apply the union rule first because that's faster, doesn't allocate, etc.
                self.subtype_of(t)
                    || self.subtype_of(u)
                    || other
                        .to_vector()
                        .map(|other| {
                            v1.len() == other.len()
                                && v1
                                    .iter()
                                    .zip(other.iter())
                                    .all(|(v1, v2)| v1.subtype_of(v2))
                        })
                        .unwrap_or(false)
            }
            (Type::Vectorof(_, _), Type::NatRange(_, _)) => false,
            (Type::Vectorof(v1_all, v1_len), Type::Vector(v2)) => v1_len
                .try_eval()
                .map(|v1_len| {
                    v1_len.as_usize() == v2.len() && v2.iter().all(|v2| v1_all.subtype_of(v2))
                })
                .unwrap_or(false),
            (Type::Vectorof(v1_all, v1_len), Type::Vectorof(v2_all, v2_len)) => {
                // equal lengths
                v1_len == v2_len && v1_all.subtype_of(v2_all)
            }
            (Type::Vectorof(_, _), Type::Struct(_, _)) => false,
            (Type::Vectorof(v1_all, v1_len), Type::Union(t, u)) => {
                // Similar to elementwise vectors
                self.subtype_of(t)
                    || self.subtype_of(u)
                    || v1_len
                        .try_eval()
                        .and_then(|v1_len| {
                            let other = other.to_vector()?;
                            Some(
                                other.len() == v1_len.as_usize()
                                    && other.iter().all(|o| v1_all.subtype_of(o)),
                            )
                        })
                        .unwrap_or(false)
            }
            (Type::Struct(_, _), Type::NatRange(_, _)) => false,
            (Type::Struct(_, _), Type::Vector(_)) => false,
            (Type::Struct(_, _), Type::Vectorof(_, _)) => false,
            (Type::Struct(a, _), Type::Struct(b, _)) => a == b,
            (Type::Struct(_, _), Type::Union(t, u)) => self.subtype_of(t) || self.subtype_of(u),
        }
    }

    /// Subtracts another type, conservatively. That is, it produces a type that represents values that are in `self` but not in `other`.
    pub fn subtract(&self, other: &Self) -> Cow<Self> {
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
                if let Some(other) = other.to_vector() {
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
                if let Type::Vectorof(their_t, their_n) = other {
                    if n != their_n {
                        Cow::Borrowed(self)
                    } else {
                        Cow::Owned(Type::Vectorof(
                            t.subtract(their_t).into_owned().into(),
                            n.clone(),
                        ))
                    }
                } else {
                    Cow::Borrowed(self)
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
        }
    }

    /// Interpret a vector type into a list of types. Returns None if this is not a vector type, or if the vector type has an indeterminate length.
    pub fn to_vector(&self) -> Option<Cow<List<Self>>> {
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
                let x = x.to_vector()?;
                let y = y.to_vector()?;
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

#[derive(Clone, Hash, PartialEq, Eq)]
pub enum ConstExpr<CVar: Variable> {
    Literal(U256),
    Var(CVar),
    Plus(Arc<Self>, Arc<Self>),
}

impl<CVar: Variable> Debug for ConstExpr<CVar> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ConstExpr::Literal(lit) => lit.fmt(f),
            ConstExpr::Var(v) => v.fmt(f),
            ConstExpr::Plus(a, b) => std::fmt::Display::fmt(&format!("({:?} + {:?})", a, b), f),
        }
    }
}

impl<CVar: Variable> ConstExpr<CVar> {
    fn leq(&self, other: &Self) -> bool {
        // TODO: cool polynomial stuff
        self == other
            || self
                .try_eval()
                .and_then(|this| Some(this <= other.try_eval()?))
                .unwrap_or(false)
    }

    /// Reduces the const-expr down to a single number if possible
    pub fn try_eval(&self) -> Option<U256> {
        match self {
            ConstExpr::Var(_) => None,
            ConstExpr::Plus(x, y) => Some(x.try_eval()? + y.try_eval()?),
            ConstExpr::Literal(x) => Some(*x),
        }
    }

    /// Adds 1
    pub fn add1(&self) -> Self {
        ConstExpr::Plus(self.clone().into(), Arc::new(1.into()))
    }

    /// Subtract 1, if possible.
    pub fn sub1(&self) -> Option<Self> {
        let val = self.try_eval()?;
        Some(ConstExpr::Literal(val.checked_sub(U256::from(1u8))?))
    }
}

impl<CVar: Variable> From<i32> for ConstExpr<CVar> {
    fn from(i: i32) -> Self {
        ConstExpr::Literal((i as u64).into())
    }
}

impl<CVar: Variable> From<U256> for ConstExpr<CVar> {
    fn from(i: U256) -> Self {
        ConstExpr::Literal(i)
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
    fn sub_hole_punching() {
        init_logs();
        let r1: Type = Type::NatRange(0.into(), 500.into());
        assert!(r1
            .subtract(&Type::NatRange(0.into(), 500.into()))
            .subtype_of(&Type::None));
        assert!(r1
            .subtract(&Type::NatRange(0.into(), 400.into()))
            .subtype_of(&Type::NatRange(401.into(), 500.into())));
        assert!(r1
            .subtract(&Type::NatRange(400.into(), 501.into()))
            .subtype_of(&Type::NatRange(0.into(), 399.into())));
        assert!(r1
            .subtract(&Type::NatRange(100.into(), 400.into()))
            .subtype_of(&Type::Union(
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
