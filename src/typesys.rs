use ethnum::U256;
use std::hash::Hash;
use std::sync::Arc;
use tap::Tap;

use crate::containers::{IStr, List, Set, Void};

pub trait Variable: Clone + Hash + Eq {}

impl Variable for Void {}

/// A Melodeon type. Generic over a "placeholder" type that represents type variables.
#[derive(Clone, Debug)]
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

impl<TVar: Variable, CVar: Variable> Type<TVar, CVar> {
    /// Create a canonical type from this type. This essentially "lifts" all unions to the top level.
    pub fn to_canon(&self) -> CanonType<TVar, CVar> {
        match self {
            Type::None => CanonType(Set::new()),
            Type::Any => CanonType::one_case(FlatType::Any),
            Type::Var(var) => CanonType::one_case(FlatType::Var(var.clone())),
            Type::NatRange(start, end) => {
                CanonType::one_case(FlatType::NatRange(start.clone(), end.clone()))
            }
            Type::Vector(elems) => {
                let mut cases: List<FlatType<TVar, CVar>> = List::with_capacity(elems.len());
                cases.push(FlatType::Vector(List::new()));
                // iterate over the inner canonical types, adding into the cases.
                // If some inner canonical type has more than 1 case, then we "fork" the cases.
                for elem in elems {
                    let elem = elem.to_canon().0;
                    if elem.is_empty() {
                        // This means that this element of the vector has type None. Anything that includes None is itself None.
                        return CanonType(Set::new());
                    }
                    let mut new_cases = Vec::new();
                    // then for each of our case, we add to all the possible cases.
                    for case in cases.iter_mut() {
                        let mut elem_iter = elem.iter().cloned();
                        let first_elem = elem_iter.next().unwrap();
                        for rest in elem_iter {
                            let mut case = case.clone();
                            if let FlatType::Vector(case) = &mut case {
                                case.push(rest);
                            }
                            new_cases.push(case);
                        }
                        if let FlatType::Vector(case) = case {
                            case.push(first_elem);
                        }
                    }
                    cases.extend(new_cases.into_iter());
                }
                CanonType(cases.into())
            }
            Type::Vectorof(t, count) => CanonType(
                t.to_canon()
                    .0
                    .into_iter()
                    .map(|t| FlatType::Vectorof(t.into(), count.clone()))
                    .collect(),
            ),
            Type::Struct(label, elems) => {
                let stolen = Type::Vector(elems.clone()).to_canon();
                CanonType(
                    stolen
                        .0
                        .into_iter()
                        .map(|t| {
                            if let FlatType::Vector(elems) = t {
                                FlatType::Struct(*label, elems)
                            } else {
                                panic!("stolen something that isn't vec")
                            }
                        })
                        .collect(),
                )
            }
            Type::Union(left, right) => {
                let left = left.to_canon();
                let right = right.to_canon();
                CanonType(left.0.union(right.0))
            }
        }
    }
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub enum ConstExpr<CVar> {
    Literal(U256),
    Var(CVar),
    Plus(Arc<Self>, Arc<Self>),
}

impl<CVar> From<i32> for ConstExpr<CVar> {
    fn from(i: i32) -> Self {
        ConstExpr::Literal((i as u64).into())
    }
}

#[derive(Clone, Debug)]
pub struct CanonType<TVar: Variable, CVar: Variable>(Set<FlatType<TVar, CVar>>);

impl<TVar: Variable, CVar: Variable> CanonType<TVar, CVar> {
    /// From a single flattype
    pub fn one_case(ftype: FlatType<TVar, CVar>) -> Self {
        Self(Set::new().tap_mut(|s| {
            s.insert(ftype);
        }))
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
/// A "flat" type that cannot contain any set-theoretical operators.
pub enum FlatType<TVar: Variable, CVar: Variable> {
    Any,
    Var(TVar),
    NatRange(ConstExpr<CVar>, ConstExpr<CVar>),
    Vector(List<Self>),
    Vectorof(Arc<Self>, ConstExpr<CVar>),
    Struct(IStr, List<Self>),
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn simple_union() {
        let t: Type = Type::NatRange(1.into(), 1.into());
        let u: Type = Type::NatRange(2.into(), 3.into());
        let v = Type::Union(t.into(), u.into());
        let vec = Type::Vectorof(v.into(), 200.into());
        eprintln!("before: {:?}", vec);
        let vec_canon = vec.to_canon();
        eprintln!("after: {:?}", vec_canon);
    }
}
