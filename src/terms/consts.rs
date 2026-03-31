use std::collections::HashSet;
use std::fmt;
use crate::types::{TypeSubstitution, Types};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Const {
    TT,
    FF,
    Zero,
    Succ,
    Nil(Types),
    Cons(Types),
    Pair(Types, Types),
    Split(Types, Types, Types),
    Cases(Types),
    RecNat(Types),
    RecList(Types, Types),
}

impl fmt::Display for Const {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Const::TT => write!(f, "tt"),
            Const::FF => write!(f, "ff"),
            Const::Zero => write!(f, "0"),
            Const::Succ => write!(f, "S"),
            Const::Nil(ty) => write!(f, "nil_{}", ty),
            Const::Cons(ty) => write!(f, "cons_{}", ty),
            Const::Pair(ty1, ty2) => write!(f, "pair_{{{}, {}}}", ty1, ty2),
            Const::Split(ty1, ty2, ty3) => write!(f, "split_{{{}, {}, {}}}", ty1, ty2, ty3),
            Const::Cases(ty) => write!(f, "cases_{}", ty),
            Const::RecNat(ty) => write!(f, "R_ℕ^{}", ty),
            Const::RecList(arg, rec) => write!(f, "R_𝕃({})^{}", arg, rec),
        }
    }
}

impl Const {
    pub fn ty(&self) -> Types {
        match self {
            Const::TT => Types::Boolean,

            Const::FF => Types::Boolean,

            Const::Zero => Types::Nat,

            Const::Succ => {Types::arr(Types::Nat, Types::Nat)},

            Const::Nil(ty) => Types::list(ty.clone()),

            Const::Cons(ty) => {
                Types::arr(ty.clone(),
                           Types::arr(Types::list(ty.clone()), Types::list(ty.clone())))
            },
            Const::Pair(ty1, ty2) => {
                Types::arr(ty1.clone(),
                           Types::arr(ty2.clone(),
                                      Types::pair(ty1.clone(), ty2.clone())))
            },
            Const::Split(ty1, ty2, ty3) => {
                Types::arr(Types::pair(ty1.clone(), ty2.clone()),
                           Types::arr(Types::arr(ty1.clone(),Types::arr(ty2.clone(), ty3.clone())),
                                      ty3.clone()))
            },
            Const::Cases(ty) => {
                Types::arr(Types::Boolean,Types::arr(ty.clone(),Types::arr(ty.clone(),ty.clone())))
            },
            Const::RecNat(ty) => {
                Types::arr(Types::Nat,
                           Types::arr(ty.clone(),
                                      Types::arr(Types::arr(Types::Nat,Types::arr(ty.clone(),ty.clone()))
                                                 ,ty.clone())))
            },
            Const::RecList(t, tau) => Types::arr(
                Types::list(t.clone()),
                Types::arr(tau.clone(),
                           Types::arr(
                               Types::arr(
                                   t.clone(),
                                   Types::arr(
                                       Types::list(t.clone()),
                                       Types::arr(tau.clone(), tau.clone()),
                                   ),
                               ),
                               tau.clone(),
                           ),
                ),
            ),
        }
    }
    pub fn free_type_vars(&self) -> HashSet<usize> {
        match self {
            Const::TT | Const::FF | Const::Zero | Const::Succ => HashSet::new(),
            Const::Nil(ty) | Const::Cons(ty) | Const::Cases(ty) |
            Const::RecNat(ty) => {
                ty.free_vars()
            }
            Const::Pair(ty1, ty2) | Const::RecList(ty1, ty2) => {
                let mut a = ty1.free_vars();
                a.extend(ty2.free_vars());
                a
            }
            Const::Split(ty1, ty2, ty3) => {
                let mut a = ty1.free_vars();
                a.extend(ty2.free_vars());
                a.extend(ty3.free_vars());
                a
            }
        }
    }
    pub fn subst_type(&self, sigma: &TypeSubstitution) -> Self {
        match self {
            Const::TT => Const::TT,
            Const::FF => Const::FF,
            Const::Zero => Const::Zero,
            Const::Succ => Const::Succ,
            Const::Nil(ty) => Const::Nil(ty.subst(sigma)),
            Const::Cons(ty) => Const::Cons(ty.subst(sigma)),
            Const::Pair(ty1, ty2) => {
                Const::Pair(ty1.subst(sigma), ty2.subst(sigma))
            }
            Const::Split(ty1, ty2, ty3) => {
                Const::Split(ty1.subst(sigma), ty2.subst(sigma), ty3.subst(sigma))
            }
            Const::Cases(ty) => Const::Cases(ty.subst(sigma)),
            Const::RecNat(ty) => Const::RecNat(ty.subst(sigma)),
            Const::RecList(t, tau) => {
                Const::RecList(t.subst(sigma), tau.subst(sigma))
            }
        }
    }

}
#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::Types;
    use std::collections::{HashMap, HashSet};
    #[test]
    fn ty_of_basic_constants() {
        assert_eq!(Const::TT.ty(), Types::Boolean);
        assert_eq!(Const::FF.ty(), Types::Boolean);
        assert_eq!(Const::Zero.ty(), Types::Nat);
        assert_eq!(Const::Succ.ty(), Types::arr(Types::Nat, Types::Nat));
    }
    #[test]
    fn ty_of_nil_and_cons() {
        let alpha = Types::TypeVar(0);

        assert_eq!(Const::Nil(alpha.clone()).ty(), Types::list(alpha.clone()));

        assert_eq!(
            Const::Cons(alpha.clone()).ty(),
            Types::arr(
                alpha.clone(),
                Types::arr(Types::list(alpha.clone()), Types::list(alpha.clone()))
            )
        );
    }
    #[test]
    fn ty_of_pair() {
        let alpha = Types::TypeVar(0);
        let beta = Types::TypeVar(1);

        assert_eq!(
            Const::Pair(alpha.clone(), beta.clone()).ty(),
            Types::arr(
                alpha.clone(),
                Types::arr(beta.clone(), Types::pair(alpha.clone(), beta.clone()))
            )
        );
    }
    #[test]
    fn free_type_vars_of_split() {
        let c = Const::Split(
            Types::TypeVar(0),
            Types::TypeVar(1),
            Types::TypeVar(2),
        );

        let expected: HashSet<usize> = HashSet::from([0, 1, 2]);
        assert_eq!(c.free_type_vars(), expected);
    }
    #[test]
    fn subst_type_on_nil() {
        let c = Const::Nil(Types::TypeVar(0));
        let sigma: TypeSubstitution = HashMap::from([
            (0, Types::Nat),
        ]);

        assert_eq!(c.subst_type(&sigma), Const::Nil(Types::Nat));
    }
    #[test]
    fn subst_type_does_nothing_on_closed_constants() {
        let c = Const::Succ;
        let sigma: TypeSubstitution = HashMap::from([
            (0, Types::Nat),
        ]);

        assert_eq!(c.subst_type(&sigma), Const::Succ);
    }
}