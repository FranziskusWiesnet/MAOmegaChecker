use std::fmt;
use std::collections::{HashMap, HashSet};

pub type TypeSubstitution = HashMap<usize, Types>;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Types {
    TypeVar(usize),
    Boolean,
    Nat,
    List(Box<Types>),
    Arr(Box<Types>, Box<Types>),
    Pair(Box<Types>, Box<Types>),
}

impl fmt::Display for Types {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Types::TypeVar(n) => write!(f, "ξ{}",n),
            Types::Boolean => write!(f, "𝔹"),
            Types::Nat =>  write!(f, "ℕ"),
            Types::List(t) => write!(f, "𝕃({})", t),
            Types::Arr(t, s) => write!(f, "({} ⇒ {})",t,s),
            Types::Pair(t, s) => write!(f, "{} × {}",t,s),
        }
    }
}

impl Types {
    pub fn subst(&self, sigma: &TypeSubstitution) -> Types {
        match self {
            Types::TypeVar(xi) => {
                match sigma.get(&xi) {
                    Some(ty) => ty.clone(),
                    None => self.clone(),
                }
            },
            Types::Boolean => Types::Boolean,
            Types::Nat => Types::Nat,
            Types::List(t) => Types::List(Box::new(t.subst(sigma))),
            Types::Arr(t, s) => {
                Types::Arr(Box::new(t.subst(sigma)), Box::new(s.subst(sigma)))
            }
            Types::Pair(t, s) => {
                Types::Pair(Box::new(t.subst(sigma)), Box::new(s.subst(sigma)))
            }
        }
    }
    pub fn free_var(&self) -> HashSet<usize> {
        match self {
            Types::TypeVar(n) => {
                HashSet::from_iter(vec![n.clone()])
            }
            Types::Boolean => HashSet::new(),
            Types::Nat => HashSet::new(),
            Types::List(ty) => ty.free_var(),
            Types::Arr(ty1, ty2) => {
                let mut a = ty1.free_var();
                a.extend(ty2.free_var());   
                a
            }
            Types::Pair(ty1, ty2) => {
                let mut a = ty1.free_var();
                a.extend(ty2.free_var());
                a
            }
        }
    }
}

#[derive(Debug, Clone)]
pub enum TypeError {
    Mismatch {expected: Types, found: Types },
    ExpectedFunction(Types),
    ExpectedBoolean(Types),
    ExpectedList(Types),
}