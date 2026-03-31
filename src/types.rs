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
            Types::Pair(t, s) => write!(f, "({} × {})",t,s),
        }
    }
}
impl Types {
    pub fn arr(from: Types, to: Types) -> Types {
        Types::Arr(Box::new(from), Box::new(to))
    }
    pub fn pair(left: Types, right: Types) -> Types {
        Types::Pair(Box::new(left), Box::new(right))
    }
    pub fn list(tau: Types) -> Types {
        Types::List(Box::new(tau))
    }
    pub fn free_vars(&self) -> HashSet<usize> {
        match self {
            Types::TypeVar(n) =>HashSet::from([*n]),
            Types::Boolean => HashSet::new(),
            Types::Nat => HashSet::new(),
            Types::List(ty) => ty.free_vars(),
            Types::Arr(ty1, ty2) => {
                let mut a = ty1.free_vars();
                a.extend(ty2.free_vars());
                a
            }
            Types::Pair(ty1, ty2) => {
                let mut a = ty1.free_vars();
                a.extend(ty2.free_vars());
                a
            }
        }
    }
    pub fn subst(&self, sigma: &TypeSubstitution) -> Types {
        match self {
            Types::TypeVar(xi) => {
                match sigma.get(xi) {
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
}
pub fn new_type_var(set: &HashSet<usize>) -> usize {
    let mut n: usize = 0;
    while set.contains(&n) {
        n += 1;
    }
    n
}
#[derive(Debug, Clone)]
pub enum TypeError {
    Mismatch {expected: Types, found: Types},
    ExpectedFunction(Types),
    ExpectedBoolean(Types),
    ExpectedList(Types),
}
impl std::error::Error for TypeError {}
impl fmt::Display for TypeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TypeError::Mismatch { expected, found } => {
                write!(f, "type mismatch: expected {}, found {}", expected, found)
            }
            TypeError::ExpectedFunction(ty) => {
                write!(f, "expected function type, found {}", ty)
            }
            TypeError::ExpectedBoolean(ty) => {
                write!(f, "expected boolean type, found {}", ty)
            }
            TypeError::ExpectedList(ty) => {
                write!(f, "expected list type, found {}", ty)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashSet;

    #[test]
    fn new_type_var_empty_set() {
        let h = HashSet::new();
        assert_eq!(new_type_var(&h), 0);
    }
    #[test]
    fn new_type_var_skips_existing_prefix() {
        let h = HashSet::from([0, 1, 2, 3]);
        assert_eq!(new_type_var(&h), 4);
    }
    #[test]
    fn new_type_var_unsorted_set() {
        let h = HashSet::from([5, 2, 0, 1]);
        assert_eq!(new_type_var(&h), 3);
    }
    #[test]
    fn new_type_var_ignores_large_elements() {
        let h = HashSet::from([100, 200, 300]);
        assert_eq!(new_type_var(&h), 0);
    }
    #[test]
    fn subst_replaces_type_variable() {
        let ty = Types::TypeVar(0);
        let sigma = HashMap::from([
            (0, Types::Nat),
        ]);

        assert_eq!(ty.subst(&sigma), Types::Nat);
    }
    #[test]
    fn subst_leaves_unmapped_variable_unchanged() {
        let ty = Types::TypeVar(1);
        let sigma = HashMap::from([
            (0, Types::Nat),
        ]);

        assert_eq!(ty.subst(&sigma), Types::TypeVar(1));
    }
    #[test]
    fn subst_recurses_through_compound_type() {
        let ty = Types::arr(Types::TypeVar(0),Types::list(Types::TypeVar(1)));
        let sigma = HashMap::from([
            (0, Types::Boolean),
            (1, Types::Nat),
        ]);

        let expected = Types::Arr(
            Box::new(Types::Boolean),
            Box::new(Types::List(Box::new(Types::Nat))),
        );

        assert_eq!(ty.subst(&sigma), expected);
    }
    #[test]
    fn subst_replaces_multiple_variables_in_nested_type() {
        let ty =
            Types::pair(Types::TypeVar(0),Types::arr(Types::TypeVar(1),Types::TypeVar(0)));
        let sigma = HashMap::from([
            (0, Types::Nat),
            (1, Types::Boolean),
        ]);

        let expected = Types::Pair(
            Box::new(Types::Nat),
            Box::new(Types::Arr(
                Box::new(Types::Boolean),
                Box::new(Types::Nat),
            )),
        );

        assert_eq!(ty.subst(&sigma), expected);
    }
}