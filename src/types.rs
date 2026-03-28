use std::fmt;

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

#[derive(Debug, Clone)]
pub enum TypeError {
    Mismatch {expected: Types, found: Types },
    ExpectedFunction(Types),
    ExpectedBoolean(Types),
}