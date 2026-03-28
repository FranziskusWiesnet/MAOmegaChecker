use std::fmt;
use crate::terms::{Const, ObjVar, Term};
use crate::types::{TypeError, Types};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Formula {
    Atom(Term),
    Imp(Box<Formula>, Box<Formula>),
    Forall(ObjVar, Box<Formula>),
    Bottom,
}

impl Formula {
    pub fn atom(t: &Term) -> Result<Self, TypeError> {
        if *t.ty() != Types::Boolean {
            return Err(TypeError::ExpectedBoolean(t.ty().clone()));
        }

        Ok(Formula::Atom(t.clone()))
    }
    pub fn imp(a: &Formula, b: &Formula) -> Self {
        Formula::Imp(Box::new(a.clone()), Box::new(b.clone()))
    }
    pub fn forall(x: &ObjVar, a: &Formula) -> Self {
        Formula::Forall(x.clone(), Box::new(a.clone()))
    }
    pub fn bottom() -> Self {
        Formula::Bottom
    }

    pub fn F(&self) -> Self {
        let F = Formula::Atom(Term::constant(Const::FF));
        match self {
            Formula::Bottom => F,
            Formula::Atom(_) => self.clone(),
            Formula::Imp(a, b) =>  Formula::Imp(Box::new(a.F()), Box::new(b.F())),
            Formula::Forall(x, a) => Formula::Forall( x.clone(), Box::new(a.F()) ),

        }
    }
}

impl fmt::Display for Formula {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Formula::Bottom => write!(f, "⊥"),
            Formula::Atom(t) => {if *t == Term::constant(Const::FF) {write!(f, "F")} else {write!(f, "{}",t)}},
            Formula::Imp(a, b) => write!(f, "({} -> {})", a, b),
            Formula::Forall(x, a) => write!(f, "(∀ x{}. {})", x, a),
        }
    }
}

pub fn isQFree(formula: &Formula) -> bool {
    match formula {
        Formula::Bottom => true,
        Formula::Atom(_) => true,
        Formula::Forall(_, _) => false,
        Formula::Imp(g, h) => isQFree(&g) && isQFree(&h),
    }
}