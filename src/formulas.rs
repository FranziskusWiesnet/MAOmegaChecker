use std::collections::HashMap;
use std::fmt;
use crate::terms::{Const, ObjVar, Term, check_term_substitution};
use crate::types::{TypeError, Types};

pub type TypeSubstitution = HashMap<usize, Types>;
pub type TermSubstitution = HashMap<ObjVar, Term>;

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

    pub fn falsum() -> Self {Formula::Atom(Term::constant(Const::FF))}
    pub fn verum() -> Self {Formula::Atom(Term::constant(Const::TT))}

    pub fn F(&self) -> Self {
        let F = Formula::Atom(Term::constant(Const::FF));
        match self {
            Formula::Bottom => F,
            Formula::Atom(_) => self.clone(),
            Formula::Imp(a, b) =>  Formula::Imp(Box::new(a.F()), Box::new(b.F())),
            Formula::Forall(x, a) => Formula::Forall( x.clone(), Box::new(a.F()) ),

        }
    }
    pub fn subst_type(&self, sigma: &TypeSubstitution) -> Formula {
        match self {
            Formula::Atom(t) => Formula::Atom(t.subst_type(sigma)),

            Formula::Imp(a, b) => Formula::Imp(
                Box::new(a.subst_type(sigma)),
                Box::new(b.subst_type(sigma)),
            ),

            Formula::Forall(v, f) => Formula::Forall(
                v.subst_type(sigma),
                Box::new(f.subst_type(sigma)),
            ),

            Formula::Bottom => Formula::Bottom,
        }
    }
    pub fn subst(&self, sigma: &TermSubstitution) -> Result<Formula, TypeError> {
        check_term_substitution(sigma)?;
        Ok(self.subst_unchecked(sigma))
    }
    fn subst_unchecked(&self, sigma: &TermSubstitution) -> Formula {
        match self {
            Formula::Atom(t) => Formula::Atom(t.subst(sigma).unwrap()),

            Formula::Imp(a, b) => Formula::Imp(
                Box::new(a.subst_unchecked(sigma)),
                Box::new(b.subst_unchecked(sigma)),
            ),

            Formula::Forall(bound, body) => {
                let mut restricted = sigma.clone();
                restricted.remove(bound);

                Formula::Forall(
                    bound.clone(),
                    Box::new(body.subst_unchecked(&restricted)),
                )
            }

            Formula::Bottom => Formula::Bottom,
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

