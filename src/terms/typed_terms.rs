use std::fmt;
use std::fmt::Debug;
use std::collections::{HashMap, HashSet};
use std::hash::Hash;
use crate::terms::{TermKind, ObjVar, Const, TermKindSubstitution};
use crate::types::{Types, TypeError, TypeSubstitution};

pub type TermSubstitution = HashMap<ObjVar, Term>;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Term {
    ty: Types,
    kind: TermKind,
}
impl Term {
    pub fn var(v: &ObjVar) -> Self {
        Self {
            ty: v.ty().clone(),
            kind: TermKind::Var(v.clone()),
        }
    }
    pub fn constant(c: Const) -> Self {
        Self {
            ty: c.ty(),
            kind: TermKind::Const(c),
        }
    }
    pub fn tt() -> Self {
        Self{
            ty: Types::Boolean,
            kind: TermKind::Const(Const::TT)
        }
    }
    pub fn ff() -> Self {
        Self{
            ty: Types::Boolean,
            kind: TermKind::Const(Const::FF)
        }
    }
    pub fn abs(var: &ObjVar, t: &Term) -> Self {
        Self{
            ty: Types::arr(var.ty().clone(), t.ty().clone()),
            kind: TermKind::abs(var.clone(), t.kind.clone()),
        }
    }
    pub fn app(fun: &Term, arg: &Term) -> Result<Self, TypeError> {
        match &fun.ty {
            Types::Arr(dom, codom) => {
                if dom.as_ref() != arg.ty() {
                    Err(TypeError::Mismatch {
                        expected: dom.as_ref().clone(),
                        found: arg.ty().clone(),
                    })
                }
                else {
                    Ok(Self{
                        ty: codom.as_ref().clone(),
                        kind: TermKind::app(fun.kind.clone(), arg.kind.clone()),
                    })
                }
            }
            other => Err(TypeError::ExpectedFunction(other.clone())),
        }
    }
    pub fn from_kind(kind: &TermKind) -> Result<Self, TypeError> {
        match kind {
            TermKind::Var(v) => Ok(Self {
                ty: v.ty().clone(),
                kind: kind.clone(),
            }),
            TermKind::Const(c) => Ok(Self {
                ty: c.ty().clone(),
                kind: kind.clone(),
            }),
            TermKind::Abs(x, a) => {
                let body_term = Term::from_kind(a)?;
                Ok(Self{
                    ty: Types::arr(x.ty().clone(),body_term.ty.clone()),
                    kind: kind.clone(),
                })
            }
            TermKind::App(a, b) => {
                let fun_term = Term::from_kind(a)?;
                let arg_term = Term::from_kind(b)?;
                Term::app(&fun_term, &arg_term)
                }
            }
        }
    pub fn ty(&self) -> &Types {
        &self.ty
    }
    pub fn kind(&self) -> &TermKind {&self.kind}
    pub fn free_var(&self) -> HashSet<ObjVar> {
        self.kind.free_vars()
    }
    pub fn used_var_names(&self) -> HashSet<ObjVar> {self.kind.used_var_names()}
}


pub fn check_term_substitution(sigma: &TermSubstitution) -> Result<(), TypeError> {
    for (v, t) in sigma {
        if v.ty() != t.ty() {
            return Err(TypeError::Mismatch {
                expected: v.ty().clone(),
                found: t.ty().clone(),
            });
        }
    }
    Ok(())
}
impl Term {
    pub fn free_type_vars(&self) -> HashSet<usize> {
        self.kind.free_type_vars()
    }
    pub fn free_vars(&self) -> HashSet<ObjVar> {
        self.kind.free_vars()
    }
    pub fn subst_type(&self, sigma: &TypeSubstitution) -> Self {
        Self {
            ty: self.ty.subst(sigma),
            kind: self.kind.subst_type(sigma),
        }
    }
    pub fn subst_type_with_map(&self, 
                               sigma: &TypeSubstitution, 
                               var_subst: &HashMap<ObjVar,ObjVar>) -> Self {
        Self {
            ty: self.ty.subst(sigma),
            kind: self.kind.subst_type_with_map(sigma,var_subst),
        }
    }

    pub fn subst(&self, sigma: &TermSubstitution) -> Result<Self, TypeError> {
        check_term_substitution(sigma)?;

        let sigma_on_kinds: TermKindSubstitution = sigma
            .iter()
            .map(|(var, term)| (var.clone(), term.kind.clone()))
            .collect();

        Ok(Self {
            ty: self.ty.clone(),
            kind: self.kind.subst(&sigma_on_kinds),
        })
    }
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.kind)
    }
}
pub fn term_free_vars(set: HashSet<Term>) -> HashSet<ObjVar> {
    let mut h : HashSet<ObjVar> = HashSet::new();
    for t in set {
        h.extend(t.free_var());
    }
    h
}
pub fn free_vars_of_term_substitution(sigma: &TermSubstitution) -> HashSet<ObjVar> {
    let h: HashSet<Term> = sigma.clone().into_values().collect();
    term_free_vars(h)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::terms::{Const, ObjVar, TermKind};
    use crate::types::{TypeError, Types};

    #[test]
    fn from_kind_var_gets_variable_type() {
        let x = ObjVar::with_name(0, Types::Nat, "x");
        let kind = TermKind::Var(x.clone());

        let term = Term::from_kind(&kind).unwrap();

        assert_eq!(term.ty(), &Types::Nat);
        assert_eq!(term.to_string(), "x");
    }
    #[test]
    fn from_kind_abs_gets_function_type() {
        let x = ObjVar::with_name(0, Types::Nat, "x");
        let kind = TermKind::abs(x.clone(), TermKind::Var(x.clone()));

        let term = Term::from_kind(&kind).unwrap();

        assert_eq!(term.ty(), &Types::arr(Types::Nat, Types::Nat));
        assert_eq!(term.to_string(), "(λx. x)");
    }
    #[test]
    fn from_kind_app_of_succ_to_zero_is_nat() {
        let one = TermKind::app(
            TermKind::Const(Const::Succ),
            TermKind::Const(Const::Zero),
        );

        let term = Term::from_kind(&one).unwrap();

        assert_eq!(term.ty(), &Types::Nat);
        assert_eq!(term.to_string(), "(S 0)");
    }
    #[test]
    fn from_kind_app_with_wrong_argument_type_returns_mismatch() {
        let kind = TermKind::app(
            TermKind::Const(Const::Succ),
            TermKind::Const(Const::TT),
        );

        let err = Term::from_kind(&kind).unwrap_err();

        assert_eq!(
            err,
            TypeError::Mismatch {
                expected: Types::Nat,
                found: Types::Boolean,
            }
        );
    }
    #[test]
    fn from_kind_app_of_non_function_returns_expected_function_error() {
        let kind = TermKind::app(
            TermKind::Const(Const::Zero),
            TermKind::Const(Const::Zero),
        );

        let err = Term::from_kind(&kind).unwrap_err();

        assert_eq!(err, TypeError::ExpectedFunction(Types::Nat));
    }
    #[test]
    fn subst_type_in_term() {
        let x = ObjVar::with_name(0, Types::TypeVar(0), "x");
        let term = Term::from_kind(&TermKind::abs(
            x.clone(),
            TermKind::Var(x),
        )).unwrap();

        let sigma: TypeSubstitution = HashMap::from([
            (0, Types::Nat),
        ]);

        let result = term.subst_type(&sigma);

        assert_eq!(result.ty(), &Types::arr(Types::Nat, Types::Nat));
        assert_eq!(result.to_string(), "(λx. x)");
    }
    #[test]
    fn subst_replaces_variable_by_typed_term() {
        let x = ObjVar::with_name(0, Types::Nat, "x");
        let y = ObjVar::with_name(1, Types::Nat, "y");

        let term = Term::from_kind(&TermKind::app(
            TermKind::Const(Const::Succ),
            TermKind::Var(x.clone()))).unwrap();

        let sigma: TermSubstitution = HashMap::from([(x.clone(), Term::var(&y))]);

        let result = term.subst(&sigma).unwrap();

        assert_eq!(result.ty(), &Types::Nat);
        assert_eq!(result.to_string(), "(S y)");
    }
    #[test]
    fn subst_type_followed_by_subst() {
        let x = ObjVar::with_name(0, Types::TypeVar(0), "x");

        let kind = TermKind::app(
            TermKind::Const(Const::Cons(Types::TypeVar(0))),
            TermKind::Var(x.clone()),
        );

        let type_sigma: TypeSubstitution = HashMap::from([
            (0, Types::Nat),
        ]);

        let term_sigma: TermSubstitution = HashMap::from([
            (ObjVar::with_name(0, Types::Nat, "x"), Term::constant(Const::Zero)),
        ]);

        let term = Term::from_kind(&kind).unwrap();
        let result = term.subst_type(&type_sigma).subst(&term_sigma).unwrap();
        let expected = Types::arr(Types::list(Types::Nat), Types::list(Types::Nat));
        assert_eq!(result.ty(), &expected);
        assert_eq!(result.to_string(), "(cons_ℕ 0)");
    }
    #[test]
    fn equal_terms_respect_alpha_equivalence_of_abstractions() {
        let alpha = Types::TypeVar(0);

        let x = ObjVar::new(0, alpha.clone());
        let y = ObjVar::new(1, alpha.clone());

        let tx = Term::abs(&x, &Term::var(&x));
        let ty = Term::abs(&y, &Term::var(&y));

        assert_eq!(tx.ty(), &Types::arr(alpha.clone(), alpha.clone()));
        assert_eq!(ty.ty(), &Types::arr(alpha.clone(), alpha.clone()));

        assert_eq!(tx, ty);
    }
}