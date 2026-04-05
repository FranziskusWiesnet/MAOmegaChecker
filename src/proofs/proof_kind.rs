use std::collections::{HashMap, HashSet};
use std::fmt;
use crate::formulas::Formula;
use crate::terms::{ObjVar, Term, TermSubstitution};
use crate::proofs::axioms::{Axiom};
use crate::proofs::assumptions::{ProofAssumption};
use crate::types::{TypeError, TypeSubstitution};

pub type ProofKindSubstitution = HashMap<ProofAssumption, ProofKind>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ProofKind {
    Assumption(ProofAssumption),
    Ax(Axiom),
    ImpIntro(ProofAssumption,Box<ProofKind>),
    ImpElim(Box<ProofKind>,Box<ProofKind>),
    AllIntro(ObjVar,Box<ProofKind>),
    AllElim(Box<ProofKind>,Term),
}

impl fmt::Display for ProofKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ProofKind::Assumption(p) =>
                write!(f, "{}", p),
            ProofKind::Ax(a) =>
                write!(f, "{}", a),
            ProofKind::ImpIntro(assumption,body) =>
                write!(f, "(λ {}. {})", assumption, body),
            ProofKind::ImpElim(m,n) =>
                write!(f, "({} {})", m, n),
            ProofKind::AllIntro(var,body) =>
                write!(f, "(λ {}. {})", var, body),
            ProofKind::AllElim(a,t) =>
                write!(f, "({} {})", a, t),
        }
    }
}
#[derive(Debug, Clone, PartialEq)]
pub enum ProofError {
    Type(TypeError),
    Mismatch(Formula,Formula),
    ExpectedImplication(Formula),
    ExpectedForall(Formula),
    AllIntro(ObjVar, ProofKind),
}
impl std::error::Error for ProofError {}
impl fmt::Display for ProofError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ProofError::Type(e) => {write!(f,"{}",e)}
            ProofError::Mismatch(expected, found) =>
                write!(f, "implication mismatch: expected {}, found {}", expected, found),
            ProofError::ExpectedImplication(found) =>
                write!(f, "implication expected, found {}", found),
            ProofError::ExpectedForall(found) =>
                write!(f, "universal formula expected, found {}", found),
            ProofError::AllIntro(var, proof) =>
                write!(f, "{} free in the assumptions of {}", var, proof),
        }
    }
}
impl ProofKind {
    pub fn formula(&self) -> Result<Formula,ProofError> {
        match self {
            ProofKind::Assumption(p) => Ok(p.form()),
            ProofKind::Ax(a) => {
                match a.form() {
                    Ok(a) => Ok(a),
                    Err(e) => Err(ProofError::Type(e)),
                }
            }
            ProofKind::ImpIntro(assumption,body) => {
                Ok(Formula::imp(assumption.form(), body.formula()?))
            }
            ProofKind::ImpElim(left,right) => {
                let prem_to_conclusion = left.formula()?;
                match prem_to_conclusion {
                    Formula::Imp(prem,conclusion) => {
                        let right_formula = right.formula()?;
                        if right_formula == *prem {
                            Ok(conclusion.as_ref().clone())
                        } else {
                            Err(ProofError::Mismatch(right_formula, prem.as_ref().clone()))
                        }
                    },
                    _ => Err(ProofError::ExpectedImplication(prem_to_conclusion)),
                }
            }
            ProofKind::AllIntro(var,body) => {
                Ok(Formula::forall(var.clone(), body.formula()?))
            }
            ProofKind::AllElim(forall_proof,t) => {
                let forall_formula = forall_proof.formula()?;
                match forall_formula {
                    Formula::Forall(var,form) => {
                        let sigma: TermSubstitution =HashMap::from([(var.clone(), t.clone())]);
                        match form.subst(&sigma) {
                            Ok(subs) => Ok(subs),
                            Err(e) => Err(ProofError::Type(e)),
                        }
                    }
                     _ => Err(ProofError::ExpectedForall(forall_formula)),
                }
            }
        }
    }
    pub fn free_assumptions(&self) -> HashSet<ProofAssumption> {
        match self {
            ProofKind::Assumption(p) => {
                HashSet::from([p.clone()])
            }
            ProofKind::Ax(_) => {HashSet::new()}
            ProofKind::ImpIntro(u, m) => {
                let mut set = m.free_assumptions();
                set.remove(u);
                set
            }
            ProofKind::ImpElim(m, n) => {
                let mut set = m.free_assumptions();
                set.extend(n.free_assumptions());
                set
            }
            ProofKind::AllIntro(_var,m) => {
                m.free_assumptions()
            }
            ProofKind::AllElim(m, _) => {
                m.free_assumptions()
            }
        }
    }
    pub fn free_vars_in_assumptions(&self) -> HashSet<ObjVar> {
        let free_assumptions = self.free_assumptions();
        let mut set = HashSet::new();
        for u in free_assumptions {
            set.extend(u.form().free_vars().clone())
        }
        set
    }
    pub fn free_type_vars(&self) -> HashSet<usize> {
        match self {
            ProofKind::Assumption(p) => {p.form().free_type_vars()}
            ProofKind::Ax(a) => {a.free_type_vars()}
            ProofKind::ImpIntro(u, m) => {
                let mut set = m.free_type_vars();
                set.extend(u.form().free_type_vars().clone());
                set
            }
            ProofKind::ImpElim(m, n) => {
                let mut set = m.free_type_vars();
                set.extend(n.free_type_vars());
                set
            }
            ProofKind::AllIntro(var,m) => {
                let mut set = m.free_type_vars();
                set.extend(var.free_type_vars());
                set
            }
            ProofKind::AllElim(forall_proof,t) => {
                let mut set = forall_proof.free_type_vars();
                set.extend(t.free_type_vars());
                set
            }
        }
    }
    pub fn subst_type(&self, sigma: &TypeSubstitution) -> Self  {
        match self {
            ProofKind::Assumption(p) => {
                ProofKind::Assumption(p.subst_type(sigma))
            }
            ProofKind::Ax(a) => {ProofKind::Ax(a.subst_type(sigma))}
            ProofKind::ImpIntro(u, m) => {
                ProofKind::ImpIntro(u.subst_type(sigma),Box::new(m.subst_type(sigma)))
            }
            ProofKind::ImpElim(m, n) => {
                ProofKind::ImpElim(Box::new(m.subst_type(sigma)),Box::new(n.subst_type(sigma)))
            }
            ProofKind::AllIntro(var,m) => {
                ProofKind::AllIntro(var.subst_type(sigma),Box::new(m.subst_type(sigma)))
            }
            ProofKind::AllElim(forall_proof,t) => {
                ProofKind::AllElim(Box::new(forall_proof.subst_type(sigma)), t.subst_type(sigma))
            }
        }
    }
    pub fn free_vars(&self) -> HashSet<ObjVar> {
        match self {
            ProofKind::Assumption(p) => p.form().free_vars(),
            ProofKind::Ax(a) => {a.free_vars()}
            ProofKind::ImpIntro(u, m) => {
                let mut set = m.free_vars();
                set.extend(u.form().free_vars());
                set
            }
            ProofKind::ImpElim(m, n) => {
                let mut set = m.free_vars();
                set.extend(n.free_vars());
                set
            }
            ProofKind::AllIntro(var,m) => {
                let mut set = m.free_vars();
                set.remove(&var);
                set
            }
            ProofKind::AllElim(forall_proof,t) => {
                let mut set = forall_proof.free_vars();
                set.extend(t.free_vars());
                set
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::formulas::Formula;
    use crate::proofs::assumptions::ProofAssumption;
    use crate::terms::{Const, ObjVar, Term};
    use crate::types::Types;
    #[test]
    fn formula_of_assumption_is_its_formula() {
        let a = ProofAssumption::new(0, Formula::verum());
        let p = ProofKind::Assumption(a);
        assert_eq!(p.formula().unwrap(), Formula::verum());
    }
    #[test]
    fn formula_of_imp_intro_is_implication() {
        let a_form = Formula::verum();
        let b_form = Formula::falsum();

        let a = ProofAssumption::new(0, a_form.clone());
        let body = ProofKind::Assumption(ProofAssumption::new(1, b_form.clone()));
        let proof = ProofKind::ImpIntro(a, Box::new(body));
        assert_eq!(proof.formula().unwrap(), Formula::imp(a_form, b_form));
    }
    #[test]
    fn formula_of_imp_elim_returns_conclusion() {
        let a = Formula::verum();
        let b = Formula::falsum();

        let left = ProofKind::Assumption(
            ProofAssumption::new(0, Formula::imp(a.clone(), b.clone()))
        );
        let right = ProofKind::Assumption(
            ProofAssumption::new(1, a.clone())
        );

        let proof = ProofKind::ImpElim(Box::new(left), Box::new(right));
        println!("{}:{}",proof, proof.formula().unwrap());
        assert_eq!(proof.formula().unwrap(), b);
    }
    #[test]
    fn formula_of_imp_elim_reports_mismatch() {
        let a = Formula::verum();
        let b = Formula::falsum();

        let left = ProofKind::Assumption(
            ProofAssumption::new(0, Formula::imp(a.clone(), b))
        );
        let right = ProofKind::Assumption(
            ProofAssumption::new(1, Formula::Bottom)
        );

        let proof = ProofKind::ImpElim(Box::new(left), Box::new(right));

        match proof.formula() {
            Err(ProofError::Mismatch(found, expected)) => {
                assert_eq!(found, Formula::Bottom);
                assert_eq!(expected, a);
            }
            other => panic!("unexpected result: {:?}", other),
        }
    }
    #[test]
    fn formula_of_all_elim_substitutes_term() {
        let x = ObjVar::with_name(0, Types::Nat, "x");
        let p = ObjVar::with_name(1, Types::arr(Types::Nat, Types::Boolean), "p");

        let px = Formula::atom(
            &Term::app(&Term::var(&p), &Term::var(&x)).unwrap()
        ).unwrap();

        let forall_px = Formula::forall(x.clone(), px);

        let proof = ProofKind::AllElim(
            Box::new(ProofKind::Assumption(
                ProofAssumption::new(0, forall_px)
            )),
            Term::constant(Const::Zero),
        );

        let expected = Formula::atom(
            &Term::app(&Term::var(&p), &Term::constant(Const::Zero)).unwrap()
        ).unwrap();
        println!("{}", proof.formula().unwrap());
        assert_eq!(proof.formula().unwrap(), expected);
    }
    #[test]
    fn free_assumptions_removes_discharged_assumption_in_imp_intro() {
        let a = Formula::verum();
        let u0 = ProofAssumption::new(0, a.clone());
        let u1 = ProofAssumption::new(0, Formula::falsum());

        let body = ProofKind::ImpElim(
            Box::new(ProofKind::Assumption(u0.clone())),
            Box::new(ProofKind::Assumption(u1.clone())),
        );

        let proof = ProofKind::ImpIntro(u0.clone(), Box::new(body));

        let expected = HashSet::from([u1]);

        assert_eq!(proof.free_assumptions(), expected);
    }
    #[test]
    fn free_assumptions_unions_both_branches_of_imp_elim() {
        let u0 = ProofAssumption::new(0, Formula::verum());
        let u1 = ProofAssumption::new(1, Formula::falsum());

        let proof = ProofKind::ImpElim(
            Box::new(ProofKind::Assumption(u0.clone())),
            Box::new(ProofKind::Assumption(u1.clone())),
        );

        let expected = HashSet::from([u0, u1]);

        assert_eq!(proof.free_assumptions(), expected);
    }
    #[test]
    fn free_vars_in_assumptions_collects_only_from_free_assumptions() {
        let x = ObjVar::with_name(0, Types::Nat, "x");
        let y = ObjVar::with_name(1, Types::Nat, "y");
        let p = ObjVar::with_name(2, Types::arr(Types::Nat, Types::Boolean), "p");

        let px = Formula::atom(&Term::app(&Term::var(&p), &Term::var(&x)).unwrap()).unwrap();
        let py = Formula::atom(&Term::app(&Term::var(&p), &Term::var(&y)).unwrap()).unwrap();

        let u0 = ProofAssumption::new(0, px);
        let u1 = ProofAssumption::new(1, py);

        let body = ProofKind::ImpElim(
            Box::new(ProofKind::Assumption(u0.clone())),
            Box::new(ProofKind::Assumption(u1.clone())),
        );

        let proof = ProofKind::ImpIntro(u0, Box::new(body));

        let expected = HashSet::from([p, y]);

        assert_eq!(proof.free_vars_in_assumptions(), expected);
    }
}
