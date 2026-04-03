use std::collections::{HashMap, HashSet};
use std::fmt;
use crate::formulas::Formula;
use crate::terms::{ObjVar, Term, TermSubstitution};
use crate::proofs::axioms::{Axiom};
use crate::proofs::assumptions::{ProofAssumption};
use crate::types::TypeError;

#[derive(Debug, Clone, PartialEq)]
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
            ProofKind::AllIntro(var,m) => {
                m.free_assumptions()
            }
            ProofKind::AllElim(m, t) => {
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
