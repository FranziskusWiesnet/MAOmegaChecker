use std::collections::{HashMap, HashSet};
use std::fmt;
use crate::formulas::Formula;
use crate::proofs::axioms::Axiom;
use crate::proofs::proof_kind::{ProofError, ProofKind};
use crate::proofs::ProofAssumption;
use crate::terms::{ObjVar, Term, TermSubstitution};
#[derive(Debug, Clone, PartialEq)]
pub struct Proof {
    formula: Formula,
    kind: ProofKind,
}
impl fmt::Display for Proof {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.kind)
    }
}
impl Proof {
    pub fn from_assumption(assumption: ProofAssumption) -> Self {
        Self {
            formula: assumption.clone().form(),
            kind: ProofKind::Assumption(assumption),
        }
    }
    pub fn from_axiom(axiom: Axiom) -> Result<Self,ProofError> {
        match axiom.form() {
            Ok(form) =>
            Ok(Self {
                   formula: form.clone(),
                   kind: ProofKind::Ax(axiom.clone()),
               }),
            Err(e) => {Err(ProofError::Type(e))}
        }
    }
    pub fn imp_intro(u: ProofAssumption, m: Proof) -> Self{
        Self {
            formula: Formula::imp(u.form(),m.formula),
            kind: ProofKind::ImpIntro(u, Box::new(m.kind))
        }
    }
    pub fn imp_elim(left: Proof,right: Proof) -> Result<Self,ProofError> {
        let prem_to_conclusion = left.formula;
        match prem_to_conclusion {
            Formula::Imp(prem, conclusion) => {
                if right.formula == *prem {
                    Ok(Self {
                        formula: conclusion.as_ref().clone(),
                        kind: ProofKind::ImpElim(Box::new(left.kind), Box::new(right.kind))
                    })
                } else {
                    Err(ProofError::Mismatch(right.formula, prem.as_ref().clone()))
                }
            }
            _ => Err(ProofError::ExpectedImplication(prem_to_conclusion)),
        }
    }
        pub fn all_intro(var: ObjVar, proof: Proof) -> Result<Self,ProofError> {
            let free_assumption_vars = proof.kind.free_vars_in_assumptions();
            if free_assumption_vars.contains(&var) {
                Err(ProofError::AllIntro(var,proof.kind))
            } else {
                Ok(Self{
                    formula: Formula::forall(var.clone(), proof.formula),
                    kind: ProofKind::AllIntro(var.clone(), Box::new(proof.kind))
                })
            }
        }
        pub fn all_elim(proof: Proof, term: Term) -> Result<Self,ProofError> {
            let forall_formula = proof.formula;
            match forall_formula {
                Formula::Forall(var,form) => {
                    let sigma: TermSubstitution =HashMap::from([(var.clone(), term.clone())]);
                    match form.subst(&sigma) {
                        Ok(formula_subst) => Ok(Self {
                            formula: formula_subst,
                            kind: ProofKind::AllElim(Box::new(proof.kind),term)
                        }),
                        Err(e) => Err(ProofError::Type(e)),
                    }
                }
                _ => Err(ProofError::ExpectedForall(forall_formula)),
            }
        }
    pub fn from_kind(kind: ProofKind) -> Result<Self, ProofError> {
        match kind.clone() {
            ProofKind::Assumption(assumption) =>
                Ok(Self::from_assumption(assumption)),
            ProofKind::Ax(ax) => Self::from_axiom(ax),
            ProofKind::ImpIntro(u, m) =>
                Ok(Self::imp_intro(u,Self::from_kind(m.as_ref().clone())?)),
            ProofKind::ImpElim(n, m) =>
                Self::imp_elim(
                    Self::from_kind(n.as_ref().clone())?,
                    Self::from_kind(m.as_ref().clone())?),
            ProofKind::AllIntro(var, m) =>
                Self::all_intro(var,Self::from_kind(m.as_ref().clone())?),
            ProofKind::AllElim(m, t) =>
                Self::all_elim(Self::from_kind(m.as_ref().clone())?,t)
        }
    }
    pub fn free_assumptions(self) -> HashSet<ProofAssumption> {
        self.kind.free_assumptions()
    }
    pub fn cases(b: ObjVar, formula: Formula, proof_tt: Proof, proof_ff: Proof)
        -> Result<Self, ProofError> {
        let ax = Proof::from_axiom(Axiom::Case(b,formula))?;
        Proof::imp_elim(Proof::imp_elim(ax,proof_tt)?,proof_ff)
    }
    pub fn induction(x: ObjVar, formula: Formula, proof_base: Proof, proof_step: Proof)
        -> Result<Self, ProofError> {
        let ax = Proof::from_axiom(Axiom::Ind(x.clone(),formula))?;
        Proof::imp_elim(Proof::imp_elim(
            Proof::all_elim(ax,Term::var(&x))?,proof_base)?,proof_step)
    }
}
#[cfg(test)]
mod tests {
    use super::*;
    use crate::formulas::Formula;
    use crate::proofs::axioms::Axiom;
    use crate::proofs::ProofAssumption;
    use crate::terms::{Const, ObjVar, Term};
    use crate::types::Types;

    #[test]
    fn from_assumption_builds_proof_with_same_formula() {
        let u = ProofAssumption::new(0, Formula::verum());

        let proof = Proof::from_assumption(u);

        assert_eq!(proof.formula, Formula::verum());
        assert_eq!(proof.to_string(), "u_0");
    }

    #[test]
    fn from_axiom_builds_proof_with_axiom_formula() {
        let proof = Proof::from_axiom(Axiom::AxTrue).unwrap();

        assert_eq!(proof.formula, Formula::verum());
        assert_eq!(proof.to_string(), "AxT");
    }

    #[test]
    fn imp_intro_builds_implication_formula() {
        let u = ProofAssumption::new(0, Formula::verum());
        let body = Proof::from_assumption(ProofAssumption::new(1, Formula::falsum()));

        let proof = Proof::imp_intro(u, body);

        assert_eq!(proof.formula, Formula::imp(Formula::verum(), Formula::falsum()));
        assert_eq!(proof.to_string(), "(λ u_0. u_1)");
    }

    #[test]
    fn imp_elim_returns_conclusion_when_premise_matches() {
        let a = Formula::verum();
        let b = Formula::falsum();

        let left = Proof::from_assumption(
            ProofAssumption::new(0, Formula::imp(a.clone(), b.clone()))
        );
        let right = Proof::from_assumption(
            ProofAssumption::new(1, a)
        );

        let proof = Proof::imp_elim(left, right).unwrap();

        assert_eq!(proof.formula, b);
    }

    #[test]
    fn imp_elim_returns_mismatch_error_when_premise_does_not_match() {
        let left = Proof::from_assumption(
            ProofAssumption::new(0, Formula::imp(Formula::verum(), Formula::falsum()))
        );
        let right = Proof::from_assumption(
            ProofAssumption::new(1, Formula::Bottom)
        );

        let err = Proof::imp_elim(left, right).unwrap_err();

        match err {
            ProofError::Mismatch(found, expected) => {
                assert_eq!(found, Formula::Bottom);
                assert_eq!(expected, Formula::verum());
            }
            other => panic!("unexpected error: {:?}", other),
        }
    }

    #[test]
    fn all_intro_builds_forall_formula_when_variable_not_free_in_assumptions() {
        let x = ObjVar::with_name(0, Types::Nat, "x");
        let proof = Proof::from_assumption(
            ProofAssumption::new(0, Formula::verum())
        );

        let result = Proof::all_intro(x.clone(), proof).unwrap();

        assert_eq!(result.formula, Formula::forall(x, Formula::verum()));
    }

    #[test]
    fn all_elim_substitutes_term_into_formula() {
        let x = ObjVar::with_name(0, Types::Nat, "x");
        let p = ObjVar::with_name(0, Types::arr(Types::Nat, Types::Boolean), "p");

        let px = Formula::atom(
            &Term::app(&Term::var(&p), &Term::var(&x)).unwrap()
        ).unwrap();

        let forall_px = Formula::forall(x.clone(), px);

        let proof = Proof::from_assumption(
            ProofAssumption::new(0, forall_px)
        );

        let result = Proof::all_elim(proof, Term::constant(Const::Zero)).unwrap();

        let expected = Formula::atom(
            &Term::app(&Term::var(&p), &Term::constant(Const::Zero)).unwrap()
        ).unwrap();

        assert_eq!(result.formula, expected);
    }

    #[test]
    fn from_kind_reconstructs_formula_correctly() {
        let u = ProofAssumption::new(0, Formula::verum());
        let kind = ProofKind::ImpIntro(
            u.clone(),
            Box::new(ProofKind::Assumption(u)),
        );

        let proof = Proof::from_kind(kind).unwrap();

        assert_eq!(proof.formula, Formula::imp(Formula::verum(), Formula::verum()));
    }
    #[test]
    fn induction_on_nat_builds_expected_formula() {
        let n = ObjVar::with_name(0, Types::Nat, "n");
        let p = ObjVar::with_name(1, Types::arr(Types::Nat, Types::Boolean), "P");

        let pn = Formula::atom(
            &Term::app(&Term::var(&p), &Term::var(&n)).unwrap()
        ).unwrap();

        let assumption_base = ProofAssumption::new(
            0,
            Formula::atom(
                &Term::app(&Term::var(&p), &Term::constant(Const::Zero)).unwrap()
            ).unwrap(),
        );
        let proof_base = Proof::from_assumption(
            assumption_base.clone(),
        );

        let succ_n = Term::app(&Term::constant(Const::Succ), &Term::var(&n)).unwrap();

        let step_formula = Formula::forall(
            n.clone(),
            Formula::imp(
                pn.clone(),
                Formula::atom(
                    &Term::app(&Term::var(&p), &succ_n).unwrap()
                ).unwrap(),
            ),
        );

        let assumption_step = ProofAssumption::new(1, step_formula.clone());
        let proof_step = Proof::from_assumption(
            assumption_step.clone(),
        );

        let proof_part = Proof::induction(
            n.clone(),
            pn.clone(),
            proof_base,
            proof_step,
        ).unwrap();
        let proof = Proof::all_intro(n.clone(), Proof::imp_intro(assumption_base,Proof::imp_intro(assumption_step, proof_part))).unwrap();


        assert_eq!(proof.formula.to_string(),
                   "(∀ n. ((P 0) -> ((∀ n. ((P n) -> (P (S n)))) -> (P n))))");
    }
    #[test]
    fn induction_on_lists_builds_expected_formula() {
        let xs = ObjVar::with_name(0, Types::list(Types::Nat), "xs");
        let a = ObjVar::with_name(1, Types::Nat, "a");
        let p = ObjVar::with_name(
            2,
            Types::arr(Types::list(Types::Nat), Types::Boolean),
            "P",
        );

        let pxs = Formula::atom(
            &Term::app(&Term::var(&p), &Term::var(&xs)).unwrap()
        ).unwrap();

        let nil_nat = Term::constant(Const::Nil(Types::Nat));
        let p_nil = Formula::atom(
            &Term::app(&Term::var(&p), &nil_nat).unwrap()
        ).unwrap();

        let cons_a_xs = Term::app(
            &Term::app(
                &Term::constant(Const::Cons(Types::Nat)),
                &Term::var(&a),
            ).unwrap(),
            &Term::var(&xs),
        ).unwrap();

        let step_formula = Formula::forall(
            a.clone(),
            Formula::forall(
                xs.clone(),
                Formula::imp(
                    pxs.clone(),
                    Formula::atom(
                        &Term::app(&Term::var(&p), &cons_a_xs).unwrap()
                    ).unwrap(),
                ),
            ),
        );

        let proof_base = Proof::from_assumption(
            ProofAssumption::new(0, p_nil.clone()),
        );
        println!("{}", proof_base.formula);
        let proof_step = Proof::from_assumption(
            ProofAssumption::new(1, step_formula.clone()),
        );
        println!("{}", proof_step.formula);
        let proof = Proof::induction(
            xs.clone(),
            pxs.clone(),
            proof_base,
            proof_step,
        );
        println!("{}", proof.unwrap());

    }
}