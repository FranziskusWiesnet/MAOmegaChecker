use std::collections::{HashMap, HashSet};
use std::fmt;
use crate::formulas::Formula;
use crate::proofs::assumptions::{assumption_map_for_type_subst};
use crate::proofs::axioms::Axiom;
use crate::proofs::proof_kind::{ProofError, ProofKind};
use crate::proofs::ProofAssumption;
use crate::terms::{new_var, ObjVar, Term, TermSubstitution};
use crate::terms::obj_var::substitution_map;
use crate::types::{TypeError, TypeSubstitution, Types};
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
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
    pub fn formula(&self) -> &Formula {
        &self.formula
    }
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
    pub fn free_assumptions(&self) -> HashSet<ProofAssumption> {
        self.kind.free_assumptions()
    }
    pub fn used_assumptions(&self) -> HashSet<ProofAssumption> {
        self.kind.used_assumptions()
    }
    pub fn free_type_vars(&self) -> HashSet<usize> {
        self.kind.free_type_vars()
    }
    pub fn subst_type(&self, sigma: &TypeSubstitution) -> Self {
        let mut used_vars = self.formula.used_var_names();
        used_vars.extend(self.kind.used_var_names());
        let used_var_subst = substitution_map(&used_vars,&sigma);
        let used_assumptions = self.kind.used_assumptions();
        let used_assumption_map =
            assumption_map_for_type_subst(&used_assumptions, sigma, &used_var_subst);
        Self{
            formula: self.formula.subst_type_with_map(sigma,&used_var_subst),
            kind: self.kind.subst_type_with_maps(sigma, &used_var_subst, &used_assumption_map)
        }
    }
    pub fn subst(&self, sigma: &TermSubstitution) -> Result<Self,TypeError> {
        Ok(Self{
            kind: self.kind.subst(sigma)?,
            formula: self.formula.subst(sigma)?,
        })
    }
    pub fn free_vars(&self) -> HashSet<ObjVar> {
        self.kind.free_vars()
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
    pub fn efq (form: &Formula) -> Self {
        match form {
            Formula::Bottom => {Self {
                formula: Formula::imp(Formula::falsum(),Formula::Bottom),
                kind: ProofKind::Ax(Axiom::BotIntro)
            }}
            Formula::Atom(t) => {
                let fv = t.free_vars();
                let b = new_var(&Types::Boolean,fv);

                Self {
                    formula: Formula::imp(Formula::falsum(),Formula::Atom(t.clone())),
                    kind: ProofKind::ImpElim(
                        Box::new(ProofKind::AllElim(Box::new(ProofKind::Ax(Axiom::Case(b.clone(),Formula::Atom(Term::var(&b))))),t.clone())),
                        Box::new(ProofKind::Ax(Axiom::AxTrue))
                    )
                }
            }
            Formula::Imp(premise, conclusion) => {
                let assumption_f = ProofAssumption::new(0,Formula::falsum());
                let assumption_premise = ProofAssumption::new(0,premise.as_ref().clone());
                let proof_conclusion = Proof::efq(conclusion);
                Self {
                    formula: Formula::imp(Formula::falsum(),form.clone()),
                    kind:
                    ProofKind::ImpIntro(
                        assumption_f.clone(),
                        Box::new(ProofKind::ImpIntro(
                            assumption_premise,
                            Box::new(ProofKind::ImpElim(
                                Box::new(proof_conclusion.kind),
                                Box::new(ProofKind::Assumption(assumption_f)))))))
                }
            }
            Formula::Forall(var, body) => {
                let assumption_f = ProofAssumption::new(0,Formula::falsum());
                let proof_body = Proof::efq(body);
                Self {
                    formula: Formula::imp(Formula::falsum(),form.clone()),
                    kind:
                    ProofKind::ImpIntro(
                        assumption_f.clone(),
                        Box::new(ProofKind::AllIntro(
                            var.clone(),
                            Box::new(ProofKind::ImpElim(
                                Box::new(proof_body.kind),
                                Box::new(ProofKind::Assumption(assumption_f)))))))
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::formulas::Formula;
    use crate::proofs::axioms::Axiom;
    use crate::proofs::ProofAssumption;
    use crate::terms::{Const, ObjVar, Term};
    use crate::types::{Types, TypeSubstitution};

    #[test]
    fn from_assumption_builds_proof_with_same_formula() {
        let u = ProofAssumption::with_name(0, Formula::verum(),"u_0");

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
        let u = ProofAssumption::with_name(0, Formula::verum(),"u_0");
        let body = Proof::from_assumption(
            ProofAssumption::with_name(1, Formula::falsum(),"u_1"));

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
        let proof = Proof::all_intro(n.clone(),
                                     Proof::imp_intro(assumption_base,
                                                      Proof::imp_intro(assumption_step,
                                                                       proof_part)))
            .unwrap();


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
            ProofAssumption::with_name(0, p_nil.clone(), "u_0"),
        );

        let proof_step = Proof::from_assumption(
            ProofAssumption::with_name(1, step_formula.clone(), "u_1"),
        );

        let proof = Proof::induction(
            xs.clone(),
            pxs.clone(),
            proof_base,
            proof_step,
        ).unwrap();
        assert_eq!(proof.to_string(),"(((𝓘𝓷𝓭(xs.(P xs)) xs) u_0) u_1)")
    }
    #[test]
    fn proof_in_propositional_logic_with_subst(){
        let alpha = Types::TypeVar(0);
        let beta = Types::TypeVar(1);
        let gamma = Types::TypeVar(2);

        let a = ObjVar::with_name(0,  alpha.clone(),"a");
        let b = ObjVar::with_name(0, beta.clone(),"b");
        let c = ObjVar::with_name(0, gamma.clone(),"c");

        let bool_var = ObjVar::with_name(0, Types::Boolean,"bool");

        let f = ObjVar::with_name(0, Types::arr(alpha.clone(), Types::Boolean),"f");
        let g = ObjVar::with_name(0, Types::arr(beta.clone(), Types::Boolean),"g");
        let h = ObjVar::with_name(0, Types::arr(gamma.clone(), Types::Boolean),"h");

        let fa = Term::app(&Term::var(&f),&Term::var(&a)).unwrap();
        let gb = Term::app(&Term::var(&g),&Term::var(&b)).unwrap();
        let hc = Term::app(&Term::var(&h),&Term::var(&c)).unwrap();

        let fa_form = Formula::atom(&fa).unwrap();
        let gb_form = Formula::atom(&gb).unwrap();
        // let hc_form = Formula::atom(&hc).unwrap();
        let bool_form = Formula::atom(&Term::var(&bool_var)).unwrap();

        let fa_to_gb = Formula::imp(fa_form.clone(), gb_form.clone());
        //let fa_to_gb_to_hc =
        //    Formula::imp(fa_form.clone(), Formula::imp(gb_form.clone(), hc_form.clone()));
        let fa_to_gb_to_bool =
            Formula::imp(fa_form.clone(), Formula::imp(gb_form.clone(), bool_form.clone()));

        let u0 = ProofAssumption::with_name(0, fa_to_gb_to_bool,"u");
        let u1 = ProofAssumption::with_name(1, fa_to_gb, "v");
        let u2 = ProofAssumption::with_name(2, fa_form, "w");

        let proof_gb =
            Proof::imp_elim(Proof::from_assumption(u1.clone()),Proof::from_assumption(u2.clone())).unwrap();
        let proof_gb_to_hc =
            Proof::imp_elim(Proof::from_assumption(u0.clone()),Proof::from_assumption(u2.clone())).unwrap();
        let proof_hc = Proof::imp_elim(proof_gb_to_hc,proof_gb).unwrap();

        let proof =   Proof::imp_intro(u0.clone(),Proof::imp_intro(u1.clone(),Proof::imp_intro(u2.clone(),proof_hc)));
        assert_eq!(proof.free_assumptions(), HashSet::new());
        assert_eq!(proof.used_assumptions(), HashSet::from_iter(vec![u0, u1, u2]));
        assert_eq!(proof.to_string(), "(λ u. (λ v. (λ w. ((u w) (v w)))))");

        let sigma: TypeSubstitution = HashMap::from([
            (0, Types::Nat),
            (1, Types::Nat),]);
        let proof_subst_types = proof.subst_type(&sigma);
        println!("{}",proof_subst_types);

        let rho: TermSubstitution = HashMap::from([
            (bool_var.clone(), hc.clone()),
        ]);
        let proof_subst = proof.subst(&rho).unwrap();
        println!("{}",proof);
        print!("{}",proof_subst);

    }
    #[test]
    fn proof_in_predicate_logic_with_subst(){
        let alpha = Types::TypeVar(0);

        let x = ObjVar::with_name(0,  alpha.clone(),"x");

        let p = ObjVar::with_name(0, Types::arr(alpha.clone(), Types::Boolean),"P");
        let q = ObjVar::with_name(1, Types::arr(alpha.clone(), Types::Boolean),"Q");

        let px = Term::app(&Term::var(&p),&Term::var(&x)).unwrap();
        let qx = Term::app(&Term::var(&q),&Term::var(&x)).unwrap();

        let px_form = Formula::atom(&px).unwrap();
        let qx_form = Formula::atom(&qx).unwrap();

        let all_px = Formula::forall(x.clone(), px_form.clone());
        let px_to_qx =
            Formula::forall(x.clone(), Formula::imp(px_form.clone(), qx_form.clone()));

        let u0 = ProofAssumption::with_name(0, px_to_qx.clone(),"u0");
        let u1 = ProofAssumption::with_name(0, all_px.clone(),"u1");

        let proof =
            Proof::imp_intro(u0.clone(),
                             Proof::imp_intro(u1.clone(),
                                              Proof::all_intro(x.clone(),
                                                               Proof::imp_elim(
                                                                   Proof::all_elim(
                                                                       Proof::from_assumption(
                                                                           u0.clone()),
                                                                       Term::var(&x)).unwrap(),
                                                                   Proof::all_elim(
                                                                       Proof::from_assumption(
                                                                           u1.clone()),
                                                                       Term::var(&x)).unwrap())
                                                                   .unwrap()).unwrap()));
        assert_eq!(proof.to_string(), "(λ u0. (λ u1. (λ x. ((u0 x) (u1 x)))))");
        assert_eq!(proof.formula.to_string(),
            "((∀ x. ((P x) -> (Q x))) -> ((∀ x. (P x)) -> (∀ x. (Q x))))");
        assert_eq!(proof.free_assumptions(), HashSet::new());
        assert_eq!(proof.used_assumptions(), HashSet::from_iter(vec![u0, u1]));

        let sigma: TypeSubstitution = HashMap::from([
            (0, Types::Nat),
            (1, Types::Nat)]);
        let proof_subst_types = proof.subst_type(&sigma);
        let p_subst: ObjVar = ObjVar::new(0, Types::arr(Types::Nat, Types::Boolean));
        let q_subst: ObjVar = ObjVar::new(1, Types::arr(Types::Nat, Types::Boolean));
        assert_eq!(proof_subst_types.formula.free_vars(), HashSet::from_iter([p_subst, q_subst]));
        let id: TermSubstitution = HashMap::from([
            (q.clone(), Term::var(&q)),
        ]);
        let proof_subst_id = proof.subst(&id).unwrap();
        assert_eq!(proof_subst_id, proof);
        let rho: TermSubstitution = HashMap::from([
            (q.clone(), Term::var(&p)),
            (p.clone(), Term::var(&q)),
        ]);
        let proof_subst = proof.subst(&rho).unwrap();
        assert_ne!(proof_subst, proof);
        assert_eq!(proof_subst.subst(&rho).unwrap(), proof);

    }
    #[test]
    fn efq_of_atom(){
        let b = ObjVar::with_name(0, Types::Boolean, "b");
        let b_form = Formula::atom(&Term::var(&b)).unwrap();
        let proof = Proof::efq(&b_form);

        assert_eq!(proof.kind.formula().unwrap(),proof.formula);
    }
    #[test]
    fn efq_of_implication(){
        let p = ObjVar::with_name(0, Types::Boolean, "P");
        let p_form = Formula::atom(&Term::var(&p)).unwrap();
        let q = ObjVar::with_name(0, Types::Boolean, "Q");
        let q_form = Formula::atom(&Term::var(&q)).unwrap();
        let proof = Proof::efq(&Formula::imp(p_form,q_form));
        assert_eq!(proof.kind.formula().unwrap(),proof.formula);
    }
    #[test]
    fn efq_of_universal_formula(){
        let p = ObjVar::with_name(0, Types::arr(Types::Nat,Types::Boolean), "P");
        let q = ObjVar::with_name(1, Types::arr(Types::Nat,Types::Boolean), "Q");
        let n = ObjVar::with_name(2, Types::Nat, "n");
        let pn = Term::app(&Term::var(&p), &Term::var(&n)).unwrap();
        let qn = Term::app(&Term::var(&q), &Term::var(&n)).unwrap();
        let pn_form = Formula::atom(&pn).unwrap();
        let qn_form = Formula::atom(&qn).unwrap();
        let formula = Formula::forall(n,Formula::imp(pn_form,qn_form));
        let proof = Proof::efq(&formula);
        // println!("{}", proof);
        // (λ u_0. (λ n. ((λ u_0. (λ u_0. (((𝒞((𝔹)_0.(𝔹)_0) (Q n)) AxT) u_0))) u_0)))
        assert_eq!(proof.kind.formula().unwrap(),proof.formula);
    }
}