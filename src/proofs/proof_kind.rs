use std::collections::{HashMap, HashSet};
use std::fmt;
use std::hash::{Hash, Hasher};
use crate::formulas::Formula;
use crate::terms::{new_var, ObjVar, Term, TermSubstitution};
use crate::proofs::axioms::{Axiom};
use crate::proofs::assumptions::{new_assumption, ProofAssumption};
use crate::terms::typed_terms::free_vars_of_term_substitution;
use crate::types::{TypeError, TypeSubstitution};

pub type ProofKindSubstitution = HashMap<ProofAssumption, ProofKind>;


#[derive(Debug, Clone)]
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
    pub fn formula(&self) -> Result<Formula, ProofError> {
        match self {
            ProofKind::Assumption(p) => Ok(p.form()),
            ProofKind::Ax(a) => {
                match a.form() {
                    Ok(a) => Ok(a),
                    Err(e) => Err(ProofError::Type(e)),
                }
            }
            ProofKind::ImpIntro(assumption, body) => {
                Ok(Formula::imp(assumption.form(), body.formula()?))
            }
            ProofKind::ImpElim(left, right) => {
                let prem_to_conclusion = left.formula()?;
                match prem_to_conclusion {
                    Formula::Imp(prem, conclusion) => {
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
            ProofKind::AllIntro(var, body) => {
                Ok(Formula::forall(var.clone(), body.formula()?))
            }
            ProofKind::AllElim(forall_proof, t) => {
                let forall_formula = forall_proof.formula()?;
                match forall_formula {
                    Formula::Forall(var, form) => {
                        let sigma: TermSubstitution = HashMap::from([(var.clone(), t.clone())]);
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
            ProofKind::Ax(_) => { HashSet::new() }
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
            ProofKind::AllIntro(_var, m) => {
                m.free_assumptions()
            }
            ProofKind::AllElim(m, _) => {
                m.free_assumptions()
            }
        }
    }
}
pub fn free_assumptions(set: HashSet<ProofKind>) -> HashSet<ProofAssumption> {
    let mut h = HashSet::new();
    for proof in set {
        h.extend(proof.free_assumptions())
    }
    h
}
pub fn free_assumptions_of_substitution(sigma: &ProofKindSubstitution) -> HashSet<ProofAssumption> {
    let mut set = HashSet::new();
    for (_,p) in sigma {
        set.extend(p.free_assumptions());
    }
    set
}

impl ProofKind {
pub fn subst_assumption(&self, sigma: &ProofKindSubstitution) -> Self {
        match self {
            ProofKind::Assumption(p) => {
                match sigma.get(p) {
                    Some(proof) => proof.clone(),
                    None => {self.clone()}
                }
            }
            ProofKind::Ax(_) => {self.clone()},
            ProofKind::ImpElim(m, n) => {
                ProofKind::ImpElim(Box::new(m.subst_assumption(sigma)),
                                   Box::new(n.subst_assumption(sigma)))
            }
            ProofKind::ImpIntro(u, m) => {
                let mut sigma_wo_assumption = sigma.clone();
                sigma_wo_assumption.remove(u);
                let set_free_assumptions =
                    free_assumptions_of_substitution(&sigma_wo_assumption);
                if set_free_assumptions.contains(u) {
                    let mut forbidden = m.free_assumptions();
                    forbidden.remove(u);
                    forbidden.extend(set_free_assumptions);
                    let fresh_assumption = new_assumption(&u.form(), forbidden);
                    sigma_wo_assumption
                        .insert(u.clone(), ProofKind::Assumption(fresh_assumption.clone()));
                    ProofKind::ImpIntro(fresh_assumption,
                                        Box::new(m.subst_assumption(&sigma_wo_assumption)))
                } else {
                    ProofKind::ImpIntro(u.clone(),
                                        Box::new(m.subst_assumption(&sigma_wo_assumption)))
                }
            }
            ProofKind::AllIntro(var,body) => {
                ProofKind::AllIntro(var.clone(),Box::new(body.subst_assumption(sigma)))
            }
            ProofKind::AllElim(a,t) => {
                ProofKind::AllElim(Box::new(a.subst_assumption(sigma)),t.clone())
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
    pub fn subst(&self, sigma: &TermSubstitution) -> Result<Self,TypeError> {
        match self {
            ProofKind::Assumption(p) => {
                Ok(ProofKind::Assumption(p.subst(sigma)?))
            }
            ProofKind::Ax(ax) => {
                Ok(ProofKind::Ax(ax.subst(sigma)?))
            }
            ProofKind::ImpIntro(u, m) => {
                Ok(ProofKind::ImpIntro(u.subst(sigma)?,Box::new(m.subst(sigma)?)))
            }
            ProofKind::ImpElim(m, n) => {
                Ok(ProofKind::ImpElim(Box::new(m.subst(sigma)?),Box::new(n.subst(sigma)?)))
            }
            ProofKind::AllElim(m,t) => {
                Ok(ProofKind::AllElim(Box::new(m.subst(sigma)?),t.subst(sigma)?))
            }
            ProofKind::AllIntro(var,m) => {
                let mut sigma_wo_var = sigma.clone();
                sigma_wo_var.remove(var);
                let set_fv = free_vars_of_term_substitution(&sigma_wo_var);
                if set_fv.contains(var) {
                    let mut forbidden = m.free_vars();
                    forbidden.remove(var);
                    forbidden.extend(set_fv);
                    let fresh_var = new_var(var.ty(), forbidden);
                    sigma_wo_var.insert(var.clone(), Term::var(&fresh_var));
                    Ok(ProofKind::AllIntro(fresh_var,Box::new(m.subst(&sigma_wo_var)?)))
                } else {
                    Ok(ProofKind::AllIntro(var.clone(),Box::new(m.subst(&sigma_wo_var)?)))
                }
            }
        }
    }
}
impl PartialEq for ProofKind {
    fn eq(&self, other: &Self) -> bool {
        match (self,other) {
            (ProofKind::Assumption(p1),
                ProofKind::Assumption(p2)) => {
                p1==p2
            }
            (ProofKind::Ax(a1), ProofKind::Ax(a2)) => a1 == a2,
            (ProofKind::ImpElim(m1,n1),
                ProofKind::ImpElim(m2,n2)) => {
                m1 == m2 && n1 == n2
            }
            (ProofKind::ImpIntro(u1, m1),
                ProofKind::ImpIntro(u2,m2)) => {
                if u1.form() != u2.form() {
                    return false;
                }
                let mut set = m1.free_assumptions();
                set.extend(m2.free_assumptions());
                let fresh_assumption = new_assumption(&u1.form(), set);
                let sigma_1: ProofKindSubstitution = HashMap::from(
                    [(u1.clone(),ProofKind::Assumption(fresh_assumption.clone()))]);
                let sigma_2: ProofKindSubstitution = HashMap::from(
                    [(u2.clone(),ProofKind::Assumption(fresh_assumption.clone()))]);
                m1.subst_assumption(&sigma_1) == m2.subst_assumption(&sigma_2)
            }
            (ProofKind::AllElim(m1,t1),
                ProofKind::AllElim(m2,t2)) => {
                m1 == m2 && t1 == t2
            }
            (ProofKind::AllIntro(var1,m1),
                ProofKind::AllIntro(var2,m2)) => {
                if var1.ty() != var2.ty() {
                    return false;
                }
                let mut set = m1.free_vars();
                set.extend(m2.free_vars());
                let fresh_var = new_var(var1.ty(), set);
                let sigma_1: TermSubstitution =
                    HashMap::from([(var1.clone(),Term::var(&fresh_var))]);
                let sigma_2: TermSubstitution =
                    HashMap::from([(var2.clone(),Term::var(&fresh_var))]);
                m1.subst(&sigma_1) == m2.subst(&sigma_2)
            }
            _ => false,
        }
    }
}
impl Eq for ProofKind {}
impl Hash for ProofKind {
    fn hash<H: Hasher>(&self, state: &mut H) {
        let mut term_env: HashMap<ObjVar, usize> = HashMap::new();
        let mut assumption_env: HashMap<ProofAssumption, usize> = HashMap::new();
        self.hash_rec(state, &mut term_env, &mut assumption_env, 0, 0);
    }
}
impl ProofKind {
    fn hash_rec<H: Hasher>(
        &self,
        state: &mut H,
        term_env: &mut HashMap<ObjVar, usize>,
        assumption_env: &mut HashMap<ProofAssumption, usize>,
        term_depth: usize,
        assumption_depth: usize,
    ) {
        match self {
            ProofKind::Assumption(u) => {
                0u8.hash(state);
                if let Some(binder_depth) = assumption_env.get(u) {
                    0u8.hash(state);
                    (assumption_depth - 1 - binder_depth).hash(state);
                    u.form().hash(state);
                } else {
                    1u8.hash(state);
                    u.hash(state);
                }
            }
            ProofKind::Ax(a) => {
                1u8.hash(state);
                a.hash(state);
            }
            ProofKind::ImpIntro(u, body) => {
                2u8.hash(state);
                u.form().hash(state);

                let old = assumption_env.insert(u.clone(), assumption_depth);
                body.hash_rec(state, term_env, assumption_env, term_depth,
                              assumption_depth + 1);

                match old {
                    Some(prev) => {
                        assumption_env.insert(u.clone(), prev);
                    }
                    None => {
                        assumption_env.remove(u);
                    }
                }
            }
            ProofKind::ImpElim(m, n) => {
                3u8.hash(state);
                m.hash_rec(state, term_env, assumption_env, term_depth, assumption_depth);
                n.hash_rec(state, term_env, assumption_env, term_depth, assumption_depth);
            }
            ProofKind::AllIntro(x, body) => {
                4u8.hash(state);
                x.ty().hash(state);

                let old = term_env.insert(x.clone(), term_depth);
                body.hash_rec(state, term_env, assumption_env, term_depth + 1,
                              assumption_depth);

                match old {
                    Some(prev) => {
                        term_env.insert(x.clone(), prev);
                    }
                    None => {
                        term_env.remove(x);
                    }
                }
            }
            ProofKind::AllElim(m, t) => {
                5u8.hash(state);
                m.hash_rec(state, term_env, assumption_env, term_depth, assumption_depth);
                t.hash(state);
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
    #[test]
    fn subst_replaces_free_variable_in_assumption() {
        let alpha = Types::TypeVar(0);

        let x = ObjVar::new(0, alpha.clone());
        let y = ObjVar::new(1, alpha.clone());

        let p = ObjVar::new(2, Types::arr(alpha.clone(), Types::Boolean));

        let px = Term::app(&Term::var(&p), &Term::var(&x)).unwrap();
        let py = Term::app(&Term::var(&p), &Term::var(&y)).unwrap();

        let u = ProofAssumption::new(0, Formula::Atom(px));
        let proof = ProofKind::Assumption(u);

        let sigma: TermSubstitution =
            HashMap::from([(x.clone(), Term::var(&y))]);

        let result = proof.subst(&sigma).unwrap();

        let expected =
            ProofKind::Assumption(ProofAssumption::new(0, Formula::Atom(py)));
        println!("{:?}",result.formula().unwrap());
        assert_eq!(result, expected);
    }
    #[test]
    fn subst_all_intro_keeps_binder_when_no_capture_is_possible() {
        let alpha = Types::TypeVar(0);

        let x = ObjVar::new(0, alpha.clone());
        let y = ObjVar::new(1, alpha.clone());
        let z = ObjVar::new(2, alpha.clone());

        let p = ObjVar::new(0, Types::arr(alpha.clone(), Types::Boolean));

        let py = Term::app(&Term::var(&p), &Term::var(&y)).unwrap();
        // py: (((ξ0 ⇒ 𝔹))_0 (ξ0)_1)

        let proof = ProofKind::AllIntro(
            x.clone(),
            Box::new(ProofKind::Assumption(
                ProofAssumption::new(0, Formula::Atom(py)),
            )),
        );
        // proof: (λ (ξ0)_0. u_0) with formula (∀ (ξ0)_0. (((ξ0 ⇒ 𝔹))_0 (ξ0)_1))

        let sigma: TermSubstitution =
            HashMap::from([(y.clone(), Term::var(&z))]);

        let result = proof.subst(&sigma).unwrap();

        match result {
            ProofKind::AllIntro(bound, body) => {
                assert_eq!(bound, x);

                let expected_pz =
                    Term::app(&Term::var(&p), &Term::var(&z)).unwrap();

                let expected = ProofKind::Assumption(
                    ProofAssumption::new(0, Formula::Atom(expected_pz)),
                );

                assert_eq!(*body, expected);
            }
            _ => panic!("expected AllIntro"),
        }
    }
}
