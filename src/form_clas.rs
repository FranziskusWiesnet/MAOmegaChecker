use crate::formulas::Formula;
use crate::proofs::axioms::Axiom;
use crate::proofs::checked_proofs::{Proof};
use crate::proofs::ProofAssumption;
use crate::terms::{ObjVar, Term};
use crate::types::Types;

fn imp(a: &Formula, b: &Formula) -> Formula {
    Formula::Imp(Box::new(a.clone()), Box::new(b.clone()))
}
fn all(x: &ObjVar, a: &Formula) -> Formula {
    Formula::Forall(x.clone(), Box::new(a.clone()))
}

fn F() -> Formula {
    Formula::falsum()
}
fn ass(u : &ProofAssumption) -> Proof {
    Proof::from_assumption(u.clone())
}
fn imp_elim(m: Proof, n : Proof) -> Option<Proof> {
    match Proof::imp_elim(m, n) {
        Ok(p) => Some(p),
        Err(_) => None
    }
}
fn imp_intro (u: &ProofAssumption, m: Proof) -> Proof {
    Proof::imp_intro(u.clone(), m)
}
fn all_intro(var: &ObjVar, M: Proof) -> Option<Proof> {
    match Proof::all_intro(var.clone(), M) {
        Ok(p) => Some(p),
        Err(_) => None
    }
}
fn all_elim(M: Proof, t: Term) -> Option<Proof> {
    match Proof::all_elim(M, t) {
        Ok(p) => Some(p),
        Err(_) => None
    }
}
fn axiom(axiom: Axiom) -> Option<Proof> {
    match Proof::from_axiom(axiom) {
        Ok(p) => Some(p),
        Err(_) => None
    }
}

fn r_prop_to_d_prop(formula: &Formula) -> Option<Proof> {
    let u = ProofAssumption::new(0, imp(&formula.F(), &F()));
    let v = ProofAssumption::new(0, formula.F());
    let f_to_bot = Proof::from_axiom(Axiom::BotIntro).unwrap();
    let r_prop =
        ProofAssumption::new(
            0,
            imp(&imp(&imp(&formula.F(), &F()), &Formula::Bottom), formula));
    Some(imp_intro(&r_prop,
                   imp_intro(&v,
                             imp_elim(ass(&r_prop),
                                      imp_intro(&u,
                                                imp_elim(f_to_bot,
                                                         imp_elim(ass(&u),ass(&v))?)?))?)))
}

fn i_prop_to_g_prop (formula: &Formula) -> Option<Proof> {
    let u = ProofAssumption::new(0, formula.clone());
    let v = ProofAssumption::new(0, imp(&formula.F(),&Formula::Bottom));
    let i_prop =   ProofAssumption::new(
        0,
        imp(formula, &formula.F()),
    );
    Some(imp_intro(&i_prop,
                   imp_intro(&u,
                             imp_intro(&v,
                                       imp_elim(ass(&v),
                                                imp_elim(ass(&i_prop),
                                                         ass(&u))?)?))))
}

pub fn case_dist(formula: &Formula, goal: &Formula) -> Option<Proof> {
    // We construct a proof of (A -> goal) ->((A -> F) -> goal) -> goal, if possible.
    match formula {
        Formula::Atom(t) => {
            let b = ObjVar::new(0,Types::Boolean);
            let b_term = Term::var(&b);
            let b_form = Formula::Atom(b_term);
            let case_dist =
                imp(
                    &imp(
                        &b_form,
                        goal),
                    &imp(
                        &imp(
                            &imp(&b_form, &F()),
                            goal),
                        goal));
            let ax_case = axiom(Axiom::Case(b, case_dist))?;
            // Case tt:
            let u = ProofAssumption::new(
                0,
                imp(&Formula::Atom(Term::tt()),goal));
            let v = ProofAssumption::new(
                0,
                imp(&imp(&Formula::Atom(Term::tt()),&F()),goal));
            let proof_tt =
                imp_intro(&u,imp_intro
                    (&v,imp_elim(ass(&u),axiom(Axiom::AxTrue)?)?));
            // Case ff:
            let u = ProofAssumption::new(
                0,
                imp(&F(),goal));
            let v = ProofAssumption::new(
                0,
                imp(&imp(&F(),&F()),goal));
            let w = ProofAssumption::new(0,F());
            let proof_ff = imp_intro(&u,
                                     imp_intro(&v,
                                               imp_elim(ass(&v),
                                                        imp_intro(&w,ass(&w)))?));
            imp_elim(imp_elim(all_elim(ax_case,t.clone())?,proof_tt)?,proof_ff)
        }
        Formula::Bottom => None,
        Formula::Imp(a, b) => {
            if let (Some(m),Some(n)) =
                (case_dist(&a,&imp(&imp(&b,&F()),goal)),
                 case_dist(&b,goal)) {

                let u = ProofAssumption::new(
                    0,
                    imp(&imp(a.as_ref(),b.as_ref()),goal));
                // u : (A → B) → goal
                let v = ProofAssumption::new(
                    0,
                    imp(&imp(&imp(a.as_ref(), b.as_ref()), &F()), goal));
                // v : ¬(A → B) → goal
                let w = ProofAssumption::new(0, a.as_ref().clone());
                // w : A
                let z = ProofAssumption::new(0, b.as_ref().clone());
                // z : B
                let x = ProofAssumption::new(0, imp(a.as_ref(), b.as_ref()));
                // x : A → B
                let y = ProofAssumption::new(0, imp(b.as_ref(), &F()));
                // x : ¬B
                let s = ProofAssumption::new(0, imp(a.as_ref(), &F()));
                // s : ¬A
                let proof1 =
                    imp_elim( //(¬B → goal) →  goal
                              n, // (B → goal) → (¬B → goal) → goal
                              imp_intro( // B → goal
                                         &z, // B
                                         imp_elim( // goal
                                             ass(&u), // (A → B) → goal
                                             imp_intro( // A → B
                                                 &w, // A
                                                 ass(&z), // B
                                             ))?),
                    )?;
                let proof2 =
                    imp_intro( // A → ¬B → goal
                        &w, // A
                        imp_intro( // ¬B → goal
                            &y, // ¬B
                            imp_elim( //goal
                                ass(&v), // ¬(A → B) → goal
                                imp_intro( // ¬(A → B)
                                    &x, // A → B
                                    imp_elim( //F
                                        ass(&y), // ¬B
                                        imp_elim( // B
                                            ass(&x), // A → B
                                            ass(&w), // A
                                        )?)?))?));
                let proof3 =
                    imp_intro( // ¬A → ¬B → goal
                        &s, // ¬A
                        imp_intro( // ¬B → goal
                            &y, // ¬B
                            imp_elim( //goal
                                      ass(&u), // (A → B) → goal
                                      imp_intro( // A → B
                                                 &w, // A
                                                 imp_elim( //B
                                                           Proof::efq(b.as_ref()), // F → B
                                                           imp_elim( // F
                                                                     ass(&s), // ¬A
                                                                     ass(&w), // A
                                                           )?)?))?));

                Some(
                    imp_intro( //((A → B) → goal) → (¬(A → B) → goal) → goal
                        &u, // (A → B) → goal
                        imp_intro(  // (¬(A → B) → goal) → goal
                            &v, // ¬(A → B) → goal
                            imp_elim( // goal
                                      proof1, //(¬B → goal) →  goal
                                      imp_elim( // ¬B → goal
                                                imp_elim(  // (¬A → ¬B → goal) -> ¬B → goal
                                                           m, // (A → ¬B → goal) → (¬A → ¬B → goal) -> ¬B → goal
                                                           proof2)?, // A -> ¬B -> goal
                                                proof3, // ¬A → ¬B → goal
                                      )?)?)))
            } else {
                None
            }
        }
        Formula::Forall(_, _) => {None}
    }
}

pub fn d_proof(formula: &Formula) -> Option<Proof> {
    // If A\in D, we construct a proof of A^F -> A
    match formula {
        Formula::Bottom => {
            match Proof::from_axiom(Axiom::BotIntro) {
                Ok(proof) => Some(proof),
                Err(_) => None,
            }
        },
        Formula::Atom(_) => {let u = ProofAssumption::new(0, formula.clone());
            Some(imp_intro(&u, ass(&u)))},
        Formula::Forall(x, body) =>  {
            let proof_body : Proof;
            if let  Some(m) = d_proof(body) {
                proof_body = m;
            } else if let Some(m) = r_proof(body) {
                proof_body = imp_elim(m, r_prop_to_d_prop(body)?)?;
            } else {
                return None
            }
            let body_F = body.F();
            let u = ProofAssumption::new(0, all(x, &body_F));
            let term_x = Term::var(x);
            Some(imp_intro(&u,all_intro(x,imp_elim(proof_body,all_elim(ass(&u), term_x)?)?)?))
        }
        Formula::Imp(a, b) =>  {
            if let (Some(m),Some(n)) = (i_proof(a),d_proof(b)) {
            let u = ProofAssumption::new(0, a.as_ref().clone());
            let v = ProofAssumption::new(
                0,
                imp(&a.as_ref().F(),&b.as_ref().F()));
            Some(
                imp_intro(&v,
                          imp_intro(&u,
                                    imp_elim(n,
                                             imp_elim(ass(&v),
                                                      imp_elim(m,
                                                               ass(&u))?)?)?)))
        } else if let (Some(m),Some(n)) = (g_proof(a),r_proof(b)) {
                let u = ProofAssumption::new(0, a.as_ref().clone());
                let v = ProofAssumption::new(
                    0,
                    imp(&a.as_ref().F(), &b.as_ref().F()));
                let w = ProofAssumption::new(
                    0,
                    imp(&b.as_ref().F(), &F()));
                let z = ProofAssumption::new(0, a.as_ref().F());
                Some(
                    imp_intro(
                        &v,
                        imp_intro(
                            &u,
                            imp_elim(
                                n,
                                imp_intro(
                                    &w,
                                    imp_elim(
                                        imp_elim(m, ass(&u))?,
                                        imp_intro(
                                            &z,
                                            imp_elim(
                                                axiom(Axiom::BotIntro)?,
                                                imp_elim(
                                                    ass(&w),
                                                    imp_elim(ass(&v),
                                                             ass(&z))?)?)?))?))?)))
        } else {None}}
    }
}
pub fn g_proof(formula: &Formula) -> Option<Proof> {
    // If A\in G, we construct a proof of A -> (A^F->bot) -> bot
    match formula {
        Formula::Bottom => {
            let u = ProofAssumption::new(0, Formula::Bottom);
            let v = ProofAssumption::new(0, imp(&F(), &Formula::Bottom));
            Some(Proof::imp_intro(u.clone(), Proof::imp_intro(v, Proof::from_assumption(u))))
        }
        Formula::Atom(_) => {
            let u = ProofAssumption::new(0, formula.clone());
            let v = ProofAssumption::new(0, imp(&formula, &Formula::Bottom));
            Some(imp_intro(&u, imp_intro(&v, imp_elim(ass(&v), ass(&u))?)))
        },
        Formula::Forall(x, body) => {
            if let Some(m) = i_proof(body) {
                let u = ProofAssumption::new(0, all(x, formula));
                let x_term = Term::var(x);
                let v =
                    ProofAssumption::new(0, imp(
                        &all(&x,&formula.F()),
                        &Formula::Bottom));
                Some(imp_intro(&u,
                               imp_intro(&v,
                                         imp_elim(ass(&v),
                                                  all_intro(&x,
                                                            imp_elim(m,
                                                                     all_elim(ass(&u),
                                                                              x_term)?)?)?)?)))
            } else {
                None
            }
        }
        Formula::Imp(a, b) => {
            todo!()
        }
    }
}
pub fn r_proof(formula: &Formula) -> Option<Proof>{
    match formula {
        Formula::Bottom => {
            let u = ProofAssumption::new(0, F());
            let v =
                ProofAssumption::new(0, imp(&imp(&F(),&F()),&Formula::Bottom));
            let proof = imp_elim(ass(&v),imp_intro(&u,ass(&u)))?;
            Some(imp_intro(&v,proof))
        },
        Formula::Atom(_) => None,
        Formula::Forall(x, body) => {
            let m = r_proof(body)?;
            let u = ProofAssumption::new(0, all(x, &formula.F()));
            let v = ProofAssumption::new(0, imp(&formula.F(),&F()));
            let w  = ProofAssumption::new(
                0,
                imp(&imp(&all(x, &formula.F()),&F()),&Formula::Bottom)
            );
            let x_term = Term::var(x);
            Some(
                imp_intro(
                    &w,
                    all_intro(
                        &x,
                        imp_elim(
                            m,
                            imp_intro(
                                &v,
                                imp_elim(
                                    ass(&w),
                                    imp_intro(&u,
                                              imp_elim(
                                                  ass(&v),
                                                  all_elim(
                                                      ass(&u)
                                                      , x_term)?)?))?))?)?))
        }
        Formula::Imp(_, _) => {todo!()}
    }
}
pub fn i_proof(formula: &Formula) -> Option<Proof>{
    match formula {
        Formula::Bottom => None,
        Formula::Atom(_) => {
            let u = ProofAssumption::new(0, formula.clone());
            Some(imp_intro(&u, ass(&u)))
        },
        Formula::Forall(x, body) => {
            let u = ProofAssumption::new(0, all(x, formula));
            let x_term = Term::var(x);
            Some(imp_intro(&u,
                           all_intro(&x,
                                     imp_elim(i_proof(body)?,
                                              all_elim(ass(&u), x_term)?)?)?))
        }
        Formula::Imp(_, _) => {todo!()}
    }
}

pub fn prop_d (formula: &Formula) -> bool {
    match formula {
        Formula::Imp(a, b) => {
            *a.as_ref() == b.as_ref().F()
        }
        _ => false,
    }
}

pub fn prop_g (formula: &Formula) -> bool {
    match formula {
        Formula::Imp(a,b) => {
            imp(&imp(&a.as_ref().F(),&Formula::Bottom),&Formula::Bottom) == *b.as_ref()
        }
        _ => false,
    }
}
pub fn prop_r (formula: &Formula) -> bool {
    match formula {
        Formula::Imp(a,b) => {
            *a.as_ref() == imp(&imp(&b.as_ref().F(),&F()),&Formula::Bottom)
        }
        _ => false,
    }
}
pub fn prop_i (formula: &Formula) -> bool {
    match formula {
        Formula::Imp(a, b) => {
            a.as_ref().F() == *b.as_ref()
        }
        _ => false,
    }
}


#[cfg(test)]

mod tests {
    use std::collections::HashSet;
    use crate::terms::Term;
    use crate::types::Types;
    use super::*;

    #[test]
    fn set_g_for_bottom() {
        let bot = Formula::Bottom;
        let proof = g_proof(&bot).unwrap();
        println!("{}", proof.formula());
        println!("{}", proof);
    }
    #[test]
    fn set_r_for_bottom() {
        let bot = Formula::Bottom;
        let proof = r_proof(&bot).unwrap();
        println!("{}", proof.formula());
        println!("{}", proof);
        assert!(prop_r(proof.formula()));
    }
    #[test]
    fn set_d_for_atomic() {
        let b = ObjVar::with_name(0, Types::Boolean, "b");
        let b_term = Term::var(&b);
        let b_form = Formula::atom(&b_term).unwrap();

        let proof = d_proof(&b_form).unwrap();
        println!("{}", proof.formula());
        println!("{}", proof);
        assert!(prop_d(proof.formula()));
    }
    #[test]
    fn set_g_for_atomic() {
        let b = ObjVar::with_name(0, Types::Boolean, "b");
        let b_term = Term::var(&b);
        let b_form = Formula::atom(&b_term).unwrap();
        let proof = g_proof(&b_form).unwrap();
        println!("{}", proof.formula());
        println!("{}", proof);
        assert!(prop_g(proof.formula()));
    }
    #[test]
    fn set_i_for_atomic() {
        let b = ObjVar::with_name(0, Types::Boolean, "b");
        let b_term = Term::var(&b);
        let b_form = Formula::atom(&b_term).unwrap();
        let proof = i_proof(&b_form).unwrap();
        println!("{}", proof.formula());
        println!("{}", proof);
        assert!(prop_i(proof.formula()));
    }
    #[test]
    fn d_proof_for_universal_formula() {
        let f = ObjVar::with_name(0, Types::arr(Types::Nat, Types::Boolean), "f");
        let n = ObjVar::with_name(0, Types::Nat, "n");
        let fn_term = Term::app(&Term::var(&f),&Term::var(&n)).unwrap();
        let fn_form = all(&n, &Formula::atom(&fn_term).unwrap());

        let proof = d_proof(&fn_form).unwrap();
        println!("{}", proof.formula());
        println!("{}", proof);
        assert!(prop_d(proof.formula()));
        assert_eq!(proof.free_assumptions(),HashSet::new());
    }
    #[test]
     fn d_proof_for_g_to_r() {
        let form = imp(&Formula::Bottom,&Formula::Bottom);
        let proof = d_proof(&form).unwrap();
        println!("{}", proof.formula());
        println!("{}", proof);
        assert!(prop_d(proof.formula()));
        assert_eq!(proof.free_assumptions(), HashSet::new());
    }
    #[test]
    fn case_dist_for_atomic_formula() {
        let b = ObjVar::new(0, Types::Boolean);
        let x = ObjVar::with_name(1, Types::Boolean,"X");
        let b_form = Formula::Atom(Term::var(&b));
        let x_form = Formula::Atom(Term::var(&x));
        let stable_proof = case_dist(&b_form,&x_form).unwrap();
        println!("{}", stable_proof.formula());
        assert_eq!(stable_proof.free_assumptions(), HashSet::new());
    }
    #[test]
    fn case_dist_for_implications() {
        let a = ObjVar::with_name(1, Types::Boolean, "A");
        let b = ObjVar::with_name(2, Types::Boolean, "B");
        let x = ObjVar::with_name(1, Types::Boolean,"X");
        let a_form = Formula::Atom(Term::var(&a));
        let b_form = Formula::Atom(Term::var(&b));
        let x_form = Formula::Atom(Term::var(&x));
        let stable_proof = case_dist(&imp(&a_form,&b_form),&x_form).unwrap();
        println!("{}", stable_proof.formula());
        assert_eq!(stable_proof.free_assumptions(), HashSet::new());
    }
}