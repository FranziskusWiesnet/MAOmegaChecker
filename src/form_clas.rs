use std::collections::{HashMap};
use crate::formulas::Formula;
use crate::proofs::axioms::Axiom;
use crate::proofs::checked_proofs::{Proof};
use crate::proofs::ProofAssumption;
use crate::terms::{ObjVar, Term, TermSubstitution};
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
    let v = ProofAssumption::new(1, formula.F());
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
    let v = ProofAssumption::new(1, imp(&formula.F(),&Formula::Bottom));
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
    // We construct a proof of (A → goal) →((A → F) → goal) → goal, if possible.
    match formula {
        Formula::Atom(t) => {
            let b = ObjVar::new(0,Types::Boolean);
            let b_term = Term::var(&b);
            let b_form = Formula::Atom(b_term);
            let case_dist = // (b → goal) → (¬B → goal) → goal
                imp(&imp(&b_form, goal),
                    &imp(&imp(&imp(&b_form, &F()), goal), goal));
            let ax_case = axiom(Axiom::Case(b, case_dist))?;
            // ax_case : ∀ b. ((T → goal) → (¬T → goal) → goal) →
            //                ((F → goal) → (¬F → goal) → goal) →
            //                ((b → goal) → (¬b → goal) → goal)
            // Case tt:
            let u = ProofAssumption::new(
                0,
                imp(&Formula::Atom(Term::tt()),goal));
            // u : T → goal
            let v = ProofAssumption::new(
                1,
                imp(&imp(&Formula::Atom(Term::tt()),&F()),goal));
            // v : ¬T → goal
            let proof_tt =
                imp_intro( // (T → goal) → (¬T → goal) → goal
                    &u, // T → goal
                    imp_intro // (¬T → goal) → goal
                        (&v, // ¬T → goal
                         imp_elim( // goal
                             ass(&u), // T → goal
                             axiom(Axiom::AxTrue)?, // T
                         )?));
            // Case ff:
            let u = ProofAssumption::new(
                2,
                imp(&F(),goal));
            // u : F → goal
            let v = ProofAssumption::new(
                3,
                imp(&imp(&F(),&F()),goal));
            // v : (F → F)  → goal
            let w = ProofAssumption::new(2,F());
            // w : F
            let proof_ff =
                imp_intro( // (F → goal) →  ((F → F) → goal) → goal
                           &u, //  F → goal
                           imp_intro( //  ((F → F) → goal) → goal
                                      &v, // (F → F)  → goal
                                      imp_elim( // goal
                                                ass(&v), // (F → F)  → goal
                                                imp_intro( // F → F
                                                           &w, // F
                                                           ass(&w), // F
                                                ))?));
            imp_elim( // ((t → goal) → (¬t → goal) → goal)
                imp_elim( // ((F → goal) → (¬F → goal) → goal) →
                             // ((t → goal) → (¬t → goal) → goal)
                    all_elim( //   ((T → goal) → (¬T → goal) → goal) →
                                 //   ((F → goal) → (¬F → goal) → goal) →
                                 //   ((t → goal) → (¬t → goal) → goal)
                        ax_case, //  ∀ b. ((T → goal) → (¬T → goal) → goal) →
                        //                ((F → goal) → (¬F → goal) → goal) →
                        //                ((b → goal) → (¬b → goal) → goal)
                        t.clone())? // t
                    , proof_tt)?, // ((T → goal) → (¬T → goal) → goal)
                proof_ff) // ((F → goal) → (¬F → goal) → goal)
        }
        Formula::Bottom => None,
        Formula::Imp(a, b) => {
            if let (Some(m),Some(n)) =
                (case_dist(&a,&imp(&imp(&b,&F()),goal)),
                 case_dist(&b,goal)) {
                // m : (A → ¬B → goal) → (¬A → ¬B → goal) → ¬B → goal
                // n : (B → goal) → (¬B → goal) → goal
                let u = ProofAssumption::new(
                    0,
                    imp(&imp(a.as_ref(),b.as_ref()),goal));
                // u : (A → B) → goal
                let v = ProofAssumption::new(
                    1,
                    imp(&imp(&imp(a.as_ref(), b.as_ref()), &F()), goal));
                // v : ¬(A → B) → goal
                let w = ProofAssumption::new(2, a.as_ref().clone());
                // w : A
                let z = ProofAssumption::new(3, b.as_ref().clone());
                // z : B
                let x = ProofAssumption::new(4, imp(a.as_ref(), b.as_ref()));
                // x : A → B
                let y = ProofAssumption::new(5, imp(b.as_ref(), &F()));
                // x : ¬B
                let s = ProofAssumption::new(6, imp(a.as_ref(), &F()));
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
                            imp_elim( // goal
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
                            imp_elim( // goal
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
                    imp_intro( // ((A → B) → goal) → (¬(A → B) → goal) → goal
                        &u, // (A → B) → goal
                        imp_intro(  // (¬(A → B) → goal) → goal
                            &v, // ¬(A → B) → goal
                            imp_elim( // goal
                                      proof1, // (¬B → goal) →  goal
                                      imp_elim( // ¬B → goal
                                                imp_elim(  // (¬A → ¬B → goal) → ¬B → goal
                                                           m, // (A → ¬B → goal) → (¬A → ¬B → goal) → ¬B → goal
                                                           proof2)?, // A → ¬B → goal
                                                proof3, // ¬A → ¬B → goal
                                      )?)?)))
            } else {None}
        }
        Formula::Forall(var, a) => {
            if *var.ty() == Types::Boolean {
                let sigma_tt : TermSubstitution = HashMap::from([(var.clone(),Term::tt())]);
                let sigma_ff: TermSubstitution = HashMap::from([(var.clone(),Term::ff())]);
                if let (Ok(a_tt),Ok(a_ff)) =
                    (a.subst(&sigma_tt),a.subst(&sigma_ff)) {
                    if let (Some(m0),Some(m1),Some(n)) =
                        (case_dist(&a_tt,&imp(&a_ff,goal)),
                         case_dist(&a_tt,&imp(&imp(&a_ff,&F()),goal)),
                         case_dist(&a_ff,goal)) {
                        // m0 :  (A(tt) → A(ff) → goal) → (¬A(tt) → A(ff) → goal) → A(ff) → goal
                        // m1 :  (A(tt) → ¬A(ff) → goal) → (¬A(tt) → ¬A(ff) → goal) → ¬A(ff) → goal
                        // n :  (A(ff) → goal) → (¬A(ff) → goal) → goal
                        let ax_case = axiom(Axiom::Case(var.clone(), a.as_ref().clone()))?;
                        // ax_case : ∀ var. ((A(tt) → A(ff) → A(var))
                        let u = ProofAssumption::new(
                            0,
                            imp(&all(&var,a),goal));
                        // u : (∀ var.A(var)) → goal
                        let v = ProofAssumption::new(
                            1,
                            imp(&imp(&all(&var,a),&F()),goal));
                        // v : ¬(∀ var.A(var)) → goal
                        let u00 = ProofAssumption::new(
                            2,
                            a_tt.clone());
                        // u00 : A(tt)
                        let u01 = ProofAssumption::new(
                            3,
                            a_ff.clone());
                        // u01 : A(ff)
                        let u10 = ProofAssumption::new(
                            4,
                            imp(&a_tt,&F()));
                        // u10 : ¬A(tt)
                        let u11 = ProofAssumption::new(
                            5,
                            imp(&a_ff,&F()));
                        // u11 : ¬A(ff)
                        let w = ProofAssumption::new(
                            6,
                            all(&var,a));
                        // w : ∀ var.A(var)
                        let proof00 =
                            imp_intro( // A(tt) → A(ff) → goal
                               &u00, // A(tt)
                               imp_intro( // A(ff) → goal
                                   &u01, // A(ff)
                                   imp_elim( // goal
                                          ass(&u), // (∀ var.A(var)) → goal
                                          all_intro( // ∀ var.A(var)
                                                &var,
                                                imp_elim( //A(var)
                                                       imp_elim( //A(ff) → A(var)
                                                              all_elim( // (A(tt) → A(ff) → A(var)
                                                                     ax_case, //∀ var. ((A(tt) → A(ff) → A(var))
                                                                     Term::var(var))?, // var
                                                              ass(&u00))?, // A(tt)
                                                       ass(&u01))?)?)?)); // A(ff)
                        let proof10 =
                            imp_intro( // ¬A(tt) → A(ff) → goal
                               &u10, // ¬A(tt)
                               imp_intro( // A(ff) → goal
                                  &u01, // A(ff)
                                  imp_elim( //goal
                                         ass(&v), // ¬(∀ var.A(var)) → goal
                                         imp_intro( // ¬ ∀ var.A(var)
                                            &w, // ∀ var.A(var)
                                            imp_elim( // F
                                                   ass(&u10), // ¬A(tt)
                                                   all_elim( // A(tt)
                                                         ass(&w), // ∀ var.A(var)
                                                         Term::tt())?)?))?)); // tt
                        let proof11 =
                            imp_intro( // ¬A(tt) → ¬A(ff) → goal
                               &u10, // ¬A(tt)
                               imp_intro( // ¬A(ff) → goal
                                  &u11, // ¬A(ff)
                                  imp_elim( //goal
                                        ass(&v), // ¬(∀ var.A(var)) → goal
                                        imp_intro( // ¬ ∀ var.A(var)
                                           &w, // ∀ var.A(var)
                                           imp_elim( // F
                                                 ass(&u10), // ¬A(tt)
                                                 all_elim( // A(tt)
                                                       ass(&w), // ∀ var.A(var)
                                                       Term::tt())?)?))?)); // tt
                        let proof01 =
                            imp_intro( // A(tt) → ¬A(ff) → goal
                                &u00, // A(tt)
                                imp_intro( // ¬A(ff) → goal
                                   &u11, // ¬A(ff)
                                   imp_elim( //goal
                                          ass(&v), // ¬(∀ var.A(var)) → goal
                                          imp_intro( // ¬ ∀ var.A(var)
                                             &w, // ∀ var.A(var)
                                             imp_elim( // F
                                                   ass(&u11), // ¬A(ff)
                                                   all_elim( // A(ff)
                                                         ass(&w), // ∀ var.A(var)
                                                         Term::ff())?)?))?)); // ff
                        return
                        Some(
                            imp_intro( // (∀ var.A(var) → goal) → (¬(∀ var.A(var)) → goal) → goal
                                       &u, // (∀ var.A(var)) → goal
                                       imp_intro( // (¬(∀ var.A(var)) → goal) → goal
                                                  &v,    // ¬(∀ var.A(var)) → goal
                                                  imp_elim( // goal
                                                            imp_elim( //(¬A(ff) → goal) → goal
                                                                      n, // (A(ff) → goal) → (¬A(ff) → goal) → goal
                                                                      imp_elim( // A(ff) → goal
                                                                                imp_elim( // (¬A(tt) → A(ff) → goal) → A(ff) → goal
                                                                                          m0, // (A(tt) → A(ff) → goal) → (¬A(tt) → A(ff) → goal) → A(ff) → goal
                                                                                          proof00)?, // A(tt) → A(ff) → goal
                                                                                proof10)?)?, // ¬A(tt) → A(ff) → goal
                                                            imp_elim( // ¬A(ff) → goal
                                                                      imp_elim( // (¬A(tt) → ¬A(ff) → goal) → ¬A(ff) → goal
                                                                                m1, // (A(tt) → ¬A(ff) → goal) → (¬A(tt) → ¬A(ff) → goal) → ¬A(ff) → goal
                                                                                proof01)?, // A(tt) → ¬A(ff) → goal
                                                                      proof11)?)?))) // ¬A(tt) → ¬A(ff) → goal
                    }
                }
            }
            None
        }
    }
}

pub fn d_proof(formula: &Formula) -> Option<Proof> {
    // We construct a proof of D^F → D, if possible.
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
                // m : A → A^F
                // n : B^F → B
            let u = ProofAssumption::new(0, a.as_ref().clone());
                // u : A
            let v = ProofAssumption::new(
                1,
                imp(&a.as_ref().F(),&b.as_ref().F()));
                // v : A^F → B^F
            Some(
                imp_intro( // (A^F → B^F) → A → B
                    &v, // A^F → B^F
                          imp_intro( // A → B
                              &u, // A
                                    imp_elim( // B
                                        n, // B^F → B
                                             imp_elim( //B^F
                                                 ass(&v), // A^F → B^F
                                                      imp_elim( // A^F
                                                          m, // A → A^F
                                                               ass(&u))?)?)?))) // A
        } else if let (Some(m),Some(n)) = (g_proof(a),r_proof(b)) {
                // m : A → (A^F → ⊥) → ⊥
                // n : (¬B^F → ⊥) → B
                let u = ProofAssumption::new(0, a.as_ref().clone());
                // u : A
                let v = ProofAssumption::new(
                    1,
                    imp(&a.as_ref().F(), &b.as_ref().F()));
                // v : A^F → B^F
                let w = ProofAssumption::new(
                    2,
                    imp(&b.as_ref().F(), &F()));
                // w: ¬B^F
                let z = ProofAssumption::new(3, a.as_ref().F());
                // z: A^F
                Some(
                    imp_intro( //  (A^F → B^F) → A → B
                        &v, // A^F → B^F
                        imp_intro( // A → B
                            &u, // A
                            imp_elim( // B
                                n, // (¬B^F → ⊥) → B
                                imp_intro( // ¬B^F → ⊥
                                    &w, // ¬B^F
                                    imp_elim( // ⊥
                                        imp_elim( // (A^F → ⊥) → ⊥
                                            m, // A → (A^F → ⊥) → ⊥
                                            ass(&u))?, // A
                                        imp_intro( // A^F → ⊥
                                            &z, // A^F
                                            imp_elim( // ⊥
                                                axiom(Axiom::BotIntro)?, // F → ⊥
                                                imp_elim( // F
                                                    ass(&w), // ¬B^F
                                                    imp_elim( // B^F
                                                        ass(&v), // A^F → B^F
                                                        ass(&z))?)?)?))?))?))) // A^F
        } else {None}}
    }
}
pub fn g_proof(formula: &Formula) -> Option<Proof> {
    // We construct a proof of G → (G^F → ⊥) → ⊥, if possible.
    match formula {
        Formula::Bottom => {
            let u = ProofAssumption::new(0, Formula::Bottom);
            let v = ProofAssumption::new(1, imp(&F(), &Formula::Bottom));
            Some(Proof::imp_intro(u.clone(), Proof::imp_intro(v, Proof::from_assumption(u))))
        }
        Formula::Atom(_) => {
            let u = ProofAssumption::new(0, formula.clone());
            let v = ProofAssumption::new(1, imp(&formula, &Formula::Bottom));
            Some(imp_intro(&u, imp_intro(&v, imp_elim(ass(&v), ass(&u))?)))
        },
        Formula::Forall(x, body) => {
            if let Some(m) = i_proof(body) {
                let u = ProofAssumption::new(0, all(x, formula));
                let x_term = Term::var(x);
                let v =
                    ProofAssumption::new(1, imp(
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
            if let (Some(m), Some(n)) = (r_proof(a), g_proof(b)) {
                // m : (¬A^F → ⊥) → A,
                // n : B → (B^F → ⊥) → ⊥
                let u = ProofAssumption::new(
                    0,
                    imp(a.as_ref(),b.as_ref()));
                // u : A → B
                let v = ProofAssumption::new(
                    1,
                    imp(&imp(&a.as_ref().F(),&b.as_ref().F()),&Formula::Bottom));
                // v : (A^F → B^F) → ⊥
                let w = ProofAssumption::new(2, a.F());
                // w : A
                let z = ProofAssumption::new(3, b.F());
                // z : B^F
                let s = ProofAssumption::new(4, a.as_ref().clone());
                // s : A
                let x = ProofAssumption::new(5, imp(a.as_ref(),&a.F()));
                // x : ¬A^F
                let proof1 =
                    imp_intro( // A → ⊥
                               &s, // A
                               imp_elim( // ⊥
                                         imp_elim( // (B^F → ⊥) → ⊥
                                                   n, // B → (B^F → ⊥) → ⊥
                                                   imp_elim( // B
                                                             ass(&u), // A → B
                                                             ass(&s))?)?, // A
                                         imp_intro( // B^F → ⊥
                                                    &z, // B^F
                                                    imp_elim( // ⊥
                                                              ass(&v), // (A^F → B^F) → ⊥
                                                              imp_intro( // A^F → B^F
                                                                         &w, // A^F
                                                                         ass(&z)))?))?); // B^F
                let proof2 =
                imp_intro( // ¬A^F → ⊥
                    &x, // ¬A^F
                imp_elim( // ⊥
                    ass(&v), // (A^F → B^F) → ⊥
                imp_intro( //A^F → B^F
                    &w, //A^F
                    imp_elim( // B^F
                              Proof::efq(&b.F()), // F → B^F
                              imp_elim( // F
                                        ass(&x), // ¬A^F
                                        ass(&w), // A^F
                              )?)?))?);
                Some(
                    imp_intro( // (A → B) → ((A^F → B^F) → ⊥) → ⊥
                        &u,  // A → B
                        imp_intro( // ((A^F → B^F) → ⊥) → ⊥
                            &v, // (A^F → B^F) → ⊥
                            imp_elim( // ⊥
                                      proof1, // A → ⊥
                                      imp_elim( // A
                                                m, // (¬A^F → ⊥) → A,
                                                proof2, // ¬A^F → ⊥
                                      )?)?)))
            } else if let (Some(m), Some(n), Some(l)) =
                (d_proof(a), g_proof(b), case_dist(&a.F(), &Formula::Bottom)) {
                // m : A^F → A,
                // n : B → (B^F → ⊥) → ⊥
                // l : (A^F → ⊥) → (¬A^F → ⊥) → ⊥
                let u = ProofAssumption::new(
                    0,
                    imp(a.as_ref(),b.as_ref()));
                // u : A → B
                let v = ProofAssumption::new(
                    1,
                    imp(&imp(&a.as_ref().F(),&b.as_ref().F()),&Formula::Bottom));
                // v : (A^F → B^F) → ⊥
                let w = ProofAssumption::new(2, a.as_ref().F());
                // w : A^F
                let z = ProofAssumption::new(3, b.as_ref().F());
                // z : B^F
                let x = ProofAssumption::new(4, imp(&a.as_ref().F(),&F()));
                // x : ¬A^F
                let proof1 =
                imp_intro( // A^F → ⊥
                    &w, // A^F
                    imp_elim( // ⊥
                              imp_elim( //(B^F → ⊥) → ⊥
                                        n, // B → (B^F → ⊥) → ⊥
                                        imp_elim( // B
                                                  ass(&u), // A → B
                                                  imp_elim( // A
                                                            m, // A^F → A,
                                                            ass(&w))?)?)?, // A^F
                              imp_intro( // B^F → ⊥
                                  &z, // B^F
                                  imp_elim( // ⊥
                                            ass(&v), // (A^F → B^F) → ⊥
                                            imp_intro( // A^F → B^F
                                                       &w, // A^F
                                                       ass(&z)))?))?); // B^F
                let proof2 =
                    imp_intro( // ¬A^F → ⊥
                               &x, // ¬A^F
                               imp_elim( // ⊥
                                         ass(&v), // (A^F → B^F) → ⊥
                                         imp_intro( // A^F → B^F
                                                    &w, // A^F
                                                    imp_elim( //  B^F
                                                              Proof::efq(&b.F()), // F → B^F
                                                              imp_elim( // F
                                                                        ass(&x), // ¬A^F
                                                                        ass(&w))?)?))?); // A^F
                Some(
                imp_intro( // (A → B) → ((A^F → B^F) → ⊥) → ⊥
                    &u, // A → B
                imp_intro( // ((A^F → B^F) → ⊥) → ⊥
                    &v, // (A^F → B^F) → ⊥
                imp_elim( // ⊥
                imp_elim( // (¬A^F → ⊥) → ⊥
                    l, // (A^F → ⊥) → (¬A^F → ⊥) → ⊥
                    proof1)?, // A^F → ⊥
                    proof2)?))) // ¬A^F → ⊥
            } else if let (Some(m), Some(n)) = (d_proof(a), i_proof(b)) {
                // m : A^F → A,
                // n : B → B^F
                let u = ProofAssumption::new(0, imp(a.as_ref(),b.as_ref()));
                // u : A → B
                let v = ProofAssumption::new(
                    1,
                    imp(&imp(&a.as_ref().F(),&b.as_ref().F()),&Formula::Bottom));
                // v : (A^F → B^F) → ⊥
                let w = ProofAssumption::new(2, a.as_ref().F());
                // w : A^F
                Some(
                    imp_intro( // (A → B) → ((A^F → B^F) → ⊥) → ⊥
                        &u, // A → B
                        imp_intro( // ((A^F → B^F) → ⊥) → ⊥
                            &v, // (A^F → B^F) → ⊥
                            imp_elim( // ⊥
                                   ass(&v), // (A^F → B^F) → ⊥
                                   imp_intro( // A^F → B^F
                                      &w, // A^F
                                      imp_elim( // B^F
                                             n, // B → B^F
                                              imp_elim( // B
                                                    ass(&u), // A → B
                                                     imp_elim( // A
                                                           m, // A^F → A
                                                           ass(&w))?)?)?))?))) // A^F
            } else {None}
        }
    }
}
pub fn r_proof(formula: &Formula) -> Option<Proof>{
    // We construct a proof of (¬R^F → ⊥) → R, if possible.
    match formula {
        Formula::Bottom => {
            let u = ProofAssumption::new(0, F());
            let v =
                ProofAssumption::new(1, imp(&imp(&F(),&F()),&Formula::Bottom));
            let proof = imp_elim(ass(&v),imp_intro(&u,ass(&u)))?;
            Some(imp_intro(&v,proof))
        },
        Formula::Atom(_) => None,
        Formula::Forall(x, body) => {
            let m = r_proof(body)?;
            let u = ProofAssumption::new(0, all(x, &formula.F()));
            let v = ProofAssumption::new(1, imp(&formula.F(),&F()));
            let w  = ProofAssumption::new(
                2,
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
        Formula::Imp(a, b) => {
            if let (Some(m), Some(n)) = (g_proof(a), r_proof(b)) {
                // m : A → (A^F → ⊥) → ⊥
                // n : (¬B^F → ⊥) → B
                let u = ProofAssumption::new(
                    0,
                    imp(&imp(&imp(&a.as_ref().F(),&b.as_ref().F()),&F()),&Formula::Bottom));
                // u : (¬(A^F → B^F) → ⊥)
                let v = ProofAssumption::new(1, a.as_ref().clone());
                // v : A
                let w = ProofAssumption::new(2, a.as_ref().F());
                // w : A^F
                let z = ProofAssumption::new(
                    3,
                    imp(&a.as_ref().F(),&b.as_ref().F()));
                // z : A^F → B^F
                let x = ProofAssumption::new(4, imp(&b.as_ref().F(),&F()));
                // x : ¬B^F
                Some(
                    imp_intro( // (¬(A^F → B^F) → ⊥) → A → B
                        &u, // ¬(A^F → B^F) → ⊥
                        imp_intro( //  A → B
                            &v, // A
                            imp_elim( // B
                                   n, // (¬B^F → ⊥) → B
                                   imp_intro( // ¬B^F → ⊥
                                      &x, // ¬B^F
                                      imp_elim( // ⊥
                                            imp_elim( // (A^F → ⊥) → ⊥
                                                  m, // A → (A^F → ⊥) → ⊥
                                                  ass(&v))?, // A
                                            imp_intro( //A^F → ⊥
                                               &w, // A^F
                                               imp_elim( // ⊥
                                                     ass(&u), // (¬(A^F → B^F) → ⊥)
                                                     imp_intro( // ¬(A^F → B^F)
                                                        &z, // A^F → B^F
                                                        imp_elim( // F
                                                               ass(&x), // ¬B^F
                                                                imp_elim( // B^F
                                                                      ass(&z), // A^F → B^F
                                                                      ass(&w))?)?))?))?))?))) // A^F

            } else {None}
        }
    }
}
pub fn i_proof(formula: &Formula) -> Option<Proof>{
    // We construct a proof of I → I^F, if possible.
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
        Formula::Imp(a, b) => {
            if let (Some(m),Some(n)) = (d_proof(a),i_proof(b)) {
                // m : A^F → A
                // n : B → B^F
                let u = ProofAssumption::new(0, imp(a.as_ref(),b.as_ref()));
                // u : A → B
                let v = ProofAssumption::new(1, a.as_ref().F());
                // v : A^F
                Some(
                    imp_intro( // (A → B) → A^F → B^F
                               &u, // A → B
                               imp_intro( // A^F → B^F
                                          &v, // A^F
                                          imp_elim( // B^F
                                                    n, // B → B^F
                                                    imp_elim( // B
                                                              ass(&u), // A → B
                                                              imp_elim( // A
                                                                        m, // A^F → A
                                                                        ass(&v))?)?)?))) // A^F
            } else {None}
        }
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