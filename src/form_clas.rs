use crate::formulas::Formula;
use crate::proofs::axioms::Axiom;
use crate::proofs::checked_proofs::{Proof};
use crate::proofs::ProofAssumption;
use crate::terms::{ObjVar, Term};


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

pub fn d_proof(formula: &Formula) -> Option<Proof> {
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
        Formula::Imp(_, _) =>  { todo!() }
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
        Formula::Imp(_, _) => { todo!() }
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
        Formula::Forall(x, body) => {todo!()}
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
}