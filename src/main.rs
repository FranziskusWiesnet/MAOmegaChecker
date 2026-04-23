#![allow(non_snake_case)]
#![allow(dead_code)]
mod types;
mod formulas;
mod terms;
mod proofs;
mod form_clas;

use crate::form_clas::d_proof;
use crate::types::Types;
use crate::terms::obj_var::ObjVar;
use crate::terms::Term;
use crate::terms::Const;
use crate::formulas::{Formula, Stab};
use crate::types::Types::TypeVar;


fn setPrint(formula: &Formula) -> bool {
    println!("{}", formula);
    true
}

fn isStab(formula: &Formula) -> Option<Formula> {
    let F = Formula::Atom(Term::ff());
    match formula {
        Formula::Imp(A,B) =>
        match A.as_ref() {
            Formula::Imp(A_1,A_2) =>
                {
                    if *A_2.as_ref() != F {
                        None
                    } else{
                        match A_1.as_ref(){
                            Formula::Imp(A_11,A_12) => {
                                if *A_12.as_ref() != F || A_11 != B {
                                    None
                                } else {
                                    Some(B.as_ref().clone())
                                }
                            }
                            _ => None,
                        }
                    }
                }
            _ => None,
        }
        _=> None
    }
}

fn isNegBot(formula: &Formula) -> Option<Formula> {
    let B = Formula::Bottom;
    match formula {
        Formula::Imp(a, b) => {
            if *b.as_ref() != B {
                None
            } else {
                match a.as_ref() {
                    Formula::Imp(a1,_) =>
                        {
                            if *b.as_ref() != B {
                                None
                            } else {
                                Some(a1.as_ref().clone())
                            }
                        }
                    _ => None,
                }
            }
        }
        _ => None,
    }
}
fn isUniversalStab(formula: &Formula) -> Option<Formula> {
    match formula {
        Formula::Forall(_, A) => isUniversalStab(A.as_ref()),
        _ => isStab(formula)
    }
}

fn imp(a: &Formula, b: &Formula) -> Formula {
    Formula::Imp(Box::new(a.clone()), Box::new(b.clone()))
}

fn all(x: &ObjVar, a: &Formula) -> Formula {
    Formula::Forall(x.clone(), Box::new(a.clone()))
}

fn main() {
    let bot = Formula::Bottom;
    let F = Formula::Atom(Term::constant(Const::FF));
    let xi = TypeVar(0);
    let q = ObjVar::with_name(0, Types::arr(xi.clone(), Types::Boolean), "Q");
    let x = ObjVar::with_name(0, xi, "x");
    let qx = Term::app(&Term::var(&q), &Term::var(&x)).unwrap();
    let qx_form = Formula::Atom(qx.clone());
    let _Stab = Stab(&qx_form);
    let S = all(&x, &imp(&imp(&imp(&qx_form, &F), &F), &qx_form));
    let AllQx = all(&x, &qx_form);
    let T = imp(&imp(&AllQx, &bot), &bot);
    let StoT = imp(&S, &T);

    println!("{StoT}");
    println!("{:?}", d_proof(&StoT));
    let B = imp(&imp(&qx_form, &bot), &bot);
    println!("{B}");
    println!("{}",d_proof(&B).unwrap().formula());
    println!("{}", isStab(&S.kernel()).unwrap());
    println!("{}", isNegBot(&T).unwrap().kernel());
}
