#![allow(non_snake_case)]
#![allow(dead_code)]
mod types;
mod formulas;
mod terms;
mod proofs;

use crate::types::Types;
use crate::terms::obj_var::ObjVar;
use crate::terms::Term;
use crate::terms::Const;
use crate::formulas::{Formula, is_qfree};
use crate::types::Types::TypeVar;


fn setPrint(formula: &Formula) -> bool {
    println!("{}", formula);
    true
}
fn setD(formula: &Formula) -> bool {
    match formula {
        Formula::Bottom => true,
        Formula::Atom(_) => true,
        Formula::Forall(_, A) => setD(A) || setR(A),
        Formula::Imp(A, B) => setI(A) && setD(B) || setG(A) && setR(B),
    }
}

fn setG(formula: &Formula) -> bool {
    match formula {
        Formula::Bottom => true,
        Formula::Atom(_) => true,
        Formula::Forall(_, A) => setI(A),
        Formula::Imp(A, B) =>
            setR(A) && setG(B) ||
            setD(A) && setG(B) && setPrint(A) && is_qfree(A) ||
                //setD(A) && setI(A) && setG(B) && setPrint(A) && setPrint(B) ||
                setD(A) && setI(B)
    }
}
fn setR(formula: &Formula) -> bool {
    match formula {
        Formula::Bottom => false,
        Formula::Atom(_) => true,
        Formula::Forall(_, A) => setR(A),
        Formula::Imp(A, B) => setG(A) && setR(B),
    }
}
fn setI(formula: &Formula) -> bool {
    match formula {
        Formula::Bottom => false,
        Formula::Atom(_) => true,
        Formula::Forall(_, A) => setI(A),
        Formula::Imp(A, B) => setD(A) && setI(B),
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
    let S = all(&x, &imp(&imp(&imp(&qx_form, &F), &F), &qx_form));
    let AllQx = all(&x, &qx_form);
    let T = imp(&imp(&AllQx, &bot), &bot);
    let StoT = imp(&S, &T);

    println!("{StoT}");
    println!("{}", setD(&StoT));
    let B = imp(&imp(&qx_form, &bot), &bot);
    println!("{B}");
    println!("{}", setG(&B));
    println!("{}", setD(&B));

}
