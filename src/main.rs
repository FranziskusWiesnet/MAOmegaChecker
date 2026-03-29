#![allow(non_snake_case)]

mod types;
mod terms;
mod formulas;

use std::fmt;
use crate::types::Types;
use crate::terms::ObjVar;
use crate::terms::Term;
use crate::terms::Const;
use crate::formulas::{Formula, isQFree};
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
            setD(A) && setG(B) && setPrint(A) && isQFree(A) ||
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
    let A: Formula =  Formula::Atom(Term::var(&ObjVar::new(0, Types::Boolean)));
    let xi = TypeVar(0);
    let x = ObjVar::new(0,xi);
    let S = all(&x, &imp(&imp(&imp(&A,&F),&F),&A));
    let AllA = all(&x,&A);
    let T = imp(&imp(&AllA,&bot),&bot);
    let StoT = imp(&S,&T);
    //println!("{}", imp(&T.F(),&T));
    println!("{StoT}");
    println!("{}", setD(&StoT));
    let B = imp(&imp(&A,&bot),&bot);
    println!("{B}");
    println!("{}", setG(&B));
}
