#![allow(non_snake_case)]
mod types;
mod formulas;
mod proofs;
mod terms;

use crate::types::Types;
use crate::terms::obj_var::ObjVar;
use crate::terms::Term;
use crate::terms::{TermKind, TermKindSubstitution};
use crate::terms::Const;
use crate::formulas::{Formula, isQFree};
use crate::types::Types::TypeVar;
use std::collections::HashMap;


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
    println!("{}", setD(&B));

    let x = ObjVar::new(0, Types::Boolean);
    let y = ObjVar::new(1, Types::Boolean);
    let z = ObjVar::new(2, Types::Boolean);
    let x = ObjVar::with_name(0, Types::Boolean, "x");
    let y = ObjVar::with_name(1, Types::Boolean, "y");

    let t = TermKind::abs(
        y.clone(),
        TermKind::Var(x.clone()),
    );

    let mut sigma: TermKindSubstitution = HashMap::new();
    sigma.insert(x.clone(), TermKind::Var(y.clone()));

    println!("t     = {}", t);
    for (v, s) in &sigma {
        println!("sigma = {} ↦ {}", v, s);
    }

    let result = t.subst(&sigma);
    println!("tσ    = {}", result);
}
