#![allow(non_snake_case)]

mod types;
mod terms;
mod formulas;

use std::fmt;
use crate::types::Types;
use crate::terms::ObjVar;


#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum Formula {
    Atom(u16), // Atom(0) := ⊥ und Atom(1) := False
    Imp(Box<Formula>, Box<Formula>),
    Forall(u16, Box<Formula>),
}

impl fmt::Display for Formula {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Formula::Atom(0) => write!(f, "⊥"),
            Formula::Atom(1) => write!(f, "F"),
            Formula::Atom(n) => write!(f, "A{}", n-2),
            Formula::Imp(a, b) => write!(f, "({} -> {})", a, b),
            Formula::Forall(x, a) => write!(f, "(∀ x{}. {})", x, a),
        }
    }
}

impl Formula {
    fn F(&self) -> Formula {
        match self {
            Formula::Atom(0) => Formula::Atom(1),
            Formula::Atom(n) => Formula::Atom(*n),
            Formula::Imp(a, b) => imp(&a.F(),&b.F()),
            Formula::Forall(x, a) => all(*x,&a.F()),
        }
    }
}

fn imp(A: &Formula, B: &Formula) -> Formula {
    Formula::Imp(Box::new(A.clone()), Box::new(B.clone()))
}

fn all(x: u16, A: &Formula) -> Formula {
    Formula::Forall(x, Box::new(A.clone()))
}

fn isQFree(formula: &Formula) -> bool {
        match formula {
        Formula::Atom(_) => true,
        Formula::Forall(_, _) => false,
        Formula::Imp(g, h) => isQFree(&g) && isQFree(&h),
        }
}

fn setD(formula: &Formula) -> bool {
    match formula {
        Formula::Atom(_) => true,
        Formula::Forall(_, A) => setD(A) || setR(A),
        Formula::Imp(A, B) => setI(A) && setD(B) || setG(A) && setR(B),
    }
}

fn setPrint(formula: &Formula) -> bool {
    println!("{}", formula);
    true
}
fn setG(formula: &Formula) -> bool {
    match formula {
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
        Formula::Atom(n) => *n == 0,
        Formula::Forall(_, A) => setR(A),
        Formula::Imp(A, B) => setG(A) && setR(B),
    }
}
fn setI(formula: &Formula) -> bool {
    match formula {
        Formula::Atom(n) => *n != 0,
        Formula::Forall(_, A) => setI(A),
        Formula::Imp(A, B) => setD(A) && setI(B),
    }
}

fn main() {
    let bot = Formula::Atom(0);
    let F = Formula::Atom(1);
    let A = Formula::Atom(2);
    let S = all(0, &imp(&imp(&imp(&A,&F),&F),&A));
    let AllA = all(0,&A);
    let T = imp(&imp(&AllA,&bot),&bot);
    let StoT = imp(&S,&T);
    //println!("{}", imp(&T.F(),&T));
    println!("{StoT}");
    println!("{}", setD(&StoT));
    println!("{}", setD(&imp(&imp(&A,&bot),&bot)));
    let x = ObjVar::new(0, Types::Nat);
    let y = ObjVar::with_name(1, Types::Boolean, "y");

    println!("{}", x); // x0
    println!("{}", y); // y1
}
