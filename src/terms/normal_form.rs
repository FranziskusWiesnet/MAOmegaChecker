use std::collections::HashMap;
use crate::terms::{TermKind, TermKindSubstitution};

impl TermKind {
    fn beta_normalize(&self) -> Self {
        match self {
            TermKind::App(t,s) => {
                let t_red = t.beta_normalize();
                let s_red = s.beta_normalize();
                match t_red {
                    TermKind::Abs(u,body) => {
                        let sigma: TermKindSubstitution = HashMap::from([(u,s_red)]);
                        body.subst(&sigma).beta_normalize()

                    }
                    _ => TermKind::app(t_red,s_red)
                }
            }
            TermKind::Abs(u,s) => {
                let s_red = s.beta_normalize();
                TermKind::Abs(u.clone(), Box::new(s_red))
            }
            _ => self.clone(),

        }
    }
}



#[cfg(test)]
mod tests {
    use crate::terms::{Const, ObjVar, Term};
    use crate::types::Types;
    use super::*;
    fn app(t: TermKind, s: TermKind) -> TermKind {
        TermKind::app(t, s)
    }
    fn abs(x: &ObjVar, t: TermKind) -> TermKind {
        TermKind::abs(x.clone(), t)
    }
    fn var(v: &ObjVar) -> TermKind {
        TermKind::Var(v.clone())
    }
    fn succ(t: TermKind) -> TermKind {
        app(TermKind::Const(Const::Succ), t)
    }
    fn zero() -> TermKind {
        TermKind::Const(Const::Zero)
    }
    #[test]
    fn test_beta_red() {
        let f = ObjVar::with_name(0, Types::arr(Types::Nat, Types::Nat), "f");
        let x = ObjVar::with_name(0, Types::Nat, "x");
        let y = ObjVar::with_name(1, Types::Nat, "y");
        let z = ObjVar::with_name(2, Types::Nat, "z");

        let term =
            app(
                abs(&f,
                    abs(&x,
                        app(var(&f),
                            app(
                                abs(&y, var(&y)),
                                var(&x))))),
                abs(&z,
                    succ(succ(var(&z)))),
            );
        println!("{}",term.beta_normalize());
    }
    #[test]
    fn test_long_term_for_beta_red(){
        let f = ObjVar::with_name(0, Types::arr(Types::Nat, Types::Nat), "f");
        let g = ObjVar::with_name(1, Types::arr(Types::Nat, Types::Nat), "g");
        let x = ObjVar::with_name(0, Types::Nat, "x");
        let y = ObjVar::with_name(1, Types::Nat, "y");
        let u = ObjVar::with_name(2, Types::Nat, "u");
        let v = ObjVar::with_name(3, Types::Nat, "v");

        let term =
            app(
                app(
                    abs(&g, abs(&x,
                                app(abs(&u,
                                        succ(var(&u))),
                                    app(var(&g),
                                        app(abs(&y,
                                                var(&y)),
                                            var(&x)))))),
                    abs(&v, succ(succ(var(&v)))),
                ),
                zero(),
            );
        // (((λg. (λx. ((λu. (S u)) (g ((λy. y) x))))) (λv. (S (S v)))) 0)
        let proper_term = Term::from_kind(&term).unwrap();
        assert_eq!(term.beta_normalize(),succ(succ(succ(zero()))));
        assert_eq!(proper_term.ty().clone(),Types::Nat)
    }
    #[test]
    fn beta_red_form_non_noralisable_term() {
        let x = ObjVar::with_name(0, Types::Nat, "x");

        let omega = app(abs(&x,app(var(&x),var(&x))),abs(&x,app(var(&x),var(&x))));
        // ((λx. (x x)) (λx. (x x)))

        let fail = Term::from_kind(&omega).unwrap_err();
        println!("{}",fail)
    }
}
