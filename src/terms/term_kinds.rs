use std::collections::{HashMap, HashSet};
use std::fmt;
use crate::types::TypeSubstitution;
use crate::terms::ObjVar;
use crate::terms::Const;
use crate::terms::new_var;
pub type TermKindSubstitution = HashMap<ObjVar, TermKind>;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TermKind {
    Var(ObjVar),
    Const(Const),
    App(Box<TermKind>, Box<TermKind>),
    Abs(ObjVar, Box<TermKind>),
}

impl fmt::Display for TermKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TermKind::Var(v) => write!(f, "{}", v),
            TermKind::Const(c) => write!(f, "{}", c),
            TermKind::App(a, b) => write!(f, "({} {})", a, b),
            TermKind::Abs(v, b) => write!(f, "(λ{}. {})", v, b),
        }
    }
}

impl TermKind {
    pub fn app(from: TermKind, to: TermKind) -> Self {
        TermKind::App(Box::new(from), Box::new(to))
    }
    pub fn abs(var: ObjVar, body: TermKind) -> Self {
        TermKind::Abs(var, Box::new(body))
    }

    pub fn free_type_vars(&self) -> HashSet<usize> {
        match self {
            TermKind::Var(u) => u.free_type_vars(),
            TermKind::Const(c) => c.free_type_vars(),
            TermKind::App(a, b) => {
                let mut h = a.free_type_vars();
                h.extend(b.free_type_vars());
                h
            }
            TermKind::Abs(x, a) => {
                let mut h = x.free_type_vars();
                h.extend(a.free_type_vars());
                h
            }
        }
    }
    pub fn free_vars(&self) -> HashSet<ObjVar> {
        match self {
            TermKind::Var(u) => HashSet::from([u.clone()]),
            TermKind::Const(_) => {
                HashSet::new()
            }
            TermKind::App(s, t) => {
                let mut a = s.free_vars();
                a.extend(t.free_vars());
                a
            }
            TermKind::Abs(x, t) => {
                let mut a = t.free_vars();
                a.remove(x);
                a
            }
        }
    }
    pub fn subst_type(&self, sigma: &TypeSubstitution) -> Self {
        match self {
            TermKind::Var(v) => TermKind::Var(v.subst_type(sigma)),
            TermKind::Const(c) => TermKind::Const(c.subst_type(sigma)),
            TermKind::App(fun, arg) => {
                TermKind::app(fun.subst_type(sigma),arg.subst_type(sigma))
            }
            TermKind::Abs(v, body) => {
                TermKind::abs(v.subst_type(sigma),body.subst_type(sigma))
            }
        }
    }
    pub fn subst(&self, sigma: &TermKindSubstitution) -> Self {
        match self {
            TermKind::Var(v) => match sigma.get(v) {
                Some(t) => t.clone(),
                None => self.clone(),
            }
            TermKind::Const(_) => self.clone(),
            TermKind::App(fun, arg) =>
                TermKind::app(fun.subst(sigma),arg.subst(sigma)),
            TermKind::Abs(var, body) => {
                let mut sigma_wo_var = sigma.clone();
                sigma_wo_var.remove(var);
                let set_fv = free_vars_of_substitution(&sigma_wo_var);
                if set_fv.contains(var) {
                    let mut forbidden = body.free_vars();
                    forbidden.remove(var);
                    forbidden.extend(set_fv);
                    let fresh_var = new_var(var.ty(), forbidden);
                    sigma_wo_var.insert(var.clone(), TermKind::Var(fresh_var.clone()));
                    TermKind::abs(fresh_var,body.subst(&sigma_wo_var))
                } else {
                    TermKind::abs(var.clone(),body.subst(&sigma_wo_var))
                }
            }
        }
    }
}
fn free_vars_of_substitution(sigma: &TermKindSubstitution) -> HashSet<ObjVar> {
    let h: HashSet<TermKind> = sigma.clone().into_values().collect();
    free_vars(h)
}
fn free_vars(h: HashSet<TermKind>) -> HashSet<ObjVar> {
    let mut set = HashSet::new();
    for t in h {
        set.extend(t.free_vars());
    }
    set
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::Types;
    use std::collections::{HashMap, HashSet};
    #[test]
    fn free_type_vars_collects_variables_from_whole_term() {
        let x = ObjVar::with_name(0, Types::TypeVar(0), "x");
        let y = ObjVar::with_name(1, Types::list(Types::TypeVar(1)), "y");

        let t = TermKind::app(
            TermKind::abs(x.clone(), TermKind::Var(x)),
            TermKind::app(
                TermKind::Const(Const::Nil(Types::TypeVar(2))),
                TermKind::Var(y),
            ),
        );

        assert_eq!(t.free_type_vars(), HashSet::from([0, 1, 2]));
    }
    #[test]
    fn free_vars_of_substitution_collects_free_variables_with_abstraction() {
        let x = ObjVar::with_name(0, Types::Nat, "x");
        let y = ObjVar::with_name(1, Types::Nat, "y");
        let z = ObjVar::with_name(2, Types::Nat, "z");
        let u = ObjVar::with_name(3, Types::Nat, "u");

        let sigma: TermKindSubstitution = HashMap::from([
            (x.clone(),
                TermKind::abs(
                    u.clone(),
                    TermKind::app(
                        TermKind::Var(u),
                        TermKind::Var(y.clone())))),
            (z.clone(),
                TermKind::app(
                    TermKind::Var(y.clone()),
                    TermKind::Var(z.clone())))
        ]);

        let expected = HashSet::from([y, z]);

        assert_eq!(free_vars_of_substitution(&sigma), expected);
    }
    #[test]
    fn subst_replaces_variables_recursively() {
        let x = ObjVar::with_name(0, Types::Nat, "x");
        let y = ObjVar::with_name(1, Types::Nat, "y");
        let z = ObjVar::with_name(2, Types::Nat, "z");

        let term = TermKind::app(
            TermKind::Var(x.clone()),
            TermKind::app(TermKind::Var(y.clone()), TermKind::Const(Const::Zero)),
        );

        let sigma: TermKindSubstitution = HashMap::from([
            (x.clone(), TermKind::Var(z.clone())),
            (y.clone(),
                TermKind::app(TermKind::Const(Const::Succ), TermKind::Const(Const::Zero)))
        ]);

        let expected = TermKind::app(
            TermKind::Var(z),
            TermKind::app(
                TermKind::app(TermKind::Const(Const::Succ), TermKind::Const(Const::Zero)),
                TermKind::Const(Const::Zero),
            ),
        );

        assert_eq!(term.subst(&sigma), expected);
    }
    #[test]
    fn subst_avoids_variable_capture_under_abstraction() {
        let x = ObjVar::with_name(0, Types::Nat, "x");
        let y = ObjVar::with_name(1, Types::Nat, "y");

        let term = TermKind::abs(
            y.clone(),
            TermKind::app(TermKind::Var(x.clone()), TermKind::Var(y.clone())),
        );

        let sigma: TermKindSubstitution = HashMap::from([
            (x.clone(), TermKind::Var(y.clone())),
        ]);

        let result = term.subst(&sigma);

        let fresh = crate::terms::new_var(
            &Types::Nat,
            HashSet::from([x.clone(),y.clone()]),
        );

        let expected = TermKind::abs(
            fresh.clone(),
            TermKind::app(TermKind::Var(y), TermKind::Var(fresh)),
        );

        assert_eq!(result, expected);
    }
}