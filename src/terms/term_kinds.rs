use std::collections::{HashMap, HashSet};
use std::fmt;
use crate::types::TypeSubstitution;
use crate::terms::ObjVar;
use crate::terms::Const;
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
}
impl TermKind {
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
                    let fresh_var = crate::terms::new_var(var.ty(), forbidden);
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