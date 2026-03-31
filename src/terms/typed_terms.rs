use std::fmt;
use std::fmt::Debug;
use std::collections::{HashMap, HashSet};
use crate::terms::{TermKind,ObjVar,Const,TermKindSubstitution};
use crate::types::{Types,TypeError,TypeSubstitution};

pub type TermSubstitution = HashMap<ObjVar, Term>;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Term {
    ty: Types,
    kind: TermKind,
}
impl Term {
    pub fn from_kind(kind: &TermKind) -> Result<Self, TypeError> {
        match kind {
            TermKind::Var(v) => Ok(Self {
                ty: v.ty().clone(),
                kind: kind.clone(),
            }),
            TermKind::Const(c) => Ok(Self {
                ty: c.ty().clone(),
                kind: kind.clone(),
            }),
            TermKind::Abs(x, a) => {
                let body_term = Term::from_kind(a)?;
                Ok(Self{
                    ty: Types::arr(x.ty().clone(),body_term.ty.clone()),
                    kind: kind.clone(),
                })
            }
            TermKind::App(a, b) => {
                let fun_term = Term::from_kind(a)?;
                let arg_term = Term::from_kind(b)?;
                match fun_term.ty() {
                    Types::Arr(dom, img) => {
                        if **dom != arg_term.ty {
                            Err(TypeError::Mismatch {
                                expected: (**dom).clone(),
                                found: arg_term.ty.clone(),
                            })
                        } else {
                            Ok(Self {
                                ty: (**img).clone(),
                                kind: kind.clone(),
                            })
                        }
                    }
                    other => Err(TypeError::ExpectedFunction(other.clone())),
                }
            }
        }
    }
    pub fn var(v: &ObjVar) -> Self {
        Self {
            ty: v.ty().clone(),
            kind: TermKind::Var(v.clone()),
        }
    }
    pub fn constant(c: Const) -> Self {
        Self {
            ty: c.ty(),
            kind: TermKind::Const(c),
        }
    }
    pub fn abs(var: &ObjVar, t: &Term) -> Self {
        Self{
            ty: Types::arr(var.ty().clone(), t.ty().clone()),
            kind: TermKind::abs(var.clone(), t.kind.clone()),
        }
    }
    pub fn app(fun: &Term, arg: &Term) -> Result<Self, TypeError> {
        match &fun.ty {
            Types::Arr(dom, codom) => {
                if **dom != arg.ty {
                    Err(TypeError::Mismatch {
                        expected: (**dom).clone(),
                        found: arg.ty.clone(),
                    })
                }
                else {
                    Ok(Self{
                        ty: (**codom).clone(),
                        kind: TermKind::App(Box::new(fun.kind.clone()), Box::new(arg.kind.clone())),
                    })
                }
            }
            other => Err(TypeError::ExpectedFunction(other.clone())),
        }
    }
    pub fn ty(&self) -> &Types {
        &self.ty
    }
    pub fn free_var(&self) -> HashSet<ObjVar> {
        self.kind.free_vars()
    }
}

pub fn check_term_substitution(sigma: &TermSubstitution) -> Result<(), TypeError> {
    for (v, t) in sigma {
        if v.ty() != t.ty() {
            return Err(TypeError::Mismatch {
                expected: v.ty().clone(),
                found: t.ty().clone(),
            });
        }
    }
    Ok(())
}
impl Term {
    pub fn subst_type(&self, sigma: &TypeSubstitution) -> Self {
        Self {
            ty: self.ty.subst(sigma),
            kind: self.kind.subst_type(sigma),
        }
    }

    pub fn subst(&self, sigma: &TermSubstitution) -> Result<Self, TypeError> {
        check_term_substitution(sigma)?;

        let sigma_on_kinds: TermKindSubstitution = sigma
            .iter()
            .map(|(var, term)| (var.clone(), term.kind.clone()))
            .collect();

        Ok(Self {
            ty: self.ty.clone(),
            kind: self.kind.subst(&sigma_on_kinds),
        })
    }
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.kind)
    }
}