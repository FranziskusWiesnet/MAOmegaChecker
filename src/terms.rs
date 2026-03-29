use std::fmt;
use crate::types::Types;
use crate::types::TypeError;
use std::collections::HashMap;
use std::hash::{Hash, Hasher};


pub type TypeSubstitution = HashMap<usize, Types>;
pub type TermSubstitution = HashMap<ObjVar, Term>;

#[derive(Debug, Clone)]
pub struct ObjVar {
    id: usize,
    ty: Types,
    name: Option<String>
}

impl PartialEq for ObjVar {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id && self.ty == other.ty
    }
}

impl Eq for ObjVar {}

impl Hash for ObjVar {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.id.hash(state);
        self.ty.hash(state);
    }
}

impl fmt::Display for ObjVar {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.name {
            Some(name) => write!(f, "{}", name),
            None => write!(f, "({})_{}", self.ty, self.id),
        }
    }
}

impl ObjVar {
    pub fn id(&self) -> usize {
        self.id
    }

    pub fn ty(&self) -> &Types {
        &self.ty
    }

    pub fn name(&self) -> Option<&str> {
        self.name.as_deref()
    }
    pub fn new(id: usize, ty: Types) -> Self {
        Self { id, ty, name: None }
    }

    pub fn with_name(id: usize, ty: Types, name: impl Into<String>) -> Self {
        Self {
            id,
            ty,
            name: Some(name.into()),
        }
    }
    pub fn subst_type(&self, sigma: &TypeSubstitution) -> Self {
        Self {
            id: self.id,
            ty: self.ty.subst(sigma),
            name: self.name.clone(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Const {
    TT,
    FF,
    Zero,
    Succ,
    Nil(Types),
    Cons(Types),
    Pair(Types, Types),
    Split(Types, Types, Types),
    Cases(Types),
    RecNat(Types),
    RecList(Types, Types),
}

impl Const {
    pub fn ty(&self) -> Types {
        match self {
            Const::TT => Types::Boolean,

            Const::FF => Types::Boolean,

            Const::Zero => Types::Nat,

            Const::Succ => {Types::Arr(Box::new(Types::Nat), Box::new(Types::Nat))},

            Const::Nil(ty) => Types::List(Box::new(ty.clone())),

            Const::Cons(ty) => {
                Types::Arr(Box::new(ty.clone()), Box::new(
                           Types::Arr(Box::new(Types::List(Box::new(ty.clone()))),
                                      Box::new(Types::List(Box::new(ty.clone()))))))},

            Const::Pair(ty1, ty2) => {
                Types::Arr(Box::new(ty1.clone()), Box::new(
                    Types::Arr(Box::new(ty2.clone()),  Box::new(
                        Types::Pair(Box::new(ty1.clone()), Box::new(ty2.clone()))))))
            },

            Const::Split(ty1, ty2, ty3) => {
                Types::Arr(
                    Box::new(Types::Pair(Box::new(ty1.clone()), Box::new(ty2.clone()))),
                    Box::new(Types::Arr(
                        Box::new(Types::Arr(
                            Box::new(ty1.clone()),
                            Box::new(Types::Arr(Box::new(ty2.clone()), Box::new(ty3.clone()))),
                        )),
                        Box::new(ty3.clone()),
                    )),
                )
            },

            Const::Cases(ty) => {
                Types::Arr(
                    Box::new(Types::Boolean),
                    Box::new(Types::Arr(Box::new(ty.clone()),
                                        Box::new(Types::Arr(Box::new(ty.clone()),
                                                            Box::new(ty.clone()))),
                )),
            )
            },

            Const::RecNat(ty) => Types::Arr(
                Box::new(Types::Nat),
                Box::new(Types::Arr(
                    Box::new(ty.clone()),
                    Box::new(Types::Arr(
                        Box::new(Types::Arr(
                            Box::new(Types::Nat),
                            Box::new(Types::Arr(Box::new(ty.clone()), Box::new(ty.clone()))),
                        )),
                        Box::new(ty.clone()),
                    )),
                )),
            ),

            Const::RecList(t, tau) => Types::Arr(
                Box::new(Types::List(Box::new(t.clone()))),
                Box::new(Types::Arr(
                    Box::new(tau.clone()),
                    Box::new(Types::Arr(
                        Box::new(Types::Arr(
                            Box::new(t.clone()),
                            Box::new(Types::Arr(
                                Box::new(Types::List(Box::new(t.clone()))),
                                Box::new(Types::Arr(Box::new(tau.clone()), Box::new(tau.clone()))),
                            )),
                        )),
                        Box::new(tau.clone()),
                    )),
                )),
            ),
        }
    }
    pub fn subst_type(&self, sigma: &TypeSubstitution) -> Self {
        match self {
            Const::TT => Const::TT,
            Const::FF => Const::FF,
            Const::Zero => Const::Zero,
            Const::Succ => Const::Succ,
            Const::Nil(ty) => Const::Nil(ty.subst(sigma)),
            Const::Cons(ty) => Const::Cons(ty.subst(sigma)),
            Const::Pair(ty1, ty2) => {
                Const::Pair(ty1.subst(sigma), ty2.subst(sigma))
            }
            Const::Split(ty1, ty2, ty3) => {
                Const::Split(ty1.subst(sigma), ty2.subst(sigma), ty3.subst(sigma))
            }
            Const::Cases(ty) => Const::Cases(ty.subst(sigma)),
            Const::RecNat(ty) => Const::RecNat(ty.subst(sigma)),
            Const::RecList(t, tau) => {
                Const::RecList(t.subst(sigma), tau.subst(sigma))
            }
        }
    }

}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TermKind {
    TermVar(ObjVar),
    TermConst(Const),
    TermApp(Box<Term>, Box<Term>),
    TermAbs(ObjVar, Box<Term>),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Term {
    ty: Types,
    kind: TermKind,
}


impl Term {
    pub fn ty(&self) -> &Types {
        &self.ty
    }

    pub fn var(v: &ObjVar) -> Self {
        Self {
            ty: v.ty.clone(),
            kind: TermKind::TermVar(v.clone()),
        }
    }
    pub fn constant(c: Const) -> Self {
        Self {
            ty: c.ty(),
            kind: TermKind::TermConst(c),
        }
    }

    pub fn abs(var: &ObjVar, t: &Term) -> Self {
        Self{
            ty: Types::Arr(Box::new(var.ty.clone()), Box::new(t.ty.clone())),
            kind: TermKind::TermAbs(var.clone(), Box::new(t.clone())),
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
                        kind: TermKind::TermApp(Box::new(fun.clone()), Box::new(arg.clone())),
                    })
                }
            }
            other => Err(TypeError::ExpectedFunction(other.clone())),
        }
    }

    pub fn subst_type(&self, sigma: &TypeSubstitution) -> Self {
        let new_kind = match &self.kind {
            TermKind::TermVar(v) => TermKind::TermVar(v.subst_type(sigma)),
            TermKind::TermConst(c) => TermKind::TermConst(c.subst_type(sigma)),
            TermKind::TermApp(fun, arg) => {
                TermKind::TermApp(
                    Box::new(fun.subst_type(sigma)),
                    Box::new(arg.subst_type(sigma)),
                )
            }
            TermKind::TermAbs(v, body) => {
                TermKind::TermAbs(
                    v.subst_type(sigma),
                    Box::new(body.subst_type(sigma)),
                )
            }
        };

        Self {
            ty: self.ty.subst(sigma),
            kind: new_kind,
        }
    }
    pub fn subst(&self, sigma: &TermSubstitution) -> Result<Term, TypeError> {
        check_term_substitution(sigma)?;
        Ok(self.subst_unchecked(sigma))
    }

    pub fn subst_unchecked(&self, sigma: &TermSubstitution) -> Self {
        match &self.kind {
            TermKind::TermVar(v) => match sigma.get(v) {
                Some(t) => t.clone(),
                None => self.clone(),
            }
            TermKind::TermConst(_) => self.clone(),
            TermKind::TermApp(fun, arg) => Term {
                ty: self.ty.clone(),
                kind: TermKind::TermApp(
                    Box::new(fun.subst_unchecked(sigma)),
                    Box::new(arg.subst_unchecked(sigma)),
                ),
            },
            TermKind::TermAbs(var, body) => {
                let mut restricted_sigma = sigma.clone();
                restricted_sigma.remove(var);
                Term {
                    ty: self.ty.clone(),
                    kind: TermKind::TermAbs(
                        var.clone(),
                        Box::new(body.subst_unchecked(&restricted_sigma)),
                    ),
                }
            }
        }
    }
}

impl fmt::Display for Const {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Const::TT => write!(f, "tt"),
            Const::FF => write!(f, "ff"),
            Const::Zero => write!(f, "0"),
            Const::Succ => write!(f, "S"),
            Const::Nil(ty) => write!(f, "nil_{}", ty),
            Const::Cons(ty) => write!(f, "cons_{}", ty),
            Const::Pair(ty1, ty2) => write!(f, "pair_{{{}, {}}}", ty1, ty2),
            Const::Split(ty1, ty2, ty3) => write!(f, "split_{{{}, {}, {}}}", ty1, ty2, ty3),
            Const::Cases(ty) => write!(f, "cases_{}", ty),
            Const::RecNat(ty) => write!(f, "R_ℕ^{}", ty),
            Const::RecList(arg, rec) => write!(f, "R_𝕃({})^{}", arg, rec),
        }
    }
}
impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.kind {
            TermKind::TermVar(v) => write!(f, "{v}"),
            TermKind::TermConst(c) => write!(f, "{c}"),
            TermKind::TermApp(fun, arg) => write!(f, "({} {})", fun, arg),
            TermKind::TermAbs(v, body) => write!(f, "(λ{}. {})", v, body),
        }
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_objvar_equality_ignores_name() {
        let x1 = ObjVar::with_name(0, Types::Nat, "x");
        let x2 = ObjVar::with_name(0, Types::Nat, "y");
        assert_eq!(x1, x2);
    }

    #[test]
    fn test_term_substitution_variable() {
        let x = ObjVar::with_name(0, Types::Nat, "x");
        let y = ObjVar::with_name(1, Types::Nat, "y");

        let tx = Term::var(&x);
        let ty = Term::var(&y);

        let mut sigma = TermSubstitution::new();
        sigma.insert(x.clone(), ty.clone());

        let result = tx.subst(&sigma).unwrap();
        assert_eq!(result, ty);
    }

    #[test]
    fn test_term_substitution_under_binder() {
        let x = ObjVar::with_name(0, Types::Nat, "x");
        let y = ObjVar::with_name(1, Types::Nat, "y");

        let body = Term::var(&x);
        let abs = Term::abs(&x, &body);
        let ty = Term::var(&y);

        let mut sigma = TermSubstitution::new();
        sigma.insert(x.clone(), ty);

        let result = abs.subst(&sigma).unwrap();

        assert_eq!(result, abs);
    }

    #[test]
    fn test_term_substitution_type_mismatch() {
        let x = ObjVar::with_name(0, Types::Nat, "x");
        let b = ObjVar::with_name(1, Types::Boolean, "b");

        let tx = Term::var(&x);
        let tb = Term::var(&b);

        let mut sigma = TermSubstitution::new();
        sigma.insert(x, tb);

        assert!(tx.subst(&sigma).is_err());
    }
}