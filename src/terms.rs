use std::fmt;
use crate::types::Types;
use crate::types::TypeError;
use std::collections::{HashMap, HashSet};
use std::hash::{Hash, Hasher};


pub type TypeSubstitution = HashMap<usize, Types>;
pub type TermSubstitution = HashMap<ObjVar, Term>;
pub type TermKindSubstitution = HashMap<ObjVar, TermKind>;

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
    pub fn free_type_var(&self) -> HashSet<usize> {
        self.ty.free_var()
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
    pub fn free_type_var(&self) -> HashSet<usize> {
        match self {
            Const::TT => {HashSet::new()},
            Const::FF => {HashSet::new()},
            Const::Zero => {HashSet::new()},
            Const::Succ => {HashSet::new()},
            Const::Nil(ty) => {ty.free_var()}
            Const::Cons(ty) => {ty.free_var()}
            Const::Pair(ty1, ty2) => {
                let mut a = ty1.free_var();
                a.extend(ty2.free_var());
                a
            }
            Const::Split(ty1, ty2, ty3) => {
                let mut a = ty1.free_var();
                a.extend(ty2.free_var());
                a.extend(ty3.free_var());
                a
            }
            Const::Cases(ty) => {ty.free_var()}
            Const::RecNat(ty) => {ty.free_var()}
            Const::RecList(ty1, ty2) => {
                let mut a = ty1.free_var();
                a.extend(ty2.free_var());
                a
            }
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
    TermApp(Box<TermKind>, Box<TermKind>),
    TermAbs(ObjVar, Box<TermKind>),
}

impl TermKind {
    pub fn free_type_var(&self) -> HashSet<usize> {
        match self {
            TermKind::TermVar(u) => u.free_type_var(),
            TermKind::TermConst(c) => c.free_type_var(),
            TermKind::TermApp(a, b) => {
                let mut h = a.free_type_var();
                h.extend(b.free_type_var());
                h
            }
            TermKind::TermAbs(x, a) => {
                let mut h = x.free_type_var();
                h.extend(a.free_type_var());
                h
            }
        }
    }
    pub fn free_var(&self) -> HashSet<ObjVar> {
        match self {
            TermKind::TermVar(u) => [u.clone()].into_iter().collect(),
            TermKind::TermConst(_) => {
                HashSet::new()
            }
            TermKind::TermApp(s, t) => {
                let mut a = s.free_var();
                a.extend(t.free_var());
                a

            }
            TermKind::TermAbs(x, t) => {
                let mut a = t.free_var();
                a.remove(x);
                a
            }
        }
    }
    pub fn subst_type(&self, sigma: &TypeSubstitution) -> Self {
        match self {
            TermKind::TermVar(v) => TermKind::TermVar(v.subst_type(sigma)),
            TermKind::TermConst(c) => TermKind::TermConst(c.subst_type(sigma)),
            TermKind::TermApp(fun, arg) => {
                let a = *fun.clone();
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
        }
    }

    pub fn subst(&self, sigma: &TermKindSubstitution) -> Self {
        match self {
            TermKind::TermVar(v) => match sigma.get(v) {
                Some(t) => t.clone(),
                None => self.clone(),
            }
            TermKind::TermConst(_) => self.clone(),
            TermKind::TermApp(fun, arg) =>
                    TermKind::TermApp(
                    Box::new(fun.subst(sigma)),
                    Box::new(arg.subst(sigma))),
            TermKind::TermAbs(var, body) => {
                let mut set = body.free_var();
                set.remove(var);
                let mut mod_sigma = sigma.clone();
                mod_sigma.remove(var);
                let h: HashSet<TermKind> = mod_sigma.clone().into_values().collect();
                let h2 = free_var(h);
                if h2.contains(&var) {
                    set.extend(h2);
                    let x = new_var(&var.ty, set);
                    mod_sigma.insert(var.clone(), TermKind::TermVar(x.clone()));
                    TermKind::TermAbs(
                        x,
                        Box::new(body.subst(&mod_sigma)))
                } else {
                    TermKind::TermAbs(
                        var.clone(),
                        Box::new(body.subst(&mod_sigma)))
                }
                }
            }
        }
    }

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Term {
    ty: Types,
    kind: TermKind,
}


impl Term {
    pub fn from_kind(kind: &TermKind) -> Result<Self, TypeError> {
        match kind {
            TermKind::TermVar(v) => Ok(Self {
                ty: v.ty().clone(),
                kind: kind.clone(),
            }),
            TermKind::TermConst(c) => Ok(Self {
                ty: c.ty().clone(),
                kind: kind.clone(),
            }),
            TermKind::TermAbs(x, a) => {
                let body_term = Term::from_kind(a)?;
                Ok(Self{
                    ty: Types::Arr(
                        Box::new(x.ty().clone()),
                        Box::new(body_term.ty.clone())),
                    kind: kind.clone(),
                })
            }
            TermKind::TermApp(a, b) => {
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
    pub fn free_var(&self) -> HashSet<ObjVar> {
        self.kind.free_var()
    }
    pub fn abs(var: &ObjVar, t: &Term) -> Self {
        Self{
            ty: Types::Arr(Box::new(var.ty.clone()), Box::new(t.ty.clone())),
            kind: TermKind::TermAbs(var.clone(), Box::new(t.kind.clone())),
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
                        kind: TermKind::TermApp(Box::new(fun.kind.clone()), Box::new(arg.kind.clone())),
                    })
                }
            }
            other => Err(TypeError::ExpectedFunction(other.clone())),
        }
    }

    pub fn subst_type(&self, sigma: &TypeSubstitution) -> Self {
        Self {
            ty: self.ty.subst(sigma),
            kind: self.kind.subst_type(sigma),
        }
    }
    pub fn subst(&self, sigma: &TermSubstitution) -> Result<Term, TypeError> {
        check_term_substitution(sigma)?;
        Ok(self.subst_unchecked(sigma))
    }

    pub fn subst_unchecked(&self, sigma: &TermSubstitution) -> Self {
            todo!()
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
impl fmt::Display for TermKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TermKind::TermVar(v) => write!(f, "{}", v),
            TermKind::TermConst(c) => write!(f, "{}", c),
            TermKind::TermApp(a, b) => write!(f, "({} {})", a, b),
            TermKind::TermAbs(v, b) => write!(f, "(λ{}. {})", v, b),
        }
    }
}
impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.kind.fmt(f)
    }
}

fn free_var(h: HashSet<TermKind>) -> HashSet<ObjVar> {
    let mut set = HashSet::new();
    for t in h {
        set.extend(t.free_var());
    }
    set
}

fn new_var(ty: &Types, h: HashSet<ObjVar>) -> ObjVar {
    let set_id: HashSet<usize> = h
        .iter()
        .cloned()
        .filter(|v| v.ty == *ty)
        .map(|v| v.id)
        .collect();
    let mut id = 0;
    while set_id.contains(&id) {
        id += 1;
    }
    ObjVar::new(id, ty.clone())
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
}