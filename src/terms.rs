use std::fmt;
use crate::types::Types;
use crate::types::TypeError;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ObjVar {
    id: usize,
    ty: Types,
    name: Option<String>
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