use std::collections::HashSet;
use std::fmt;
use std::hash::{Hash, Hasher};
use crate::types::{TypeSubstitution, Types};

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
    pub fn free_type_vars(&self) -> HashSet<usize> {
        self.ty.free_vars()
    }
    pub fn subst_type(&self, sigma: &TypeSubstitution) -> Self {
        Self {
            id: self.id,
            ty: self.ty.subst(sigma),
            name: self.name.clone(),
        }
    }
}
pub fn new_var(ty: &Types, h: HashSet<ObjVar>) -> ObjVar {
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