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
    pub fn subst_type_with_env(&self, sigma: &TypeSubstitution, env: &mut HashSet<ObjVar>) -> Self {
        todo!()
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::Types;
    use std::collections::{HashMap, HashSet};
    #[test]
    fn equality_ignores_names() {
        let x = ObjVar::with_name(0, Types::Nat, "x");
        let y = ObjVar::with_name(0, Types::Nat, "y");

        assert_eq!(x, y)
    }
    #[test]
    fn equal_objvars_have_equal_hash() {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};

        let x = ObjVar::with_name(0, Types::Nat, "x");
        let y = ObjVar::with_name(0, Types::Nat, "y");

        let mut hx = DefaultHasher::new();
        x.hash(&mut hx);

        let mut hy = DefaultHasher::new();
        y.hash(&mut hy);

        assert_eq!(hx.finish(), hy.finish());
    }
    #[test]
    fn hashset_identifies_objvars_with_same_id_and_type() {
        let x = ObjVar::with_name(0, Types::Nat, "x");
        let y = ObjVar::with_name(0, Types::Nat, "y");

        let mut set = HashSet::new();
        set.insert(x);
        set.insert(y);

        assert_eq!(set.len(), 1);
    }
    #[test]
    fn objvars_with_same_id_but_different_type_are_different() {
        let x = ObjVar::with_name(0, Types::Nat, "x");
        let y = ObjVar::with_name(0, Types::Boolean, "x");

        assert_ne!(x, y);
    }
    #[test]
    fn free_type_vars_of_ground_typed_variable_is_empty() {
        let x = ObjVar::with_name(0, Types::Nat, "x");

        assert_eq!(x.free_type_vars(), HashSet::new());
    }
    #[test]
    fn free_type_vars_of_variable_collects_type_variables() {
        let ty = Types::arr(
            Types::TypeVar(0),
            Types::pair(Types::TypeVar(1), Types::list(Types::TypeVar(0))));
        let x = ObjVar::with_name(0, ty, "x");

        assert_eq!(x.free_type_vars(), HashSet::from([0, 1]));
    }
    #[test]
    fn subst_type_replaces_type_variables_in_objvar_type() {
        let x = ObjVar::with_name(0,
                                  Types::arr(Types::TypeVar(0),Types::list(Types::TypeVar(1))),
                                  "x");

        let sigma: TypeSubstitution = HashMap::from([
            (0, Types::Nat),
            (1, Types::Boolean)]);

        let expected = ObjVar::with_name(
            0, Types::arr(Types::Nat, Types::list(Types::Boolean)),"x");

        assert_eq!(x.subst_type(&sigma), expected);
    }
    #[test]
    fn new_var_chooses_smallest_fresh_id_of_given_type() {
        let x0 = ObjVar::new(0, Types::Nat);
        let x1 = ObjVar::new(1, Types::Nat);
        let x3 = ObjVar::new(3, Types::Nat);

        let h = HashSet::from([x0, x1, x3]);

        let fresh = new_var(&Types::Nat, h);

        assert_eq!(fresh, ObjVar::new(2, Types::Nat));
    }
    #[test]
    fn new_var_ignores_variables_of_other_types() {
        let n0 = ObjVar::new(0, Types::Nat);
        let b0 = ObjVar::new(0, Types::Boolean);
        let b1 = ObjVar::new(1, Types::Boolean);

        let h = HashSet::from([n0, b0, b1]);

        let fresh = new_var(&Types::Nat, h);

        assert_eq!(fresh, ObjVar::new(1, Types::Nat));
    }

}