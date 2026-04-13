use std::collections::{HashMap, HashSet};
use std::fmt;
use std::hash::{Hash, Hasher};
use crate::types::TypeSubstitution;
use crate::terms::ObjVar;
use crate::terms::Const;
use crate::terms::new_var;
use crate::terms::obj_var::substitution_map;

pub type TermKindSubstitution = HashMap<ObjVar, TermKind>;


#[derive(Debug, Clone)]
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
    pub fn used_var_names(&self) -> HashSet<ObjVar> {
        let mut set = HashSet::new();
        match self {
            TermKind::Var(u) => {set.insert(u.clone());}
            TermKind::Const(_) => {}
            TermKind::Abs(x, t) => {
                set.insert(x.clone());
            set.extend(t.used_var_names());
            }
            TermKind::App(s, t) => {
                set.extend(s.used_var_names());
                set.extend(t.used_var_names());
            }
        }
        set
    }
    pub fn subst_type_with_map(&self,
                               sigma: &TypeSubstitution,
                               var_subst: &HashMap<ObjVar,ObjVar>)
        -> Self {
        match self {
            TermKind::Var(v) => {
                match var_subst.get(v) {
                    Some(x) => TermKind::Var(x.clone()),
                    None => TermKind::Var(v.clone()),
                }
            },
            TermKind::Const(c) => TermKind::Const(c.subst_type(sigma)),
            TermKind::App(fun, arg) => {
                TermKind::app(fun.subst_type_with_map(sigma,var_subst),
                              arg.subst_type_with_map(sigma,var_subst))
            }
            TermKind::Abs(v, body) => {
                match var_subst.get(v) {
                    Some(x) => TermKind::abs(x.clone(),body.subst_type_with_map(sigma,var_subst)),
                    None =>  TermKind::abs(v.clone(),body.subst_type_with_map(sigma,var_subst))
                }

            }
        }
    }

    pub fn subst_type(&self, sigma: &TypeSubstitution) -> Self {
        let used_vars = self.used_var_names();
        let var_subst = substitution_map(&used_vars,&sigma);
        self.subst_type_with_map(sigma, &var_subst)
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
pub fn free_vars(h: HashSet<TermKind>) -> HashSet<ObjVar> {
    let mut set = HashSet::new();
    for t in h {
        set.extend(t.free_vars());
    }
    set
}
impl PartialEq for TermKind {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (TermKind::Var(u), TermKind::Var(v)) => u==v,
            (TermKind::Const(c), TermKind::Const(d)) => c == d,
            (TermKind::App(f, t),
                TermKind::App(g, s)) => f == g && t == s,
            (TermKind::Abs(x, t),
                TermKind::Abs(y, s)) => {
                    if x.ty() != y.ty() {
                        return false;
                    }
                    let mut set = t.free_vars();
                    set.extend(s.free_vars());
                    let fresh_var = new_var(x.ty(), set);
                    let sigma_x: TermKindSubstitution =
                        HashMap::from([(x.clone(),TermKind::Var(fresh_var.clone()))]);
                    let sigma_y:TermKindSubstitution =
                        HashMap::from([(y.clone(),TermKind::Var(fresh_var.clone()))]);
                    t.subst(&sigma_x) == s.subst(&sigma_y)
                }
            _ => false,
            }
        }
    }
impl Eq for TermKind {}
impl Hash for TermKind {
    fn hash<H: Hasher>(&self, state: &mut H) {
        let mut env: HashMap<ObjVar, usize> = HashMap::new();
        self.hash_rec(state, &mut env, 0);
    }
}
impl TermKind {
    pub fn hash_rec<H: Hasher>(
        &self,
        state: &mut H,
        env: &mut HashMap<ObjVar, usize>,
        depth: usize,
    ) {
        match self {
            TermKind::Var(v) => {
                0u8.hash(state);
                if let Some(binder_depth) = env.get(v) {
                    0u8.hash(state);
                    (depth - 1 - binder_depth).hash(state);
                    v.ty().hash(state);
                } else {
                    1u8.hash(state);
                    v.hash(state);
                }
            }
            TermKind::Const(c) => {
                1u8.hash(state);
                c.hash(state);
            }
            TermKind::App(f, a) => {
                2u8.hash(state);
                f.hash_rec(state, env, depth);
                a.hash_rec(state, env, depth);
            }
            TermKind::Abs(x, body) => {
                3u8.hash(state);
                x.ty().hash(state);

                let old = env.insert(x.clone(), depth);
                body.hash_rec(state, env, depth + 1);

                match old {
                    Some(prev) => {
                        env.insert(x.clone(), prev);
                    }
                    None => {
                        env.remove(x);
                    }
                }
            }
        }
    }
}
pub fn free_vars_of_substitution(sigma: &TermKindSubstitution) -> HashSet<ObjVar> {
    let h: HashSet<TermKind> = sigma.clone().into_values().collect();
    free_vars(h)
}
#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::Types;
    use std::collections::{HashMap, HashSet};
    use std::collections::hash_map::DefaultHasher;
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
    fn subst_type_avoids_collision_between_two_free_variables() {
        let alpha = Types::TypeVar(0);
        let nat = Types::Nat;

        let x_alpha = ObjVar::new(0, alpha.clone());
        let x_nat   = ObjVar::new(0, nat.clone());

        let term = TermKind::App(
            Box::new(TermKind::Var(x_alpha.clone())),
            Box::new(TermKind::Var(x_nat.clone())),
        );

        let sigma: TypeSubstitution = HashMap::from([
            (0, nat.clone()),
        ]);

        let result = term.subst_type(&sigma);
        match result {
            TermKind::App(left, right) => {
                match (left.as_ref(), right.as_ref()) {
                    (TermKind::Var(v1), TermKind::Var(v2)) => {

                        assert_ne!(v1, v2);

                        assert_eq!(v2, &x_nat);

                        assert_eq!(v1.ty(), &nat);
                    }
                    _ => panic!("expected two variables"),
                }
            }
            _ => panic!("expected application"),
        }
    }
    #[test]
    fn subst_type_avoids_collision_with_bound_variable() {
        let alpha = Types::TypeVar(0);
        let nat = Types::Nat;

        let x_alpha = ObjVar::new(0, alpha.clone());
        let x_nat   = ObjVar::new(0, nat.clone());

        let term = TermKind::Abs(
            x_alpha.clone(),
            Box::new(TermKind::Var(x_nat.clone())),
        );

        let sigma: TypeSubstitution = HashMap::from([
            (0, nat.clone()),
        ]);

        let result = term.subst_type(&sigma);

        match result {
            TermKind::Abs(bound, body) => {
                assert_eq!(bound.ty(), &nat);

                match body.as_ref() {
                    TermKind::Var(v) => {
                        assert_eq!(v, &x_nat);
                        assert_ne!(&bound, v);
                    }
                    _ => panic!("expected variable in body"),
                }
            }
            _ => panic!("expected abstraction"),
        }
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
    fn hash_of<T: Hash>(x: &T) -> u64 {
        let mut h = DefaultHasher::new();
        x.hash(&mut h);
        h.finish()
    }
    #[test]
    fn alpha_equivalent_abstractions_are_equal() {
        let alpha = Types::TypeVar(0);

        let x = ObjVar::new(0, alpha.clone());
        let y = ObjVar::new(1, alpha.clone());

        let tx = TermKind::abs(x.clone(), TermKind::Var(x.clone()));
        let ty = TermKind::abs(y.clone(), TermKind::Var(y.clone()));

        assert_eq!(tx, ty);
        assert_eq!(hash_of(&tx), hash_of(&ty));
    }
    #[test]
    fn alpha_equivalents_is_type_dependent() {
        let alpha = Types::TypeVar(0);
        let beta = Types::TypeVar(1);

        let x = ObjVar::new(0, alpha.clone());
        let y = ObjVar::new(1, beta.clone());

        let tx = TermKind::abs(x.clone(), TermKind::Var(x.clone()));
        let ty = TermKind::abs(y.clone(), TermKind::Var(y.clone()));

        assert_ne!(tx, ty);
    }
    #[test]
    fn alpha_equivalents_dependents_on_the_abstraction_order() {
        let alpha = Types::TypeVar(0);

        let x = ObjVar::new(0, alpha.clone());
        let y = ObjVar::new(1, alpha.clone());

        let t1 = TermKind::abs(
            x.clone(),
            TermKind::abs(y.clone(), TermKind::Var(x.clone())),
        );

        let t2 = TermKind::abs(
            x.clone(),
            TermKind::abs(y.clone(), TermKind::Var(y.clone())),
        );

        assert_ne!(t1, t2);
    }

}