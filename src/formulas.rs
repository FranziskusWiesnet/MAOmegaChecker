use std::collections::{HashMap, HashSet};
use std::fmt;
use std::hash::{Hash, Hasher};
use crate::imp;
use crate::terms::{Const, ObjVar, Term, free_vars_of_substitution,
                   TermSubstitution, TermKindSubstitution, new_var};
use crate::types::{TypeError, Types, TypeSubstitution};

#[derive(Debug, Clone)]
pub enum Formula {
    Atom(Term),
    Imp(Box<Formula>, Box<Formula>),
    Forall(ObjVar, Box<Formula>),
    Bottom,
}


impl fmt::Display for Formula {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Formula::Bottom => write!(f, "⊥"),
            Formula::Atom(t) => {
                if *t == Term::constant(Const::FF) {
                    write!(f, "F")
                } else {
                    write!(f, "{}",t)}},
            Formula::Imp(a, b) => write!(f, "({} -> {})", a, b),
            Formula::Forall(x, a) => write!(f, "(∀ {}. {})", x, a),
        }
    }
}
impl Formula {
    pub fn atom(t: &Term) -> Result<Self, TypeError> {
        if *t.ty() != Types::Boolean {
            return Err(TypeError::ExpectedBoolean(t.ty().clone()));
        }
        Ok(Formula::Atom(t.clone()))
    }
    pub fn imp(a: Formula, b: Formula) -> Self {
        Formula::Imp(Box::new(a), Box::new(b))
    }
    pub fn forall(x: ObjVar, a: Formula) -> Self {
        Formula::Forall(x.clone(), Box::new(a))
    }
    pub fn falsum() -> Self { Formula::Atom(Term::constant(Const::FF)) }
    pub fn verum() -> Self { Formula::Atom(Term::constant(Const::TT)) }

    pub fn F(&self) -> Self {
        match self {
            Formula::Bottom => Formula::falsum(),
            Formula::Atom(_) => self.clone(),
            Formula::Imp(a, b) => Formula::Imp(Box::new(a.F()), Box::new(b.F())),
            Formula::Forall(x, a) => Formula::Forall(x.clone(), Box::new(a.F())),
        }
    }
    pub fn free_type_vars(&self) -> HashSet<usize> {
        match self {
            Formula::Atom(t) => t.free_type_vars(),
            Formula::Imp(prem, concl) => {
                let mut set = prem.free_type_vars();
                set.extend(concl.free_type_vars());
                set
            }
            Formula::Forall(var, body) => {
                let mut set = var.free_type_vars();
                set.extend(body.free_type_vars());
                set
            }
            Formula::Bottom => HashSet::new()
        }
    }
    pub fn free_vars(&self) -> HashSet<ObjVar> {
        match self {
            Formula::Atom(t) => t.free_vars(),
            Formula::Imp(prem, concl) => {
                let mut set = prem.free_vars();
                set.extend(concl.free_vars());
                set
            }
            Formula::Forall(var, body) => {
                let mut set = body.free_vars();
                set.remove(var);
                set
            }
            Formula::Bottom => HashSet::new()
        }
    }
    pub fn used_var_names(&self) -> HashSet<ObjVar> {
        match self {
            Formula::Atom(t) => t.used_var_names(),
            Formula::Imp(prem, conclusion) => {
                let mut set = prem.used_var_names();
                set.extend(conclusion.used_var_names());
                set
            }
            Formula::Forall(var, body) => {
                let mut set = body.used_var_names();
                set.insert(var.clone());
                set
            }
            Formula::Bottom => HashSet::new()
        }
    }
}

impl Formula {
    pub fn subst_type_with_map(&self,
                               sigma: &TypeSubstitution,
                               var_subst: &HashMap<ObjVar,ObjVar>) -> Self {
        match self {
            Formula::Atom(t) => {
                Formula::Atom(t.subst_type_with_map(sigma, var_subst))
            }
            Formula::Imp(a, b) => Formula::Imp(
                Box::new(a.subst_type_with_map(sigma, var_subst)),
                Box::new(b.subst_type_with_map(sigma, var_subst)),
            ),

            Formula::Forall(v, f) =>
                match var_subst.get(v) {
                    Some(var) =>
                        Formula::Forall(var.clone(),
                                        Box::new(f.subst_type_with_map(sigma, var_subst))),
                    None => Formula::Forall(v.clone(),
                                            Box::new(f.subst_type_with_map(sigma, var_subst)))
                }
            Formula::Bottom => Formula::Bottom,
        }
    }

    pub fn subst_type(&self, sigma: &TypeSubstitution) -> Formula {
        match self {
            Formula::Atom(t) => Formula::Atom(t.subst_type(sigma)),

            Formula::Imp(a, b) => Formula::Imp(
                Box::new(a.subst_type(sigma)),
                Box::new(b.subst_type(sigma)),
            ),

            Formula::Forall(v, f) => Formula::Forall(
                v.subst_type(sigma),
                Box::new(f.subst_type(sigma)),
            ),

            Formula::Bottom => Formula::Bottom,
        }
    }
    pub fn subst(&self, sigma: &TermSubstitution) -> Result<Formula, TypeError> {
        match self {
            Formula::Atom(t) =>
                {
                    let s = t.subst(sigma)?;
                    Ok(Formula::Atom(s))
                },

            Formula::Imp(a, b) =>
                {
                    // In both cases, we check the substitution.
                    // This could probably be done more efficiently.
                    let s = a.subst(sigma)?;
                    let t = b.subst(sigma)?;
                    Ok(Formula::imp(s,t))
                }

            Formula::Forall(var, body) => {
                let mut sigma_wo_var = sigma.clone();
                sigma_wo_var.remove(var);
                let sigma_kind: TermKindSubstitution =
                    sigma_wo_var.iter()
                        .map(|(k, t)| (k.clone(), t.kind().clone()))
                        .collect();
                let set_fv = free_vars_of_substitution(&sigma_kind);
                if set_fv.contains(&var) {
                    let mut forbidden = body.free_vars();
                    forbidden.extend(set_fv);
                    let fresh_var = new_var(var.ty(), forbidden);
                    sigma_wo_var.insert(var.clone(), Term::var(&fresh_var));
                    let body_subst = body.subst(&sigma_wo_var)?;
                    Ok(Formula::forall(fresh_var, body_subst))

                } else {
                    let body_subst = body.subst(&sigma_wo_var)?;
                    Ok(Formula::forall(var.clone(), body_subst))
                }

            }
            Formula::Bottom => Ok(Formula::Bottom),
        }
    }
}

impl PartialEq for Formula {
    fn eq(&self, other: &Formula) -> bool {
        match (self,other) {
            (Formula::Bottom, Formula::Bottom) => true,
            (Formula::Atom(a), Formula::Atom(b)) => a == b,
            (Formula::Imp(a,b),
                Formula::Imp(c,d)) => a == c && d == b,
            (Formula::Forall(x,a),
                Formula::Forall(y,b)) => {
                if x.ty() != y.ty() {
                    return false;
                }
                let mut set = a.free_vars();
                set.extend(b.free_vars());
                let fresh_var = new_var(x.ty(), set);
                let sigma_x: TermSubstitution =
                    HashMap::from([(x.clone(),Term::var(&fresh_var.clone()))]);
                let sigma_y: TermSubstitution =
                    HashMap::from([(y.clone(),Term::var(&fresh_var.clone()))]);
                a.subst(&sigma_x) == b.subst(&sigma_y)
            }
            _ => false,
        }
    }
}
impl Eq for Formula {}

impl Hash for Formula {
    fn hash<H: Hasher>(&self, state: &mut H) {
        let mut env: HashMap<ObjVar, usize> = HashMap::new();
        self.hash_rec(state, &mut env, 0);
    }
}
impl Formula {
    fn hash_rec<H: Hasher>(&self, state: &mut H, env: &mut HashMap<ObjVar, usize>, depth: usize) {
        match self {
            Formula::Bottom => {
                0u8.hash(state);
            },
            Formula::Atom(t) => {
                1u8.hash(state);
                t.ty().hash(state);
                t.kind().hash_rec(state, env, depth);
            }
            Formula::Imp(a,b) => {
                2u8.hash(state);
                a.hash_rec(state, env, depth);
                b.hash_rec(state, env, depth);
            }
            Formula::Forall(v,body) => {
                3u8.hash(state);
                v.ty().hash(state);
                let old = env.insert(v.clone(), depth);
                body.hash_rec(state, env, depth + 1);
                match old {
                    Some(prev) => {env.insert(v.clone(), prev);}
                    None => {env.remove(v);}
                }
            }
        }
    }
}

impl Formula {
    pub(crate) fn kernel(&self) -> Formula {
        match self {
            Formula::Forall(_,body) => {
                body.kernel()
            }
            _=> self.clone(),

        }
    }
}


pub fn is_qfree(formula: &Formula) -> bool {
    match formula {
        Formula::Bottom => true,
        Formula::Atom(_) => true,
        Formula::Forall(_, _) => false,
        Formula::Imp(g, h) => is_qfree(&g) && is_qfree(&h),
    }
}

pub fn Stab(formula: &Formula) -> Formula {
    let F = Formula::Atom(Term::ff());
    imp(&imp(&imp(formula,&F),&F),formula)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::{HashMap,HashSet};
    use crate::terms::{ObjVar, Term};
    use crate::types::Types;

    #[test]
    fn free_type_vars_collects_from_atoms_implications_and_binders() {
        // type variables: 1, 2, 3
        let alpha = Types::TypeVar(1);
        let beta  = Types::TypeVar(2);
        let gamma = Types::TypeVar(3);

        let x = ObjVar::new(0, alpha.clone());
        let y = ObjVar::new(0, beta.clone());
        let z = ObjVar::new(0, gamma.clone());

        let f = ObjVar::new(0, Types::arr(alpha.clone(),Types::Boolean));
        let g = ObjVar::new(0, Types::arr(beta.clone(),Types::Boolean));

        let fx = Term::app(&Term::var(&f),&Term::var(&x)).unwrap();
        let gy = Term::app(&Term::var(&g),&Term::var(&y)).unwrap();
        // Atomic formulas with free type vars {1} and {2}
        let form_fx = Formula::atom(&fx).unwrap();
        let form_gy = Formula::atom(&gy).unwrap();


        let imp = Formula::imp(form_fx, form_gy);

        let formula = Formula::forall(z, imp);

        let expected: HashSet<usize> = HashSet::from([1, 2, 3]);

        assert_eq!(formula.free_type_vars(), expected);
    }
    #[test]
    fn subst_type_replaces_types_in_atoms_implications_and_binders() {
        let alpha = Types::TypeVar(1);
        let beta  = Types::TypeVar(2);
        let gamma = Types::TypeVar(3);

        let x = ObjVar::new(0, alpha.clone());
        let y = ObjVar::new(0, beta.clone());
        let z = ObjVar::new(0, gamma.clone());

        let f = ObjVar::new(0, Types::arr(alpha.clone(), Types::Boolean));
        let g = ObjVar::new(0, Types::arr(beta.clone(), Types::Boolean));
        let h = ObjVar::new(0, Types::arr(gamma.clone(), Types::Boolean));

        let fx = Term::app(&Term::var(&f), &Term::var(&x)).unwrap();
        let gy = Term::app(&Term::var(&g), &Term::var(&y)).unwrap();
        let hz = Term::app(&Term::var(&h), &Term::var(&z)).unwrap();

        let form_fx = Formula::atom(&fx).unwrap();
        let form_gy = Formula::atom(&gy).unwrap();
        let form_hz = Formula::atom(&hz).unwrap();

        let formula = Formula::forall(
            z.clone(),
            Formula::imp(form_fx, Formula::imp(form_hz, form_gy)),
        );

        let expected: HashSet<ObjVar> =
            HashSet::from([x.clone(), y.clone(), f.clone(), g.clone(), h.clone()]);

        assert_eq!(formula.free_vars(), expected);

        let sigma: TypeSubstitution = HashMap::from([
            (1, Types::Boolean),
            (3, Types::arr(Types::Boolean, Types::Boolean)),
        ]);

        let result = formula.subst_type(&sigma);

        let x_sub = ObjVar::new(0, Types::Boolean);
        let y_sub = ObjVar::new(0, beta.clone());
        let z_sub = ObjVar::new(0, Types::arr(Types::Boolean, Types::Boolean));

        let f_sub = ObjVar::new(0, Types::arr(Types::Boolean, Types::Boolean));
        let g_sub = ObjVar::new(0, Types::arr(beta.clone(), Types::Boolean));
        let h_sub = ObjVar::new(
            0,
            Types::arr(Types::arr(Types::Boolean, Types::Boolean), Types::Boolean),
        );

        let fx_sub = Term::app(&Term::var(&f_sub), &Term::var(&x_sub)).unwrap();
        let gy_sub = Term::app(&Term::var(&g_sub), &Term::var(&y_sub)).unwrap();
        let hz_sub = Term::app(&Term::var(&h_sub), &Term::var(&z_sub)).unwrap();

        let expected = Formula::forall(
            z_sub,
            Formula::imp(
                Formula::atom(&fx_sub).unwrap(),
                Formula::imp(
                    Formula::atom(&hz_sub).unwrap(),
                    Formula::atom(&gy_sub).unwrap(),
                ),
            ),
        );

        assert_eq!(result, expected);
    }
    #[test]
    fn subst_avoids_variable_capture_under_forall() {
        let alpha = Types::TypeVar(1);

        let x = ObjVar::new(0, alpha.clone());
        let y = ObjVar::new(1, alpha.clone());
        let p = ObjVar::new(0, Types::arr(alpha.clone(), Types::Boolean));

        let px = Term::app(&Term::var(&p), &Term::var(&x)).unwrap();
        let py = Term::app(&Term::var(&p), &Term::var(&y)).unwrap();

        let formula = Formula::forall(
            y.clone(),
            Formula::imp(
                Formula::atom(&px).unwrap(),
                Formula::atom(&py).unwrap(),
            ),
        );

        let sigma: TermSubstitution =
            HashMap::from([(x.clone(), Term::var(&y))]);

        let result = formula.subst(&sigma).unwrap();

        match result {
            Formula::Forall(bound, body) => {
                assert_ne!(bound, y);

                let expected_left = Formula::atom(&py).unwrap();
                let expected_right_term =
                    Term::app(&Term::var(&p), &Term::var(&bound)).unwrap();
                let expected_right = Formula::atom(&expected_right_term).unwrap();

                assert_eq!(
                    *body,
                    Formula::imp(expected_left, expected_right)
                );
            }
            _ => panic!("Expected a universally quantified formula"),
        }
    }
}