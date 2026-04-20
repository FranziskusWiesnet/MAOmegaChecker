use std::collections::{HashMap, HashSet};
use std::fmt;
use std::hash::{Hash, Hasher};
use crate::formulas::Formula;
use crate::terms::{new_var, Const, ObjVar, Term, TermSubstitution};
use crate::terms::obj_var::substitution_map;
use crate::terms::typed_terms::free_vars_of_term_substitution;
use crate::types::{TypeError, TypeSubstitution, Types};
#[derive(Debug, Clone)]
pub enum Axiom {
    AxTrue,
    BotIntro,
    Case(ObjVar, Formula),
    Ind(ObjVar, Formula),
}

impl fmt::Display for Axiom {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Axiom::AxTrue => write!(f, "AxT"),
            Axiom::BotIntro => write!(f, "⊥+"),
            Axiom::Case(obj_var, formula) => write!(f, "𝒞({obj_var}.{formula})"),
            Axiom::Ind(obj_var, formula) => write!(f, "𝓘𝓷𝓭({obj_var}.{formula})"),
        }
    }
}

impl Axiom {
    pub fn form(&self) -> Result<Formula,TypeError> {
        match self {
            Axiom::AxTrue => Ok(Formula::verum()),
            Axiom::BotIntro => Ok(Formula::imp(Formula::falsum(),Formula::Bottom)),
            Axiom::Case(b, form) => {
                if *b.ty() != Types::Boolean {
                    return Err(TypeError::Mismatch {
                        expected: Types::Boolean,
                        found: b.ty().clone(),})
                }
                let sigma: TermSubstitution = HashMap::from([
                    (b.clone(), Term::constant(Const::TT))]);
                let form_tt = form.subst(&sigma)?;
                let sigma: TermSubstitution = HashMap::from([
                    (b.clone(), Term::constant(Const::FF))
                ]);
                let form_ff = form.subst(&sigma)?;
                Ok(Formula::forall(b.clone(),
                                   Formula::imp(form_tt, Formula::imp(form_ff,form.clone()))))
            }
            Axiom::Ind(var, form) => {
                match var.ty() {
                    Types::Nat => {
                        let sigma: TermSubstitution = HashMap::from(
                            [(var.clone(),Term::constant(Const::Zero))]);
                        let form_zero = form.subst(&sigma)?;
                        let succ_var = Term::app(&Term::constant(Const::Succ),
                                                 &Term::var(var))?;
                        let sigma: TermSubstitution = HashMap::from(
                            [(var.clone(),succ_var)]);
                        let form_succ_var = form.subst(&sigma)?;
                        Ok(
                            Formula::forall(var.clone(),
                                        Formula::imp(form_zero, Formula::imp(
                                            Formula::forall(var.clone(),
                                                            Formula::imp(form.clone(),
                                                                         form_succ_var)),
                                        form.clone()))))
                    }
                    Types::List(tau) => {
                        let sigma: TermSubstitution = HashMap::from(
                            [(var.clone(),Term::constant(Const::Nil(tau.as_ref().clone())))]);
                        let form_nil = form.subst(&sigma)?;
                        let fv = form.free_vars();
                        let fresh_var = new_var(tau, fv);
                        let cons_fresh_var =
                            Term::app(&Term::app(
                                &Term::constant(Const::Cons(tau.as_ref().clone())),
                                &Term::var(&fresh_var))?,&Term::var(&var))?;
                        let sigma: TermSubstitution = HashMap::from(
                            [(var.clone(),cons_fresh_var)]);
                        let form_cons_fresh_var = form.subst(&sigma)?;
                        let step = Formula::forall(
                            fresh_var.clone(),
                            Formula::forall(
                                var.clone(),
                                Formula::imp(form.clone(), form_cons_fresh_var)
                                ));
                        Ok(Formula::forall(var.clone(),
                                           Formula::imp(form_nil,
                                                        Formula::imp(step,form.clone()))))
                    }
                    _ => Err(TypeError::ExpectedInd(var.ty().clone()))
                }
            }
        }
    }
    pub fn free_type_vars(&self) -> HashSet<usize> {
        match self {
            Axiom::AxTrue => HashSet::new(),
            Axiom::BotIntro => HashSet::new(),
            Axiom::Case(b, form) => {
                let mut set = form.free_type_vars();
                set.extend(b.free_type_vars());
                set
            }
            Axiom::Ind(var, form) => {
                let mut set = form.free_type_vars();
                set.extend(var.free_type_vars());
                set
            }
        }
    }
    pub fn used_var_names(&self) -> HashSet<ObjVar> {
        let mut set = HashSet::new();
        match self {
            Axiom::AxTrue => {},
            Axiom::BotIntro => {},
            Axiom::Case(b, form) => {
                set.extend(form.used_var_names());
                set.insert(b.clone());
            }
            Axiom::Ind(var, form) => {
                set.extend(form.used_var_names());
                set.insert(var.clone());
            }
        }
        set
    }
    pub fn subst_type_with_map(&self,
                               sigma: &TypeSubstitution,
                               var_subst: &HashMap<ObjVar,ObjVar>) -> Self {
        match self {
            Axiom::AxTrue => Axiom::AxTrue,
            Axiom::BotIntro => Axiom::BotIntro,
            Axiom::Case(b, form) => {
                match var_subst.get(b) {
                    Some(var) => {
                        Axiom::Case(var.clone(), form.subst_type_with_map(sigma, var_subst))
                    },
                    None => {
                        Axiom::Case(b.clone(), form.subst_type_with_map(sigma, var_subst))
                    },
                }
            }
            Axiom::Ind(v, form) => {
                match var_subst.get(v) {
                    Some(var) => {
                        Axiom::Ind(var.clone(), form.subst_type_with_map(sigma, var_subst))
                    }
                    None => {
                        Axiom::Ind(v.clone(), form.subst_type_with_map(sigma, var_subst))
                    }
                }
            }
        }
    }

    pub fn subst_type(&self, sigma: &TypeSubstitution) -> Self {
        let used_vars = self.used_var_names();
        let substitution_map = substitution_map(&used_vars,sigma);
        self.subst_type_with_map(sigma, &substitution_map)
    }
    
    pub fn free_vars(&self) -> HashSet<ObjVar> {
        let mut set = HashSet::new();
        match self {
            Axiom::AxTrue => {},
            Axiom::BotIntro => {},
            Axiom::Case(b, form) => {
                set.extend(form.free_vars());
                set.remove(b);
            }
            Axiom::Ind(var, form) => {
                set.extend(form.free_vars());
                set.remove(var);
            }
        }
        set
    }
    pub fn bounded_vars(&self) -> HashSet<ObjVar> {
        let mut set = HashSet::new();
        match self {
            Axiom::AxTrue => {},
            Axiom::BotIntro => {},
            Axiom::Case(b, form) => {
                set.extend(form.bounded_vars());
                set.insert(b.clone());
            }
           Axiom::Ind(var, form) => {
               set.extend(form.bounded_vars());
               set.insert(var.clone());
           } 
        }
        set
    }

    pub fn subst(&self, sigma: &TermSubstitution) -> Result<Self,TypeError> {
        match self {
            Axiom::AxTrue => Ok(Axiom::AxTrue),
            Axiom::BotIntro => Ok(Axiom::BotIntro),
            Axiom::Case(b, form) => {
                let mut sigma_wo_var = sigma.clone();
                sigma_wo_var.remove(b);
                let set_fv = free_vars_of_term_substitution(&sigma_wo_var);
                if set_fv.contains(b) {
                    let mut forbidden = form.free_vars();
                    forbidden.extend(set_fv);
                    let fresh_var = new_var(b.ty(), forbidden);
                    sigma_wo_var.insert(b.clone(), Term::var(&fresh_var));
                    Ok(Axiom::Case(fresh_var,form.subst(&sigma_wo_var)?))
                } else {
                    Ok(Axiom::Case(b.clone(), form.subst(&sigma_wo_var)?))
                }
            }
            Axiom::Ind(var, form) => {
                let mut sigma_wo_var = sigma.clone();
                sigma_wo_var.remove(var);
                let set_fv = free_vars_of_term_substitution(&sigma_wo_var);
                if set_fv.contains(var) {
                    let mut forbidden = form.free_vars();
                    forbidden.extend(set_fv);
                    let fresh_var = new_var(var.ty(), forbidden);
                    sigma_wo_var.insert(var.clone(), Term::var(&fresh_var));
                    Ok(Axiom::Ind(fresh_var,form.subst(&sigma_wo_var)?))
                } else {
                    Ok(Axiom::Ind(var.clone(), form.subst(&sigma_wo_var)?))
                }
            }
        }
    }
}
impl PartialEq for Axiom {
    fn eq(&self, other: &Axiom) -> bool {
        match (self,other) {
            (Axiom::AxTrue,Axiom::AxTrue) => true,
            (Axiom::BotIntro,Axiom::BotIntro) => true,
            (Axiom::Case(b0,a0),Axiom::Case(b1,a1)) => {
            Formula::forall(b0.clone(),a0.clone()) == Formula::forall(b1.clone(),a1.clone())
            }
            (Axiom::Ind(var0,a0),Axiom::Ind(var1,a1)) => {
                Formula::forall(var0.clone(),a0.clone()) == Formula::forall(var1.clone(),a1.clone())
            }
            _ => false,
        }
    }
}
impl Eq for Axiom {}

impl Hash for Axiom {
    fn hash<H: Hasher>(&self, state: &mut H) {
        match self {
            Axiom::AxTrue => {
                0u8.hash(state);
            }
            Axiom::BotIntro => {
                1u8.hash(state);
            }
            Axiom::Case(b, a) => {
                2u8.hash(state);
                Formula::forall(b.clone(), a.clone()).hash(state);
            }
            Axiom::Ind(var, a) => {
                3u8.hash(state);
                Formula::forall(var.clone(), a.clone()).hash(state);
            }
        }
    }
}


#[cfg(test)]
mod tests {
    use super::*;
    use crate::formulas::Formula;
    use crate::terms::{TermKind,ObjVar};
    use crate::types::{TypeError, Types};

    #[test]
    fn ax_true_has_verum_formula() {
        let ax = Axiom::AxTrue;

        let form = ax.form().unwrap();

        assert_eq!(form, Formula::verum());
    }
    #[test]
    fn bot_intro_has_expected_formula() {
        let ax = Axiom::BotIntro;

        let form = ax.form().unwrap();

        assert_eq!(
            form,
            Formula::imp(Formula::falsum(), Formula::Bottom)
        );
    }
    #[test]
    fn case_on_boolean_variable_builds_expected_formula() {
        let b = ObjVar::with_name(0, Types::Boolean, "b");
        let f = ObjVar::with_name(0,
                                  Types::arr(Types::Boolean, Types::Boolean),
                                  "f");

        let fb = Term::from_kind(&TermKind::app(
            TermKind::Var(f.clone()),
            TermKind::Var(b.clone()),
        ))
            .unwrap();

        let form = Formula::Atom(fb);

        let ax = Axiom::Case(b.clone(), form.clone());
        let result = ax.form().unwrap();

        let expected= "(∀ b. ((f tt) -> ((f ff) -> (f b))))";

        assert_eq!(result.to_string(), expected);
    }
    #[test]
    fn case_on_non_boolean_variable_returns_type_error() {
        let n = ObjVar::with_name(0, Types::Nat, "n");
        let form = Formula::Atom(Term::var(&n));
        let ax = Axiom::Case(n.clone(), form);

        let err = ax.form().unwrap_err();

        assert_eq!(
            err,
            TypeError::Mismatch {
                expected: Types::Boolean,
                found: Types::Nat,
            }
        );
    }
    #[test]
    fn ind_on_nat_builds_expected_formula() {
        let n = ObjVar::with_name(0, Types::Nat, "n");
        let f = ObjVar::with_name(0, Types::arr(Types::Nat,Types::Boolean), "A");
        let form = Formula::Atom(Term::app(&Term::var(&f),&Term::var(&n)).unwrap());
        let ax = Axiom::Ind(n.clone(), form.clone());

        let result = ax.form().unwrap();
        let expected = "(∀ n. ((A 0) -> ((∀ n. ((A n) -> (A (S n)))) -> (A n))))";

        assert_eq!(result.to_string(), expected);
    }
    #[test]
    fn ind_on_invalid_type_returns_error() {
        let b = ObjVar::with_name(0, Types::Boolean, "b");
        let form = Formula::Atom(Term::var(&b));
        let ax = Axiom::Ind(b.clone(), form);

        let err = ax.form().unwrap_err();

        assert_eq!(err, TypeError::ExpectedInd(Types::Boolean));
    }
    #[test]
    fn ind_on_list_builds_expected_formula() {
        let l = ObjVar::with_name(0, Types::list(Types::Nat), "l");
        let f =  ObjVar::with_name(0,
                                   Types::arr(Types::list(Types::Nat),Types::Boolean), "A");
        let form = Formula::Atom(Term::app(&Term::var(&f),&Term::var(&l)).unwrap());
        let ax = Axiom::Ind(l.clone(), form.clone());
        let result = ax.form().unwrap();
        let expected =
            "(∀ l. ((A nil_ℕ) -> ((∀ (ℕ)_0. (∀ l. ((A l) -> (A ((cons_ℕ (ℕ)_0) l))))) -> (A l))))";
        assert_eq!(result.to_string(), expected);
    }
    }

