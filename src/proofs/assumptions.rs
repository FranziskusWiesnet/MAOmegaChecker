use std::collections::{HashMap, HashSet};
use std::fmt;
use crate::formulas::Formula;
use crate::terms::{ObjVar, TermSubstitution};
use crate::types::{TypeError, TypeSubstitution};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ProofAssumption {
    id: usize,
    form: Formula,
}
impl fmt::Display for ProofAssumption {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "u_{}", self.id)
    }
}
impl ProofAssumption {
    pub fn id(&self) -> usize {
        self.id
    }
    pub fn form(&self) -> Formula {
        self.form.clone()
    }
    pub fn subst_type(&self, sigma: &TypeSubstitution) -> Self {
        Self {
            id: self.id,
            form: self.form.clone().subst_type(sigma),
        }
    }

    pub fn subst(&self, sigma: &TermSubstitution) -> Result<Self, TypeError> {
        Ok(Self {
            id: self.id,
            form: self.form.clone().subst(sigma)?,
        })
    }
    pub fn new(id: usize, form: Formula) -> Self {
        Self {id, form}
    }
}
pub fn new_assumption(formula: &Formula, h: HashSet<ProofAssumption>) -> ProofAssumption {
    let set_id: HashSet<usize> = h
        .iter()
        .cloned()
        .filter(|v| v.form == *formula)
        .map(|v| v.id)
        .collect();
    let mut id = 0;
    while set_id.contains(&id) {
        id += 1;
    }
    ProofAssumption::new(id, formula.clone())
}
pub fn assumption_map_for_type_subst (used_assumption: &HashSet<ProofAssumption>,
                       sigma: &TypeSubstitution,
                       var_subst: &HashMap<ObjVar,ObjVar>)
    -> HashMap<ProofAssumption,ProofAssumption> {
    let mut forbidden = used_assumption.clone();
    let mut rho: HashMap<ProofAssumption, ProofAssumption> = HashMap::new();
    for u in used_assumption {
        let new_form = u.form.subst_type_with_map(sigma, var_subst);
        if new_form != u.form {
            let fresh_assumption = new_assumption(&new_form, forbidden.clone());
            forbidden.insert(fresh_assumption.clone());
            rho.insert(u.clone(), fresh_assumption);
        }
    }
    rho
}
pub fn assumption_map_for_term_subst (used_assumption: &HashSet<ProofAssumption>,
                                      sigma: &TermSubstitution)
    -> Result<HashMap<ProofAssumption,ProofAssumption>, TypeError> {
    let mut forbidden = used_assumption.clone();
    let mut rho: HashMap<ProofAssumption, ProofAssumption> = HashMap::new();
    for u in used_assumption {
        let new_form = u.form.subst(sigma)?;
        let fresh_assumption = new_assumption(&new_form, forbidden.clone());
        forbidden.insert(fresh_assumption.clone());
        rho.insert(u.clone(), fresh_assumption);
    }
    Ok(rho)
    }
