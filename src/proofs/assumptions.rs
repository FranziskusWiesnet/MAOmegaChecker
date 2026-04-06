use std::collections::HashSet;
use std::fmt;
use crate::formulas::Formula;
use crate::terms::{TermSubstitution};
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