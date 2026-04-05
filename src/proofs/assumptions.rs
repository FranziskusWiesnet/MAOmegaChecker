use std::fmt;
use crate::formulas::Formula;
use crate::types::TypeSubstitution;

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
    pub fn new(id: usize, form: Formula) -> Self {
        Self {id, form}
    }
}