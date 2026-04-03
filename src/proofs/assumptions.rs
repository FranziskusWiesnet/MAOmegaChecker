use std::fmt;
use crate::formulas::Formula;
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
    pub fn new(id: usize, form: Formula) -> Self {
        Self {id, form}
    }
}