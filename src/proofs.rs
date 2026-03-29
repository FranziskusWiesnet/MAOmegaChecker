use std::collections::HashMap;
use crate::formulas::Formula;
use crate::imp;
use crate::terms::{Const, Term, ObjVar};
use crate::types::{TypeError, Types};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct ProofAssumption {
    id: usize,
    Form: Formula,
}

enum Axiom {
    AxTrue,
    BotIntro,
    Case(ObjVar, Formula),
    IndNat(ObjVar, Formula),
    IndList(ObjVar, Formula),
}

impl Axiom  {
    pub fn form(&self) -> Result<Formula,TypeError> {
        match self {
            Axiom::AxTrue => Ok(Formula::verum()),
            Axiom::BotIntro => Ok(imp(&Formula::falsum(),&Formula::Bottom)),
            Axiom::Case(b, form) => {
                if *b.ty() != Types::Boolean {
                    return Err(TypeError::Mismatch {
                        expected: Types::Boolean,
                        found: b.ty().clone(),})
                }
                let sigma = HashMap::from([
                    (b.clone(), Term::constant(Const::TT))
                ]);
                let form_tt = &form.subst(&sigma)?;
                let sigma = HashMap::from([
                    (b.clone(), Term::constant(Const::FF))
                ]);
                let form_ff = &form.subst(&sigma)?;
                Ok(Formula::forall(b,&imp(&form_tt,&imp(&form_ff,&form))))
            }
            Axiom::IndNat(_, _) => {}
            Axiom::IndList(_, _) => {}
        }
    }
}

enum ProofKind {
    Assumption(Formula),
    AxT(Axiom),
    ImpIntro(Box<ProofKind>,Box<ProofKind>),
    ImpElim(Box<ProofKind>,Box<ProofKind>,Box<ProofKind>),
    AllIntro(ObjVar,Box<ProofKind>),
    AllElim(Box<ProofKind>,Term),
}