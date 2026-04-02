use std::collections::HashMap;
use crate::formulas::Formula;
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
            Axiom::BotIntro => Ok(Formula::imp(Formula::falsum(),Formula::Bottom)),
            Axiom::Case(b, form) => {
                if *b.ty() != Types::Boolean {
                    return Err(TypeError::Mismatch {
                        expected: Types::Boolean,
                        found: b.ty().clone(),})
                }
                let sigma = HashMap::from([
                    (b.clone(), Term::constant(Const::TT))
                ]);
                let form_tt = form.subst(&sigma)?;
                let sigma = HashMap::from([
                    (b.clone(), Term::constant(Const::FF))
                ]);
                let form_ff = form.subst(&sigma)?;
                Ok(Formula::forall(b.clone(),Formula::imp(form_tt,Formula::imp(form_ff,form.clone()))))
            }
            Axiom::IndNat(n, form) => {
                if *n.ty() != Types::Nat {
                    return Err(TypeError::Mismatch {
                        expected: Types::Nat,
                        found: n.ty().clone(),})
                }
                let sigma = HashMap::from([
                    (n.clone(), Term::constant(Const::Zero))
                ]);
                let form_zero = form.subst(&sigma)?;
                let sigma = HashMap::from([
                    (n.clone(), Term::app(&Term::constant(Const::Succ), &Term::var(&n))?)
                ]);
                let form_succ = form.subst(&sigma)?;
                Ok(Formula::forall(n.clone(),
                                   Formula::imp(form_zero,
                                                Formula::imp(Formula::forall(n.clone(),Formula::imp(form.clone(),form_succ)),
                                        form.clone()))))
            }
            Axiom::IndList(_l, _a) => {todo!()}
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