use std::collections::HashMap;
use crate::terms::{TermKind, TermKindSubstitution};

impl TermKind {
    fn beta_red(&self) -> Self {
        match self {
            TermKind::App(t,s) => {
                let t_red = t.beta_red();
                let s_red = s.beta_red();
                match t_red {
                    TermKind::Abs(u,body) => {
                        let sigma: TermKindSubstitution = HashMap::from([(u,s_red)]);
                        body.subst(&sigma).beta_red()

                    }
                    _ => TermKind::app(t_red,s_red)
                }
            }
            TermKind::Abs(u,s) => {
                let s_red = s.beta_red();
                TermKind::Abs(u.clone(), Box::new(s_red))
            }
            _ => self.clone(),

        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn test_beta_red() {
        
    }

}
