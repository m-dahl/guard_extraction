use itertools::Itertools;
use std::collections::HashMap;
use crate::bdd_context::{BDDContext, ExprType};

#[derive(Debug, Clone, PartialEq)]
pub enum Ex {
    AND(Vec<Ex>),
    OR(Vec<Ex>),
    NOT(Box<Ex>),
    TRUE,
    FALSE,
    VAR(usize), // index in context
    EQ(usize, Value)
}

#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    Bool(bool), // special case for booleans
    InDomain(usize), // index into domain
    Var(usize),   // value of other variable
    Free,        // for free actions.
}

#[derive(Debug, Clone, PartialEq)]
pub struct Ac {
    pub var: usize, // index in context
    pub val: Value,
}

pub enum Domain {
    Bool,
    Enum(usize)
}

pub (crate) struct Var {
    pub name: String,
    pub domain: Domain,
}

pub (crate) struct Trans {
    pub (crate) name: String,
    pub (crate) guard: Ex,
    pub (crate) actions: Vec<Ac>,
}

#[derive(Default)]
pub struct Context {
    pub (crate) vars: Vec<Var>,
    pub (crate) c_trans: Vec<Trans>,
    pub (crate) uc_trans: Vec<Trans>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Lit {
    pub var: usize, // variable index
    pub neg: bool,  // negated?
}

#[derive(Debug, Clone, PartialEq)]
pub struct Clause(pub Vec<Lit>);

#[derive(Debug, Clone, PartialEq)]
pub struct SATModel {
    pub num_vars: usize,
    pub model_clauses: Vec<Clause>,
    pub norm_vars: Vec<usize>,
    pub next_vars: Vec<usize>,
    pub init_clauses: Vec<Clause>,
    pub goal_clauses: Vec<Clause>,
    pub goal_tops: Vec<Lit>,
    pub invar_clauses: Vec<Clause>,
    pub invar_tops: Vec<Lit>,
}

impl Context {
    pub fn get_var(&self, name: &str) -> usize {
        self.vars.iter().position(|v| v.name == name).unwrap()
    }

    pub fn add_bool(&mut self, name: &str) -> usize {
        self.vars.push(Var { name: name.to_owned(), domain: Domain::Bool });
        self.vars.len() - 1
    }

    pub fn add_enum(&mut self, name: &str, domain: usize) -> usize {
        self.vars.push(Var { name: name.to_owned(), domain: Domain::Enum(domain) });
        self.vars.len() - 1
    }

    pub fn add_c_trans(&mut self, name: &str, guard: &Ex, actions: &[Ac]) {
        self.c_trans.push(Trans { name: name.into(), guard: guard.clone(), actions: actions.to_vec() });
    }

    pub fn add_uc_trans(&mut self, name: &str, guard: &Ex, actions: &[Ac]) {
        self.uc_trans.push(Trans { name: name.into(), guard: guard.clone(), actions: actions.to_vec() });
    }

    pub fn pretty_print(&self, expr: &Ex) -> String {
        match expr {
            Ex::AND(v) => {
                format!("( {} )", v.iter().map(|e|self.pretty_print(e)).join(" && "))
            },
            Ex::OR(v) => {
                format!("( {} )", v.iter().map(|e|self.pretty_print(e)).join(" || "))
            },
            Ex::NOT(e) => {
                format!("!( {} )", self.pretty_print(e))
            },
            Ex::FALSE => "F".to_string(),
            Ex::TRUE => "T".to_string(),
            Ex::VAR(var) =>
                self.vars.get(*var).map(|v|v.name.clone()).unwrap_or(format!("{}", var)),
            Ex::EQ(var, value) => {
                let var = self.vars.get(*var).map(|v|v.name.clone()).unwrap_or(format!("{}", var));
                match value {
                    Value::Bool(true) => var,
                    Value::Bool(false) => format!("!{}", var),
                    Value::InDomain(v) => format!("{} == {}", var, *v),
                    Value::Var(other) => {
                        let other = self.vars.get(*other)
                            .map(|v|v.name.clone())
                            .unwrap_or(format!("{}", other));
                        format!("{} == {}", var, other)
                    },
                    Value::Free => format!("{} == [anything]", var),
                }
            }
        }
    }

    pub fn model_as_sat_model(&self, init: &Ex, goals: &[(Ex,Ex)]) -> SATModel {
        let b = buddy_rs::take_manager(10000, 10000);
        let mut bc = BDDContext::from(&self, &b);

        let init = bc.from_expr(&init);

        let goals: Vec<(buddy_rs::BDD, buddy_rs::BDD)> = goals
            .iter()
            .map(|(i,g)|(bc.from_expr(&i),bc.from_expr(&g)))
            .collect();

        let model = bc.model_as_satmodel(&init, &goals);

        drop(bc);
        buddy_rs::return_manager(b);
        model
    }

    pub fn compute_guards(&self, initial: &Ex, forbidden: &Ex) -> (HashMap<String, Ex>, Ex) {
        let b = buddy_rs::take_manager(10000, 10000);
        let mut bc = BDDContext::from(&self, &b);

        let forbidden = bc.from_expr(&forbidden);
        let initial = bc.from_expr(&initial);
        let (_reachable, bad, controllable) = bc.controllable(&initial, &forbidden);

        let new_guards = bc.compute_guards(&controllable, &bad);

        let supervisor = bc.to_expr(&controllable, ExprType::DNF);

        let new_guards = new_guards.into_iter()
            .map(|(name,guard)| {
                let dnf = bc.to_expr(&guard, ExprType::DNF);
                let cnf = bc.to_expr(&guard, ExprType::CNF);
                let dnf_size = self.pretty_print(&dnf).len();
                let cnf_size = self.pretty_print(&cnf).len();
                let guard = if cnf_size < dnf_size {
                    cnf
                } else {
                    dnf
                };
                (name, guard)
            }).collect();


        // must drop the context first to release the sets and pairs
        drop(bc);
        buddy_rs::return_manager(b);

        (new_guards, supervisor)
    }

    pub fn extend_forbidden(&self, forbidden: &Ex) -> Ex {
        let b = buddy_rs::take_manager(10000, 10000);
        let mut bc = BDDContext::from(&self, &b);

        let forbidden = bc.from_expr(&forbidden);

        let new_forbidden = bc.extend_forbidden(&forbidden);
        let new_forbidden = bc.to_expr(&new_forbidden, ExprType::DNF);

        // must drop the context first to release the sets and pairs
        drop(bc);
        buddy_rs::return_manager(b);

        new_forbidden
    }
}
