use itertools::Itertools;

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

pub struct Var {
    pub name: String,
    pub domain: Domain,
}

#[derive(Default)]
pub struct Context {
    pub vars: Vec<Var>,
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
}
