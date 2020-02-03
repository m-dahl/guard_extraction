use boolean_expression::*;
use std::collections::HashMap;
use std::collections::HashSet;
use std::iter::FromIterator;
use itertools::Itertools;

mod bdd_helpers;
pub use bdd_helpers::*;

mod bdd_domain;
pub use bdd_domain::*;


fn reach(bdd: &buddy_rs::BDDManager, initial: &buddy_rs::BDD,
         forward_trans: &buddy_rs::BDD, vars: &buddy_rs::BDD, pair: &buddy_rs::BDDPair) -> buddy_rs::BDD {
    let mut r = initial.clone();
    loop {
        let old = r;
        let new = bdd.relprod(&old, forward_trans, vars);
        let new = bdd.replace(&new, pair);
        r = bdd.or(&old, &new);

        if old == r {
            break;
        }
    }
    r
}

// compute controllability and return the forbidden states
pub fn ctrl2(
    bdd: &buddy_rs::BDDManager, forbidden: &buddy_rs::BDD,
    backward_unc_trans: &buddy_rs::BDD, vars: &buddy_rs::BDD, pair: &buddy_rs::BDDPair)
    -> buddy_rs::BDD {
    let mut fx = forbidden.clone();
    loop {
        let old = fx;
        let new = bdd.relprod(&old, backward_unc_trans, vars);
        let new = bdd.replace(&new, pair);
        fx = bdd.or(&old, &new);

        if old == fx {
            break;
        }
    }
    fx
}

fn compute_minimal_guard(
    b: &mut BDD,
    orig_guard: BDDFunc,
    new_guard: BDDFunc,
    trans: BDDFunc,
    bt: BDDFunc, // TODO these
    good_states: BDDFunc,
    bad_states: BDDFunc,
    vars: &[BDDLabel],
    pairing: &[(BDDLabel, BDDLabel)],
    temps: &[BDDLabel],
) -> BDDFunc {
    let forbx = relprod(b, bad_states, bt, vars);
    let mut forbx = replace(b, forbx, pairing);

    let tie = terms_in_bddfunc(b, orig_guard);

    // now hack f out of x
    // TODO: revisit this... need to think about this again
    let mut xx = new_guard;
    xx = exist(b, xx, &tie);
    forbx = exist(b, forbx, &tie);

    // assert that my thinking is correct...
    let tot = b.and(xx, orig_guard);
    assert_eq!(tot, new_guard);

    // guard need to stop us from reaching forbidden
    forbx = b.not(forbx);

    let f_and_forb = b.and(trans, forbx);
    let bt = swap(b, f_and_forb, &pairing, &temps);
    // assert that my thinking is correct...
    assert_eq!(relprod(b, bad_states, bt, &vars), BDD_ZERO);

    // chose the smallest guard representation in terms of terminals used
    let tie_x = terms_in_bddfunc(b, xx);
    let tie_y = terms_in_bddfunc(b, forbx);
    let (new_guard, new_terms) = if tie_x.len() <= tie_y.len() {
        (xx, tie_x)
    } else {
        println!("chosing forbidden");
        (forbx, tie_y)
    };

    // try to remove terms that doesnt lead us to a forbidden state
    // and doesn't over-constrain us wrt the reachable states
    let temp = b.and(trans, new_guard);
    let bt = swap(b, temp, &pairing, &temps);
    let z = relprod(b, good_states, bt, &vars);

    let mut ntps = powerset(&new_terms);
    let _all = ntps.pop(); // no use trying to remove all terms
    ntps.reverse(); // remove the largest amount of terms first,
                    // stop as soon as we succeed

    let ntps = vec![new_terms.clone()];
    let mut cache = HashMap::new();
    for s in ntps {
        // remove elemts in s
        let mut temp_ng = new_guard;
        temp_ng = exist(b, temp_ng, &s);
        // for t in &s {
        //     let sf = b.restrict(temp_ng, *t, false);
        //     let st = b.restrict(temp_ng, *t, true);
        //     temp_ng = b.or(sf, st);
        // }

        // check if still works and cache result
        let temp = b.and(trans, temp_ng);

        let ok = match cache.get(&temp) {
            Some(&ok) => ok,
            None => {
                let bt = swap(b, temp, &pairing, &temps);
                let y = relprod(b, bad_states, bt, &vars); //was bad
                let y = replace(b, y, &pairing);
                let y = b.and(y, good_states);

                let ok = if y == BDD_ZERO {
                    let zz = relprod(b, good_states, bt, &vars);
                    z == zz // no loss of permissiveness
                } else {
                    false
                };
                cache.insert(temp, ok);
                ok
            }
        };

        if ok {
            // println!("choosing: {:?} out of {:?}", s, _all);
            return temp_ng; // greedy done, dont search all
        }
    }

    // nothing better found
    return new_guard;
}

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
    Bool(bool), // special case for booleans?
    InDomain(usize), // index into domain
    Var(usize),   // value of other variable
}

pub enum Domain {
    Bool,
    Enum(usize)
}

pub struct Var {
    name: String,
    domain: Domain,
}

pub struct Context {
    pub vars: Vec<Var>,

}

impl Context {
    pub fn new() -> Self {
        Context { vars: Vec::new() }
    }

    pub fn get_var(&self, name: &str) -> usize {
        self.vars.iter().position(|v| v.name == name).unwrap()
    }

    pub fn add_bool(&mut self, name: &str) -> usize {
        self.vars.push(Var { name: name.to_owned(), domain: Domain::Bool });
        return self.vars.len() - 1
    }

    pub fn add_enum(&mut self, name: &str, domain: usize) -> usize {
        self.vars.push(Var { name: name.to_owned(), domain: Domain::Enum(domain) });
        return self.vars.len() - 1
    }

    pub fn pretty_print(&self, expr: &Ex) -> String {
        match expr {
            Ex::AND(v) => {
                v.iter().map(|e|self.pretty_print(e)).join(" && ")
            },
            Ex::OR(v) => {
                v.iter().map(|e|self.pretty_print(e)).join(" || ")
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
                    Value::Bool(true) => format!("{}", var),
                    Value::Bool(false) => format!("!{}", var),
                    Value::InDomain(v) => format!("{} == {}", var, *v),
                    Value::Var(other) => {
                        let other = self.vars.get(*other)
                            .map(|v|v.name.clone())
                            .unwrap_or(format!("{}", other));
                        format!("{} == {}", var, other)
                    },
                }
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum BDDVarType {
    Bool,
    Enum(BDDDomain)
}

#[derive(Debug, Clone)]
pub struct BDDVar {
    orig_var_id: usize,
    bdd_var_id: usize,
    var_type: BDDVarType
}

#[derive(Debug, Clone)]
pub struct BDDContext {
    pub b: BDD,
    pub vars: Vec<BDDVar>,
    pub num_vars: usize,
    pub destvars: Vec<BDDLabel>,
    pub temps: Vec<BDDLabel>,
    pub pairing: Vec<(BDDLabel,BDDLabel)>,
    pub transitions: HashMap<String, BDDFunc>,
    pub uc_transitions: HashMap<String, BDDFunc>,
}

impl BDDContext {
    // TODO: the litterature is fairly decided on using an interleaved
    // variable ordering for better performance. for now we just put all
    // next values at the end.
    pub fn from(c: &Context) -> Self {
        let mut b = BDD::new();
        let mut vars = Vec::new();
        let mut offset = 0; // keep track of last added variable
        for (i, v) in c.vars.iter().enumerate() {
            match v.domain {
                Domain::Bool => {
                    let var = BDDVar { orig_var_id: i, bdd_var_id: offset,
                                       var_type: BDDVarType::Bool };
                    vars.push(var);
                    offset += 1;
                },
                Domain::Enum(n) => {
                    let domain = BDDDomain::new(&mut b, n, offset);
                    let bs = domain.binsize;
                    let var = BDDVar { orig_var_id: i, bdd_var_id: offset,
                                       var_type: BDDVarType::Enum(domain) };
                    offset += bs;
                    vars.push(var);
                }
            }
        }

        let num_vars = offset;
        let destvars: Vec<_> = (0..num_vars).map(|i| i + num_vars).collect();
        let temps: Vec<_> = (0..num_vars).map(|i| i + 2 * num_vars).collect();
        let pairing: Vec<_> = (0..num_vars)
            .zip(destvars.iter())
            .map(|(x, y)| (x, *y))
            .collect();

        BDDContext {
            b,
            vars,
            num_vars: num_vars,
            destvars: destvars,
            temps: temps,
            pairing: pairing,
            transitions: HashMap::new(),
            uc_transitions: HashMap::new(),
        }
    }

    pub fn term_orig_to_bdd(&self, t: usize) -> usize {
        self.vars.iter().find(|v| v.orig_var_id == t).unwrap().bdd_var_id
    }
    pub fn term_bdd_to_orig(&self, t: usize) -> usize {
        self.vars.iter().find(|v| v.bdd_var_id == t).unwrap().orig_var_id
    }

    pub fn from_expr(&mut self, e: &Ex) -> BDDFunc {
        println!("from expr");
        match e {
            Ex::AND(v) => {
                let mut x = BDD_ONE;
                for a in v {
                    let a = self.from_expr(a);
                    x = self.b.and(x, a);
                }
                x
            },
            Ex::OR(v) => {
                let mut x = BDD_ZERO;
                for a in v {
                    let a = self.from_expr(a);
                    x = self.b.or(x, a);
                }
                x
            },
            Ex::NOT(x) => {
                let xval = self.from_expr(x);
                self.b.not(xval)
            },
            Ex::TRUE => self.b.constant(true),
            Ex::FALSE => self.b.constant(false),
            Ex::VAR(t) => {
                // typecheck to make sure VAR is a boolean
                // domains can only be used for equality checks
                let v = self.vars.iter().find(|v| v.orig_var_id == *t).unwrap();
                assert!(v.var_type == BDDVarType::Bool);
                self.b.terminal(v.bdd_var_id)
            },
            Ex::EQ(var, value) => {
                // handle bools and enums separately
                let v = self.vars.iter().find(|v| v.orig_var_id == *var).unwrap();

                match v.var_type {
                    BDDVarType::Bool => {
                        let bv = self.b.terminal(v.bdd_var_id);

                        match value {
                            Value::Bool(true) => bv,
                            Value::Bool(false) => self.b.not(bv),
                            Value::InDomain(_n) => panic!("bool does not have a domain!"),
                            Value::Var(other) => {
                                let ov = self.vars.iter().find(|v| v.orig_var_id == *other).unwrap();
                                // other var needs to be a bool also
                                assert!(ov.var_type == BDDVarType::Bool);

                                // ok, now encode logical equivalence
                                let ov = self.b.terminal(ov.bdd_var_id);
                                let nbv = self.b.not(bv);
                                let nov = self.b.not(ov);
                                let bv_and_ov = self.b.and(bv,ov);
                                let nbv_and_nov = self.b.and(nbv, nov);

                                // bv <-> ov
                                self.b.or(bv_and_ov, nbv_and_nov)
                            },
                        }
                    },
                    BDDVarType::Enum(ref bdddom) => {

                        match value {
                            Value::Bool(_b) => panic!("not a boolean!"),
                            Value::InDomain(n) => {
                                // check if value is in domain...
                                assert!(*n<bdddom.size);

                                let f = bdddom.digit(&mut self.b, *n);
                                // let fe = self.b.to_expr(f, self.num_vars);
                                // println!("DIGIT EXPR ({}): {:?}", *n, fe);
                                f
                            },
                            Value::Var(other) => {
                                // check that other value is also an enum
                                let ov = self.vars.iter().find(|v| v.orig_var_id == *other).unwrap();
                                // other var needs to be a bool also
                                if let BDDVarType::Enum(ref od) = ov.var_type {
                                    // ensure the same number of bdd terminals
                                    assert!(bdddom.binsize == od.binsize);
                                    bdddom.equals(od, &mut self.b)
                                    // panic!("domain assignment is todo!");
                                } else {
                                    panic!("other needs to be enum also...");
                                }

                            }
                        }

                    },
                }
            },
        }
    }


    pub fn to_expr(&mut self, f: BDDFunc) -> Ex {
        let num_vars = self.num_vars;
        let domains: Vec<_> = self.vars.iter().filter_map(|v| {
            match &v.var_type {
                BDDVarType::Enum(d) => Some(d.clone()),
                _ => None
            }
        }).collect();

        let cubes = self.b.to_max_cubes(f, num_vars);

        // println!("-------------- TO EXPR ---------------");
        // println!("{:?}", cubes);
        let mut remaining_added: Vec<_> = cubes.cubes().map(|c| (c.clone(), Vec::new())).collect();

        for d in domains {
            let mut next = remaining_added.clone();
            next.sort_by(|a, b| b.0.cmp(&a.0));
            remaining_added.clear();
            for (key, group) in &next.iter().group_by(|&(c,s)| {
                let mut c = c.clone();
                for i in 0..d.binsize {
                    c = c.with_var(i + d.offset, CubeVar::DontCare);
                }
                (c,s)
            }) {
                let mut allowed = BDD_ONE;
                let g: Vec<_> = group.cloned().collect();
                // println!("GROUP: {:?}", g);
                g.into_iter().for_each(|c| {
                    let mut allowed_cube = BDD_ZERO;
                    c.0.vars().enumerate().for_each(|(i, v)| match v {
                        &CubeVar::False if d.belongs(i) => {
                            let t = self.b.terminal(i);
                            let nt = self.b.not(t);
                            allowed_cube = self.b.or(allowed_cube, nt);
                        },
                        &CubeVar::True if d.belongs(i) => {
                            let t = self.b.terminal(i);
                            allowed_cube = self.b.or(allowed_cube, t);
                        },
                        _ => {} ,
                    });
                    allowed = self.b.and(allowed, allowed_cube);
                });
                let v = d.allowed_values(&mut self.b, allowed);
                // println!("xxx:  {} -- {} ", v.len(), d.size);
                let s =
                    if v.len() == d.size {
                        // println!(" new case: v({}) IN {:?} OR {:?}", d.offset, v, key.1);
                        key.1.clone()
                    } else
                    if v.len() > 0 {
                        // println!("d IN {:?} AND ", v);
                        // println!(" v({}) IN {:?} OR {:?}", d.offset, v, key.1);
                        let var = self.term_bdd_to_orig(d.offset);
                        // TODO: here we should check if its shorter to write the negation of an expr
                        let indomain = if v.len() > 1 {
                            // println!("v len more than one");
                            Ex::OR(v.iter().map(|v| Ex::EQ(var, Value::InDomain(*v))).collect())
                        } else {
                            // println!("v len not more than one");
                            Ex::EQ(var, Value::InDomain(v[0]))
                        };
                        let mut new = key.1.clone();
                        new.push(indomain);
                        new
                    } else {
                        // println!("AND");
                        key.1.clone()
                    };
                // println!("{:?} - {:?}", key, v);

                remaining_added.push((key.0, s));
            }
        }

        // for (cube, domains) in &remaining_added {
        //     cube.vars().enumerate().for_each(|(i, v)| match v {
        //         &CubeVar::False => print!(" NOT {} OR", i),
        //         &CubeVar::True => print!(" {} OR", i),
        //         _ => {},
        //     });
        //     print!("{:?}", domains);
        //     println!(" AND ");
        // }

        let ands = remaining_added.iter().flat_map(|(cube, enums)| {
            let mut ors: Vec<_> = cube.vars().enumerate().flat_map(|(i, v)| {
                match v {
                    &CubeVar::False => {
                        let orig_v = self.term_bdd_to_orig(i);
                        Some(Ex::NOT(Box::new(Ex::VAR(orig_v))))
                    },
                    &CubeVar::True => {
                        let orig_v = self.term_bdd_to_orig(i);
                        Some(Ex::VAR(orig_v))
                    },
                    _ => None,
                }}).collect();
            if enums.len() > 1 {
                ors.push(Ex::OR(enums.clone()));
            } else if enums.len() > 0 {
                ors.push(enums[0].clone());
            }

            if ors.len() > 1 {
                Some(Ex::OR(ors))
            } else if ors.len() == 1{
                Some(ors[0].clone())
            } else {
                // panic!("should not happen {:?}", remaining_added);
                None
            }
        }).collect();
        Ex::AND(ands)
    }

    fn make_trans(&mut self, guard: BDDFunc, action: BDDFunc) -> BDDFunc {
        let vl = self.num_vars;

        let vs: HashSet<BDDLabel> = HashSet::from_iter(0..vl);
        let t = terms_in_bddfunc(&mut self.b, action);
        let ts = HashSet::from_iter(t.iter().cloned());

        let not_updated: Vec<_> = vs.difference(&ts).cloned().collect();

        let iffs = not_updated.iter().fold(BDD_ONE, |acc, i| {
            let a = self.b.terminal(*i);
            let na = self.b.not(a);
            let b = self.b.terminal(*i + vl);
            let nb = self.b.not(b);
            let a_and_b = self.b.and(a, b);
            let na_and_nb = self.b.and(na, nb);
            let iff = self.b.or(a_and_b, na_and_nb);

            self.b.and(acc, iff)
        });

        let action = swap(&mut self.b, action, &self.pairing, &self.temps); // change action to next indexes

        // return guards + action + additional iffs for keeping others unchanged
        let trans = self.b.and(guard, action);

        self.b.and(trans, iffs)
    }


    pub fn c_trans(&mut self, name: &str, guard: Ex, action: Ex) {
        let g = self.from_expr(&guard);
        let a = self.from_expr(&action);
        let f = self.make_trans(g, a);
        self.transitions.insert(name.into(), f);
    }

    pub fn uc_trans(&mut self, name: &str, guard: Ex, action: Ex) {
        let g = self.from_expr(&guard);
        let a = self.from_expr(&action);
        let f = self.make_trans(g, a);
        self.transitions.insert(name.into(), f);
        self.uc_transitions.insert(name.into(), f);

    }

    pub fn controllable(&mut self, initial: BDDFunc, forbidden: BDDFunc) -> (BDDFunc, BDDFunc, BDDFunc) {
        let mut ft = BDD_ZERO;
        for t in self.transitions.values() {
            ft = self.b.or(ft, *t);
        }

        let mut uc = BDD_ZERO;
        for t in self.uc_transitions.values() {
            uc = self.b.or(uc, *t);
        }

        // uncontrollable backwards
        let ub = swap(&mut self.b, uc, &self.pairing, &self.temps);

        // make sure initial states take the variable domains into account.
        let mut fi = initial;
        for v in &self.vars {
            match &v.var_type {
                BDDVarType::Enum(d) => {
                    // let e = self.b.to_expr(d.dom, self.num_vars);
                    // println!("DOM IS: {:?}", e);
                    fi = self.b.and(fi, d.dom)
                },
                _ => {} ,
            }
        }

        let not_forbidden = self.b.not(forbidden);
        let fi = self.b.and(fi, not_forbidden);

        // find all reachable states
        let now = std::time::Instant::now();

        let vars: Vec<_> = (0..self.num_vars).map(|i|i).collect();

        let r = reachable(&mut self.b, &vars, &self.pairing, ft, fi);

        let bad = ctrl(&mut self.b, &vars, &self.pairing, ub, forbidden);

        let n_bad = self.b.not(bad);
        let controllable = self.b.and(n_bad, r); // the intersection and not bad and reachable

        println!("Controllable computed in: {}ms\n", now.elapsed().as_millis());

        return (r, bad, controllable);
    }


    pub fn compute_guards(&mut self, controllable: BDDFunc, bad: BDDFunc) -> HashMap<String, Ex> {
        let vars: Vec<_> = (0..self.num_vars).map(|i|i).collect();

        let mut new_guards = HashMap::new();

        for (name, &trans) in &self.transitions {
            // compute the states from which we can reach a safe state as x
            let bt = swap(&mut self.b, trans, &self.pairing, &self.temps);
            let x = relprod(&mut self.b, controllable, bt, &vars);
            let x = replace(&mut self.b, x, &self.pairing);

            // x is new guard. use it and compare with original trans
            let xf = self.b.and(trans, x);
            let y = relprod(&mut self.b, controllable, trans, &vars);

            let z = relprod(&mut self.b, controllable, xf, &vars);

            if y != z {
                let now_ = std::time::Instant::now();

                let orig_guard = exist(&mut self.b, trans, &self.destvars);
                let new_guard = x;
                let good_states = controllable;
                let bad_states = bad;
                let mg = compute_minimal_guard(
                    &mut self.b,
                    orig_guard,
                    new_guard,
                    trans,
                    bt,
                    good_states,
                    bad_states,
                    &vars,
                    &self.pairing,
                    &self.temps,
                );

                // println!("new guard computed in {}ms", now.elapsed().as_millis());

                new_guards.insert(name.clone(), mg);
            }

        }

        // for (name, &ng) in &new_guards {
        //     let te = self.to_expr(ng);
        //     // new guard!
        //     println!("guard added for transition {}", name);
        //     println!("new guard:");
        //     println!("{:?}", te);

        //     // TODO: fix below...

        //     let cubes = self.b.to_max_cubes(ng, self.num_vars);
        //     let new_guard = self.from_expr(&te);
        //     let cubes1 = self.b.to_max_cubes(new_guard, self.num_vars);

        //     if new_guard != ng {
        //         println!("new_guard: {}, ng: {}", new_guard, ng);
        //         println!("ng cube {:#?}", cubes);
        //         println!("re cube {:#?}", cubes1);
        //     }
        // }

        new_guards.iter().map(|(k, v)| (k.clone(), self.to_expr(*v))).collect()
    }
}


#[derive(Debug, Clone, PartialEq)]
pub enum BDDVarType2 {
    Bool,
    Enum(BDDDomain2)
}

#[derive(Debug, Clone)]
pub struct BDDVar2 {
    orig_var_id: i32,
    bdd_var_id: i32,
    var_type: BDDVarType2
}

#[derive(Debug, Eq, PartialEq, PartialOrd, Ord, Clone)]
enum DomainCubeVal {
    DontCare,
    Bool(bool),
    Domain(Vec<i32>),
}

pub struct BDDContext2 {
    pub b: buddy_rs::BDDManager,
    pub vars: Vec<BDDVar2>,
    pub num_vars: i32,
    pub destvars: Vec<buddy_rs::BDDVar>,
    pub temps: Vec<buddy_rs::BDDVar>,
    pub pairing: Vec<(buddy_rs::BDDVar,buddy_rs::BDDVar)>,
    pub transitions: HashMap<String, buddy_rs::BDD>,
    pub uc_transitions: HashMap<String, buddy_rs::BDD>,

    next_to_normal: buddy_rs::BDDPair,
    normal_to_next: buddy_rs::BDDPair,
    next_to_temp: buddy_rs::BDDPair,
    temp_to_normal: buddy_rs::BDDPair,

    normal_vars: buddy_rs::BDD,
    next_vars: buddy_rs::BDD,
}

pub fn terms_in_bddfunc2(b: &buddy_rs::BDDManager, f: buddy_rs::BDD) -> Vec<buddy_rs::BDDVar> {
    let support = b.support(&f);
    b.scan_set(&support)
}


impl BDDContext2 {
    // TODO: the litterature is fairly decided on using an interleaved
    // variable ordering for better performance. for now we just put all
    // next values at the end.
    pub fn from(c: &Context) -> Self {
        //let b = buddy_rs::take_manager(10000, 10000, 24);
        let b = buddy_rs::take_manager(10000, 10000, 36);
        let mut vars = Vec::new();
        let mut offset = 0; // keep track of last added variable
        for (i, v) in c.vars.iter().enumerate() {
            match v.domain {
                Domain::Bool => {
                    let var = BDDVar2 { orig_var_id: i as i32, bdd_var_id: offset,
                                       var_type: BDDVarType2::Bool };
                    vars.push(var);
                    offset += 1;
                },
                Domain::Enum(n) => {
                    let domain = BDDDomain2::new(&b, n as i32, offset as i32);
                    let bs = domain.binsize;
                    let var = BDDVar2 { orig_var_id: i as i32, bdd_var_id: offset,
                                        var_type: BDDVarType2::Enum(domain) };
                    offset += bs as i32;
                    vars.push(var);
                }
            }
        }

        let num_vars = offset as i32;
        let destvars: Vec<_> = (0..num_vars).map(|i| (i + num_vars) as i32).collect();
        let temps: Vec<_> = (0..num_vars).map(|i| (i + 2 * num_vars) as i32).collect();
        let pairing: Vec<_> = (0..num_vars)
            .zip(destvars.iter())
            .map(|(x, y)| (x as i32, *y as i32))
            .collect();

        println!("pairing: {:?}", pairing);

        let next_to_normal: Vec<_> = pairing.iter().map(|(x,y)| (*y,*x)).collect();
        let next_to_normal = b.make_pair(&next_to_normal);

        let normal_to_next: Vec<_> = pairing.iter().map(|(x,y)| (*x,*y)).collect();
        let normal_to_next = b.make_pair(&normal_to_next);

        let next_to_temp: Vec<_> = destvars
            .iter()
            .zip(temps.iter())
            .map(|(y, z)| (*y, *z))
            .collect();
        let next_to_temp = b.make_pair(&next_to_temp);

        let temp_to_normal: Vec<_> = (0..num_vars)
            .zip(temps.iter())
            .map(|(y, z)| (*z, y))
            .collect();
        let temp_to_normal = b.make_pair(&temp_to_normal);

        let normal_vars: Vec<_> = (0..num_vars).collect();
        let normal_vars = b.make_set(&normal_vars);
        let next_vars = b.make_set(&destvars);

        BDDContext2 {
            b,
            vars,
            num_vars: num_vars,
            destvars: destvars,
            temps: temps,
            pairing: pairing,
            transitions: HashMap::new(),
            uc_transitions: HashMap::new(),

            next_to_normal: next_to_normal,
            normal_to_next: normal_to_next,
            next_to_temp: next_to_temp,
            temp_to_normal: temp_to_normal,

            normal_vars: normal_vars,
            next_vars: next_vars,
        }
    }

    fn swap_normal_and_next(&self, f: &buddy_rs::BDD) -> buddy_rs::BDD {
        let nf = self.b.replace(&f, &self.next_to_temp);
        let nf = self.b.replace(&nf, &self.normal_to_next);
        self.b.replace(&nf, &self.temp_to_normal)
    }

    pub fn term_orig_to_bdd(&self, t: i32) -> i32 {
        self.vars.iter().find(|v| v.orig_var_id == t).unwrap().bdd_var_id
    }
    pub fn term_bdd_to_orig(&self, t: i32) -> i32 {
        self.vars.iter().find(|v| v.bdd_var_id == t).unwrap().orig_var_id
    }

    pub fn from_expr(&mut self, e: &Ex) -> buddy_rs::BDD {
        match e {
            Ex::AND(v) => {
                let mut x = self.b.one();
                for a in v {
                    let a = self.from_expr(a);
                    x = self.b.and(&x, &a);
                }
                x
            },
            Ex::OR(v) => {
                let mut x = self.b.zero();
                for a in v {
                    let a = self.from_expr(a);
                    x = self.b.or(&x, &a);
                }
                x
            },
            Ex::NOT(x) => {
                let xval = self.from_expr(x);
                self.b.not(&xval)
            },
            Ex::TRUE => self.b.one(),
            Ex::FALSE => self.b.zero(),
            Ex::VAR(t) => {
                // typecheck to make sure VAR is a boolean
                // domains can only be used for equality checks
                let v = self.vars.iter().find(|v| v.orig_var_id == *t as i32).unwrap();
                assert!(v.var_type == BDDVarType2::Bool);
                self.b.ithvar(v.bdd_var_id)
            },
            Ex::EQ(var, value) => {
                // handle bools and enums separately
                let v = self.vars.iter().find(|v| v.orig_var_id == *var as i32).unwrap();

                match v.var_type {
                    BDDVarType2::Bool => {
                        let bv = self.b.ithvar(v.bdd_var_id);

                        match value {
                            Value::Bool(true) => bv,
                            Value::Bool(false) => self.b.not(&bv),
                            Value::InDomain(_n) => panic!("bool does not have a domain!"),
                            Value::Var(other) => {
                                let ov = self.vars.iter().find(|v| v.orig_var_id == *other as i32).unwrap();
                                // other var needs to be a bool also
                                assert!(ov.var_type == BDDVarType2::Bool);

                                // ok, now encode logical equivalence
                                let ov = self.b.ithvar(ov.bdd_var_id);
                                let nbv = self.b.not(&bv);
                                let nov = self.b.not(&ov);
                                let bv_and_ov = self.b.and(&bv,&ov);
                                let nbv_and_nov = self.b.and(&nbv, &nov);

                                // bv <-> ov
                                self.b.or(&bv_and_ov, &nbv_and_nov)
                            },
                        }
                    },
                    BDDVarType2::Enum(ref bdddom) => {

                        match value {
                            Value::Bool(_b) => panic!("not a boolean!"),
                            Value::InDomain(n) => {
                                // check if value is in domain...
                                assert!((*n as i32) < bdddom.size);

                                let f = bdddom.digit(&mut self.b, *n as i32);
                                // let fe = self.b.to_expr(f, self.num_vars);
                                // println!("DIGIT EXPR ({}): {:?}", *n, fe);
                                f
                            },
                            Value::Var(other) => {
                                // check that other value is also an enum
                                let ov = self.vars.iter().find(|v| v.orig_var_id == *other as i32).unwrap();
                                // other var needs to be a bool also
                                if let BDDVarType2::Enum(ref od) = ov.var_type {
                                    // ensure the same number of bdd terminals
                                    assert!(bdddom.binsize == od.binsize);
                                    bdddom.equals(od, &mut self.b)
                                    // panic!("domain assignment is todo!");
                                } else {
                                    panic!("other needs to be enum also...");
                                }

                            }
                        }

                    },
                }
            },
        }
    }

    fn domain_cubes_to_ex(&self, cubes: &Vec<Vec<DomainCubeVal>>) -> Ex {
        let sums = cubes.iter().map(|c| {
            let e = c.iter().enumerate().flat_map(|(i, v) | {
                match v {
                    DomainCubeVal::DontCare => None,
                    DomainCubeVal::Bool(false) => Some(Ex::NOT(Box::new(Ex::VAR(i)))),
                    DomainCubeVal::Bool(true) => Some(Ex::VAR(i)),
                    DomainCubeVal::Domain(vals) => {
                        let e = if vals.len() == 1 {
                            Ex::EQ(i, Value::InDomain(vals[0] as usize))
                        } else {
                            Ex::OR(vals.iter().map(|v| Ex::EQ(i, Value::InDomain(*v as usize))).collect())
                        };
                        Some(e)
                    }

                }
            }).collect();
            Ex::AND(e)
        }).collect();

        Ex::OR(sums)
    }

    pub fn to_expr(&self, f: &buddy_rs::BDD) -> Ex {
        let cubes = self.b.allsat_vec(f);

        // transform these cubes back into their original definitions

        let mut domain_cubes = Vec::new();

        for cube in &cubes {

            let mut new_cube = Vec::new();
            for v in &self.vars {

                let res = match &v.var_type {
                    BDDVarType2::Bool => {
                        // easy, just copy index
                        match cube[v.bdd_var_id as usize] {
                            buddy_rs::Valuation::DontCare => DomainCubeVal::DontCare,
                            buddy_rs::Valuation::True =>
                                DomainCubeVal::Bool(true),
                            buddy_rs::Valuation::False =>
                                DomainCubeVal::Bool(false),
                        }
                    },
                    BDDVarType2::Enum(dom) => {
                        // here we need to do more work.
                        let slice = &cube[(v.bdd_var_id) as usize ..(v.bdd_var_id+dom.binsize) as usize];

                        if slice.iter().all(|v| v == &buddy_rs::Valuation::DontCare) {
                            DomainCubeVal::DontCare
                        } else {
                            // build expression in cube, check which digits it matches
                            let mut allowed = self.b.one();

                            slice.iter().enumerate().for_each(|(i, val)| match val {
                                buddy_rs::Valuation::DontCare => {},
                                buddy_rs::Valuation::True => {
                                    let t = self.b.ithvar(v.bdd_var_id+i as i32);
                                    allowed = self.b.and(&allowed, &t);
                                },
                                buddy_rs::Valuation::False => {
                                    let f = self.b.nithvar(v.bdd_var_id+i as i32);
                                    allowed = self.b.and(&allowed, &f);
                                },
                            });

                            let allowed = dom.allowed_values(&self.b, &allowed);
                            DomainCubeVal::Domain(allowed)
                        }

                    }
                };

                new_cube.push(res)
            }
            domain_cubes.push(new_cube);
        }

        self.domain_cubes_to_ex(&domain_cubes)
    }

    fn make_trans(&mut self, guard: buddy_rs::BDD, action: buddy_rs::BDD) -> buddy_rs::BDD {

        // println!("guard: {:?}", terms_in_bddfunc2(&self.b, guard.clone()));
        // println!("action: {:?}", terms_in_bddfunc2(&self.b, action.clone()));

        let vl = self.num_vars;

        let vs: HashSet<buddy_rs::BDDVar> = HashSet::from_iter(0..vl);
        let t = terms_in_bddfunc2(&self.b, action.clone());
        let ts = HashSet::from_iter(t.iter().cloned());

        let not_updated: Vec<_> = vs.difference(&ts).cloned().collect();

        let iffs = not_updated.iter().fold(self.b.one(), |acc, i| {
            let a = self.b.ithvar(*i);
            let na = self.b.not(&a);
            let b = self.b.ithvar(*i + vl);
            let nb = self.b.not(&b);
            let a_and_b = self.b.and(&a, &b);
            let na_and_nb = self.b.and(&na, &nb);
            let iff = self.b.or(&a_and_b, &na_and_nb);

            self.b.and(&acc, &iff)
        });

        let action = self.swap_normal_and_next(&action);

        // return guards + action + additional iffs for keeping others unchanged
        let trans = self.b.and(&guard, &action);

        self.b.and(&trans, &iffs)
    }


    pub fn c_trans(&mut self, name: &str, guard: Ex, action: Ex) {
        let g = self.from_expr(&guard);
        let a = self.from_expr(&action);
        let f = self.make_trans(g, a);
        self.transitions.insert(name.into(), f);
    }

    pub fn uc_trans(&mut self, name: &str, guard: Ex, action: Ex) {
        let g = self.from_expr(&guard);
        let a = self.from_expr(&action);
        let f = self.make_trans(g, a);
        self.transitions.insert(name.into(), f.clone());
        self.uc_transitions.insert(name.into(), f.clone());

    }

    pub fn reachable(&mut self, initial: &buddy_rs::BDD, forbidden: &buddy_rs::BDD) -> (buddy_rs::BDD,buddy_rs::BDD,buddy_rs::BDD) {
        let mut ft = self.b.zero();
        for t in self.transitions.values() {
            ft = self.b.or(&ft, t);
        }

        let mut uc = self.b.zero();
        for t in self.uc_transitions.values() {
            uc = self.b.or(&uc, t);
        }

        // make sure initial states take the variable domains into account.
        let mut fi = initial.clone();
        for v in &self.vars {
            match &v.var_type {
                BDDVarType2::Enum(d) => {
                    // let e = self.b.to_expr(d.dom, self.num_vars);
                    // println!("DOM IS: {:?}", e);
                    fi = self.b.and(&fi, &d.dom)
                },
                _ => {} ,
            }
        }

        let not_forbidden = self.b.not(&forbidden);
        let fi = self.b.and(&fi, &not_forbidden);

        // find all reachable states
        let now = std::time::Instant::now();

        let r = reach(&self.b, &fi, &ft, &self.normal_vars, &self.next_to_normal);
        println!("Controllable computed in: {}ms\n", now.elapsed().as_millis());
        let sat = self.b.satcount_set(&r, &self.normal_vars);
        println!("Satcount: {}\n", sat);

        // uncontrollable backwards
        let ub = self.swap_normal_and_next(&uc);

        let bad = ctrl2(&self.b, &forbidden, &ub, &self.normal_vars, &self.next_to_normal);

        let n_bad = self.b.not(&bad);
        let controllable = self.b.and(&n_bad, &r); // the intersection and not bad and reachable


        println!("Controllable computed in: {}ms\n", now.elapsed().as_millis());

        let sat = self.b.satcount_set(&controllable, &self.normal_vars);
        println!("Satcount controllable: {}\n", sat);

        return (r, bad, controllable);
    }


    pub fn compute_guards(&mut self, controllable: &buddy_rs::BDD, bad: &buddy_rs::BDD) -> HashMap<String, Ex> {
        let mut new_guards = HashMap::new();

        for (name, trans) in &self.transitions {
            // compute the states from which we can reach a safe state as x
            let bt = self.swap_normal_and_next(&trans);

            let x = self.b.relprod(&controllable, &bt, &self.normal_vars);
            let x = self.b.replace(&x, &self.next_to_normal);

            // x is new guard. use it and compare with original trans
            let orig_guard = self.b.exist(&trans, &self.next_vars);
            let new_guard = self.b.exist(&x, &self.next_vars);

            // TODO: investigate which of these is more suitable
            // let constrained = self.b.constrain(&new_guard, &orig_guard);
            let mut x = self.b.simplify(&new_guard, &orig_guard);

            let xf = self.b.and(&trans, &x);
            let y = self.b.relprod(&controllable, &trans, &self.normal_vars);
            let z = self.b.relprod(&controllable, &xf, &self.normal_vars);

            if y != z {
                let now = std::time::Instant::now();

                let orig_guard = self.b.exist(&trans, &self.next_vars);
                let good_states = controllable;
                let new_guard = x;
                let mg = self.compute_minimal_guard(
                    &orig_guard,
                    &new_guard,
                    &trans,
                    &bt,
                    &good_states,
                    &bad,
                );

                println!("new guard computed in {}ms", now.elapsed().as_millis());

                new_guards.insert(name.clone(), mg);
            }

        }

        new_guards.iter().map(|(k, v)| (k.clone(), self.to_expr(v))).collect()
    }


    fn compute_minimal_guard(
        &self,
        orig_guard: &buddy_rs::BDD,
        new_guard: &buddy_rs::BDD,
        trans: &buddy_rs::BDD,
        bt: &buddy_rs::BDD, // TODO these
        good_states: &buddy_rs::BDD,
        bad_states: &buddy_rs::BDD) -> buddy_rs::BDD {

        // try to remove terms that doesnt lead us to a forbidden state
        // and doesn't over-constrain us wrt the reachable states
        let temp = self.b.and(&trans, &new_guard);
        let bt = self.swap_normal_and_next(&temp);
        let z = self.b.relprod(&good_states, &bt, &self.normal_vars);

        let support = self.b.support(&new_guard);
        let support_vars = self.b.scan_set(&support);

        let mut ntps = powerset(&support_vars);

        let all = ntps.pop(); // no use trying to remove all terms
        ntps.reverse(); // remove the largest amount of terms first,
        // stop as soon as we succeed

        let mut num_iters = 0;
        for s in ntps {
            // remove elemts in s
            let mut temp_ng = new_guard.clone();
            let varset = self.b.make_set(&s);
            temp_ng = self.b.exist(&temp_ng, &varset);

            // check if guard still works as it should
            let temp = self.b.and(&trans, &temp_ng);

            let bt = self.swap_normal_and_next(&temp);
            let y = self.b.relprod(&bad_states, &bt, &self.normal_vars);
            let y = self.b.replace(&y, &self.next_to_normal);
            let y = self.b.and(&y, &good_states);


            if y == self.b.zero() {
                let zz = self.b.relprod(&good_states, &bt, &self.normal_vars);
                if z == zz { // no loss of permissiveness
                    println!("choosing {:?} out of {:?} after {} iters", s, all, num_iters);
                    return temp_ng;
                }
            }
            num_iters += 1;
        }

        // nothing better found
        return new_guard.clone();
    }
}

#[test]
fn new_expr_test() {

    let mut c =  Context::new();
    let tc = c.add_bool("tool_closed");
    let robot_p_m = c.add_enum("robot_p_m", 3); // p0, p1, p2
    let robot_p_c = c.add_enum("robot_p_c", 3); // p0, p1, p2
    let to = c.add_bool("tool_opened");

    let mut bc = BDDContext::from(&c);

    println!("{:#?}", bc.vars);
    println!("{:#?}", bc.num_vars);

    // convenience
    let v = |n| Ex::VAR(n);
    let nv = |n| Ex::NOT(Box::new(Ex::VAR(n)));
    let and = |x| Ex::AND(x);
    let or = |x| Ex::OR(x);
    let not = |x| Ex::NOT(Box::new(x));

    let tool_open_d_guard = and(vec![v(tc), nv(to), or(vec![Ex::EQ(robot_p_m, Value::InDomain(1)), Ex::EQ(robot_p_c, Value::InDomain(0))])]);
    // let tool_open_d_guard = and(vec![or(vec![Ex::EQ(robot_p_m, Value::InDomain(1)), Ex::EQ(robot_p_c, Value::InDomain(0))])]);
    let tool_open_d_action = v(tc);

    let n = bc.from_expr(&tool_open_d_guard);
    let n2 = bc.from_expr(&tool_open_d_action);

    let tool_open_d = bc.make_trans(n, n2);

    println!("func {}", n);
    println!("func {}", tool_open_d);

    let real = bc.to_expr(n);
    println!("real func {:?}", real);
    let realb = bc.from_expr(&real);
    assert!(n == realb);

    let s = c.pretty_print(&real);
    println!("THE EXPR: {}", s);

    assert!(!s.is_empty());
}
