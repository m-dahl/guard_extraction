use boolean_expression::*;
use std::collections::HashMap;
use std::collections::HashSet;
use std::iter::FromIterator;
use itertools::Itertools;

mod bdd_helpers;
use bdd_helpers::*;


mod bdd_domain;
use bdd_domain::*;




fn main() {
    println!("Hello, world!");
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

pub struct Ac {  // basically assign
    var: usize,
    val: Ex,
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
    fn new() -> Self {
        Context { vars: Vec::new() }
    }

    fn get_var(&self, name: &str) -> usize {
        self.vars.iter().position(|v| v.name == name).unwrap()
    }

    fn add_bool(&mut self, name: &str) -> usize {
        self.vars.push(Var { name: name.to_owned(), domain: Domain::Bool });
        return self.vars.len() - 1
    }

    fn add_enum(&mut self, name: &str, domain: usize) -> usize {
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
                format!("!{}", self.pretty_print(e))
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
    fn from(c: &Context) -> Self {
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

        let destvars: Vec<_> = (0..offset).map(|i| 1+ i + vars.len()).collect();
        let temps: Vec<_> = (0..offset).map(|i| 2 + i + 2 * vars.len()).collect();
        let pairing: Vec<_> = (0..offset)
            .zip(destvars.iter())
            .map(|(x, y)| (x, *y))
            .collect();

        BDDContext {
            b,
            vars,
            num_vars: offset,
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
                                    panic!("domain assignment is todo!");
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

    pub fn controllable(&mut self, forbidden: BDDFunc) -> (BDDFunc, BDDFunc, BDDFunc) {
        let mut ft = BDD_ZERO;
        for t in self.transitions.values() {
            ft = self.b.or(ft, *t);
        }

        let mut uc = BDD_ZERO;
        for t in self.uc_transitions.values() {
            uc = self.b.or(uc, *t);
        }

        let ub = swap(&mut self.b, uc, &self.pairing, &self.temps); // uncontrollable backwards

        // make sure initial states take the variable domains into account.
        let mut fi = BDD_ONE;
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

        let state_count = satcount(&mut self.b, controllable, vars.len());
        println!("Nbr of states in supervisor: {}\n", state_count);
        println!("Computed in: {}ms\n", now.elapsed().as_millis());
        let reachable_state_count = satcount(&mut self.b, r, vars.len());
        println!("Nbr of reachable states: {}\n", reachable_state_count);

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
    let expr = bc.b.to_expr2(tool_open_d, 2*bc.num_vars);
    let expr = bc.b.to_expr2(n, 2*bc.num_vars);
    println!("func {:?}", expr);

    let real = bc.to_expr(n);
    println!("real func {:?}", real);
    let realb = bc.from_expr(&real);
    assert!(n == realb);

    let s = c.pretty_print(&real);
    println!("THE EXPR: {}", s);

    assert!(!s.is_empty());
}


#[test]
fn sp_expr_test() {
    // set up variables

    let mut c =  Context::new();

    let tool_closed_m = c.add_bool("tool_closed_m");
    let tool_opened_m = c.add_bool("tool_opened_m");
    let tool_gs_c = c.add_enum("tool_gs_c", 2); // 0 = closed, 1 = opened
    let rsp_lock_l_c = c.add_bool("rsp_lock_l_c");
    let rsp_lock_u_c = c.add_bool("rsp_lock_u_c");
    let rsp_lock_e = c.add_enum("rsp_lock_e", 3); // 0 = locked, 1 = unlocked, 2 = unknown,
//    let robot_p_m = c.add_enum("robot_p_m", 3); // positions
//    let robot_p_c = c.add_enum("robot_p_c", 3); // positions
//    let robot_p_e = c.add_enum("robot_p_e", 3); // positions
    let robot_p_m = c.add_bool("robot_p_m"); // p0/p1
    let robot_p_c = c.add_bool("robot_p_c"); // p0/p1
    let robot_p_e = c.add_bool("robot_p_e"); // p0/p1 init p1 = true
    let robot_moving_m = c.add_bool("robot_moving_m");
    let tool_e = c.add_enum("tool_e", 2); // 0 = home, 1 = robot

    let mut bc = BDDContext::from(&c);


    println!("{:?}", bc.vars);
    let vars: Vec<_> = (0..bc.num_vars).map(|x|x).collect();
    println!("{:?}",vars);
    println!("{:?}", bc.destvars);
    println!("{:?}", bc.temps);

    // convenience
    let v = |n| Ex::VAR(n);
    let nv = |n| Ex::NOT(Box::new(Ex::VAR(n)));
    let and = |x| Ex::AND(x);
    let or = |x| Ex::OR(x);
    let not = |x| Ex::NOT(Box::new(x));
    let imp = |a, b| Ex::OR(vec![not(a), b]);
    let eq = |v, n| Ex::EQ(v, Value::InDomain(n));

    bc.c_trans("tool_open_d", not(v(tool_opened_m)), eq(tool_gs_c, 1));
    bc.uc_trans("tool_open_e", and(vec![eq(tool_gs_c, 1), not(v(tool_opened_m))]),
             and(vec![v(tool_opened_m), not(v(tool_closed_m))]));

    bc.c_trans("tool_close_d", not(v(tool_closed_m)), eq(tool_gs_c, 0));
    bc.uc_trans("tool_close_e", and(vec![eq(tool_gs_c, 0), not(v(tool_closed_m))]),
             and(vec![v(tool_closed_m), not(v(tool_opened_m))]));

    bc.c_trans("rsp_lock_d", or(vec![eq(rsp_lock_e, 1), eq(rsp_lock_e, 2)]),
            and(vec![v(rsp_lock_l_c), not(v(rsp_lock_u_c)), eq(rsp_lock_e, 0)]));

    bc.c_trans("rsp_unlock_d", or(vec![eq(rsp_lock_e, 0), eq(rsp_lock_e, 2)]),
            and(vec![not(v(rsp_lock_l_c)), v(rsp_lock_u_c), eq(rsp_lock_e, 1)]));


    bc.c_trans("robot_p0_d", and(vec![v(robot_p_m), v(robot_p_c), v(robot_p_e)]), not(v(robot_p_c)));
    bc.uc_trans("robot_p0_se", and(vec![v(robot_p_m), not(v(robot_p_c)), not(v(robot_moving_m))]), v(robot_moving_m));
    bc.uc_trans("robot_p0_ee", and(vec![v(robot_p_m), not(v(robot_p_c)), v(robot_moving_m)]),
             and(vec![not(v(robot_p_m)), not(v(robot_moving_m))]));
    bc.uc_trans("robot_p0_fa", and(vec![not(v(robot_p_m)), not(v(robot_p_c)), not(v(robot_moving_m)), v(robot_p_e)]),
             not(v(robot_p_e)));


    bc.c_trans("robot_p1_d", and(vec![not(v(robot_p_m)), not(v(robot_p_c)), not(v(robot_p_e))]), v(robot_p_c));
    bc.uc_trans("robot_p1_se", and(vec![not(v(robot_p_m)), v(robot_p_c), not(v(robot_moving_m))]), v(robot_moving_m));
    bc.uc_trans("robot_p1_ee", and(vec![not(v(robot_p_m)), v(robot_p_c), v(robot_moving_m)]),
             and(vec![v(robot_p_m), not(v(robot_moving_m))]));
    bc.uc_trans("robot_p1_fa", and(vec![v(robot_p_m), v(robot_p_c), not(v(robot_moving_m)), not(v(robot_p_e))]),
             v(robot_p_e));

    bc.uc_trans("tool_e_home_a", and(vec![eq(tool_e, 1), not(v(robot_p_m)), eq(rsp_lock_e, 1)]),
             eq(tool_e, 0));
    bc.uc_trans("tool_e_robot_a", and(vec![eq(tool_e, 0), not(v(robot_p_m)), eq(rsp_lock_e, 0)]),
             eq(tool_e, 1));

    // // let is = [false, false, false, false, false, false, true, false, false, true, false, false];
    // // let ise = state_to_expr2(&is);

    // tool cannot be closed and opened at the same time.
    let forbidden = and(vec![v(tool_closed_m), v(tool_opened_m)]);
    let forbidden = bc.from_expr(&forbidden);

    // spec A
    let mtop1exec = and(vec![not(v(robot_p_m)), v(robot_p_c), v(robot_moving_m)]);
    let forbidden_a = not(imp(and(vec![eq(tool_e, 1), not(v(robot_p_e)), mtop1exec]), v(tool_opened_m)));
    let forbidden_a = bc.from_expr(&forbidden_a);

    // spec B
    let mtop0exec = and(vec![v(robot_p_m), not(v(robot_p_c)), v(robot_moving_m)]);
    let forbidden_b = not(imp(and(vec![eq(tool_e, 1), v(robot_p_e), mtop0exec]), v(tool_opened_m)));
    let forbidden_b = bc.from_expr(&forbidden_b);

    // spec C
    let mtop0exec = and(vec![v(robot_p_m), not(v(robot_p_c)), v(robot_moving_m)]);
    let forbidden_c = not(imp(and(vec![eq(tool_e, 0), mtop0exec]), eq(rsp_lock_e, 1)));
    let forbidden_c = bc.from_expr(&forbidden_c);

    // spec D
    let forbidden_d = not(imp(and(vec![eq(tool_e, 1), eq(rsp_lock_e, 0)]),
                              and(vec![v(tool_closed_m), not(v(robot_p_m))])));
    let forbidden_d = bc.from_expr(&forbidden_d);

    // spec E
    let forbidden_e = not(imp(eq(tool_e, 0), not(v(tool_opened_m))));
    let forbidden_e = bc.from_expr(&forbidden_e);

    let forbidden = bc.b.or(forbidden, forbidden_a);
    let forbidden = bc.b.or(forbidden, forbidden_b);
    let forbidden = bc.b.or(forbidden, forbidden_c);
    let forbidden = bc.b.or(forbidden, forbidden_d);
    let forbidden = bc.b.or(forbidden, forbidden_e);

    let (reachable, bad, controllable) = bc.controllable(forbidden);

    let new_guards = bc.compute_guards(controllable, bad);

    for (trans, guard) in &new_guards {
        let s = c.pretty_print(&guard);
        println!("NEW GUARD FOR {}: {}", trans, s);
    }

    assert!(false);
}
