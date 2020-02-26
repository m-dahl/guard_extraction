use std::collections::HashMap;
use std::collections::HashSet;
use std::iter::FromIterator;
use itertools::Itertools;
use buddy_rs::*;

use crate::bdd_domain::*;
use crate::cubes::*;
use crate::context::*;

#[derive(Debug, Clone, PartialEq)]
pub enum ExprType {
    DNF,
    CNF,
}

// compute reachable states
fn reach(bdd: &BDDManager, initial: &BDD,
             forward_trans: &BDD, vars: &BDD,
             pair: &BDDPair) -> BDD {
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

fn reach2(bdd: &BDDManager, initial: &BDD,
          forward_trans: &HashMap<usize, Ts>) -> BDD {
    let mut r = initial.clone();

    loop {
        let old = r.clone();

        for t in forward_trans.values() {
            let new = bdd.relprod(&old, &t.f, &t.vars);
            let new = bdd.replace(&new, &t.next_to_normal);
            r = bdd.or(&old, &new);
        }

        if old == r {
            break;
        }
    }
    r
}


// compute controllability and return the forbidden states
fn ctrl(
    bdd: &BDDManager, forbidden: &BDD,
    backward_unc_trans: &BDD, vars: &BDD,
    pair: &BDDPair) -> BDD {
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

// backwards uncontrollable reachability
#[allow(dead_code)]
fn ucb(
    bdd: &BDDManager,
    vars: &BDD,
    pair: &BDDPair,
    backwards_uncontrollable: &BDD,
    forbidden: &BDD,
) -> BDD {
    let mut new_forbidden = forbidden.clone();

    loop {
        let old = new_forbidden;
        let new = bdd.relprod(&old, backwards_uncontrollable, vars); // possible trans
        let new = bdd.replace(&new, pair); // to source states
        new_forbidden = bdd.or(&old, &new);

        if old == new_forbidden {
            break;
        }
    }
    new_forbidden
}

// backwards reachability
#[allow(dead_code)]
fn rb(
    bdd: &BDDManager,
    vars: &BDD,
    pair: &BDDPair,
    backwards_transitions: &BDD,
    marked: &BDD,
    forbidden: &BDD,
) -> BDD {
    let not_forbidden = bdd.not(&forbidden);
    let mut s = bdd.and(marked, &not_forbidden);

    loop {
        let old = s.clone();
        let new = bdd.relprod(&old, backwards_transitions, vars); // possible trans
        let new = bdd.replace(&new, pair); // to source states
        s = bdd.or(&old, &new);
        s = bdd.and(&s, &not_forbidden);

        if old == s {
            break;
        }
    }

    s
}

// compute nonblocking and controllability and return the forbidden states
#[allow(dead_code)]
fn nbc(
    bdd: &BDDManager,
    vars: &BDD,
    pair: &BDDPair,
    backwards_transitions: &BDD,
    unc_backwards_transitions: &BDD,
    marked: &BDD,
    forbidden: &BDD,
) -> BDD {
    let mut s = forbidden.clone();

    loop {
        let old = s.clone();
        let new = rb(bdd, vars, pair, backwards_transitions, marked, &old);
        // new has safe states
        let forbidden = bdd.not(&new); // and R
        let new2 = ucb(bdd, vars, pair, unc_backwards_transitions, &forbidden);
        s = bdd.or(&s, &new2);

        if old == s {
            break;
        }
    }

    s
}

#[derive(Debug, Clone, PartialEq)]
pub enum BDDVarType {
    Bool,
    Enum(BDDDomain)
}

impl BDDVarType {
    fn size(&self) -> i32 {
        match self {
            BDDVarType::Bool => 2,
            BDDVarType::Enum(dom) => dom.size,
        }
    }

    fn binsize(&self) -> i32 {
        match self {
            BDDVarType::Bool => 1,
            BDDVarType::Enum(dom) => dom.binsize,
        }
    }
}

#[derive(Debug, Clone)]
struct BDDVar {
    orig_var_id: i32,
    bdd_var_id: i32,
    var_type: BDDVarType
}

#[derive(Debug, Eq, PartialEq, PartialOrd, Ord, Clone)]
enum DomainCubeVal {
    DontCare,
    Bool(bool),
    Domain(Vec<i32>),
}

struct Ts {
    f: BDD,
    var: usize,
    vars: BDD,
    next_to_normal: BDDPair,
}

pub struct BDDContext<'a> {
    b: &'a BDDManager,
    vars: Vec<BDDVar>,

    transitions: HashMap<String, BDD>,
    uc_transitions: HashMap<String, BDD>,
    buc_transitions: HashMap<String, BDD>,

    disj_transitions: HashMap<usize, Ts>,

    next_to_normal: BDDPair,
    normal_to_next: BDDPair,
    swap: BDDPair,

    normal_vars: BDD,
    next_vars: BDD,
}

impl<'a> BDDContext<'a> {
    pub fn from(c: &Context, b: &'a BDDManager) -> Self {
        let mut vars = Vec::new();
        let mut offset = 0i32; // keep track of last added variable

        let mut normal_vars = Vec::new();
        let mut next_vars = Vec::new();

        for (i, v) in c.vars.iter().enumerate() {
            match v.domain {
                Domain::Bool => {
                    // add bdd variables
                    b.ext_varnum(2); // we need a normal and a next variable
                    let bdd_id = offset;
                    normal_vars.push(bdd_id);
                    next_vars.push(bdd_id + 1);
                    let var = BDDVar { orig_var_id: i as i32, bdd_var_id: bdd_id,
                                       var_type: BDDVarType::Bool };
                    vars.push(var);
                    offset += 2;
                },
                Domain::Enum(n) => {
                    let binsize = BDDDomain::compute_binsize(n as i32);
                    // add bdd variables
                    b.ext_varnum(2 * binsize); // normal and next variables
                    let bdd_id = offset;
                    // TODO: domain vars should also preferably be interleaved
                    for i in 0..binsize {
                        normal_vars.push(i + bdd_id);
                    }
                    for i in 0..binsize {
                        next_vars.push(i + bdd_id + binsize);
                    }

                    let domain = BDDDomain::new(&b, n as i32, offset);
                    let var = BDDVar { orig_var_id: i as i32, bdd_var_id: bdd_id,
                                       var_type: BDDVarType::Enum(domain) };

                    offset += 2 * binsize;
                    vars.push(var);
                }
            }
        }
        // println!("used bdd variables: {}", b.get_varnum());

        let pairing: Vec<_> = normal_vars.iter().zip(next_vars.iter())
            .map(|(x, y)| (*x as i32, *y as i32)).collect();

        let mut swap: Vec<(i32, i32)> = Vec::new();

        let next_to_normal: Vec<_> = pairing.iter().map(|(x,y)| (*y,*x)).collect();
        swap.extend(next_to_normal.iter().cloned());
        let next_to_normal = b.make_pair(&next_to_normal);

        let normal_to_next: Vec<_> = pairing.iter().map(|(x,y)| (*x,*y)).collect();
        swap.extend(normal_to_next.iter().cloned());
        let normal_to_next = b.make_pair(&normal_to_next);

        let swap = b.make_pair(&swap);

        let normal_vars = b.make_set(&normal_vars);
        let next_vars = b.make_set(&next_vars);

        let mut bc = BDDContext {
            b,
            vars,

            transitions: HashMap::new(),
            uc_transitions: HashMap::new(),
            buc_transitions: HashMap::new(),

            disj_transitions: HashMap::new(),

            next_to_normal,
            normal_to_next,
            swap,

            normal_vars,
            next_vars,
        };

        // now add all transitions.
        for ct in &c.c_trans {
            bc.trans2(&ct.name, &ct.guard, &ct.actions);
            bc.c_trans(&ct.name, &ct.guard, &ct.actions);
        }
        for uct in &c.uc_trans {
            bc.trans2(&uct.name, &uct.guard, &uct.actions);
            bc.uc_trans(&uct.name, &uct.guard, &uct.actions);
        }

        bc
    }

    fn swap_normal_and_next(&self, f: &BDD) -> BDD {
        self.b.replace(&f, &self.swap)
    }

    pub fn from_expr(&mut self, e: &Ex) -> BDD {
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
                assert!(v.var_type == BDDVarType::Bool);
                self.b.ithvar(v.bdd_var_id)
            },
            Ex::EQ(var, value) => {
                // handle bools and enums separately
                let v = self.vars.iter().find(|v| v.orig_var_id == *var as i32).unwrap();

                match v.var_type {
                    BDDVarType::Bool => {
                        let bv = self.b.ithvar(v.bdd_var_id);

                        match value {
                            Value::Bool(true) => bv,
                            Value::Bool(false) => self.b.not(&bv),
                            Value::InDomain(_n) => panic!("bool does not have a domain!"),
                            Value::Var(other) => {
                                let ov = self.vars.iter().find(|v| v.orig_var_id == *other as i32).unwrap();
                                // other var needs to be a bool also
                                assert!(ov.var_type == BDDVarType::Bool);

                                // ok, now encode logical equivalence
                                let ov = self.b.ithvar(ov.bdd_var_id);
                                self.b.biimp(&bv, &ov)
                            },
                            Value::Free => {
                                panic!("cannot check for free")
                            }
                        }
                    },
                    BDDVarType::Enum(ref bdddom) => {

                        match value {
                            Value::Bool(_b) => panic!("not a boolean!"),
                            Value::InDomain(n) => {
                                // check if value is in domain...
                                assert!((*n as i32) < bdddom.size, "value must be in domain!");

                                bdddom.digit(&self.b, *n as i32)
                            },
                            Value::Var(other) => {
                                // check that other value is also an enum
                                let ov = self.vars.iter().find(|v| v.orig_var_id == *other as i32).unwrap();
                                // other var needs to be a bool also
                                if let BDDVarType::Enum(ref od) = ov.var_type {
                                    // ensure the same number of bdd terminals
                                    assert!(bdddom.binsize == od.binsize);
                                    bdddom.equals(&self.b, od)
                                    // panic!("domain assignment is todo!");
                                } else {
                                    panic!("other needs to be enum also...");
                                }
                            },
                            Value::Free => {
                                panic!("cannot check for free")
                            }
                        }

                    },
                }
            },
        }
    }


    // already handles next values.
    fn from_ac(&mut self, a: &Ac) -> (BDD, Vec<i32>) {
        let v = self.vars.iter().find(|v| v.orig_var_id == a.var as i32).expect("variable not found");

        // handle bools and enums separately
        match v.var_type {
            BDDVarType::Bool => {
                // we want to set the "next" value
                let bv = self.b.ithvar(v.bdd_var_id);
                // so we replace bv with its next pair to get bv'
                let bv = self.b.replace(&bv, &self.normal_to_next);
                match &a.val {
                    Value::Bool(true) => (bv, vec![]),
                    Value::Bool(false) => (self.b.not(&bv), vec![]),
                    Value::InDomain(_n) => panic!("bool does not have a domain!"),
                    Value::Var(other) => {
                        let ov = self.vars.iter().find(|v| v.orig_var_id == *other as i32).unwrap();
                        // other var needs to be a bool also
                        assert!(ov.var_type == BDDVarType::Bool);

                        // keed other var as "current" value
                        let ov = self.b.ithvar(ov.bdd_var_id);

                        (self.b.biimp(&bv, &ov), vec![])
                    },
                    Value::Free => {
                        (self.b.one(), vec![v.bdd_var_id]) // bv free to be set by planner
                    }
                }
            },
            BDDVarType::Enum(ref bdddom) => {
                match &a.val {
                    Value::Bool(_b) => panic!("not a boolean!"),
                    Value::InDomain(n) => {
                        // check if value is in domain...
                        assert!((*n as i32) < bdddom.size, "value must be in domain!");
                        let digit_current = bdddom.digit(&self.b, *n as i32);
                        let digit_next = self.b.replace(&digit_current, &self.normal_to_next);
                        (digit_next, vec![])
                    },
                    Value::Var(other) => {
                        // check that other value is also an enum
                        let ov = self.vars.iter().find(|v| v.orig_var_id == *other as i32).unwrap();
                        // other var needs to be a bool also
                        if let BDDVarType::Enum(ref od) = ov.var_type {
                            // ensure the same number of bdd terminals
                            assert!(bdddom.binsize == od.binsize);
                            (bdddom.equals_cur_next(&self.b, od, &self.normal_to_next), vec![])
                            // panic!("domain assignment is todo!");
                        } else {
                            panic!("other needs to be enum also...");
                        }
                    },
                    Value::Free => {
                        (self.b.one(), (0..bdddom.binsize).map(|n| v.bdd_var_id + n as i32).collect())
                    }
                }
            },
        }
    }

    fn domain_cubes_to_ex(&self, cubes: &[Vec<DomainCubeVal>], t: ExprType) -> Ex {
        let parts = cubes.iter().map(|c| {
            let e = c.iter().enumerate().flat_map(|(i, v) | {
                match v {
                    DomainCubeVal::DontCare => None,
                    DomainCubeVal::Bool(false) => Some(Ex::NOT(Box::new(Ex::VAR(i)))),
                    DomainCubeVal::Bool(true) => Some(Ex::VAR(i)),
                    DomainCubeVal::Domain(vals) => {
                        let domain_len = self.vars[i].var_type.size();
                        let e = if vals.len() == 1 {
                            Ex::EQ(i, Value::InDomain(vals[0] as usize))
                        } else if (vals.len() as i32) == domain_len - 1 {
                            let v = (0..domain_len).filter(|x| !vals.contains(x)).nth(0).unwrap();
                            Ex::NOT(Box::new(Ex::EQ(i, Value::InDomain(v as usize))))
                        } else {
                            Ex::OR(vals.iter().map(|v| Ex::EQ(i, Value::InDomain(*v as usize))).collect())
                        };
                        Some(e)
                    }

                }
            }).collect();
            match t {
                ExprType::DNF => Ex::AND(e),
                ExprType::CNF => Ex::OR(e),
            }
        }).collect();

        match t {
            ExprType::DNF => Ex::OR(parts),
            ExprType::CNF => Ex::AND(parts),
        }
    }

    pub fn to_expr(&self, f: &BDD, t: ExprType) -> Ex {
        if f == &self.b.zero() {
            return Ex::FALSE;
        }
        if f == &self.b.one() {
            return Ex::TRUE;
        }

        let f = match t {
            ExprType::DNF => f.clone(),
            ExprType::CNF => self.b.not(&f),
        };
        let cubes = self.b.allsat_vec(&f);
        let cubes: Vec<_> = cubes.into_iter().map(|c| { Cube(c) }).collect();
        let cubes = CubeList::new().merge(&CubeList::from_list(&cubes));

        let mut domain_cubes = Vec::new();

        for cube in cubes.cubes() {
            let mut new_cube = Vec::new();
            for v in &self.vars {

                let res = match &v.var_type {
                    BDDVarType::Bool => {
                        match (&cube.0[v.bdd_var_id as usize], &t) {
                            (Valuation::False, ExprType::DNF) => DomainCubeVal::Bool(false),
                            (Valuation::False, ExprType::CNF) => DomainCubeVal::Bool(true),

                            (Valuation::True, ExprType::DNF) => DomainCubeVal::Bool(true),
                            (Valuation::True, ExprType::CNF) => DomainCubeVal::Bool(false),

                            (Valuation::DontCare, _) => DomainCubeVal::DontCare,
                        }
                    },
                    BDDVarType::Enum(dom) => {
                        let slice = &cube.0[(v.bdd_var_id) as usize ..(v.bdd_var_id+dom.binsize) as usize];
                        if slice.iter().all(|v| v == &Valuation::DontCare) {
                            DomainCubeVal::DontCare
                        } else {
                            // build expression in cube, check which digits it matches
                            let mut d = match t {
                                ExprType::DNF => self.b.one(),
                                ExprType::CNF => self.b.zero(),
                            };

                            slice.iter().enumerate().for_each(|(i, val)| match val {
                                Valuation::DontCare => {},
                                Valuation::True => {
                                    match t {
                                        ExprType::DNF => {
                                            let t = self.b.ithvar(v.bdd_var_id+i as i32);
                                            d = self.b.and(&d, &t);
                                        },
                                        ExprType::CNF => {
                                            let t = self.b.nithvar(v.bdd_var_id+i as i32);
                                            d = self.b.or(&d, &t);
                                        }
                                    }
                                },
                                Valuation::False => {
                                    match t {
                                        ExprType::DNF => {
                                            let t = self.b.nithvar(v.bdd_var_id+i as i32);
                                            d = self.b.and(&d, &t);
                                        },
                                        ExprType::CNF => {
                                            let t = self.b.ithvar(v.bdd_var_id+i as i32);
                                            d = self.b.or(&d, &t);
                                        }
                                    }
                                },
                            });

                            let d = dom.allowed_values(&self.b, &d);

                            assert!(d.len() > 0);
                            DomainCubeVal::Domain(d)
                        }
                    }
                };
                new_cube.push(res)
            }
            domain_cubes.push(new_cube);
        }

        // TODO: here we should merge cubes that only differ w.r.t. enum variables.
        // eg. (x1 & v = 2) | (x1 & v = 3) should be merged to (x1 & v in [2,3])

        self.domain_cubes_to_ex(&domain_cubes, t)
    }

    fn make_trans_free(&mut self, guard: &BDD, action: &BDD, free: &[i32]) -> BDD {
        let action_support = self.b.support(&action);
        let terms_in_action = self.b.scan_set(&action_support);
        let mut terms_in_action: HashSet<_> = HashSet::from_iter(terms_in_action.iter().cloned());
        terms_in_action.extend(free.iter());

        let all_next_vars = self.b.scan_set(&self.next_vars);
        let all_next_vars: HashSet<_> = HashSet::from_iter(all_next_vars.iter().cloned());

        let not_updated: Vec<_> = all_next_vars.difference(&terms_in_action).cloned().collect();

        let iffs = not_updated.iter().fold(self.b.one(), |acc, i| {
            // we want a = a', we have b'
            let a = self.b.ithvar(*i);
            // so we replace a with its next pair to get a'
            let b = self.b.ithvar(*i);
            let b = self.b.replace(&b, &self.next_to_normal);

            let iff = self.b.biimp(&a, &b);
            self.b.and(&acc, &iff)
        });

        // let action = self.swap_normal_and_next(&action);

        // return guards + action + additional iffs for keeping others unchanged
        let trans = self.b.and(&guard, &action);

        self.b.and(&trans, &iffs)
    }

    fn make_backward_trans(&mut self, guard: &BDD, action: &BDD) -> BDD {
        let action_support = self.b.support(&action);
        let terms_in_action = self.b.scan_set(&action_support);
        let terms_in_action: HashSet<_> = HashSet::from_iter(terms_in_action.iter().cloned());

        let all_next_vars = self.b.scan_set(&self.next_vars);
        let all_next_vars: HashSet<_> = HashSet::from_iter(all_next_vars.iter().cloned());

        let not_updated: Vec<_> = all_next_vars.difference(&terms_in_action).cloned().collect();

        let iffs = not_updated.iter().fold(self.b.one(), |acc, i| {
            // we want a = a'
            let a = self.b.ithvar(*i);
            // so we replace a with its next pair to get a'
            let b = self.b.ithvar(*i);
            let b = self.b.replace(&b, &self.next_to_normal);

            let iff = self.b.biimp(&a, &b);
            self.b.and(&acc, &iff)
        });

        let action = self.swap_normal_and_next(&action);
        let guard = self.swap_normal_and_next(&guard);

        // return guards + action + additional iffs for keeping others unchanged
        let trans = self.b.and(&guard, &action);

        self.b.and(&trans, &iffs)
    }

    fn c_trans(&mut self, name: &str, guard: &Ex, actions: &[Ac]) {
        let g = self.from_expr(guard);
        let mut free = Vec::new();
        let mut action = self.b.one();
        for a in actions {
            let (a,f) = self.from_ac(&a);
            free.extend(f.iter());
            action = self.b.and(&action, &a);
        }

        let f = self.make_trans_free(&g, &action, &free);
        self.transitions.insert(name.into(), f);
    }

    fn trans2(&mut self, name: &str, guard: &Ex, actions: &[Ac]) {
        let g = self.from_expr(guard);
        for a in actions {
            let (action_bdd,_f) = self.from_ac(&a);
            let trans = self.b.and(&g, &action_bdd);

            use std::collections::hash_map::Entry;
            let c = match self.disj_transitions.entry(a.var) {
                Entry::Vacant(entry) => {
                    let var = self.vars.iter().find(|x|x.orig_var_id == a.var as i32).unwrap();
                    let binsize = var.var_type.binsize();
                    let vars: Vec<i32> = (0..binsize).map(|v| v as i32 + var.bdd_var_id).collect();
                    let vars = self.b.make_set(&vars);
                    let next_to_normal: Vec<(i32,i32)> = (0..binsize).map(|v| (v as i32 + var.bdd_var_id + binsize, v as i32 + var.bdd_var_id)).collect();
                    let pair = self.b.make_pair(&next_to_normal);

                    entry.insert(Ts {
                        f: self.b.zero(),
                        next_to_normal: pair,
                        vars: vars,
                        var: a.var
                    })
                },
                Entry::Occupied(entry) => entry.into_mut(),
            };
            c.f = self.b.or(&c.f, &trans);
        }
    }

    fn uc_trans(&mut self, name: &str, guard: &Ex, actions: &[Ac]) {
        let g = self.from_expr(guard);
        let mut free = Vec::new();
        let mut action = self.b.one();
        for a in actions {
            let (a,f) = self.from_ac(&a);
            free.extend(f.iter());
            action = self.b.and(&action, &a);
        }
        let f = self.make_trans_free(&g, &action, &free);
        self.transitions.insert(name.into(), f.clone());

        self.uc_transitions.insert(name.into(), f);
        let b = self.make_backward_trans(&g, &action);
        self.buc_transitions.insert(name.into(), b);
    }

    fn respect_domains(&self) -> BDD {
        let mut rd = self.b.one();
        self.vars.iter().for_each(|v|
            if let BDDVarType::Enum(d) = &v.var_type {
                rd = self.b.and(&rd, &d.dom)
            });
        rd
    }

    pub fn extend_forbidden(&self, forbidden: &BDD) -> BDD {
        // uncontrollable backwards
        let mut ub = self.b.zero();
        for t in self.buc_transitions.values() {
            ub = self.b.or(&ub, &t);
        }

        // forbidden states always include respecting the domains of
        // the variables.
        let rd = self.respect_domains();
        let forbidden = self.b.and(&forbidden, &rd);

        let c = ctrl(&self.b, &forbidden, &ub, &self.normal_vars, &self.next_to_normal);
        let sat = self.b.satcount_set(&c, &self.normal_vars);
        println!("Numer of forbidden: {}\n", sat);
        c
    }

    // exponential time and size!
    fn clauses_from_bdd(&self, f: &BDD) -> Vec<Clause> {
        // negate the relation to build our clauses
        let f = self.b.not(&f);

        let now = std::time::Instant::now();
        let cubes = self.b.allsat_vec(&f);
        println!("allsat computed in {}ms", now.elapsed().as_millis());

        let mut clauses = Vec::new();
        let cubes: Vec<_> = cubes.into_iter().map(|c| { Cube(c) }).collect();
        let cubes = CubeList::new().merge(&CubeList::from_list(&cubes));

        for cube in cubes.cubes() {
            let mut lits = Vec::new();
            for (i,v) in cube.0.iter().enumerate() {
                match v {
                    // negate the values again here to go from dnf to cnf
                    Valuation::False    => lits.push(Lit { var: i, neg: false}), // true
                    Valuation::True     => lits.push(Lit { var: i, neg: true}), // false
                    Valuation::DontCare => {}, // dontcare
                };
            }
            clauses.push(Clause(lits));
        }

        clauses
    }

    pub fn model_as_satmodel(&self, init: &BDD, invar_goals: &[(BDD,BDD)], invariants: &[BDD]) -> SATModel {
        let norm_vars: Vec<usize> = self.b.scan_set(&self.normal_vars).iter().map(|a|*a as usize).collect();
        let next_vars: Vec<usize> = self.b.scan_set(&self.next_vars).iter().map(|a|*a as usize).collect();
        let num_vars = norm_vars.len() + next_vars.len() + self.transitions.len();


        // add an extra var for each transition that is only used to track it...
        let var_num = self.b.get_varnum();
        // add some more
        self.b.set_varnum(var_num+self.transitions.len() as i32);

        let now = std::time::Instant::now();
        let mut trans_map = HashMap::new();

        let mut ft = self.b.zero();
        for (i, (name, t)) in self.transitions.iter().enumerate() {
            let others: Vec<usize> = (0..self.transitions.len()).filter(|a| a != &i).collect();
            let mut zero = self.b.one();
            for k in others {
                let other = self.b.nithvar(k as i32 + var_num);
                zero = self.b.and(&zero, &other);
            }
            let var_index = var_num + i as i32;
            let ith = self.b.ithvar(var_index);
            let t = self.b.and(&t, &ith);
            let t = self.b.and(&t, &zero);
            trans_map.insert(name.clone(), var_index);
            ft = self.b.or(&ft, &t);
        }

        let (top_lit, mut trans_clauses, added1) = to_cnf_tseitsin(&self.b, &ft, num_vars);
        trans_clauses.push(Clause(vec![top_lit]));

        println!("num clauses for transition relation {}", trans_clauses.len());
        println!("computed in {}ms", now.elapsed().as_millis());

        let rd = self.respect_domains();
        let (top_lit, mut global_invariants, mut added2) = to_cnf_tseitsin(&self.b, &rd, num_vars + added1);
        global_invariants.push(Clause(vec![top_lit]));

        for i in invariants {
            let (top_lit, clauses, added) = to_cnf_tseitsin(&self.b, i, num_vars + added1 + added2);
            global_invariants.extend(clauses.into_iter());
            global_invariants.push(Clause(vec![top_lit]));
            added2 += added;
        }

        let (top_lit, mut init_clauses, added3) = to_cnf_tseitsin(&self.b, &init, num_vars + added1 + added2);
        init_clauses.push(Clause(vec![top_lit]));

        // goal(s)
        let mut goal_added = 0;
        let mut goal_clauses = Vec::new();
        let mut goal_tops = Vec::new();
        let mut invar_clauses = Vec::new();
        let mut invar_tops = Vec::new();

        for (invar, goal) in invar_goals {
            let (top, new_goal_clauses, added) =
                to_cnf_tseitsin(&self.b, goal, num_vars + added1 + added2 + added3 + goal_added);
            goal_added += added;
            goal_tops.push(top);
            goal_clauses.extend(new_goal_clauses.into_iter());

            let (top, new_invar_clauses, added) =
                to_cnf_tseitsin(&self.b, invar, num_vars + added1 + added2 + added3 + goal_added);
            goal_added += added;
            invar_tops.push(top);
            invar_clauses.extend(new_invar_clauses.into_iter());
        }

        println!("num aux variables {}", added1 + added2 + added3 + goal_added);

        SATModel {
            num_aux_vars: added1 + added2 + added3 + goal_added,
            trans_map: trans_map, // name -> variable id
            trans_clauses: trans_clauses,
            global_invariants: global_invariants,
            norm_vars, // variable id
            next_vars, // variable id
            init_clauses: init_clauses,
            goal_clauses: goal_clauses,
            goal_tops: goal_tops,
            invar_clauses: invar_clauses,
            invar_tops: invar_tops,
        }
    }

    pub fn sat_result_to_values(&self, clause: &Clause) -> Vec<Value> {
        let mut result = Vec::new();

        for v in &self.vars {
            let res = match &v.var_type {
                BDDVarType::Bool => {
                    let cv = clause.0.iter().find(|l| l.var as i32 == v.bdd_var_id).unwrap();
                    if cv.neg {
                        Value::Bool(false)
                    } else {
                        Value::Bool(true)
                    }
                },
                BDDVarType::Enum(dom) => {
                    let mut d = self.b.one();
                    for i in 0 .. dom.binsize {
                        let cv = clause.0.iter().find(|l| l.var as i32 == v.bdd_var_id + i).unwrap();
                        if cv.neg {
                            let t = self.b.nithvar(v.bdd_var_id+i as i32);
                            d = self.b.and(&d, &t);
                        } else {
                            let t = self.b.ithvar(v.bdd_var_id+i as i32);
                            d = self.b.and(&d, &t);
                        }
                    }

                    let d = dom.allowed_values(&self.b, &d);

                    assert!(d.len() == 1);
                    Value::InDomain(d[0] as usize)
                }
            };
            result.push(res);
        }
        result
    }

    pub fn controllable(&self, initial: &BDD, forbidden: &BDD) -> (BDD, BDD, BDD) {
        let mut ft = self.b.zero();
        for t in self.transitions.values() {
            ft = self.b.or(&ft, t);
        }

        // make sure forbidden and initial states take the variable domains into account.
        let rd = self.respect_domains();
        let forbidden = self.b.and(&forbidden, &rd);
        let initial = self.b.and(&initial, &rd);

        // find all reachable states
        let now = std::time::Instant::now();

        let r = reach(&self.b, &initial, &ft, &self.normal_vars, &self.next_to_normal);
        println!("Reachable states computed in: {}ms\n", now.elapsed().as_micros());
        let now = std::time::Instant::now();
        let r2 = reach2(&self.b, &initial, &self.disj_transitions);
        println!("Reachable states2 computed in: {}ms\n", now.elapsed().as_micros());

        let sat = self.b.satcount_set(&r, &self.normal_vars);
        println!("Numer of reachable: {}\n", sat);

        let sat = self.b.satcount_set(&r2, &self.normal_vars);
        println!("Numer of reachable2: {}\n", sat);

        // uncontrollable backwards
        let mut ub = self.b.zero();
        for t in self.buc_transitions.values() {
            ub = self.b.or(&ub, &t);
        }

        let now = std::time::Instant::now();
        let bad = ctrl(&self.b, &forbidden, &ub, &self.normal_vars, &self.next_to_normal);

        let n_bad = self.b.not(&bad);
        // controllable is the intersection of not bad and reachable
        let controllable = self.b.and(&n_bad, &r);

        println!("Controllable states computed in: {}ms\n", now.elapsed().as_millis());

        let sat = self.b.satcount_set(&controllable, &self.normal_vars);
        println!("Numer of controllable: {}\n", sat);

        (r, bad, controllable)
    }


    pub fn compute_guards(&mut self, controllable: &BDD, bad: &BDD) -> HashMap<String, BDD> {
        let mut new_guards = HashMap::new();
        // let now = std::time::Instant::now();
        for (name, trans) in &self.transitions {
            // only need to check controllable transitions
            // if self.buc_transitions.contains_key(name) { continue };

            // compute the states from which we can reach a safe state as x
            let bt = self.swap_normal_and_next(&trans);

            let x = self.b.relprod(&controllable, &bt, &self.normal_vars);
            let new_guard = self.b.replace(&x, &self.next_to_normal);

            let xf = self.b.and(&trans, &new_guard);

            // are the transitions the same?
            let y = self.b.and(&controllable, &trans);
            let z = self.b.and(&controllable, &xf);

            if y != z {
                // simplify out previous guard from new guard.
                let orig_guard = self.b.exist(&trans, &self.next_vars);
                let new_guard = self.b.simplify(&new_guard, &orig_guard);
                let new_guard = self.compute_guard(&z, &new_guard,&trans,&controllable,&bad);
                new_guards.insert(name.clone(), new_guard);
            }
        }
        // println!("guards computed in {}ms", now.elapsed().as_millis());

        new_guards.iter().map(|(k, v)| (k.clone(), v.clone())).collect()
    }


    fn compute_guard(
        &self,
        reachable: &BDD,
        new_guard: &BDD,
        trans: &BDD,
        good_states: &BDD,
        bad_states: &BDD) -> BDD {
        let z = reachable;

        let support = self.b.support(&new_guard);
        let support_vars = self.b.scan_set(&support);

        let mut new_guard = new_guard.clone();

        for s in &support_vars {
            // remove elemts in s
            let mut temp_ng = new_guard.clone();
            let varset = self.b.make_set(&[*s]);
            temp_ng = self.b.exist(&temp_ng, &varset);

            // check if guard still works as it should
            let temp = self.b.and(&trans, &temp_ng);

            let bt = self.swap_normal_and_next(&temp);

            let y = self.b.and(&bad_states, &bt);

            if y == self.b.zero() {
                let zz = self.b.and(&good_states, &temp);
                if z == &zz { // no loss of permissiveness
                    new_guard = temp_ng.clone();
                }
            }
        }

        // return the best we have
        new_guard
    }

    // uses exhaustive search to eliminate more terms
    #[allow(dead_code)]
    fn compute_minimal_guard(
        &self,
        new_guard: &BDD,
        trans: &BDD,
        good_states: &BDD,
        bad_states: &BDD) -> BDD {

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

        for (num_iters, s) in ntps.into_iter().enumerate() {
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
        }

        // nothing better found
        new_guard.clone()
    }
}

fn powerset<T: Clone>(e: &[T]) -> Vec<Vec<T>> {
    let mut r = Vec::new();
    for x in 1..=e.len() {
        for z in e.iter().combinations(x) {
            r.push(z.iter().map(|&x| x.clone()).collect());
        }
    }

    r
}

#[test]
fn ps_test() {
    let mut x = vec![1, 2, 3, 3, 4];
    x.dedup();
    let x = powerset(&x);

    assert!(x[0] == vec![1]);
    assert!(x[x.len()-1] == vec![1,2,3,4]);
}


#[derive(Debug, Clone, PartialEq)]
struct Lit2 {
    var: usize, // variable index
    neg: bool, // negated?
    new: bool, // is this a new variable (i.e. tseitsin var)
}

#[derive(Debug, Clone, PartialEq)]
struct Clause2(Vec<Lit2>);

fn to_cnf_tseitsin(b: &BDDManager, f: &BDD, tseitsin_offset: usize) -> (Lit, Vec<Clause>, usize) {
    // base case
    if f == &b.zero() {
        return (Lit { var: tseitsin_offset, neg: false },
                vec![Clause(vec!(Lit { var: tseitsin_offset, neg: false })),
                     Clause(vec!(Lit { var: tseitsin_offset, neg: true }))], 1)
    } else if f == &b.one() {
        return (Lit { var: tseitsin_offset, neg: false },
                vec![Clause(vec!(Lit { var: tseitsin_offset, neg: false },
                                 Lit { var: tseitsin_offset, neg: true }))], 1)
    }

    // we want to generate the following clauses for each
    // node x hi low
    // x & hi -> v     => -x V -hi V v
    // x & -hi -> -v   => -x V hi V -v
    // -x & lo -> v    => x V -lo V v
    // -x & -lo -> -v  => x V lo V -v
    // hi & lo -> v    => -hi V -lo V v
    // -hi & -lo -> v  => hi V lo v -v
    // ONE -> v_one
    // ZERO -> -v_zero
    // bdd (top) -> p (i.e. the bdd must be true)

    let mut clauses = Vec::new();
    let mut visited = Vec::new();

    fn rec(b: &BDDManager, f: &BDD, clauses: &mut Vec<Clause2>, visited: &mut Vec<usize>) {
        if f == &b.zero() || f == &b.one() {
            // done!
            return;
        }
        let node = f.node_index() as usize;
        if visited.contains(&node) {
            return;
        } else {
            visited.push(node);
        }

        let var = f.var() as usize;
        let node_lo = f.low().node_index() as usize;
        let node_hi = f.high().node_index() as usize;

        let c1 = Clause2(vec![ Lit2 { var: var, neg: true, new: false },
                               Lit2 { var: node_hi, neg: true, new: true },
                               Lit2 { var: node, neg: false, new: true }, ]);
        let c2 = Clause2(vec![ Lit2 { var: var, neg: true, new: false },
                               Lit2 { var: node_hi, neg: false, new: true },
                               Lit2 { var: node, neg: true, new: true }, ]);
        let c3 = Clause2(vec![ Lit2 { var: var, neg: false, new: false },
                               Lit2 { var: node_lo, neg: true, new: true },
                               Lit2 { var: node, neg: false, new: true }, ]);
        let c4 = Clause2(vec![ Lit2 { var: var, neg: false, new: false },
                               Lit2 { var: node_lo, neg: false, new: true },
                               Lit2 { var: node, neg: true, new: true }, ]);
        let c5 = Clause2(vec![ Lit2 { var: node_hi, neg: true, new: true },
                               Lit2 { var: node_lo, neg: true, new: true },
                               Lit2 { var: node, neg: false, new: true }, ]);
        let c6 = Clause2(vec![ Lit2 { var: node_hi, neg: false, new: true },
                               Lit2 { var: node_lo, neg: false, new: true },
                               Lit2 { var: node, neg: true, new: true }, ]);

        clauses.push(c1);
        clauses.push(c2);
        clauses.push(c3);
        clauses.push(c4);
        clauses.push(c5);
        clauses.push(c6);


        rec(&b, &f.low(), clauses, visited);
        rec(&b, &f.high(), clauses, visited);
    }

    rec(&b, &f, &mut clauses, &mut visited);

    // these could be shared but I'm not sure it would make a difference
    let one = Clause2(vec![ Lit2 { var: 1, neg: false, new: true } ]);
    let zero = Clause2(vec![ Lit2 { var: 0, neg: true, new: true } ]);
    clauses.push(one);
    clauses.push(zero);

    // top clause == bdd is true. we might need this separately so dont put it in the list of clauses
    // let top = Clause2(vec![ Lit2 { var: f.node_index() as usize, neg: false, new: true } ]);
    // dont return the top clause, we might want to just use the literal instead
    // clauses.push(top);

    // rewrite into clauses where tseitsin vars are appended to the end (after "offset")
    let mut new_vars: Vec<usize> = clauses.iter().flat_map(|c| {
        let inner: Vec<usize> =
            c.0.iter().filter_map(|l| {
                if l.new { Some(l.var) } else { None } }).collect();
        inner
    }).collect();

    new_vars.sort();
    new_vars.dedup();

    // make new top literal
    let top_var = tseitsin_offset + new_vars.iter().position(|&x|x==f.node_index() as usize).unwrap();
    let top_lit = Lit { var: top_var, neg: false };

    let num_new_vars = new_vars.len();

    let mut fixed_clauses: Vec<Clause> = Vec::new();

    for c in clauses {
        let lits: Vec<Lit> = c.0.iter().map(|l| {
            let var = if l.new {
                tseitsin_offset + new_vars.iter().position(|&x|x==l.var).unwrap()
            } else {
                l.var
            };
            Lit { var: var, neg: l.neg }
        }).collect();
        fixed_clauses.push(Clause(lits));
    }

    return (top_lit, fixed_clauses, num_new_vars);
}

#[test]
fn test_to_cnf_tseitsin() {

    let b = buddy_rs::take_manager(10000, 10000);
    b.set_varnum(3);

    let x = b.ithvar(0);
    let y = b.ithvar(1);
    let z = b.ithvar(2);

    // x & (y | z)
    let yz = b.or(&y, &z);
    let xyz = b.and(&x, &yz);


    let (top_lit, clauses, added) = to_cnf_tseitsin(&b, &xyz, b.get_varnum() as usize);

    println!("added {} new variables", added);
    println!("top literal: {:?}", top_lit);
    clauses.iter().for_each(|c| {
        println!("clause {:?}", c);
    });

    let xyz2 = b.not(&xyz);

    let (top_lit, clauses, added) = to_cnf_tseitsin(&b, &xyz2, b.get_varnum() as usize + added);

    println!("added {} new variables", added);
    println!("top literal: {:?}", top_lit);
    clauses.iter().for_each(|c| {
        println!("clause {:?}", c);
    });

    buddy_rs::return_manager(b);

    assert!(false);
}

#[test]
fn test_to_cnf_tseitsin_base_cases() {

    let b = buddy_rs::take_manager(10000, 10000);

    let one = b.one();

    let (top_lit, clauses, added) = to_cnf_tseitsin(&b, &one, b.get_varnum() as usize);

    println!("added {} new variables", added);
    println!("top literal: {:?}", top_lit);
    clauses.iter().for_each(|c| {
        println!("clause {:?}", c);
    });

    let zero = b.zero();
    let (top_lit, clauses, added) = to_cnf_tseitsin(&b, &zero, b.get_varnum() as usize);

    println!("added {} new variables", added);
    println!("top literal: {:?}", top_lit);
    clauses.iter().for_each(|c| {
        println!("clause {:?}", c);
    });

    buddy_rs::return_manager(b);

    assert!(false);
}
