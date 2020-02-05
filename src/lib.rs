use std::collections::HashMap;
use std::collections::HashSet;
use std::iter::FromIterator;
use itertools::Itertools;
use buddy_rs::*;

mod bdd_domain;
pub use bdd_domain::*;

mod context;
pub use context::*;

// compute reachable states
pub fn reach(bdd: &BDDManager, initial: &BDD,
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

// compute controllability and return the forbidden states
pub fn ctrl(
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
pub fn nbc(
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

#[derive(Debug, Clone)]
pub struct BDDVar {
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

pub struct BDDContext<'a> {
    pub b: &'a BDDManager,
    pub vars: Vec<BDDVar>,
    pub num_bdd_normal_vars: i32,

    pub transitions: HashMap<String, BDD>,
    pub uc_transitions: HashMap<String, BDD>,

    next_to_normal: BDDPair,
    normal_to_next: BDDPair,
    next_to_temp: BDDPair,
    temp_to_normal: BDDPair,

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
                    b.ext_varnum(3); // we need a normal, next, and temp variable
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
                    b.ext_varnum(3 * binsize); // normal, next, and temp variables
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
        println!("used bdd variables: {}", b.get_varnum());

        let num_bdd_normal_vars = normal_vars.len() as i32;

        let temp_offset = num_bdd_normal_vars * 2;
        let temp_vars: Vec<_> = (temp_offset .. temp_offset + num_bdd_normal_vars).collect();

        let pairing: Vec<_> = normal_vars.iter().zip(next_vars.iter())
            .map(|(x, y)| (*x as i32, *y as i32)).collect();

        let next_to_normal: Vec<_> = pairing.iter().map(|(x,y)| (*y,*x)).collect();
        let next_to_normal = b.make_pair(&next_to_normal);

        let normal_to_next: Vec<_> = pairing.iter().map(|(x,y)| (*x,*y)).collect();
        let normal_to_next = b.make_pair(&normal_to_next);

        let next_to_temp: Vec<_> = next_vars.iter()
            .zip(temp_vars.iter())
            .map(|(y, z)| (*y, *z))
            .collect();
        let next_to_temp = b.make_pair(&next_to_temp);

        let temp_to_normal: Vec<_> = normal_vars.iter()
            .zip(temp_vars.iter())
            .map(|(y, z)| (*z, *y))
            .collect();
        let temp_to_normal = b.make_pair(&temp_to_normal);

        let normal_vars = b.make_set(&normal_vars);
        let next_vars = b.make_set(&next_vars);

        BDDContext {
            b,
            vars,
            num_bdd_normal_vars,
            transitions: HashMap::new(),
            uc_transitions: HashMap::new(),

            next_to_normal,
            normal_to_next,
            next_to_temp,
            temp_to_normal,

            normal_vars,
            next_vars,
        }
    }

    fn swap_normal_and_next(&self, f: &BDD) -> BDD {
        let nf = self.b.replace(&f, &self.next_to_temp);
        let nf = self.b.replace(&nf, &self.normal_to_next);
        self.b.replace(&nf, &self.temp_to_normal)
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
                                let nbv = self.b.not(&bv);
                                let nov = self.b.not(&ov);
                                let bv_and_ov = self.b.and(&bv,&ov);
                                let nbv_and_nov = self.b.and(&nbv, &nov);

                                // bv <-> ov
                                self.b.or(&bv_and_ov, &nbv_and_nov)
                            },
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

                            }
                        }

                    },
                }
            },
        }
    }

    fn domain_cubes_to_ex(&self, cubes: &[Vec<DomainCubeVal>]) -> Ex {
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

    pub fn to_expr(&self, f: &BDD) -> Ex {
        // make sure we respect the domains of our variables.
        let rd = self.respect_domains();
        let f = self.b.and(&f, &rd);
        let cubes = self.b.allsat_vec(&f);

        // transform these cubes back into their original definitions

        let mut domain_cubes = Vec::new();

        for cube in &cubes {
            let mut new_cube = Vec::new();
            for v in &self.vars {

                let res = match &v.var_type {
                    BDDVarType::Bool => {
                        match cube[v.bdd_var_id as usize] {
                            Valuation::DontCare => DomainCubeVal::DontCare,
                            Valuation::True =>
                                DomainCubeVal::Bool(true),
                            Valuation::False =>
                                DomainCubeVal::Bool(false),
                        }
                    },
                    BDDVarType::Enum(dom) => {
                        let slice = &cube[(v.bdd_var_id) as usize ..(v.bdd_var_id+dom.binsize) as usize];
                        if slice.iter().all(|v| v == &Valuation::DontCare) {
                            DomainCubeVal::DontCare
                        } else {
                            // build expression in cube, check which digits it matches
                            let mut allowed = self.b.one();

                            slice.iter().enumerate().for_each(|(i, val)| match val {
                                Valuation::DontCare => {},
                                Valuation::True => {
                                    let t = self.b.ithvar(v.bdd_var_id+i as i32);
                                    allowed = self.b.and(&allowed, &t);
                                },
                                Valuation::False => {
                                    let f = self.b.nithvar(v.bdd_var_id+i as i32);
                                    allowed = self.b.and(&allowed, &f);
                                },
                            });

                            let allowed = dom.allowed_values(&self.b, &allowed);

                            assert!(allowed.len() > 0);
                            DomainCubeVal::Domain(allowed)
                        }
                    }
                };
                new_cube.push(res)
            }
            domain_cubes.push(new_cube);
        }

        // TODO: here we should merge cubes that only differ w.r.t. enum variables.
        // eg. (x1 & v = 2) | (x1 & v = 3) should be merged to (x1 & v in [2,3])
        // additionally, if dom(v) = [1,2,3], the cube should be simplified to (x1 & v != 1])

        self.domain_cubes_to_ex(&domain_cubes)
    }

    fn make_trans(&mut self, guard: &BDD, action: &BDD) -> BDD {
        let action_support = self.b.support(&action);
        let terms_in_action = self.b.scan_set(&action_support);
        let terms_in_action: HashSet<_> = HashSet::from_iter(terms_in_action.iter().cloned());

        let all_normal_vars = self.b.scan_set(&self.normal_vars);
        let all_normal_vars: HashSet<_> = HashSet::from_iter(all_normal_vars.iter().cloned());

        let not_updated: Vec<_> = all_normal_vars.difference(&terms_in_action).cloned().collect();

        let iffs = not_updated.iter().fold(self.b.one(), |acc, i| {
            // we want a = a'
            let a = self.b.ithvar(*i);
            // so we replace a with its next pair to get a'
            let b = self.b.ithvar(*i);
            let b = self.b.replace(&b, &self.normal_to_next);

            let iff = self.b.biimp(&a, &b);
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
        let f = self.make_trans(&g, &a);
        self.transitions.insert(name.into(), f);
    }

    pub fn uc_trans(&mut self, name: &str, guard: Ex, action: Ex) {
        let g = self.from_expr(&guard);
        let a = self.from_expr(&action);
        let f = self.make_trans(&g, &a);
        self.transitions.insert(name.into(), f.clone());
        self.uc_transitions.insert(name.into(), f);

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
        let mut uc = self.b.zero();
        for t in self.uc_transitions.values() {
            uc = self.b.or(&uc, t);
        }
        let ub = self.swap_normal_and_next(&uc);

        // forbidden states always include respecting the domains of
        // the variables.
        let rd = self.respect_domains();
        let forbidden = self.b.and(&forbidden, &rd);

        ctrl(&self.b, &forbidden, &ub, &self.normal_vars, &self.next_to_normal)
    }

    pub fn controllable(&self, initial: &BDD, forbidden: &BDD) -> (BDD, BDD, BDD) {
        let mut ft = self.b.zero();
        for t in self.transitions.values() {
            ft = self.b.or(&ft, t);
        }

        let mut uc = self.b.zero();
        for t in self.uc_transitions.values() {
            uc = self.b.or(&uc, t);
        }

        // make sure initial states take the variable domains into account.
        let rd = self.respect_domains();

        let initial = self.b.and(&initial, &rd);

        let not_forbidden = self.b.not(&forbidden);
        let initial = self.b.and(&initial, &not_forbidden);

        // find all reachable states
        let now = std::time::Instant::now();

        let r = reach(&self.b, &initial, &ft, &self.normal_vars, &self.next_to_normal);
        println!("Reachable states computed in: {}ms\n", now.elapsed().as_millis());
        let sat = self.b.satcount_set(&r, &self.normal_vars);
        println!("Numer of reachable: {}\n", sat);

        // uncontrollable backwards
        let ub = self.swap_normal_and_next(&uc);

        let bad = ctrl(&self.b, &forbidden, &ub, &self.normal_vars, &self.next_to_normal);

        let n_bad = self.b.not(&bad);
        // controllable is the intersection of not bad and reachable
        let controllable = self.b.and(&n_bad, &r);

        println!("Controllable states computed in: {}ms\n", now.elapsed().as_millis());

        let sat = self.b.satcount_set(&controllable, &self.normal_vars);
        println!("Numer of controllable: {}\n", sat);

        (r, bad, controllable)
    }


    pub fn compute_guards(&mut self, controllable: &BDD, bad: &BDD) -> HashMap<String, Ex> {
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
            let new_guard = self.b.simplify(&new_guard, &orig_guard);

            let xf = self.b.and(&trans, &new_guard);
            let y = self.b.relprod(&controllable, &trans, &self.normal_vars);
            let z = self.b.relprod(&controllable, &xf, &self.normal_vars);

            if y != z {
                // let now = std::time::Instant::now();

                // let mg = self.compute_minimal_guard(&new_guard,&trans,&controllable,&bad);
                let mg = self.compute_guard(&new_guard,&trans,&controllable,&bad);

                // println!("new guard computed in {}ms", now.elapsed().as_millis());

                new_guards.insert(name.clone(), mg);
            }
        }

        new_guards.iter().map(|(k, v)| (k.clone(), self.to_expr(v))).collect()
    }


    fn compute_guard(
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

        let mut new_guard = new_guard.clone();

        for s in &support_vars {
            // remove elemts in s
            let mut temp_ng = new_guard.clone();
            let varset = self.b.make_set(&[*s]);
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
