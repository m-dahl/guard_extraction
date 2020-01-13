use boolean_expression::*;
use itertools::Itertools;
// use std::cmp::Ord;
// use std::fmt::Debug;
// use std::hash::Hash;

pub fn relprod(b: &mut BDD, states: BDDFunc, transitions: BDDFunc, variables: &[BDDLabel]) -> BDDFunc {
    let mut f = b.and(states, transitions);

    for v in variables {
        let sf = b.restrict(f, *v, false);
        let st = b.restrict(f, *v, true);
        f = b.or(sf, st);
    }

    f
}

pub fn exist(b: &mut BDD, mut f: BDDFunc, variables: &[BDDLabel]) -> BDDFunc {
    for v in variables {
        let sf = b.restrict(f, *v, false);
        let st = b.restrict(f, *v, true);
        f = b.or(sf, st);
    }

    f
}

pub fn replace(b: &mut BDD, func: BDDFunc, pairing: &[(BDDLabel, BDDLabel)]) -> BDDFunc {
    let reverse_pair: Vec<_> = pairing.iter().map(|(a,b)|(*b,*a)).collect();
    b.subst(func, &reverse_pair)
}

// swap using temporary terminals
pub fn swap(b: &mut BDD, func: BDDFunc, pairing: &[(BDDLabel, BDDLabel)], temps: &[BDDLabel]) -> BDDFunc {
    let pair1: Vec<_> = pairing
        .iter()
        .zip(temps.iter())
        .map(|((x, _y), z)| (*z, *x))
        .collect();

    let pair2: Vec<_> = pairing
        .iter()
        .zip(temps.iter())
        .map(|((_x, y), z)| (*y, *z))
        .collect();

    let nf = replace(b, func, &pair1);
    let nf = replace(b, nf, pairing);
    replace(b, nf, &pair2)
}

pub fn powerset<T: Clone>(e: &[T]) -> Vec<Vec<T>> {
    let mut r = Vec::new();
    for x in 1..(e.len() + 1) {
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
    let mut x = powerset(&x);

    assert!(x[0] == vec![1]);
    assert!(x[x.len()-1] == vec![1,2,3,4]);
}

// backwards uncontrollable reachability
fn ucb(
    b: &mut BDD,
    vars: &Vec<BDDLabel>,
    pairing: &Vec<(BDDLabel, BDDLabel)>,
    backwards_uncontrollable: BDDFunc,
    forbidden: BDDFunc,
) -> BDDFunc {
    let mut new_forbidden = forbidden;

    loop {
        let old = new_forbidden;
        let new = relprod(b, old, backwards_uncontrollable, vars); // possible trans
        let new = replace(b, new, pairing); // to source states
        new_forbidden = b.or(old, new);

        if old == new_forbidden {
            break;
        }
    }
    new_forbidden
}

// backwards reachability
fn rb(
    b: &mut BDD,
    vars: &Vec<BDDLabel>,
    pairing: &Vec<(BDDLabel, BDDLabel)>,
    backwards_transitions: BDDFunc,
    marked: BDDFunc,
    forbidden: BDDFunc,
) -> BDDFunc {
    let not_forbidden = b.not(forbidden);
    let mut s = b.and(marked, not_forbidden);

    loop {
        let old = s;
        let new = relprod(b, old, backwards_transitions, vars); // possible trans
        let new = replace(b, new, pairing); // to source states
        s = b.or(old, new);
        s = b.and(s, not_forbidden);

        if old == s {
            break;
        }
    }

    s
}

// compute nonblocking and controllability and return the forbidden states
pub fn nbc(
    b: &mut BDD,
    vars: &Vec<BDDLabel>,
    pairing: &Vec<(BDDLabel, BDDLabel)>,
    backwards_transitions: BDDFunc,
    unc_backwards_transitions: BDDFunc,
    marked: BDDFunc,
    forbidden: BDDFunc,
) -> BDDFunc {
    let mut s = forbidden;

    loop {
        let old = s;
        let new = rb(b, vars, pairing, backwards_transitions, marked, old);
        // new has safe states
        let forbidden = b.not(new); // and R
        let new2 = ucb(b, vars, pairing, unc_backwards_transitions, forbidden);
        s = b.or(s, new2);

        if old == s {
            break;
        }
    }

    s
}

// compute controllability and return the forbidden states
pub fn ctrl(
    b: &mut BDD,
    vars: &Vec<BDDLabel>,
    pairing: &Vec<(BDDLabel, BDDLabel)>,
    ub: BDDFunc,
    forbidden: BDDFunc,
) -> BDDFunc {
    let mut fx = forbidden;
    loop {
        let old = fx;

        let new = relprod(b, old, ub, vars); // possible trans
        let new = replace(b, new, pairing); // to source states

        fx = b.or(new, old);
        if old == fx {
            break;
        }
    }
    fx
}

pub fn reachable(
    b: &mut BDD,
    vars: &Vec<BDDLabel>,
    pairing: &Vec<(BDDLabel, BDDLabel)>,
    ft: BDDFunc,
    initial: BDDFunc,
) -> BDDFunc {
    let mut r = initial;
    loop {
        let old = r;
        let new = relprod(b, old, ft, vars); // possible trans
        let new = replace(b, new, pairing); // to source states
        r = b.or(old, new);

        if old == r {
            break;
        }
    }
    r
}


#[derive(Debug, PartialEq, Clone)]
pub struct BDDDomain {
    pub size: usize,
    pub binsize: usize,
    pub offset: usize, // where does the block start in the number of variables
    pub dom: BDDFunc,
}

impl BDDDomain {
    pub fn new(b: &mut BDD, size: usize, offset: usize) -> Self {
        let mut binsize = 1;
        let mut calcsize = 2;

        while calcsize < size {
            binsize += 1;
            calcsize *= 2;
        }

        let mut val = size - 1;
        let mut dom = BDD_ONE;

        for n in 0..binsize {
            let t = b.terminal(n + offset);
            let nt = b.not(t);
            let tmp = if val & 0x1 == 0x1 {
                b.or(nt, dom)
            } else {
                b.and(nt, dom)
            };

            val >>= 1;
            dom = tmp;
        }

        BDDDomain {
            size,
            binsize,
            offset,
            dom,
        }
    }

    pub fn belongs(&self, terminal: BDDLabel) -> bool {
        terminal >= self.offset && terminal < self.offset + self.binsize
    }

    // check if domain accepts "d"
    pub fn digit(&self, b: &mut BDD, d: usize) -> BDDFunc {
        let mut val = d;
        let mut v = BDD_ONE;
        for n in 0..self.binsize {
            let term = if val & 0x1 == 0x1 {
                b.terminal(n + self.offset)
            } else {
                let t = b.terminal(n + self.offset);
                b.not(t)
            };
            v = b.and(term, v);
            val >>= 1;
        }
        v
    }

    pub fn allowed_values(&self, b: &mut BDD, f: BDDFunc) -> Vec<usize> {
        let mut res = Vec::new();
        for i in 0..self.size {
            let v = self.digit(b, i);
            // let v = b.and(v, d); // restrict to known values of the domain
            if b.and(f, v) != BDD_ZERO {
                res.push(i);
            }
        }
        res
    }

    pub fn domain_bdd(&self) -> BDDFunc {
        self.dom
    }
}

pub fn satcount(b: &mut BDD, f: BDDFunc, varcount: usize) -> f64 {
    let size = f64::powf(2.0, varcount as f64 - 1.0);
    return size * satcount_rec(b, f);
}

fn satcount_rec(b: &mut BDD, f: BDDFunc) -> f64 {
    if f == BDD_ONE {
        return 1.0;
    } else if f == BDD_ZERO {
        return 0.0;
    }

    let node = b.nodes[f].clone();
    let mut size = 0.0;
    let mut s = 1.0;

    let low_label = if node.lo == BDD_ONE {
        1.0
    } else if node.lo == BDD_ZERO {
        0.0
    } else {
        b.nodes[node.lo].label as f64
    };
    s *= f64::powf(2.0, low_label - node.label as f64 - 1.0);
    size += s * satcount_rec(b, node.lo);

    let hi_label = if node.hi == BDD_ONE {
        1.0
    } else if node.hi == BDD_ZERO {
        0.0
    } else {
        b.nodes[node.hi].label as f64
    };
    s = 1.0;
    s *= f64::powf(2.0, hi_label - node.label as f64 - 1.0);
    size += s * satcount_rec(b, node.hi);

    return size;
}

#[test]
fn test_satcount() {
    let mut bdd = BDD::new();
    let a = bdd.terminal(0);
    let b = bdd.terminal(1);
    let c = bdd.terminal(2);

    let ab = bdd.and(a,b);
    let abc = bdd.or(ab,c);


    let count = satcount(&mut bdd, abc, 3);

    println!("count: {:#?}", count);

    assert!(false);
}

fn raw(bdd: &mut BDD, f: BDDFunc, d: &BDDDomain) {
    if f == BDD_ZERO {
        println!("input: ZERO");
    }
    else if f == BDD_ONE {
        println!("input: ONE");
    } else {
        println!("input: {:?}", f);
    }

    if f == BDD_ZERO || f == BDD_ONE {
        println!("done");
        return;
    }
    let node = bdd.nodes[f].clone();
    println!("node: {:?}", node);


    if node.label == d.offset {
        println!("node is starting the domain... {}", d.offset);
        let allowed = d.allowed_values(bdd, f);
        println!("variable can take on: {:?}", allowed);
        println!("skipping until variable {}", d.offset + d.binsize);
    }


    raw(bdd, node.lo, d);
    raw(bdd, node.hi, d);
}



pub fn raw_terms(bdd: &mut BDD, f: BDDFunc, acum: &mut Vec<BDDLabel>) {
    if f == BDD_ZERO || f == BDD_ONE {
        return;
    }

    let node = bdd.nodes[f].clone();
    acum.push(node.label);

    raw_terms(bdd, node.lo, acum);
    raw_terms(bdd, node.hi, acum);
}

pub fn terms_in_bddfunc(b: &mut BDD, f: BDDFunc) -> Vec<BDDLabel> {
    let mut v = Vec::new();
    raw_terms(b, f, &mut v);
    v.sort(); v.dedup();
    v
}


pub fn print_expr_with_domains(b: &mut BDD, num_vars: usize, f: BDDFunc, domains: &[BDDDomain]) {
    let cubes = b.to_max_cubes(f, num_vars);
    let mut remaining_added: Vec<_> = cubes.cubes().map(|c| (c.clone(), String::new())).collect();

    for d in domains {
        let next = remaining_added.clone();
        remaining_added.clear();
        for (key, group) in &next.iter().group_by(|&(c,s)| {
            let mut c = c.clone();
            for i in 0..d.binsize {
                c = c.with_var(i + d.offset, CubeVar::DontCare);
            }
            (c,s)
        }) {
            let mut x = BDD_ONE;
            let g: Vec<_> = group.into_iter().cloned().collect();
            // println!("{:?} - {:?}", key, g);
            g.into_iter().for_each(|c| {
                let mut xx = BDD_ZERO;
                c.0.vars().enumerate().for_each(|(i, v)| match v {
                    &CubeVar::False if d.belongs(i) => {
                        let t = b.terminal(i);
                        let nt = b.not(t);
                        xx = b.or(xx, nt);
                    },
                    &CubeVar::True if d.belongs(i) => {
                        let t = b.terminal(i);
                        xx = b.or(xx, t);
                    },
                    _ => {} ,
                });
                x = b.and(x, xx);
            });
            let v = d.allowed_values(b, x);
            let s =
            if v.len() > 0 {
                // println!("d IN {:?} AND ", v);
                format!(" v({}) IN {:?} OR {}", d.offset, v, key.1)
            } else { //println!("AND");
                key.1.clone()
            };
            // println!("{:?} - {:?}", key, v);

            remaining_added.push((key.0, s));
        }
    }

    for (cube, domains) in &remaining_added {
        cube.vars().enumerate().for_each(|(i, v)| match v {
            &CubeVar::False => print!(" NOT {} OR", i),
            &CubeVar::True => print!(" {} OR", i),
            _ => {},
        });
        print!("{}", domains);
        println!(" AND ");
    }
}


#[test]
fn test_domain2() {
    let domain: Vec<String> = vec![
        "l".into(),
        "u".into(),
        "unknown".into(),
        "unknown1".into(),
        "unknown2".into(),
    ];

    let domain2: Vec<String> = vec![
        "off".into(),
        "on".into(),
        "unknown".into(),
    ];

    let mut b = BDD::new();
    let d = BDDDomain::new(&mut b, domain.len(), 5);

    let d2 = BDDDomain::new(&mut b, domain2.len(), 2);

    // let x = Expr::and(Expr::not(Expr::Terminal(0)), Expr::and(
    //     Expr::Terminal(1), Expr::not(Expr::Terminal(2))));
    let x = Expr::and(Expr::not(Expr::Terminal(5)), Expr::and(
         Expr::Terminal(6), Expr::not(Expr::Terminal(7))));
    // let x = Expr::not(Expr::Terminal(5));

    let x = b.from_expr(&x);
    let xn = b.not(x);


    let y1 = b.from_expr(&Expr::not(Expr::Terminal(0)));
    let y2 = b.from_expr(&Expr::not(Expr::Terminal(1)));

    let x1 = b.and(x,y1);
    let x2 = b.and(xn,y2);

    let x = b.or(x1,x2);

    let p = b.from_expr(&Expr::not(Expr::Terminal(8)));
    let z = b.terminal(2);
    let z = b.not(z);
    let p = b.and(p, z);

    let x = b.and(x, p);

    // let allowed = d.allowed_values(&mut b, x);
    // let allowed: Vec<_> = allowed.iter().map(|a| domain[*a].clone()).collect();
    // println!("variable can take on: {:#?}", allowed);


    // let n = b.nodes[x].clone();
    // println!("NODE: {:?}", n);

    // raw(&mut b, x, &d);

    // let expr = b.to_expr2(x, 9);
    // println!("FULL: {:?}", expr);

    let domains = vec![d, d2];

    print_expr_with_domains(&mut b, 9, x, &domains);

    assert!(false);
}

#[test]
fn test_boolean_domain() {
    let domain: Vec<String> = vec![
        "off".into(),
        "on".into(),
    ];

    let mut b = BDD::new();
    let d = BDDDomain::new(&mut b, domain.len(), 5);

    // let x = Expr::and(Expr::not(Expr::Terminal(0)), Expr::and(
    //     Expr::Terminal(1), Expr::not(Expr::Terminal(2))));
    // let x = Expr::not(Expr::Terminal(5));
    let x = Expr::and(Expr::not(Expr::Terminal(0)), Expr::not(Expr::Terminal(5)));

    let x = b.from_expr(&x);

    let allowed = d.allowed_values(&mut b, x);
    let allowed: Vec<_> = allowed.iter().map(|a| domain[*a].clone()).collect();
    println!("variable can take on: {:#?}", allowed);

    let domains = vec![d];
    print_expr_with_domains(&mut b, 6, x, &domains);

    assert!(false);
}
