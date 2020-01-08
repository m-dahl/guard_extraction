use boolean_expression::*;
use Expr;
use itertools::Itertools;
use std::cmp::Ord;
use std::fmt::Debug;
use std::hash::Hash;
use std::ops::Add;

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

pub fn replace2(b: &mut BDD, func: BDDFunc, pairing: &[(BDDLabel, BDDLabel)]) -> BDDFunc {
    let mut f = func;
    for (s, t) in pairing {
        // set s to t
        let s = b.terminal(*s);
        let t = b.terminal(*t);
        let f1 = b.and(s, t);
        let ns = b.not(s);
        let nt = b.not(t);
        let f2 = b.and(ns, nt);
        let iff = b.or(f1, f2);
        f = b.and(iff, f);
    }

    for (_, t) in pairing {
        // quantify away t
        let sf = b.restrict(f, *t, false);
        let st = b.restrict(f, *t, true);
        f = b.or(sf, st);
    }
    f // now we have "s"
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

// swap using temporary terminals
pub fn swap2(b: &mut BDD, func: BDDFunc, pairing: &[(BDDLabel, BDDLabel)], temps: &[BDDLabel]) -> BDDFunc {
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

    let nf = replace2(b, func, &pair1);
    let nf = replace2(b, nf, pairing);
    replace2(b, nf, &pair2)
}

pub fn state_to_expr(state: &[bool]) -> Expr<u32> {
    state
        .iter()
        .enumerate()
        .fold(Expr::Const(true), |acc, (i, v)| {
            if *v {
                Expr::and(acc, Expr::Terminal(i as u32))
            } else {
                Expr::and(acc, Expr::not(Expr::Terminal(i as u32)))
            }
        })
}

pub fn state_to_expr2<T>(state: &[bool]) -> Expr<T>
where
    T: Clone + Debug + Eq + Ord + Hash + Copy + Add<Output=T> + From<usize>,
{
    state
        .iter()
        .enumerate()
        .fold(Expr::Const(true), |acc, (i, v)| {
            if *v {
                Expr::and(acc, Expr::Terminal(i.into()))
            } else {
                Expr::and(acc, Expr::not(Expr::Terminal(i.into())))
            }
        })
}

pub fn state_in_bddfunc(bdd: &BDD, f: BDDFunc, state: &[bool]) -> bool {
    bdd.evaluate(f, state).unwrap()
}

fn eval_bddfunc(bdd: &BDD, f: BDDFunc, state: &[bool]) -> bool {
    bdd.evaluate(f, state).unwrap()
}

struct BDDDomain {
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

    fn belongs(&self, terminal: BDDLabel) -> bool {
        terminal >= self.offset && terminal < self.offset + self.binsize
    }

    // check if domain accepts "d"
    fn bv(&self, b: &mut BDD, d: usize) -> BDDFunc {
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
            let v = self.bv(b, i);
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


#[test]
fn test_domain2() {
    let domain: Vec<String> = vec![
        "l".into(),
        "u".into(),
        "unknown".into(),
        "unknown1".into(),
        "unknown2".into(),
    ];

    let mut b = BDD::new();
    let d = BDDDomain::new(&mut b, domain.len(), 5);

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
    let x = b.and(x, p);


    let allowed = d.allowed_values(&mut b, x);
    let allowed: Vec<_> = allowed.iter().map(|a| domain[*a].clone()).collect();
    println!("variable can take on: {:#?}", allowed);


    let n = b.nodes[x].clone();
    println!("NODE: {:?}", n);

    raw(&mut b, x, &d);

    let expr = b.to_expr2(x, 9);
    println!("FULL: {:?}", expr);

    let cubes = b.to_max_cubes(x, 9);

    for (key, group) in &cubes.cubes().into_iter().group_by(|c| {
        let v: Vec<_> = c.vars()
            .enumerate()
            .flat_map(|(i, v)| match v {
                &CubeVar::False if !d.belongs(i) => Some(Expr::not(Expr::Terminal(i))),
                &CubeVar::True if !d.belongs(i) => Some(Expr::Terminal(i)),
                &CubeVar::DontCare => None,
                _ => None,
            }).collect();
        v
    }) {
        let mut x = BDD_ONE;
        let g: Vec<_> = group.into_iter().cloned().collect();
        // println!("{:?} - {:?}", key, g);
        g.into_iter().for_each(|c| {
            let mut xx = BDD_ZERO;
            c.vars().enumerate().for_each(|(i, v)| match v {
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
        let v = d.allowed_values(&mut b, x);
        for c in &key {
            print!("{:?} OR ", c);
        }
        if v.len() > 0 {
            println!("d IN {:?} AND ", v);
        } else { println!("AND"); }
        // println!("{:?} - {:?}", key, v);
    }

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

    assert!(false);
}