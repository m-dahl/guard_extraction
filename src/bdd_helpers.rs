use boolean_expression::*;
use Expr;
use std::collections::BTreeMap;
use std::collections::HashMap;
use std::cmp::Ord;
use std::fmt::Debug;
use std::hash::Hash;
use std::ops::Add;

pub fn relprod<T>(b: &mut BDD<T>, states: BDDFunc, transitions: BDDFunc, variables: &[T]) -> BDDFunc
where
    T: Clone + Debug + Eq + Ord + Hash + Copy,
{
    let mut f = b.and(states, transitions);

    for v in variables {
        let sf = b.restrict(f, *v, false);
        let st = b.restrict(f, *v, true);
        f = b.or(sf, st);
    }

    f
}

pub fn exist<T>(b: &mut BDD<T>, mut f: BDDFunc, variables: &[T]) -> BDDFunc
where
    T: Clone + Debug + Eq + Ord + Hash + Copy,
{
    for v in variables {
        let sf = b.restrict(f, *v, false);
        let st = b.restrict(f, *v, true);
        f = b.or(sf, st);
    }

    f
}

pub fn replace<T>(b: &mut BDD<T>, func: BDDFunc, pairing: &[(T, T)]) -> BDDFunc
where
    T: Clone + Debug + Eq + Ord + Hash + Copy,
{
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

// swap using temporary terminals
pub fn swap<T>(b: &mut BDD<T>, func: BDDFunc, pairing: &[(T, T)], temps: &[T]) -> BDDFunc
where
    T: Clone + Debug + Eq + Ord + Hash + Copy,
{
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

pub fn state_in_bddfunc(bdd: &BDD<u32>, f: BDDFunc, state: &[bool]) -> bool {
    let mut h = HashMap::new();
    for (i, v) in state.iter().enumerate() {
        h.insert(i as u32, *v);
    }
    bdd.evaluate(f, &h)
}

fn eval_bddfunc(bdd: &BDD<usize>, f: BDDFunc, state: &[bool]) -> bool {
    let mut h = HashMap::new();
    for (i, v) in state.iter().enumerate() {
        h.insert(i as usize, *v);
    }
    bdd.evaluate(f, &h)
}

struct BDDDomain {
    size: usize,
    binsize: usize,
    offset: usize, // where does the block start in the number of variables
    dom: BDDFunc,
}

impl BDDDomain {
    pub fn new(b: &mut BDD<usize>, size: usize, offset: usize) -> Self {
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

    // check if domain accepts "d"
    fn bv(&self, b: &mut BDD<usize>, d: usize) -> BDDFunc {
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

    pub fn allowed_values(&self, b: &mut BDD<usize>, f: BDDFunc) -> Vec<usize> {
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
    let x = Expr::not(Expr::Terminal(5));

    let x = b.from_expr(&x);

    let allowed = d.allowed_values(&mut b, x);
    let allowed: Vec<_> = allowed.iter().map(|a| domain[*a].clone()).collect();
    println!("variable can take on: {:#?}", allowed);

    assert!(false);
}
