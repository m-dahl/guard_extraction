use boolean_expression::*;
use itertools::Itertools;

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

pub fn satcount(b: &mut BDD, f: BDDFunc, varcount: usize) -> f64 {
    let s = if f == BDD_ZERO {
        0.0
    } else if f == BDD_ONE {
        f64::powf(2.0, varcount as f64)
    } else {
        let label = b.nodes[f].label;
        f64::powf(2.0, label as f64)
    };
    s * satcount_rec(b, f, varcount)
}

fn satcount_rec(b: &mut BDD, f: BDDFunc, varcount: usize) -> f64 {
    if f == BDD_ONE {
        return 1.0;
    } else if f == BDD_ZERO {
        return 0.0;
    }

    let node = b.nodes[f].clone();

    let low = if node.lo == BDD_ONE {
        // here is also a diff, if we skip down to one over multiple levels
        f64::powf(2.0, (varcount - node.label) as f64 - 1.0)
    } else if node.lo == BDD_ZERO {
        0.0
    } else {
        let low_label = b.nodes[node.lo].label as f64;
        let s = f64::powf(2.0, low_label - node.label as f64 - 1.0);
        s * satcount_rec(b, node.lo, varcount)
    };

    let high = if node.hi == BDD_ONE {
        f64::powf(2.0, (varcount - node.label) as f64 - 1.0)
    } else if node.hi == BDD_ZERO {
        0.0
    } else {
        let hi_label = b.nodes[node.hi].label as f64;
        let s = f64::powf(2.0, hi_label - node.label as f64 - 1.0);
        s * satcount_rec(b, node.hi, varcount)
    };

    return low + high;
}

#[test]
fn test_satcount() {
    let mut bdd = BDD::new();
    let a = bdd.terminal(0);
    let b = bdd.terminal(1);
    let c = bdd.terminal(2);
    let d = bdd.terminal(3);


    let ab = bdd.and(a,b);
    let abc = bdd.or(ab,c);

    let nd = bdd.not(d);
    let abcd = bdd.and(abc,nd);

    let bc = bdd.and(b,c);


    // abc
    // 000
    // 001 +
    // 010
    // 011 +
    // 100
    // 101 +
    // 110 *
    // 111 *

    let count = satcount(&mut bdd, BDD_ONE, 3);
    assert_eq!(count, (1 << 3) as f64);

    let count = satcount(&mut bdd, BDD_ZERO, 3);
    assert_eq!(count, 0f64);

    let count = satcount(&mut bdd, abc, 3);
    assert_eq!(count, 5.0);

    let count = satcount(&mut bdd, abcd, 4);
    assert_eq!(count, 5.0);

    let count = satcount(&mut bdd, abc, 4);
    assert_eq!(count, 10.0);

    let count = satcount(&mut bdd, bc, 3);
    assert_eq!(count, 2.0);

    let count = satcount(&mut bdd, bc, 4);
    assert_eq!(count, 4.0);
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
