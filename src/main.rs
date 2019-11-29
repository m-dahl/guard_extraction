use boolean_expression::*;
use Expr;

use std::cmp::Ord;
use std::collections::BTreeMap;
use std::collections::HashMap;
use std::collections::HashSet;
use std::iter::FromIterator;
use std::fmt::Debug;
use std::hash::Hash;
use std::ops::Add;


mod bdd_helpers;
use bdd_helpers::*;

pub fn terms_in_expr<T>(e: &Expr<T>) -> Vec<T>
where
    T: Clone + Debug + Eq + Ord + Hash,
{
    let mut v = Vec::new();
    match e {
        &Expr::Terminal(ref t) => v.push(t.clone()),
        &Expr::Const(_val) => {}
        &Expr::Not(ref x) => {
            let mut nv = terms_in_expr(&**x);
            v.append(&mut nv);
        }
        &Expr::And(ref a, ref b) => {
            let mut nv1 = terms_in_expr(&**a);
            let mut nv2 = terms_in_expr(&**b);
            v.append(&mut nv1);
            v.append(&mut nv2);
        }
        &Expr::Or(ref a, ref b) => {
            let mut nv1 = terms_in_expr(&**a);
            let mut nv2 = terms_in_expr(&**b);
            v.append(&mut nv1);
            v.append(&mut nv2);
        }
    }
    v
}

pub fn powerset<T>(e: &[T]) -> Vec<Vec<T>>
where
    T: Clone + Debug + Eq + Ord + Hash,
{
    use itertools::Itertools;
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
    x.pop();
    x.reverse();
    println!("{:?}", x);

    assert!(false);
}

fn iff<T>(a: Expr<T>, b: Expr<T>) -> Expr<T>
where
    T: Clone + Debug + Eq + Ord + Hash,
{
    Expr::or(
        Expr::and(a.clone(), b.clone()),
        Expr::and(Expr::not(a), Expr::not(b)),
    )
}

fn bits_to_hashmap(bits: usize, n: usize, h: &mut HashMap<u32, bool>) {
    for b in 0..bits {
        h.insert(b as u32, (n & (1 << b)) != 0);
    }
}

fn bits_to_hashmap2(bits: usize, n: usize, h: &mut HashMap<usize, bool>) {
    for b in 0..bits {
        h.insert(b, (n & (1 << b)) != 0);
    }
}

fn iffs(vs: &[u32], offset: usize) -> Expr<u32> {
    vs.iter().fold(Expr::Const(true), |acc, i| {
        Expr::and(
            acc,
            iff(
                Expr::Terminal(*i as u32),
                Expr::Terminal(*i + offset as u32),
            ),
        )
    })
}

fn iffs2<T>(vs: &[T], offset: T) -> Expr<T>
where
    T: Clone + Debug + Eq + Ord + Hash + Copy + Add<Output=T>,
{
    vs.iter().fold(Expr::Const(true), |acc, i| {
        Expr::and(
            acc,
            iff(
                Expr::Terminal(*i as T),
                Expr::Terminal(*i + offset as T),
            ),
        )
    })
}

fn ucb<T>(
    b: &mut BDD<T>,
    vars: &Vec<T>,
    pairing: &Vec<(T, T)>,
    backwards_uncontrollable: BDDFunc,
    forbidden: BDDFunc,
) -> BDDFunc
where
    T: Clone + Debug + Eq + Ord + Hash + Copy,
{
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

fn rb<T>(
    b: &mut BDD<T>,
    vars: &Vec<T>,
    pairing: &Vec<(T, T)>,
    backwards_transitions: BDDFunc,
    marked: BDDFunc,
    forbidden: BDDFunc,
) -> BDDFunc
where
    T: Clone + Debug + Eq + Ord + Hash + Copy,
{
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

fn nbc<T>(
    b: &mut BDD<T>,
    vars: &Vec<T>,
    pairing: &Vec<(T, T)>,
    backwards_transitions: BDDFunc,
    unc_backwards_transitions: BDDFunc,
    marked: BDDFunc,
    forbidden: BDDFunc,
) -> BDDFunc
where
    T: Clone + Debug + Eq + Ord + Hash + Copy,
{
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

fn main() {
    println!("Hello, world!");
}


// TODO: the litterature is fairly decided on using an interleaved
// variable ordering for better performance. for now we just put all
// next values at the end.
fn make_trans<T>(b: &mut BDD<T>, guard: Expr<T>, action: Expr<T>, vars: &[T]) -> BDDFunc
where
    T: Clone + Debug + Eq + Ord + Hash + Copy + Add<Output=T> + From<usize>,
{
    let vl: T = vars.len().into();
    let vs: HashSet<T> = HashSet::from_iter(vars.iter().cloned());
    let t = terms_in_expr(&action);
    let ts = HashSet::from_iter(t.iter().cloned());

    let not_updated: Vec<_> = vs.difference(&ts).cloned().collect();
    let iffs = iffs2(&not_updated, vl);

    let destvars: Vec<_> = vars.iter().map(|i| *i + vl).collect();
    let temps: Vec<_> = vars.iter().map(|i| *i + vl + vl).collect();

    let pairing: Vec<_> = destvars  // swap function is for y to x
        .iter()
        .zip(vars.iter())
        .map(|(x, y)| (*x, *y))
        .collect();

    let action = b.from_expr(&action);
    let action = swap(b, action, &pairing, &temps); // change to next indexes

    let guard = b.from_expr(&guard);
    let iffs = b.from_expr(&iffs);

    let trans = b.and(guard, action);
    b.and(trans, iffs)
}

#[test]
fn test_make_trans() {
    let vars = vec![
        0, // door_closed_m
        1, // door_opened_m
        2, // door_gs_c, false = closed, true = opened
        3, // lock_l_c
    ];

    let x = |n| Expr::Terminal(n);
    let and = |a, b| Expr::and(a, b);
    let not = |a| Expr::not(a);

    let mut b: BDD<usize> = BDD::new();
    let t = make_trans(&mut b, and(not(x(0)), and(not(x(1)), and(not(x(2)), not(x(3))))), x(2), &vars);
    let e = b.to_expr(t);
    println!("expr: {:#?}", e);
    assert!(false);
}


fn compute_minimal_guard<T>(b: &mut BDD<T>, orig_guard: BDDFunc, new_guard: BDDFunc,
                            f_orig: BDDFunc, bt: BDDFunc, // TODO these
                            good_states: BDDFunc, bad_states: BDDFunc,
                            vars: &[T], pairing: &[(T,T)], temps: &[T]) -> BDDFunc
where
    T: Clone + Debug + Eq + Ord + Hash + Copy,
{
    let forbx = relprod(b, bad_states, bt, vars);
    let mut forbx = replace(b, forbx, pairing);

    let fe = b.to_expr(orig_guard);
    let tie = terms_in_expr(&fe);
    // now hack f out of x
    let mut xx = new_guard;
    xx = exist(b, xx, &tie);
    forbx = exist(b, forbx, &tie);

    // assert that my thinking is correct...
    let tot = b.and(xx, orig_guard);
    assert_eq!(tot, new_guard);

    // guard need to stop us from reaching forbidden
    forbx = b.not(forbx);
    let forbe = b.to_expr(forbx);

    let f_and_forb = b.and(f_orig, forbx);
    let bt = swap(b, f_and_forb, &pairing, &temps);
    // assert that my thinking is correct...
    assert_eq!(relprod(b, bad_states, bt, &vars), BDD_ZERO);

    let fe = b.to_expr(orig_guard);
    let e = b.to_expr(xx);

    let tie_x = terms_in_expr(&e);
    let tie_y = terms_in_expr(&forbe);

    // chose the smallest guard representation
    let mut new_guard = if tie_x.len() < tie_y.len() { e } else {
        // println!("chosing forbidden");
        // forbe
        e // TODO!
    };

    // try to remove terms that doesnt lead us to a forbidden state
    // and doesn't over-constrain us wrt the reachable states
    let temp_ng = b.from_expr(&new_guard);
    let temp = b.and(f_orig, temp_ng);
    let bt = swap(b, temp, &pairing, &temps);
    let z = relprod(b, good_states, bt, &vars);

    let mut new_terms = terms_in_expr(&new_guard);
    new_terms.sort();
    new_terms.dedup(); // sort + dedup to uniquify
    let mut ntps = powerset(&new_terms);
    let all = ntps.pop(); // no use trying to remove all terms
    ntps.reverse(); // remove the largest amount of terms first,
    // stop as soon as we succeed

    let mut cache = HashMap::new();
    for s in ntps {
        // remove elemts in s
        let mut temp_ng = b.from_expr(&new_guard);
        for t in &s {
            let sf = b.restrict(temp_ng, *t, false);
            let st = b.restrict(temp_ng, *t, true);
            temp_ng = b.or(sf, st);
        }

        // check if still works and cache result
        let temp = b.and(f_orig, temp_ng);

        let ok = match cache.get(&temp) {
            Some(&ok) => ok,
            None => {
                let bt = swap(b, temp, &pairing, &temps);
                let y = relprod(b, bad_states, bt, &vars); //was bad
                let y = replace(b, y, &pairing);
                let y = b.and(y, good_states);

                let ok = if y == BDD_ZERO {
                    let zz = relprod(b, good_states, bt, &vars);
                    z == zz
                } else {
                    false
                };
                cache.insert(temp, ok);
                ok
            }
        };

        if ok {
            let te = b.to_expr(temp_ng);
            new_guard = te;
            // println!("choosing: {:?} out of {:?}", s, all);
            return temp_ng;
            break; // stop here!
        }
    }

    return b.from_expr(&new_guard);
}

#[test]
fn make_trans_full_bdd_door_lock_xy() {
    // set up variables

    let vars = vec![
        0, // door_closed_m
        1, // door_opened_m
        2, // door_gs_c, false = closed, true = opened
        3, // lock_l_c
        4, // lock_u_c
        5, // lock_e
        6, // lock_e_unknown = true
        7, // x
        8, // y
    ];

    let bits = vars.len();
    let bitsm = 1 << bits;
    println!("State bits: {}, 0..{}", bits, bitsm);

    let destvars: Vec<_> = vars.iter().map(|i| *i + vars.len()).collect();
    let temps: Vec<_> = vars.iter().map(|i| *i + 2 * vars.len()).collect();

    let pairing: Vec<_> = vars
        .iter()
        .zip(destvars.iter())
        .map(|(x, y)| (*x, *y))
        .collect();

    println!("{:?}", vars);
    println!("{:?}", destvars);
    println!("{:?}", temps);

    let mut b = BDD::new();

    // convenience
    let x = |n| Expr::Terminal(n);
    let and = |a, b| Expr::and(a, b);
    let or = |a, b| Expr::or(a, b);
    let not = |a| Expr::not(a);

    // set up transitions
    let door_open_d = ("door_open_d", make_trans(&mut b, not(x(1)), x(2), &vars));
    let door_open_e = ("door_open_e", make_trans(&mut b, and(x(2), not(x(1))), and(x(1), not(x(0))), &vars));
    let door_close_d = ("door_close_d", make_trans(&mut b, not(x(0)), not(x(2)), &vars));
    let door_close_e = ("door_close_e", make_trans(&mut b, and(not(x(2)),not(x(0))), and(not(x(1)), x(0)), &vars));
    let lock_lock_d = ("lock_lock_d", make_trans(&mut b, or(x(6), not(x(5))), and(x(3), and(not(x(4)), and(x(5), not(x(6))))), &vars));
    let lock_unlock_d = ("lock_unlock_d", make_trans(&mut b, or(x(6), x(5)), and(not(x(3)), and(x(4), and(not(x(5)), not(x(6))))), &vars));
    let xm1 = ("x1", make_trans(&mut b, not(x(7)), x(7), &vars));
    let xm2 = ("x2", make_trans(&mut b, x(7), not(x(7)), &vars));
    let ym1 = ("y1", make_trans(&mut b, not(x(8)), x(8), &vars));
    let ym2 = ("y2", make_trans(&mut b, x(8), not(x(8)), &vars));

    let mut transitions = HashMap::new();
    transitions.insert(door_open_d.0, door_open_d.1);
    transitions.insert(door_open_e.0, door_open_e.1.clone()); // todo
    transitions.insert(door_close_d.0, door_close_d.1);
    transitions.insert(door_close_e.0, door_close_e.1.clone());

    transitions.insert(lock_lock_d.0, lock_lock_d.1);
    transitions.insert(lock_unlock_d.0, lock_unlock_d.1);
    transitions.insert(xm1.0, xm1.1);
    transitions.insert(xm2.0, xm2.1);
    transitions.insert(ym1.0, ym1.1);
    transitions.insert(ym2.0, ym2.1);

    let mut uc_transitions = HashMap::new();
    uc_transitions.insert(door_open_e.0, door_open_e.1);
    uc_transitions.insert(door_close_e.0, door_close_e.1);

    let is = [false, false, false, false, false, false, true, false, false];
    let ise = state_to_expr2(&is);

    // forbid opening
    let forbidden = and(not(x(1)), and(x(2), x(5)));
    let forbidden = b.from_expr(&forbidden);

    let forbidden2 = and(not(x(1)), x(7));
    let forbidden2 = b.from_expr(&forbidden2);

    let forbidden3 = and(x(7), x(8));
    let forbidden3 = b.from_expr(&forbidden3);

    // door cannot be closed and opened at the same time.
    let forbidden4 = and(x(0), x(1));
    let forbidden4 = b.from_expr(&forbidden4);


    let forbidden = b.or(forbidden, forbidden2);
    let forbidden = b.or(forbidden, forbidden3);
    let forbidden = b.or(forbidden, forbidden4);


    let mut ft = BDD_ZERO;
    for t in transitions.values() {
        ft = b.or(ft, *t);
    }

    let mut uc = BDD_ZERO;
    for t in uc_transitions.values() {
        uc = b.or(uc, *t);
    }

    // let uc = b.or(ft2, ft4); // BDD_ZERO
    let ub = swap(&mut b, uc, &pairing, &temps); // uncontrollable backwards

    // backwards transitions
    let bt = swap(&mut b, ft, &pairing, &temps);

    let fi = b.from_expr(&ise);
    // let fi = b.not(forbidden); // b.from_expr(&ise);

    // find all reachable states
    let now = std::time::Instant::now();
    let mut r = fi;
    loop {
        let old = r;
        let new = relprod(&mut b, old, ft, &vars); // possible trans
        let new = replace(&mut b, new, &pairing); // to source states
        r = b.or(old, new);

        if old == r {
            break;
        }
    }

    let marked = BDD_ONE; // all states marked...
    let bad = nbc(&mut b, &vars, &pairing, bt, ub, marked, forbidden);

    let n_bad = b.not(bad);
    let nonblock = b.and(n_bad, r); // the intersection and not bad and reachable

    //    println!("Reachable nonblocking states");
    //    println!("============================");
    let mut bitmap = HashMap::new();
    let mut state_count = 0;
    for i in 0..bitsm {
        bits_to_hashmap2(bits, i, &mut bitmap);
        if b.evaluate(nonblock, &mut bitmap) {
            //let m: BTreeMap<_, _> = bitmap.iter().collect();
            //println!("i: {} - {:?}", i, m);
            state_count += 1;
        }
    }

    println!("Nbr of reachable states: {}\n", state_count);
    println!("Computed in: {}ms\n", now.elapsed().as_millis());

    let mut state_count = 0;
    for i in 0..bitsm {
        bits_to_hashmap2(bits, i, &mut bitmap);
        if b.evaluate(bad, &mut bitmap) {
            //let m: BTreeMap<_, _> = bitmap.iter().collect();
            //println!("i: {} - {:?}", i, m);
            state_count += 1;
        }
    }
    println!("Nbr of forbidden states: {}\n", state_count);

    let mut state_count = 0;
    for i in 0..bitsm {
        bits_to_hashmap2(bits, i, &mut bitmap);
        if b.evaluate(forbidden, &mut bitmap) {
            //let m: BTreeMap<_, _> = bitmap.iter().collect();
            //println!("i: {} - {:?}", i, m);
            state_count += 1;
        }
    }
    println!("Nbr of more forbidden states: {}\n", state_count);

    let mut state_count = 0;
    for i in 0..bitsm {
        bits_to_hashmap2(bits, i, &mut bitmap);
        if b.evaluate(r, &mut bitmap) {
            //let m: BTreeMap<_, _> = bitmap.iter().collect();
            //println!("i: {} - {:?}", i, m);
            state_count += 1;
        }
    }
    println!("Nbr of reachable states: {}\n", state_count);


    // find guards...
    for (name, t) in transitions {
        // println!("transition? {:?}", t);
        let f = t; // b.from_expr(&t);
        let f_orig = f;
        let bt = swap(&mut b, f, &pairing, &temps);
        let x = relprod(&mut b, nonblock, bt, &vars);
        let x = replace(&mut b, x, &pairing);

        // x is new guard. use it and compare with original trans
        let xf = b.and(f, x);
        let y = relprod(&mut b, nonblock, f, &vars);
        let z = relprod(&mut b, nonblock, xf, &vars);

        if y != z {
            let now = std::time::Instant::now();

            let orig_guard = exist(&mut b, f, &destvars);
            let new_guard = x;
            let good_states = nonblock;
            let bad_states = bad;
            let mg = compute_minimal_guard(&mut b, orig_guard, new_guard, f_orig, bt,
                                           good_states, bad_states,
                                           &vars, &pairing, &temps);

            let te = b.to_expr(mg);
            // new guard!
            println!("new guard computed in {}ms", now.elapsed().as_millis());
            println!("guard added for transition {}", name);
            println!("orig guard: {:?}", orig_guard);
            println!("new guard: {:?}", te);
            println!("");
        }
    }

    assert!(false);
}







#[test]
fn verify_guards_door_lock_xy() {
    // set up variables

    let vars = vec![
        0, // door_closed_m
        1, // door_opened_m
        2, // door_gs_c, false = closed, true = opened
        3, // lock_l_c
        4, // lock_u_c
        5, // lock_e
        6, // lock_e_unknown = true
        7, // x
        8, // y
    ];

    let bits = vars.len();
    let bitsm = 1 << bits;
    println!("State bits: {}, 0..{}", bits, bitsm);

    let destvars: Vec<_> = vars.iter().map(|i| *i + vars.len()).collect();
    let temps: Vec<_> = vars.iter().map(|i| *i + 2 * vars.len()).collect();

    let pairing: Vec<_> = vars
        .iter()
        .zip(destvars.iter())
        .map(|(x, y)| (*x, *y))
        .collect();

    println!("{:?}", vars);
    println!("{:?}", destvars);
    println!("{:?}", temps);

    let mut b = BDD::new();

    // convenience
    let x = |n| Expr::Terminal(n);
    let and = |a, b| Expr::and(a, b);
    let or = |a, b| Expr::or(a, b);
    let not = |a| Expr::not(a);

    // set up transitions
    let door_open_d = ("door_open_d", make_trans(&mut b, and(not(x(1)), not(x(3))), x(2), &vars));
    let door_open_e = ("door_open_e", make_trans(&mut b, and(x(2), not(x(1))), and(x(1), not(x(0))), &vars));
    let door_close_d = ("door_close_d", make_trans(&mut b, and(not(x(0)), not(x(7))), not(x(2)), &vars));
    let door_close_e = ("door_close_e", make_trans(&mut b, and(not(x(2)),not(x(0))), and(not(x(1)), x(0)), &vars));
    let lock_lock_d = ("lock_lock_d", make_trans(&mut b,
                                                 and(or(x(6), not(x(5))), or(x(1), not(x(2)))),
                                                 and(x(3), and(not(x(4)), and(x(5), not(x(6))))), &vars));
    let lock_unlock_d = ("lock_unlock_d", make_trans(&mut b, or(x(6), x(5)), and(not(x(3)), and(x(4), and(not(x(5)), not(x(6))))), &vars));
    let xm1 = ("x1", make_trans(&mut b, and(not(x(8)), and(x(1), and(x(2), not(x(7))))), x(7), &vars));
    let xm2 = ("x2", make_trans(&mut b, x(7), not(x(7)), &vars));
    let ym1 = ("y1", make_trans(&mut b, and(not(x(7)), not(x(8))), x(8), &vars));
    let ym2 = ("y2", make_trans(&mut b, x(8), not(x(8)), &vars));

    let mut transitions = HashMap::new();
    transitions.insert(door_open_d.0, door_open_d.1);
    transitions.insert(door_open_e.0, door_open_e.1.clone()); // todo
    transitions.insert(door_close_d.0, door_close_d.1);
    transitions.insert(door_close_e.0, door_close_e.1.clone());

    transitions.insert(lock_lock_d.0, lock_lock_d.1);
    transitions.insert(lock_unlock_d.0, lock_unlock_d.1);
    transitions.insert(xm1.0, xm1.1);
    transitions.insert(xm2.0, xm2.1);
    transitions.insert(ym1.0, ym1.1);
    transitions.insert(ym2.0, ym2.1);

    let mut uc_transitions = HashMap::new();
    uc_transitions.insert(door_open_e.0, door_open_e.1);
    uc_transitions.insert(door_close_e.0, door_close_e.1);

    let is = [false, false, false, false, false, false, true, false, false];
    let ise = state_to_expr2(&is);

    // forbid opening
    let forbidden = and(not(x(1)), and(x(2), x(5)));
    let forbidden = b.from_expr(&forbidden);

    let forbidden2 = and(not(x(1)), x(7));
    let forbidden2 = b.from_expr(&forbidden2);

    let forbidden3 = and(x(7), x(8));
    let forbidden3 = b.from_expr(&forbidden3);

    let forbidden = b.or(forbidden, forbidden2);
    let forbidden = b.or(forbidden, forbidden3);

    let mut ft = BDD_ZERO;
    for t in transitions.values() {
        ft = b.or(ft, *t);
    }

    let mut uc = BDD_ZERO;
    for t in uc_transitions.values() {
        uc = b.or(uc, *t);
    }

    // let uc = b.or(ft2, ft4); // BDD_ZERO
    let ub = swap(&mut b, uc, &pairing, &temps); // uncontrollable backwards

    // backwards transitions
    let bt = swap(&mut b, ft, &pairing, &temps);

    let fi = b.from_expr(&ise);

    // find all reachable states
    let now = std::time::Instant::now();
    let mut r = fi;
    loop {
        let old = r;
        let new = relprod(&mut b, old, ft, &vars); // possible trans
        let new = replace(&mut b, new, &pairing); // to source states
        r = b.or(old, new);

        if old == r {
            break;
        }
    }

    let marked = BDD_ONE; // all states marked...
    let bad = nbc(&mut b, &vars, &pairing, bt, ub, marked, forbidden);
    let n_bad = b.not(bad);
    let nonblock = b.and(n_bad, r); // the intersection and not bad and reachable

    //    println!("Reachable nonblocking states");
    //    println!("============================");
    let mut bitmap = HashMap::new();
    let mut state_count = 0;
    for i in 0..bitsm {
        bits_to_hashmap2(bits, i, &mut bitmap);
        if b.evaluate(nonblock, &mut bitmap) {
            //let m: BTreeMap<_, _> = bitmap.iter().collect();
            //println!("i: {} - {:?}", i, m);
            state_count += 1;
        }
    }

    println!("Nbr of reachable states: {}\n", state_count);
    println!("Computed in: {}ms\n", now.elapsed().as_millis());

    // find guards...
    for (name, t) in transitions {
        // println!("transition? {:?}", t);
        let f = t; // b.from_expr(&t);
        let f_orig = f;
        let bt = swap(&mut b, f, &pairing, &temps);
        let x = relprod(&mut b, nonblock, bt, &vars);
        let x = replace(&mut b, x, &pairing);

        // x is new guard. use it and compare with original trans
        let xf = b.and(f, x);
        let y = relprod(&mut b, nonblock, f, &vars);
        let z = relprod(&mut b, nonblock, xf, &vars);

        if y != z {
            let now = std::time::Instant::now();

            let orig_guard = exist(&mut b, f, &destvars);
            let new_guard = x;
            let good_states = nonblock;
            let bad_states = bad;
            let mg = compute_minimal_guard(&mut b, orig_guard, new_guard, f_orig, bt,
                                           good_states, bad_states,
                                           &vars, &pairing, &temps);

            let te = b.to_expr(mg);
            // new guard!
            println!("new guard computed in {}ms", now.elapsed().as_millis());
            println!("guard added for transition {}", name);
            println!("orig guard: {:?}", orig_guard);
            println!("new guard: {:?}", te);
            println!("");
        }
    }

    assert!(false);
}









#[test]
fn step1_bdd_door_lock_xy() {
    // set up variables

    let vars = vec![
        0, // x
        1, // y
    ];

    let bits = vars.len();
    let bitsm = 1 << bits;
    // println!("State bits: {}, 0..{}", bits, bitsm);

    let destvars: Vec<_> = vars.iter().map(|i| *i + vars.len()).collect();
    let temps: Vec<_> = vars.iter().map(|i| *i + 2 * vars.len()).collect();

    let pairing: Vec<_> = vars
        .iter()
        .zip(destvars.iter())
        .map(|(x, y)| (*x, *y))
        .collect();

    // println!("{:?}", vars);
    // println!("{:?}", destvars);
    // println!("{:?}", temps);

    let mut b = BDD::new();

    // convenience
    let x = |n| Expr::Terminal(n);
    let and = |a, b| Expr::and(a, b);
//    let or = |a, b| Expr::or(a, b);
    let not = |a| Expr::not(a);

    // set up transitions
    let xm1 = ("x1", make_trans(&mut b, not(x(0)), x(0), &vars));
    let xm2 = ("x2", make_trans(&mut b, x(0), not(x(0)), &vars));
    let ym1 = ("y1", make_trans(&mut b, not(x(1)), x(1), &vars));
    let ym2 = ("y2", make_trans(&mut b, x(1), not(x(1)), &vars));

    let mut transitions = HashMap::new();
    transitions.insert(xm1.0, xm1.1);
    transitions.insert(xm2.0, xm2.1);
    transitions.insert(ym1.0, ym1.1);
    transitions.insert(ym2.0, ym2.1);

//    let mut uc_transitions = HashMap::new();

    let is = [false, false];
    let ise = state_to_expr2(&is);

    let forbidden = and(x(0), x(1));
    let forbidden = b.from_expr(&forbidden);

    let mut ft = BDD_ZERO;
    for t in transitions.values() {
        ft = b.or(ft, *t);
    }

    let mut uc = BDD_ZERO;
    // for t in uc_transitions.values() {
    //     uc = b.or(uc, *t);
    // }

    let ub = swap(&mut b, uc, &pairing, &temps); // uncontrollable backwards

    // backwards transitions
    let bt = swap(&mut b, ft, &pairing, &temps);

    let fi = b.from_expr(&ise);
    let fi = b.not(forbidden); // test...

    // find all reachable states
    let now = std::time::Instant::now();
    let mut r = fi;
    loop {
        let old = r;
        let new = relprod(&mut b, old, ft, &vars); // possible trans
        let new = replace(&mut b, new, &pairing); // to source states
        r = b.or(old, new);

        if old == r {
            break;
        }
    }

    let marked = BDD_ONE; // all states marked...
    let bad = nbc(&mut b, &vars, &pairing, bt, ub, marked, forbidden);
    let n_bad = b.not(bad);
    let nonblock = b.and(n_bad, r); // the intersection and not bad and reachable

    //    println!("Reachable nonblocking states");
    //    println!("============================");
    let mut bitmap = HashMap::new();
    let mut state_count = 0;
    for i in 0..bitsm {
        bits_to_hashmap2(bits, i, &mut bitmap);
        if b.evaluate(nonblock, &mut bitmap) {
            //let m: BTreeMap<_, _> = bitmap.iter().collect();
            //println!("i: {} - {:?}", i, m);
            state_count += 1;
        }
    }

    println!("Nbr of reachable states: {}", state_count);
    println!("Computed in: {}ms", now.elapsed().as_millis());

    // find guards...
    for (name, t) in transitions {
        // println!("transition? {:?}", t);
        let f = t; // b.from_expr(&t);
        let f_orig = f;
        let bt = swap(&mut b, f, &pairing, &temps);
        let x = relprod(&mut b, nonblock, bt, &vars);
        let x = replace(&mut b, x, &pairing);

        // x is new guard. use it and compare with original trans
        let xf = b.and(f, x);
        let y = relprod(&mut b, nonblock, f, &vars);
        let z = relprod(&mut b, nonblock, xf, &vars);

        if y != z {
            let now = std::time::Instant::now();

            let orig_guard = exist(&mut b, f, &destvars);
            let new_guard = x;
            let good_states = nonblock;
            let bad_states = bad;
            let mg = compute_minimal_guard(&mut b, orig_guard, new_guard, f_orig, bt,
                                           good_states, bad_states,
                                           &vars, &pairing, &temps);

            let te = b.to_expr(mg);
            // new guard!
            println!("guard for {}: {:?}, computed in {}ms", name, te, now.elapsed().as_millis());
        }
    }

//    assert!(false);
}




#[test]
fn step2_bdd_door_lock_xy() {
    // set up variables

    let vars = vec![
        0, // door_closed_m
        1, // door_opened_m
        2, // door_gs_c, false = closed, true = opened
        3, // lock_l_c
        4, // lock_u_c
        5, // lock_e
        6, // lock_e_unknown = true
    ];

    let bits = vars.len();
    let bitsm = 1 << bits;
//    println!("State bits: {}, 0..{}", bits, bitsm);

    let destvars: Vec<_> = vars.iter().map(|i| *i + vars.len()).collect();
    let temps: Vec<_> = vars.iter().map(|i| *i + 2 * vars.len()).collect();

    let pairing: Vec<_> = vars
        .iter()
        .zip(destvars.iter())
        .map(|(x, y)| (*x, *y))
        .collect();

    // println!("{:?}", vars);
    // println!("{:?}", destvars);
    // println!("{:?}", temps);

    let mut b = BDD::new();

    // convenience
    let x = |n| Expr::Terminal(n);
    let and = |a, b| Expr::and(a, b);
    let or = |a, b| Expr::or(a, b);
    let not = |a| Expr::not(a);

    // set up transitions
    let door_open_d = ("door_open_d", make_trans(&mut b, not(x(1)), x(2), &vars));
    let door_open_e = ("door_open_e", make_trans(&mut b, and(x(2), not(x(1))), and(x(1), not(x(0))), &vars));
    let door_close_d = ("door_close_d", make_trans(&mut b, not(x(0)), not(x(2)), &vars));
    let door_close_e = ("door_close_e", make_trans(&mut b, and(not(x(2)),not(x(0))), and(not(x(1)), x(0)), &vars));
    let lock_lock_d = ("lock_lock_d", make_trans(&mut b, or(x(6), not(x(5))), and(x(3), and(not(x(4)), and(x(5), not(x(6))))), &vars));
    let lock_unlock_d = ("lock_unlock_d", make_trans(&mut b, or(x(6), x(5)), and(not(x(3)), and(x(4), and(not(x(5)), not(x(6))))), &vars));

    let mut transitions = HashMap::new();
    transitions.insert(door_open_d.0, door_open_d.1);
    transitions.insert(door_open_e.0, door_open_e.1.clone()); // todo
    transitions.insert(door_close_d.0, door_close_d.1);
    transitions.insert(door_close_e.0, door_close_e.1.clone());

    transitions.insert(lock_lock_d.0, lock_lock_d.1);
    transitions.insert(lock_unlock_d.0, lock_unlock_d.1);

    let mut uc_transitions = HashMap::new();
    uc_transitions.insert(door_open_e.0, door_open_e.1);
    uc_transitions.insert(door_close_e.0, door_close_e.1);

    let is = [false, false, false, false, false, false, true];
    let ise = state_to_expr2(&is);

    // forbid opening
    let forbidden = and(not(x(1)), and(x(2), x(5)));
    let forbidden = b.from_expr(&forbidden);

    let mut ft = BDD_ZERO;
    for t in transitions.values() {
        ft = b.or(ft, *t);
    }

    let mut uc = BDD_ZERO;
    for t in uc_transitions.values() {
        uc = b.or(uc, *t);
    }

    // let uc = b.or(ft2, ft4); // BDD_ZERO
    let ub = swap(&mut b, uc, &pairing, &temps); // uncontrollable backwards

    // backwards transitions
    let bt = swap(&mut b, ft, &pairing, &temps);

    let fi = b.from_expr(&ise);
    let fi = b.not(forbidden); // b.from_expr(&ise);
    let unkn = b.terminal(6);
    let fi = b.and(fi, unkn);

    // find all reachable states
    let now = std::time::Instant::now();
    let mut r = fi;
    loop {
        let old = r;
        let new = relprod(&mut b, old, ft, &vars); // possible trans
        let new = replace(&mut b, new, &pairing); // to source states
        r = b.or(old, new);

        if old == r {
            break;
        }
    }

    let marked = BDD_ONE; // all states marked...
    let bad = nbc(&mut b, &vars, &pairing, bt, ub, marked, forbidden);
    let n_bad = b.not(bad);
    let nonblock = b.and(n_bad, r); // the intersection and not bad and reachable

       // println!("Reachable nonblocking states");
       // println!("============================");
    let mut bitmap = HashMap::new();
    let mut state_count = 0;
    for i in 0..bitsm {
        bits_to_hashmap2(bits, i, &mut bitmap);
        if b.evaluate(nonblock, &mut bitmap) {
            // let m: BTreeMap<_, _> = bitmap.iter().collect();
            // println!("i: {} - {:?}", i, m);
            state_count += 1;
        }
    }

    println!("Nbr of reachable states: {}", state_count);
    println!("Computed in: {}ms", now.elapsed().as_millis());

    // find guards...
    for (name, t) in transitions {
        // println!("transition? {:?}", t);
        let f = t; // b.from_expr(&t);
        let f_orig = f;
        let bt = swap(&mut b, f, &pairing, &temps);
        let x = relprod(&mut b, nonblock, bt, &vars);
        let x = replace(&mut b, x, &pairing);

        // x is new guard. use it and compare with original trans
        let xf = b.and(f, x);
        let y = relprod(&mut b, nonblock, f, &vars);
        let z = relprod(&mut b, nonblock, xf, &vars);

        if y != z {
            let now = std::time::Instant::now();

            let orig_guard = exist(&mut b, f, &destvars);
            let new_guard = x;
            let good_states = nonblock;
            let bad_states = bad;
            let mg = compute_minimal_guard(&mut b, orig_guard, new_guard, f_orig, bt,
                                           good_states, bad_states,
                                           &vars, &pairing, &temps);

            let oe = b.to_expr(orig_guard);
            let te = b.to_expr(mg);
            // new guard!
            println!("guard for {}: {:?}, computed in {}ms", name, te, now.elapsed().as_millis());
        }
    }

//    assert!(false);
}


#[test]
fn step3_bdd_door_lock_xy() {
    // set up variables

    let vars = vec![
        0, // door_closed_m
        1, // door_opened_m
        2, // door_gs_c, false = closed, true = opened
        3, // x
    ];

    let bits = vars.len();
    let bitsm = 1 << bits;
    // println!("State bits: {}, 0..{}", bits, bitsm);

    let destvars: Vec<_> = vars.iter().map(|i| *i + vars.len()).collect();
    let temps: Vec<_> = vars.iter().map(|i| *i + 2 * vars.len()).collect();

    let pairing: Vec<_> = vars
        .iter()
        .zip(destvars.iter())
        .map(|(x, y)| (*x, *y))
        .collect();

    // println!("{:?}", vars);
    // println!("{:?}", destvars);
    // println!("{:?}", temps);

    let mut b = BDD::new();

    // convenience
    let x = |n| Expr::Terminal(n);
    let and = |a, b| Expr::and(a, b);
//    let or = |a, b| Expr::or(a, b);
    let not = |a| Expr::not(a);

    // set up transitions
    let door_open_d = ("door_open_d", make_trans(&mut b, not(x(1)), x(2), &vars));
    let door_open_e = ("door_open_e", make_trans(&mut b, and(x(2), not(x(1))), and(x(1), not(x(0))), &vars));
    let door_close_d = ("door_close_d", make_trans(&mut b, not(x(0)), not(x(2)), &vars));
    let door_close_e = ("door_close_e", make_trans(&mut b, and(not(x(2)),not(x(0))), and(not(x(1)), x(0)), &vars));
    let xm1 = ("x1", make_trans(&mut b, not(x(3)), x(3), &vars));
    let xm2 = ("x2", make_trans(&mut b, x(3), not(x(3)), &vars));

    let mut transitions = HashMap::new();
    transitions.insert(door_open_d.0, door_open_d.1);
    transitions.insert(door_open_e.0, door_open_e.1.clone()); // todo
    transitions.insert(door_close_d.0, door_close_d.1);
    transitions.insert(door_close_e.0, door_close_e.1.clone());

    transitions.insert(xm1.0, xm1.1);
    transitions.insert(xm2.0, xm2.1);

    let mut uc_transitions = HashMap::new();
    uc_transitions.insert(door_open_e.0, door_open_e.1);
    uc_transitions.insert(door_close_e.0, door_close_e.1);

    let is = [false, false, false, false, false, false, true, false, false];
    let ise = state_to_expr2(&is);

    let forbidden = and(not(x(1)), x(3));
    let forbidden = b.from_expr(&forbidden);

    let forbidden2 = and(x(0), x(1));
    let forbidden2 = b.from_expr(&forbidden2);
    let forbidden = b.or(forbidden, forbidden2);

    let mut ft = BDD_ZERO;
    for t in transitions.values() {
        ft = b.or(ft, *t);
    }

    let mut uc = BDD_ZERO;
    for t in uc_transitions.values() {
        uc = b.or(uc, *t);
    }

    // let uc = b.or(ft2, ft4); // BDD_ZERO
    let ub = swap(&mut b, uc, &pairing, &temps); // uncontrollable backwards

    // backwards transitions
    let bt = swap(&mut b, ft, &pairing, &temps);

    let fi = b.from_expr(&ise);
    let fi = b.not(forbidden); // b.from_expr(&ise);

    // find all reachable states
    let now = std::time::Instant::now();
    let mut r = fi;
    loop {
        let old = r;
        let new = relprod(&mut b, old, ft, &vars); // possible trans
        let new = replace(&mut b, new, &pairing); // to source states
        r = b.or(old, new);

        if old == r {
            break;
        }
    }

    let marked = BDD_ONE; // all states marked...
    let bad = nbc(&mut b, &vars, &pairing, bt, ub, marked, forbidden);
    let n_bad = b.not(bad);
    let nonblock = b.and(n_bad, r); // the intersection and not bad and reachable

    //    println!("Reachable nonblocking states");
    //    println!("============================");
    let mut bitmap = HashMap::new();
    let mut state_count = 0;
    for i in 0..bitsm {
        bits_to_hashmap2(bits, i, &mut bitmap);
        if b.evaluate(nonblock, &mut bitmap) {
            //let m: BTreeMap<_, _> = bitmap.iter().collect();
            //println!("i: {} - {:?}", i, m);
            state_count += 1;
        }
    }

    println!("Nbr of reachable states: {}", state_count);
    println!("Computed in: {}ms", now.elapsed().as_millis());

    // find guards...
    for (name, t) in transitions {
        // println!("transition? {:?}", t);
        let f = t; // b.from_expr(&t);
        let f_orig = f;
        let bt = swap(&mut b, f, &pairing, &temps);
        let x = relprod(&mut b, nonblock, bt, &vars);
        let x = replace(&mut b, x, &pairing);

        // x is new guard. use it and compare with original trans
        let xf = b.and(f, x);
        let y = relprod(&mut b, nonblock, f, &vars);
        let z = relprod(&mut b, nonblock, xf, &vars);

        if y != z {
            let now = std::time::Instant::now();

            let orig_guard = exist(&mut b, f, &destvars);
            let new_guard = x;
            let good_states = nonblock;
            let bad_states = bad;
            let mg = compute_minimal_guard(&mut b, orig_guard, new_guard, f_orig, bt,
                                           good_states, bad_states,
                                           &vars, &pairing, &temps);

            let te = b.to_expr(mg);
            // new guard!
            println!("guard for {}: {:?}, computed in {}ms", name, te, now.elapsed().as_millis());
        }
    }

//    assert!(false);
}

#[test]
fn all_steps_bdd_door_lock_xy() {
    let now = std::time::Instant::now();

    // these can run in parallel
    step1_bdd_door_lock_xy();
    step2_bdd_door_lock_xy();
    step3_bdd_door_lock_xy();

    println!("modular guards computed in {}ms", now.elapsed().as_millis());


    let now = std::time::Instant::now();
    make_trans_full_bdd_door_lock_xy();
    println!("monolithic guards computed in {}ms", now.elapsed().as_millis());

    assert!(false);
}
