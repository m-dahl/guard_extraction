use boolean_expression::*;
use Expr;

use std::cmp::Ord;
use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::collections::HashMap;
use std::collections::HashSet;
use std::fmt::Debug;
use std::hash::Hash;
use std::iter::FromIterator;
use std::ops::Add;

mod bdd_helpers;
use bdd_helpers::*;

use itertools::Itertools;

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

pub fn to_nuxmv(e: &Expr<usize>, num_vars: usize) -> String
{
    match e {
        &Expr::Terminal(ref t) => {
            if *t >= num_vars {
                format!("next(x{})",*t - num_vars)
            } else {
                format!("x{}",*t)
            }
        },
        &Expr::Const(val) => {
            if val {
                "TRUE".to_string()
            } else {
                "FALSE".to_string()
            }
        }
        &Expr::Not(ref x) => {
            format!("!({})", to_nuxmv(x, num_vars))
        }
        &Expr::And(ref a, ref b) => {
            format!("({} & {})", to_nuxmv(a, num_vars), to_nuxmv(b, num_vars))
        }
        &Expr::Or(ref a, ref b) => {
            format!("({} | {})", to_nuxmv(a, num_vars), to_nuxmv(b, num_vars))
        }
    }
}

pub fn powerset<T>(e: &[T]) -> Vec<Vec<T>>
where
    T: Clone + Debug + Eq + Ord + Hash,
{
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

fn bits_to_hashmap2(bits: usize, n: usize, h: &mut Vec<bool>) {
    h.resize(bits, false);
    for b in 0..bits {
        h[b] = (n & (1 << b)) != 0;
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
    T: Clone + Debug + Eq + Ord + Hash + Copy + Add<Output = T>,
{
    vs.iter().fold(Expr::Const(true), |acc, i| {
        Expr::and(
            acc,
            iff(Expr::Terminal(*i as T), Expr::Terminal(*i + offset as T)),
        )
    })
}

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
fn nbc(
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
fn ctrl(
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

fn reachable(
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


fn main() {
    println!("Hello, world!");
}

// TODO: the litterature is fairly decided on using an interleaved
// variable ordering for better performance. for now we just put all
// next values at the end.
fn make_trans(b: &mut BDD, guard: Expr<BDDLabel>, action: Expr<BDDLabel>, vars: &[BDDLabel]) -> BDDFunc {
    let vl: BDDLabel = vars.len().into();
    let vs: HashSet<BDDLabel> = HashSet::from_iter(vars.iter().cloned());
    let t = terms_in_expr(&action);
    let ts = HashSet::from_iter(t.iter().cloned());

    let not_updated: Vec<_> = vs.difference(&ts).cloned().collect();
    let iffs = iffs2(&not_updated, vl);

    let destvars: Vec<_> = vars.iter().map(|i| *i + vl).collect();
    let temps: Vec<_> = vars.iter().map(|i| *i + vl + vl).collect();

    let pairing: Vec<_> = destvars // swap function is for y to x
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

fn print_make_trans(name: &str, b: &mut BDD, guard: Expr<BDDLabel>, action: Expr<BDDLabel>, vars: &[BDDLabel])
{
    let vl: BDDLabel = vars.len().into();
    let vs: HashSet<BDDLabel> = HashSet::from_iter(vars.iter().cloned());
    let t = terms_in_expr(&action);
    let ts = HashSet::from_iter(t.iter().cloned());

    let not_updated: Vec<_> = vs.difference(&ts).cloned().collect();
    let iffs = iffs2(&not_updated, vl);

    let destvars: Vec<_> = vars.iter().map(|i| *i + vl).collect();
    let temps: Vec<_> = vars.iter().map(|i| *i + vl + vl).collect();

    let pairing: Vec<_> = destvars // swap function is for y to x
        .iter()
        .zip(vars.iter())
        .map(|(x, y)| (*x, *y))
        .collect();

    let action = b.from_expr(&action);
    let action = swap(b, action, &pairing, &temps); // change to next indexes
    let action = b.to_expr(action, vars.len());

    // hack

    let e = Expr::and(guard.clone(), Expr::and(action.clone(), iffs.clone()));
    let nx = to_nuxmv(&e, vars.len());
    println!(" -- {}", name);
    println!("{} |", nx);
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

    let mut b: BDD = BDD::new();
    let t = make_trans(
        &mut b,
        and(not(x(0)), and(not(x(1)), and(not(x(2)), not(x(3))))),
        x(2),
        &vars,
    );
    let e = b.to_expr(t, 2*vars.len());
    println!("expr: {:#?}", e);

    assert!(false);
}

#[test]
fn test_term_list() {
    let vars = vec![
        0, // door_closed_m
        1, // door_opened_m
        2, // door_gs_c, false = closed, true = opened
        3, // lock_l_c
    ];

    let x = |n| Expr::Terminal(n);
    let and = |a, b| Expr::and(a, b);
    let or = |a, b| Expr::or(a, b);
    let not = |a| Expr::not(a);

    let mut b: BDD = BDD::new();
    let t = and(not(x(0)), and(not(x(2)), not(x(3))));
    let t2 = and(x(0), x(3));
    let t = or(t,t2);

    let t = b.from_expr(&t);
    let e = b.to_expr(t, 2*vars.len());
    let mut tie = terms_in_expr(&e);
    tie.sort(); tie.dedup();
    let tib = terms_in_bddfunc(&mut b, t);
    println!("expr: {:#?}", tie);
    println!("expr: {:#?}", tib);

    assert!(false);
}

#[test]
fn test_set_minus() {
    let mut bdd = BDD::new();
    // Test: a, a+b, a+c, c', c, bd, ad, d'
    let a = bdd.terminal(0);
    let b = bdd.terminal(1);
    let c = bdd.terminal(2);
    let d = bdd.terminal(3);

    let ab = bdd.or(a,b);
    let abc = bdd.or(ab,c);
    let abcd = bdd.or(abc,d);


    let cd = bdd.or(c,d);

    let minus = bdd.set_minus(abcd, d);

    let expr = bdd.to_expr(minus, 4);

    println!("expr: {:#?}", expr);

    assert!(false);
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
            println!("choosing: {:?} out of {:?}", s, _all);
            return temp_ng; // greedy done, dont search all
        }
    }

    // nothing better found
    return new_guard;
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
    let door_open_e = (
        "door_open_e",
        make_trans(&mut b, and(x(2), not(x(1))), and(x(1), not(x(0))), &vars),
    );
    let door_close_d = (
        "door_close_d",
        make_trans(&mut b, not(x(0)), not(x(2)), &vars),
    );
    let door_close_e = (
        "door_close_e",
        make_trans(
            &mut b,
            and(not(x(2)), not(x(0))),
            and(not(x(1)), x(0)),
            &vars,
        ),
    );
    let lock_lock_d = (
        "lock_lock_d",
        make_trans(
            &mut b,
            or(x(6), not(x(5))),
            and(x(3), and(not(x(4)), and(x(5), not(x(6))))),
            &vars,
        ),
    );
    let lock_unlock_d = (
        "lock_unlock_d",
        make_trans(
            &mut b,
            or(x(6), x(5)),
            and(not(x(3)), and(x(4), and(not(x(5)), not(x(6))))),
            &vars,
        ),
    );
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
                          //let bad = nbc(&mut b, &vars, &pairing, bt, ub, marked, forbidden);
    let bad = ctrl(&mut b, &vars, &pairing, ub, forbidden);

    let n_bad = b.not(bad);
    let nonblock = b.and(n_bad, r); // the intersection and not bad and reachable

    //    println!("Reachable nonblocking states");
    //    println!("============================");
    let mut bitmap = Vec::new();
    let mut state_count = 0;
    let mut deadlock_count = 0;
    for i in 0..bitsm {
        bits_to_hashmap2(bits, i, &mut bitmap);
        if b.evaluate(nonblock, &mut bitmap) == Some(true) {
            //let m: BTreeMap<_, _> = bitmap.iter().collect();
            //println!("i: {} - {:?}", i, m);
            state_count += 1;

            // check for deadlock
            let mut d = true;
            for (name, t) in &transitions {
                let only_from = exist(&mut b, *t, &destvars);
                if b.evaluate(only_from, &mut bitmap) == Some(true) {
                    d = false;
                    break;
                }
            }
            if d {
                println!("DEADLOCK STATE: {} - {:?}", i, bitmap);
                deadlock_count += 1;
            }
        }
    }

    println!("Nbr of states in supervisor: {}\n", state_count);

    assert_eq!(state_count as f64, satcount(&mut b, nonblock, vars.len()));

    println!("Nbr of deadlock states: {}\n", deadlock_count);
    println!("Computed in: {}ms\n", now.elapsed().as_millis());

    let mut state_count = 0;
    for i in 0..bitsm {
        bits_to_hashmap2(bits, i, &mut bitmap);
        if b.evaluate(bad, &mut bitmap) == Some(true) {
            //let m: BTreeMap<_, _> = bitmap.iter().collect();
            //println!("i: {} - {:?}", i, m);
            state_count += 1;
        }
    }
    println!("Nbr of forbidden states: {}\n", state_count);

    assert_eq!(state_count as f64, satcount(&mut b, bad, vars.len()));

    let mut state_count = 0;
    for i in 0..bitsm {
        bits_to_hashmap2(bits, i, &mut bitmap);
        if b.evaluate(forbidden, &mut bitmap) == Some(true) {
            //let m: BTreeMap<_, _> = bitmap.iter().collect();
            //println!("i: {} - {:?}", i, m);
            state_count += 1;
        }
    }
    println!("Nbr of originally forbidden states: {}\n", state_count);

    assert_eq!(state_count as f64, satcount(&mut b, forbidden, vars.len()));

    let mut state_count = 0;
    for i in 0..bitsm {
        bits_to_hashmap2(bits, i, &mut bitmap);
        if b.evaluate(r, &mut bitmap) == Some(true) {
            //let m: BTreeMap<_, _> = bitmap.iter().collect();
            //println!("i: {} - {:?}", i, m);
            state_count += 1;
        }
    }
    println!("Nbr of reachable states: {}\n", state_count);

    assert_eq!(state_count as f64, satcount(&mut b, r, vars.len()));

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
            let mg = compute_minimal_guard(
                &mut b,
                orig_guard,
                new_guard,
                f_orig,
                bt,
                good_states,
                bad_states,
                &vars,
                &pairing,
                &temps,
            );

            let te = b.to_expr(mg, vars.len());
            // new guard!
            println!("new guard computed in {}ms", now.elapsed().as_millis());
            println!("guard added for transition {}", name);
            println!("orig guard: {:?}", orig_guard);
            println!("new guard: {:?}", te);
            println!("");
        }
    }

    let extra = b.to_expr(nonblock, 2*vars.len());
    println!("new initial states: {:?}", extra);

    // bdd...
    let intitial = or(
        or(
            or(
                or(
                    or(
                        and(and(not(x(2)), not(x(0))), not(x(7))),
                        and(and(not(x(2)), not(x(1))), not(x(7))),
                    ),
                    and(and(not(x(0)), not(x(5))), not(x(7))),
                ),
                and(and(not(x(0)), x(1)), not(x(7))),
            ),
            and(and(and(x(2), not(x(0))), x(1)), not(x(8))),
        ),
        and(and(not(x(1)), not(x(5))), not(x(7))),
    );

    let extra = b.to_expr(bad, 2*vars.len());
    println!("new forbidden states: {:?}", extra);

    let forbidden = or(
        or(
            or(
                or(
                    or(
                        or(and(not(x(2)), x(7)), and(x(0), x(1))),
                        and(not(x(1)), x(7)),
                    ),
                    and(and(x(2), not(x(1))), x(5)),
                ),
                and(x(7), x(8)),
            ),
            and(x(0), x(7)),
        ),
        and(and(x(2), x(0)), x(5)),
    );

    assert!(false);
}













#[test]
fn wodes_robot_rsp_gripper_cleanup() {
    // set up variables

    let vars = vec![
        0, // tool_closed_m
        1, // tool_opened_m
        2, // tool_gs_c, false = closed, true = opened
        3, // rsp_lock_l_c
        4, // rsp_lock_u_c
        5, // rsp_lock_e
        6, // rsp_lock_e_unknown = true
        7, // robot_p_m p0/p1
        8, // robot_p_c p0/p1
        9, // robot_p_e p0/p1  (init p1 = true)
        10, // robot_m_m moving
        11, // tool_e home/robot
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
    let nx = |n| Expr::not(Expr::Terminal(n));
    let and = |a, b| Expr::and(a, b);
    let or = |a, b| Expr::or(a, b);
    let not = |a| Expr::not(a);
    let imp = |a, b| Expr::or(Expr::not(a), b);

    // set up transitions
    let tool_open_d = ("tool_open_d", make_trans(&mut b, not(x(1)), x(2), &vars));
    let tool_open_e = (
        "tool_open_e",
        make_trans(&mut b, and(x(2), not(x(1))), and(x(1), not(x(0))), &vars),
    );
    let tool_close_d = (
        "tool_close_d",
        make_trans(&mut b, and(not(x(0)), x(1)), not(x(2)), &vars),
    );
    let tool_close_e = (
        "tool_close_e",
        make_trans(
            &mut b,
            and(not(x(2)), not(x(0))),
            and(not(x(1)), x(0)),
            &vars,
        ),
    );
    let rsp_lock_d = (
        "rsp_lock_d",
        make_trans(
            &mut b,
            or(x(6), not(x(5))),
            and(x(3), and(not(x(4)), and(x(5), not(x(6))))),
            &vars,
        ),
    );
    let rsp_unlock_d = (
        "rsp_unlock_d",
        make_trans(
            &mut b,
            or(x(6), x(5)),
            and(not(x(3)), and(x(4), and(not(x(5)), not(x(6))))),
            &vars,
        ),
    );
    let robot_p0_d = ("robot_p0_d", make_trans(&mut b, and(x(7), and(x(8), x(9))), nx(8), &vars));
    let robot_p0_se = ("robot_p0_se", make_trans(&mut b, and(x(7), and(nx(8), nx(10))), x(10), &vars));
    let robot_p0_ee = ("robot_p0_ee", make_trans(&mut b, and(x(7), and(nx(8), x(10))), and(nx(7), nx(10)), &vars));
    let robot_p0_fa = ("robot_p0_fa", make_trans(&mut b, and(x(9), and(nx(7), and(nx(8), nx(10)))), nx(9), &vars));

    let robot_p1_d = ("robot_p1_d", make_trans(&mut b, and(nx(7), and(nx(8), nx(9))), x(8), &vars));
    let robot_p1_se = ("robot_p1_se", make_trans(&mut b, and(nx(7), and(x(8), nx(10))), x(10), &vars));
    let robot_p1_ee = ("robot_p1_ee", make_trans(&mut b, and(nx(7), and(x(8), x(10))), and(x(7), nx(10)), &vars));
    let robot_p1_fa = ("robot_p1_fa", make_trans(&mut b, and(nx(9), and(x(7), and(x(8), nx(10)))), x(9), &vars));

    let tool_e_home_a = ("tool_e_home_a", make_trans(&mut b, and(x(11), and(nx(7), nx(5))), nx(11), &vars));
    let tool_e_rob_a = ("tool_e_rob_a", make_trans(&mut b, and(nx(11), and(nx(7), x(5))), x(11), &vars));


    // nuxsm verification for paper
    // let guard = and(x(5), x(11));
    // print_make_trans("tool_open_d", &mut b, and(guard, not(x(1))), x(2), &vars);
    // print_make_trans("tool_open_e", &mut b, and(x(2), not(x(1))), and(x(1), not(x(0))), &vars);

    // let guard = or(or(or(and(nx(7), nx(8)), and(nx(7), x(9))), and(x(7), nx(9))), and(x(7), x(8)));
    // print_make_trans("tool_close_d", &mut b, and(guard, and(not(x(0)), x(1))), not(x(2)), &vars);
    // print_make_trans("tool_close_e", &mut b,and(not(x(2)), not(x(0))),and(not(x(1)), x(0)),&vars);

    // let guard = or(and(nx(7), nx(8)), or(x(11), or(and(nx(7), x(9)), and(x(7), x(8)))));
    // print_make_trans("rsp_lock_d", &mut b,and(guard, or(x(6), not(x(5)))),and(x(3), and(not(x(4)), and(x(5), not(x(6))))),&vars);

    // let guard = or(and(nx(2), nx(11)), and(nx(2), and(x(0), and(nx(7), nx(8)))));
    // print_make_trans("rsp_unlock_d", &mut b,and(guard, or(x(6), x(5))),and(not(x(3)), and(x(4), and(not(x(5)), not(x(6))))),&vars);

    // let guard = or(and(nx(2), and(nx(1), nx(5))), and(x(2), and(x(1), x(5))));
    // print_make_trans("robot_p0_d", &mut b, and(guard, and(x(7), and(x(8), x(9)))), nx(8), &vars);
    // print_make_trans("robot_p0_se", &mut b, and(x(7), and(nx(8), nx(10))), x(10), &vars);
    // print_make_trans("robot_p0_ee", &mut b, and(x(7), and(nx(8), x(10))), and(nx(7), nx(10)), &vars);
    // print_make_trans("robot_p0_fa", &mut b, and(x(9), and(nx(7), and(nx(8), nx(10)))), nx(9), &vars);

    // let guard = or(and(nx(2), and(nx(1), and(nx(5), nx(11)))), and(x(2), and(x(1), and(x(5), x(11)))));
    // print_make_trans("robot_p1_d", &mut b, and(nx(7), and(guard, and(nx(8), nx(9)))), x(8), &vars);
    // print_make_trans("robot_p1_se", &mut b, and(nx(7), and(x(8), nx(10))), x(10), &vars);
    // print_make_trans("robot_p1_ee", &mut b, and(nx(7), and(x(8), x(10))), and(x(7), nx(10)), &vars);
    // print_make_trans("robot_p1_fa", &mut b, and(nx(9), and(x(7), and(x(8), nx(10)))), x(9), &vars);

    // print_make_trans("tool_e_home_a", &mut b, and(x(11), and(nx(7), nx(5))), nx(11), &vars);
    // print_make_trans("tool_e_rob_a", &mut b, and(nx(11), and(nx(7), x(5))), x(11), &vars);


    let mut transitions = HashMap::new();
    transitions.insert(tool_open_d.0, tool_open_d.1);
    transitions.insert(tool_open_e.0, tool_open_e.1.clone()); // todo
    transitions.insert(tool_close_d.0, tool_close_d.1);
    transitions.insert(tool_close_e.0, tool_close_e.1.clone());

    transitions.insert(rsp_lock_d.0, rsp_lock_d.1);
    transitions.insert(rsp_unlock_d.0, rsp_unlock_d.1);
    transitions.insert(robot_p0_d.0, robot_p0_d.1);
    transitions.insert(robot_p0_se.0, robot_p0_se.1);
    transitions.insert(robot_p0_ee.0, robot_p0_ee.1);
    transitions.insert(robot_p0_fa.0, robot_p0_fa.1);

    transitions.insert(robot_p1_d.0, robot_p1_d.1);
    transitions.insert(robot_p1_se.0, robot_p1_se.1);
    transitions.insert(robot_p1_ee.0, robot_p1_ee.1);
    transitions.insert(robot_p1_fa.0, robot_p1_fa.1);

    transitions.insert(tool_e_home_a.0, tool_e_home_a.1);
    transitions.insert(tool_e_rob_a.0, tool_e_rob_a.1);



    let mut uc_transitions = HashMap::new();
    uc_transitions.insert(tool_open_e.0, tool_open_e.1);
    uc_transitions.insert(tool_close_e.0, tool_close_e.1);
    uc_transitions.insert(robot_p0_se.0, robot_p0_se.1);
    uc_transitions.insert(robot_p0_ee.0, robot_p0_ee.1);
    uc_transitions.insert(robot_p0_fa.0, robot_p0_fa.1);
    uc_transitions.insert(robot_p1_se.0, robot_p1_se.1);
    uc_transitions.insert(robot_p1_ee.0, robot_p1_ee.1);
    uc_transitions.insert(robot_p1_fa.0, robot_p1_fa.1);
    uc_transitions.insert(tool_e_home_a.0, tool_e_home_a.1);
    uc_transitions.insert(tool_e_rob_a.0, tool_e_rob_a.1);

    // let is = [false, false, false, false, false, false, true, false, false, true, false, false];
    // let ise = state_to_expr2(&is);

    // tool cannot be closed and opened at the same time.
    let forbidden = and(x(0), x(1));
    let forbidden = b.from_expr(&forbidden);

    // spec A
    let mtop1exec = and(nx(7), and(x(8), x(10)));
    let forbidden_a = not(imp(and(x(11), and(nx(9), mtop1exec)), x(1)));
    let forbidden_a = b.from_expr(&forbidden_a);

    // spec B
    let mtop0exec = and(x(7), and(nx(8), x(10)));
    let forbidden_b = not(imp(and(x(11), and(x(9), mtop0exec)), x(1)));
    let forbidden_b = b.from_expr(&forbidden_b);

    // spec C
    let mtop0exec = and(x(7), and(nx(8), x(10)));
    let forbidden_c = not(imp(and(nx(11), mtop0exec), nx(5)));
    let forbidden_c = b.from_expr(&forbidden_c);

    // spec D
    let forbidden_d = not(imp(and(x(11), nx(5)), and(nx(7), x(0))));
    let forbidden_d = b.from_expr(&forbidden_d);

    // spec E
    let forbidden_e = not(imp(nx(11), nx(1)));
    let forbidden_e = b.from_expr(&forbidden_e);

    let forbidden = b.or(forbidden, forbidden_a);
    let forbidden = b.or(forbidden, forbidden_b);
    let forbidden = b.or(forbidden, forbidden_c);
    let forbidden = b.or(forbidden, forbidden_d);
    let forbidden = b.or(forbidden, forbidden_e);


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
    // let bt = swap(&mut b, ft, &pairing, &temps);

    // let fi = b.from_expr(&ise);
    let fi = b.not(forbidden); // b.from_expr(&ise);

    // find all reachable states
    let now = std::time::Instant::now();

    let r = reachable(&mut b, &vars, &pairing, ft, fi);

    // nonblocking and controllable... dont want/need it!
    // let marked = BDD_ONE; // all states marked...
    // let bad = nbc(&mut b, &vars, &pairing, bt, ub, marked, forbidden);
    let bad = ctrl(&mut b, &vars, &pairing, ub, forbidden);

    let n_bad = b.not(bad);
    let controllable = b.and(n_bad, r); // the intersection and not bad and reachable

    let state_count = satcount(&mut b, controllable, vars.len());
    println!("Nbr of states in supervisor: {}\n", state_count);
    println!("Computed in: {}ms\n", now.elapsed().as_millis());

    let forbidden_state_count = satcount(&mut b, bad, vars.len());
    println!("Nbr of forbidden states: {}\n", forbidden_state_count);

    let orig_forbidden_state_count = satcount(&mut b, forbidden, vars.len());
    println!("Nbr of originally forbidden states: {}\n", orig_forbidden_state_count);

    let reachable_state_count = satcount(&mut b, r, vars.len());
    println!("Nbr of reachable states: {}\n", reachable_state_count);

    // find guards...
    for (name, trans) in transitions {
        // compute the states from which we can reach a safe state as x
        let bt = swap(&mut b, trans, &pairing, &temps);
        let x = relprod(&mut b, controllable, bt, &vars);
        let x = replace(&mut b, x, &pairing);

        // x is new guard. use it and compare with original trans
        let xf = b.and(trans, x);
        let y = relprod(&mut b, controllable, trans, &vars);

        let z = relprod(&mut b, controllable, xf, &vars);

        if y != z {
            let now = std::time::Instant::now();

            let orig_guard = exist(&mut b, trans, &destvars);
            let new_guard = x;
            let good_states = controllable;
            let bad_states = bad;
            let mg = compute_minimal_guard(
                &mut b,
                orig_guard,
                new_guard,
                trans,
                bt,
                good_states,
                bad_states,
                &vars,
                &pairing,
                &temps,
            );

            //let te = b.to_expr(mg, vars.len());
            // new guard!
            println!("new guard computed in {}ms", now.elapsed().as_millis());
            println!("guard added for transition {}", name);
            println!("orig guard: {:?}", orig_guard);
            //println!("new guard: {:?}", te);
            println!("");
        }

    }

    let extra = b.to_expr(controllable, vars.len());
    println!("new initial states: {:?}", extra);

    // bdd...
    let intitial = or(
        or(
            or(
                or(
                    or(
                        and(and(not(x(2)), not(x(0))), not(x(7))),
                        and(and(not(x(2)), not(x(1))), not(x(7))),
                    ),
                    and(and(not(x(0)), not(x(5))), not(x(7))),
                ),
                and(and(not(x(0)), x(1)), not(x(7))),
            ),
            and(and(and(x(2), not(x(0))), x(1)), not(x(8))),
        ),
        and(and(not(x(1)), not(x(5))), not(x(7))),
    );

    let extra = b.to_expr(bad, vars.len());
    println!("new forbidden states: {:?}", extra);

    let forbidden = or(
        or(
            or(
                or(
                    or(
                        or(and(not(x(2)), x(7)), and(x(0), x(1))),
                        and(not(x(1)), x(7)),
                    ),
                    and(and(x(2), not(x(1))), x(5)),
                ),
                and(x(7), x(8)),
            ),
            and(x(0), x(7)),
        ),
        and(and(x(2), x(0)), x(5)),
    );

    assert!(false);
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


// Consumes a context when done adding variables to become a
// model checker context to which you can add transitions.
pub struct MCContext {
    pub context: Context,
    pub trans: BTreeMap<String, BDDFunc>,
}


impl MCContext {
    pub fn from(c: Context) -> Self {
        MCContext { context: c, trans: BTreeMap::new() }
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
                                let fe = self.b.to_expr(f, self.num_vars);
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

    pub fn controllable(&mut self, forbidden: BDDFunc) -> (BDDFunc, BDDFunc) {
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
                    let e = self.b.to_expr(d.dom, self.num_vars);
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

        return (controllable, bad);
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
                let now = std::time::Instant::now();

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

    // let tool_open_d_guard = and(vec![v(tc), nv(to), or(vec![Ex::EQ(robot_p_m, Value::InDomain(1)), Ex::EQ(robot_p_c, Value::InDomain(0))])]);
    let tool_open_d_guard = and(vec![or(vec![Ex::EQ(robot_p_m, Value::InDomain(1)), Ex::EQ(robot_p_c, Value::InDomain(0))])]);
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


    assert!(false);


    // // set up transitions
    // let tool_open_d = ("tool_open_d", make_trans(&mut b, not(x(1)), x(2), &vars));
    // let tool_open_e = (
    //     "tool_open_e",
    //     make_trans(&mut b, and(x(2), not(x(1))), and(x(1), not(x(0))), &vars),
    // );


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

    let (controllable, bad) = bc.controllable(forbidden);

    let new_guards = bc.compute_guards(controllable, bad);

    for (trans, guard) in &new_guards {
        let s = c.pretty_print(&guard);
        println!("NEW GUARD FOR {}: {}", trans, s);
    }

    assert!(false);
}
