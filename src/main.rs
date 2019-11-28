use boolean_expression::*;
use std::collections::BTreeMap;
use std::collections::HashMap;
use Expr;

fn term_hashmap(vals: &[bool], h: &mut HashMap<u32, bool>) {
    h.clear();
    for (i, v) in vals.iter().enumerate() {
        h.insert(i as u32, *v);
    }
}

fn test_bdd(b: &BDD<u32>, f: BDDFunc, h: &mut HashMap<u32, bool>, inputs: &[bool], expected: bool) {
    term_hashmap(inputs, h);
    assert!(b.evaluate(f, h) == expected);
}

#[test]
fn bdd_to_expr() {
    let mut b = BDD::new();
    let f_true = b.constant(true);
    assert!(b.to_expr(f_true) == Expr::Const(true));
    let f_false = b.constant(false);
    assert!(b.to_expr(f_false) == Expr::Const(false));
    let f_0 = b.terminal(0);
    let f_1 = b.terminal(1);
    let f_and = b.and(f_0, f_1);
    assert!(b.to_expr(f_and) == Expr::and(Expr::Terminal(0), Expr::Terminal(1)));
    let f_or = b.or(f_0, f_1);
    assert!(b.to_expr(f_or) == Expr::or(Expr::Terminal(1), Expr::Terminal(0)));
    let f_not = b.not(f_0);
    assert!(b.to_expr(f_not) == Expr::not(Expr::Terminal(0)));
    let f_2 = b.terminal(2);
    let f_1_or_2 = b.or(f_1, f_2);
    let f_0_and_1_or_2 = b.and(f_0, f_1_or_2);
    assert!(
        b.to_expr(f_0_and_1_or_2)
            == Expr::or(
                Expr::and(Expr::Terminal(0), Expr::Terminal(2)),
                Expr::and(Expr::Terminal(0), Expr::Terminal(1))
            )
    );
}

#[test]
fn bdd_eval() {
    let mut h = HashMap::new();
    let mut b = BDD::new();
    let expr = Expr::or(
        Expr::and(Expr::Terminal(0), Expr::Terminal(1)),
        Expr::and(Expr::not(Expr::Terminal(2)), Expr::not(Expr::Terminal(3))),
    );
    let f = b.from_expr(&expr);
    test_bdd(&b, f, &mut h, &[false, false, true, true], false);
    test_bdd(&b, f, &mut h, &[true, false, true, true], false);
    test_bdd(&b, f, &mut h, &[true, true, true, true], true);
    test_bdd(&b, f, &mut h, &[false, false, false, true], false);
    test_bdd(&b, f, &mut h, &[false, false, false, false], true);
}

use std::cmp::Ord;
use std::fmt::Debug;
use std::hash::Hash;

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

// collect toplevel ORs
pub fn disj<T>(e: &Expr<T>) -> Vec<Expr<T>>
where
    T: Clone + Debug + Eq + Ord + Hash,
{
    let mut v = Vec::new();
    match e {
        &Expr::Or(ref a, ref b) => {
            let mut nv1 = disj(&**a);
            let mut nv2 = disj(&**b);
            v.append(&mut nv1);
            v.append(&mut nv2);
        }
        _ => {
            v.push(e.clone());
        }
    }
    v
}

pub fn disj_powerset<T>(e: &Expr<T>) -> Vec<Expr<T>>
where
    T: Clone + Debug + Eq + Ord + Hash,
{
    use itertools::Itertools;
    let disj = disj(e);
    let mut disj2 = Vec::new();
    for x in 1..(disj.len() + 1) {
        for z in disj.iter().combinations(x) {
            if z.len() == 1 {
                disj2.push(z[0].clone());
            } else {
                let first = z[0].clone();
                let rest = &z[1..z.len()];
                let v: Expr<T> = rest.iter().fold(first, |acc, &t| Expr::or(acc, t.clone()));
                disj2.push(v);
            }
        }
    }

    disj2
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
    let mut x = vec![1,2,3,3,4];
    x.dedup();
    let x = powerset(&x);
    println!("{:?}", x);

    assert!(false);
}


#[test]
fn disj_test() {
    let x: Expr<u32> = Expr::or(
        Expr::and(Expr::Const(true), Expr::Const(false)),
        Expr::or(Expr::Const(true), Expr::Const(false)),
    );
    let y = disj(&x);
    println!("{:?}", y);

    use itertools::Itertools;
    let mut disj2 = Vec::new();
    for x in 1..(y.len() + 1) {
        for z in y.iter().combinations(x) {
            println!("comb: {:?}", z);
            disj2.push(z);
        }
    }

    println!("{:?}", disj2);

    println!("powerset {:#?}", disj_powerset(&x));

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

fn relprod<T>(b: &mut BDD<T>, states: BDDFunc, transitions: BDDFunc, variables: &Vec<T>) -> BDDFunc
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

fn replace<T>(b: &mut BDD<T>, func: BDDFunc, pairing: &Vec<(T, T)>) -> BDDFunc
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
fn swap<T>(b: &mut BDD<T>, func: BDDFunc, pairing: &Vec<(T, T)>, temps: &Vec<T>) -> BDDFunc
where
    T: Clone + Debug + Eq + Ord + Hash + Copy,
{
    // newBDD.replaceWith(sourceToTempVariablePairing);
    // newBDD.replaceWith(destToSourceVariablePairing);
    // newBDD.replaceWith(tempToDestVariablePairing);

    // t = (8, 0)
    // r = (0, 4)
    // f = (4, 8)

    let pair1: Vec<_> = pairing
        .iter()
        .zip(temps.iter())
        .map(|((x, y), z)| (*z, *x))
        .collect();

    let pair2: Vec<_> = pairing
        .iter()
        .zip(temps.iter())
        .map(|((x, y), z)| (*y, *z))
        .collect();

    let nf = replace(b, func, &pair1);
    let nf = replace(b, nf, pairing);
    replace(b, nf, &pair2)
}

#[test]
fn bdd_eval2() {
    let mut b = BDD::new();
    let is = Expr::and(
        Expr::Terminal(0),
        Expr::and(
            Expr::not(Expr::Terminal(1)),
            Expr::and(Expr::not(Expr::Terminal(2)), Expr::not(Expr::Terminal(3))),
        ),
    );
    //    let fi = b.from_expr(&is);

    let vals = vec![true, false, false, false];
    let mut h = HashMap::new();
    for (i, v) in vals.iter().enumerate() {
        h.insert(i as u32, *v);
    }
    let vars = vec![0, 1, 2, 3];
    let pairing = vec![(0, 4), (1, 5), (2, 6), (3, 7)];

    // transition 1, flip s_1 to false, keep others
    let t1 = Expr::and(
        is.clone(),
        Expr::and(
            Expr::not(Expr::Terminal(4)),
            Expr::and(
                iff(Expr::Terminal(1), Expr::Terminal(5)),
                Expr::and(
                    iff(Expr::Terminal(2), Expr::Terminal(6)),
                    iff(Expr::Terminal(3), Expr::Terminal(7)),
                ),
            ),
        ),
    );

    // state 1, all false.
    let state1 = Expr::and(
        Expr::not(Expr::Terminal(0)),
        Expr::and(
            Expr::not(Expr::Terminal(1)),
            Expr::and(Expr::not(Expr::Terminal(2)), Expr::not(Expr::Terminal(3))),
        ),
    );
    // t2, flib s_2 to true, keep others
    let t2 = Expr::and(
        state1.clone(),
        Expr::and(
            Expr::Terminal(5),
            Expr::and(
                iff(Expr::Terminal(0), Expr::Terminal(4)),
                Expr::and(
                    iff(Expr::Terminal(2), Expr::Terminal(6)),
                    iff(Expr::Terminal(3), Expr::Terminal(7)),
                ),
            ),
        ),
    );

    let fi = b.from_expr(&is);

    let ft1 = b.from_expr(&t1);
    let ft2 = b.from_expr(&t2);

    let ft = b.or(ft1, ft2);

    let r = b.evaluate(fi, &h);
    println!("is? {:#?}", r);

    let rp = relprod(&mut b, fi, ft, &vars);
    let ss = replace(&mut b, rp, &pairing);

    let e = b.to_expr(rp);
    println!("expr? {:#?}", e);

    // Reach(x) := Init(x);
    // REPEAT
    //  Old(x) := Reach(x);
    //  New(y) := Exists x.(Reach(x) & Trans(x,y));
    //  Reach(x) := Old(x) + New(x)
    // UNTIL Old(x) = Reach(x)

    assert!(false);
}

fn state_to_expr(state: &[bool]) -> Expr<u32> {
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

fn state_in_bddfunc(bdd: &BDD<u32>, f: BDDFunc, state: &[bool]) -> bool {
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

#[test]
fn bdd_test4() {
    let mut b = BDD::new();
    let is = Expr::and(
        Expr::Terminal(0),
        Expr::and(
            Expr::not(Expr::Terminal(1)),
            Expr::and(Expr::not(Expr::Terminal(2)), Expr::not(Expr::Terminal(3))),
        ),
    );
    let fi = b.from_expr(&is);
    let fi2 = b.from_expr(&state_to_expr(&[true, false, false, false]));
    println!("one {:?}", is);
    println!("two {:?}", state_to_expr(&[true, false, false, false]));

    assert!(false);
}

fn bits_to_hashmap(bits: usize, n: usize, h: &mut HashMap<u32, bool>) {
    for b in 0..bits {
        h.insert(b as u32, (n & (1 << b)) != 0);
    }
}

#[test]
fn bits() {
    let mut h = HashMap::new();
    for i in 0..16 {
        bits_to_hashmap(4, i, &mut h);
        println!("i: {} - {:?}", i, h);
    }
    assert!(false);
}

#[test]
fn bdd_eval3() {
    let mut b = BDD::new();
    let is = Expr::and(
        Expr::Terminal(0),
        Expr::and(
            Expr::not(Expr::Terminal(1)),
            Expr::and(Expr::not(Expr::Terminal(2)), Expr::not(Expr::Terminal(3))),
        ),
    );
    //    let fi = b.from_expr(&is);

    let vals = vec![true, false, false, false];
    let mut h = HashMap::new();
    for (i, v) in vals.iter().enumerate() {
        h.insert(i as u32, *v);
    }
    let vars = vec![0, 1, 2, 3];
    let pairing = vec![(0, 4), (1, 5), (2, 6), (3, 7)];

    // transition 1, flip s_1 to false, keep others
    let t1 = Expr::and(
        is.clone(),
        Expr::and(
            Expr::not(Expr::Terminal(4)),
            Expr::and(
                iff(Expr::Terminal(1), Expr::Terminal(5)),
                Expr::and(
                    iff(Expr::Terminal(2), Expr::Terminal(6)),
                    iff(Expr::Terminal(3), Expr::Terminal(7)),
                ),
            ),
        ),
    );

    let state1 = Expr::and(
        Expr::not(Expr::Terminal(0)),
        Expr::and(
            Expr::not(Expr::Terminal(1)),
            Expr::and(Expr::not(Expr::Terminal(2)), Expr::not(Expr::Terminal(3))),
        ),
    );
    // t2, flib s_2 to true, keep others
    let t2 = Expr::and(
        state1.clone(),
        Expr::and(
            Expr::Terminal(5),
            Expr::and(
                iff(Expr::Terminal(0), Expr::Terminal(4)),
                Expr::and(
                    iff(Expr::Terminal(2), Expr::Terminal(6)),
                    iff(Expr::Terminal(3), Expr::Terminal(7)),
                ),
            ),
        ),
    );

    let fi = b.from_expr(&is);

    let ft1 = b.from_expr(&t1);
    let ft2 = b.from_expr(&t2);

    let ft = b.or(ft1, ft2);

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

    let e = b.to_expr(r);
    println!("expr? {:#?}", e);

    // check that init state and state1 are in bdd
    let vals = vec![true, false, false, false];
    let mut h = HashMap::new();
    for (i, v) in vals.iter().enumerate() {
        h.insert(i as u32, *v);
    }
    let e = b.evaluate(r, &h);
    println!("in bdd? {:?}", e);

    let vals = vec![false, false, false, false];
    let mut h = HashMap::new();
    for (i, v) in vals.iter().enumerate() {
        h.insert(i as u32, *v);
    }
    let e = b.evaluate(r, &h);
    println!("in bdd? {:?}", e);

    // check that some other state is NOT in bdd
    let vals = vec![false, false, true, false];
    let mut h = HashMap::new();
    for (i, v) in vals.iter().enumerate() {
        h.insert(i as u32, *v);
    }
    let e = b.evaluate(r, &h);
    println!("in bdd? {:?}", e);

    assert!(false);
}

#[test]
fn bdd_eval4() {
    let vars = vec![0, 1, 2, 3];
    let destvars = vec![4, 5, 6, 7];

    let pairing = vec![(0, 4), (1, 5), (2, 6), (3, 7)];
    let temps = vec![8, 9, 10, 11]; // hmmm...

    let is = [false, false, false, false];
    let ise = state_to_expr(&is);

    let state1 = [true, false, false, false];
    let state1e = state_to_expr(&state1);

    let state2 = [true, true, false, false];
    let state2e = state_to_expr(&state2);

    let mut b = BDD::new();

    // transition 1, flip s_0 to false, keep others
    let t1 = Expr::and(
        ise.clone(),
        Expr::and(
            (Expr::Terminal(4)),
            Expr::and(
                iff(Expr::Terminal(1), Expr::Terminal(5)),
                Expr::and(
                    iff(Expr::Terminal(2), Expr::Terminal(6)),
                    iff(Expr::Terminal(3), Expr::Terminal(7)),
                ),
            ),
        ),
    );

    // t2, flip s_1 to true, keep others
    let t2 = Expr::and(
        state1e.clone(),
        Expr::and(
            Expr::Terminal(5),
            Expr::and(
                iff(Expr::Terminal(0), Expr::Terminal(4)),
                Expr::and(
                    iff(Expr::Terminal(2), Expr::Terminal(6)),
                    iff(Expr::Terminal(3), Expr::Terminal(7)),
                ),
            ),
        ),
    );

    // t3, flip from state1 back to initial state
    let t3 = Expr::and(
        state1e.clone(),
        Expr::and(
            Expr::not(Expr::Terminal(4)),
            Expr::and(
                Expr::not(Expr::Terminal(5)),
                Expr::and(
                    iff(Expr::Terminal(2), Expr::Terminal(6)),
                    iff(Expr::Terminal(3), Expr::Terminal(7)),
                ),
            ),
        ),
    );

    let fi = b.from_expr(&ise);
    let state1b = b.from_expr(&state1e);
    let state2b = b.from_expr(&state2e);

    let ft1 = b.from_expr(&t1);
    let ft2 = b.from_expr(&t2);
    let ft3 = b.from_expr(&t3);

    let ft = b.or(ft1, ft2);
    let ft = b.or(ft, ft3);

    let bt = swap(&mut b, ft, &pairing, &temps);

    let e = b.to_expr(ft);
    println!("ft? {:#?}", e);
    let e = b.to_expr(bt);
    println!("bt? {:#?}", e);
    // assert_eq!(ft,bt);

    // let ss = b.and(fi, ft);
    // let s1 = relprod(&mut b, state1b, bt, &vars);
    // let e = b.to_expr(s1);
    // println!("init e? {:#?}", e);

    // let ss = b.and(state1b, bt);
    let s1 = relprod(&mut b, fi, bt, &vars);
    //let s1 = b.and(state2b, bt);
    //let s1 = relprod(&mut b, state1b, ft2, &vars);
    let ii = replace(&mut b, s1, &pairing);

    let e = b.to_expr(s1);
    println!("e old 1? {:#?}", e);

    let e = b.to_expr(ii);
    println!("e old 2? {:#?}", e);
    let mut bitmap = HashMap::new();
    for i in 0..16 {
        bits_to_hashmap(4, i, &mut bitmap);
        if b.evaluate(ii, &mut bitmap) {
            println!("i: {} - {:?}", i, bitmap);
        }
    }

    let e = b.to_expr(fi);
    println!("fi? {:#?}", e);

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

    let e = b.to_expr(r);
    println!("expr? {:#?}", e);

    // check that init state and state1 are in bdd
    println!("in bdd? {:?}", state_in_bddfunc(&b, r, &is));
    println!("in bdd? {:?}", state_in_bddfunc(&b, r, &state1));
    println!(
        "in bdd? {:?}",
        state_in_bddfunc(&b, r, &[false, true, false, false])
    );

    // check that some other state is NOT in bdd
    println!(
        "in bdd? {:?}",
        state_in_bddfunc(&b, r, &[false, false, true, false])
    );

    let mut bitmap = HashMap::new();
    for i in 0..16 {
        bits_to_hashmap(4, i, &mut bitmap);
        if b.evaluate(r, &mut bitmap) {
            println!("i: {} - {:?}", i, bitmap);
        }
    }

    assert!(false);
}

#[test]
fn bdd_eval4_cleanup() {
    let vars = vec![0, 1, 2, 3];
    let destvars = vec![4, 5, 6, 7];

    let pairing: Vec<_> = vars
        .iter()
        .zip(destvars.iter())
        .map(|(x, y)| (*x, *y))
        .collect();
    let temps = vec![8, 9, 10, 11]; // hmmm...

    let is = [false, false, false, false];
    let ise = state_to_expr(&is);

    let state1 = [true, false, false, false];
    let state1e = state_to_expr(&state1);

    let state2 = [true, true, false, false];
    let state2e = state_to_expr(&state2);

    let mut b = BDD::new();

    // transition 1, flip s_0 to false, keep others
    let t1 = Expr::and(
        ise.clone(),
        Expr::and(
            (Expr::Terminal(4)),
            Expr::and(
                iff(Expr::Terminal(1), Expr::Terminal(5)),
                Expr::and(
                    iff(Expr::Terminal(2), Expr::Terminal(6)),
                    iff(Expr::Terminal(3), Expr::Terminal(7)),
                ),
            ),
        ),
    );

    // t2, flip s_1 to true, keep others
    let t2 = Expr::and(
        state1e.clone(),
        Expr::and(
            Expr::Terminal(5),
            Expr::and(
                iff(Expr::Terminal(0), Expr::Terminal(4)),
                Expr::and(
                    iff(Expr::Terminal(2), Expr::Terminal(6)),
                    iff(Expr::Terminal(3), Expr::Terminal(7)),
                ),
            ),
        ),
    );

    // t3, flip from state1 back to initial state
    let t3 = Expr::and(
        state1e.clone(),
        Expr::and(
            Expr::not(Expr::Terminal(4)),
            Expr::and(
                Expr::not(Expr::Terminal(5)),
                Expr::and(
                    iff(Expr::Terminal(2), Expr::Terminal(6)),
                    iff(Expr::Terminal(3), Expr::Terminal(7)),
                ),
            ),
        ),
    );

    // t4, flip last bit => forbidden state
    //let t4 = Expr::and(state1e.clone(), Expr::and(iff(Expr::Terminal(0), Expr::Terminal(4)), Expr::and(iff(Expr::Terminal(1), Expr::Terminal(5)), Expr::and(iff(Expr::Terminal(2), Expr::Terminal(6)), Expr::Terminal(7)))));
    // t4, flip last bit from any state...
    let t4 = Expr::and(
        Expr::not(Expr::Terminal(3)),
        Expr::and(
            iff(Expr::Terminal(0), Expr::Terminal(4)),
            Expr::and(
                iff(Expr::Terminal(1), Expr::Terminal(5)),
                Expr::and(iff(Expr::Terminal(2), Expr::Terminal(6)), Expr::Terminal(7)),
            ),
        ),
    );

    // t5, from the forbidden state back to s1
    let state3 = [true, false, false, true];
    let state3e = state_to_expr(&state3);

    let t5 = Expr::and(
        state3e.clone(),
        Expr::and(
            Expr::not(Expr::Terminal(4)),
            Expr::and(
                iff(Expr::Terminal(1), Expr::Terminal(5)),
                Expr::and(
                    iff(Expr::Terminal(2), Expr::Terminal(6)),
                    Expr::not(Expr::Terminal(7)),
                ),
            ),
        ),
    );

    // t6, from the 0001 state back to initial
    let state4 = [false, false, false, true];
    let state4e = state_to_expr(&state4);

    let t6 = Expr::and(
        state4e.clone(),
        Expr::and(
            iff(Expr::Terminal(0), Expr::Terminal(4)),
            Expr::and(
                iff(Expr::Terminal(1), Expr::Terminal(5)),
                Expr::and(
                    iff(Expr::Terminal(2), Expr::Terminal(6)),
                    Expr::not(Expr::Terminal(7)),
                ),
            ),
        ),
    );

    let trans = vec![
        t1.clone(),
        t2.clone(),
        t3.clone(),
        t4.clone(),
        t5.clone(),
        t6.clone(),
    ];

    let fi = b.from_expr(&ise);
    let state1b = b.from_expr(&state1e);
    let state2b = b.from_expr(&state2e);
    let state3b = b.from_expr(&state3e);

    let forbidden = b.from_expr(&state3e);

    let ft1 = b.from_expr(&t1);
    let ft2 = b.from_expr(&t2);
    let ft3 = b.from_expr(&t3);
    let ft4 = b.from_expr(&t4);
    let ft5 = b.from_expr(&t5);
    let ft6 = b.from_expr(&t6);

    let ft = b.or(ft1, ft2);
    let ft = b.or(ft, ft3);
    let ft = b.or(ft, ft4); // forbidden
    let ft = b.or(ft, ft5); // from forbidden to initial
    let ft = b.or(ft, ft6); // from forbidden to initial

    let uc = BDD_ZERO; // ft4; // uncontrollable forwards
    let ub = swap(&mut b, uc, &pairing, &temps); // uncontrollable backwards

    // backwards transitions
    let bt = swap(&mut b, ft, &pairing, &temps);

    // from which states can we reach the initial?
    let s1 = relprod(&mut b, fi, bt, &vars);
    let ii = replace(&mut b, s1, &pairing);

    // print them
    println!("Backwards reachable states (to initial state)");
    let mut bitmap = HashMap::new();
    for i in 0..16 {
        bits_to_hashmap(4, i, &mut bitmap);
        if b.evaluate(ii, &mut bitmap) {
            let m: BTreeMap<_, _> = bitmap.iter().collect();
            println!("i: {} - {:?}", i, m);
        }
    }

    // find all reachable states
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

    // print all states in bdd
    println!("Forward reachable states");
    let mut bitmap = HashMap::new();
    for i in 0..16 {
        bits_to_hashmap(4, i, &mut bitmap);
        if b.evaluate(r, &mut bitmap) {
            let m: BTreeMap<_, _> = bitmap.iter().collect();
            println!("i: {} - {:?}", i, m);
        }
    }

    // find all blocking states
    // TODO: should look for fix point here ...
    let not_blocking = relprod(&mut b, r, ft, &destvars);
    let blocking = b.not(not_blocking); // and not marked...

    let reach_blocking = b.and(r, blocking);

    println!("Blocking states");
    let mut bitmap = HashMap::new();
    for i in 0..16 {
        bits_to_hashmap(4, i, &mut bitmap);
        if b.evaluate(reach_blocking, &mut bitmap) {
            let m: BTreeMap<_, _> = bitmap.iter().collect();
            println!("i: {} - {:?}", i, m);
        }
    }

    let not_forbidden = b.not(forbidden);
    let marked = fi; // b.or(fi, state2b); // marked is only initial
    let mut nonblock = b.and(marked, not_forbidden);

    loop {
        let old = nonblock;
        let new = relprod(&mut b, old, bt, &vars); // possible trans
        let new = replace(&mut b, new, &pairing); // to source states
        nonblock = b.or(old, new);
        nonblock = b.and(nonblock, not_forbidden);

        // todo: uncontrollable/forbidden here

        // controllability
        let mut rfu = b.not(nonblock); // forbidden;
        loop {
            let old = rfu;
            let new = relprod(&mut b, old, ub, &vars); // possible trans
            let new = replace(&mut b, new, &pairing); // to source states
            rfu = b.or(old, new);

            if old == rfu {
                break;
            }
        }

        rfu = b.not(rfu);
        nonblock = b.or(rfu, old);

        // end controllability

        if old == nonblock {
            break;
        }
    }

    println!("Reachable nonblocking states 1");
    let mut bitmap = HashMap::new();
    for i in 0..16 {
        bits_to_hashmap(4, i, &mut bitmap);
        if b.evaluate(nonblock, &mut bitmap) {
            let m: BTreeMap<_, _> = bitmap.iter().collect();
            println!("i: {} - {:?}", i, m);
        }
    }

    let not_blocking = b.not(reach_blocking);
    let nonblocking = b.and(r, not_blocking);
    println!("Reachable nonblocking states");
    let mut bitmap = HashMap::new();
    for i in 0..16 {
        bits_to_hashmap(4, i, &mut bitmap);
        if b.evaluate(nonblocking, &mut bitmap) {
            let m: BTreeMap<_, _> = bitmap.iter().collect();
            println!("i: {} - {:?}", i, m);
        }
    }

    println!("Forbidden states");
    let mut bitmap = HashMap::new();
    for i in 0..16 {
        bits_to_hashmap(4, i, &mut bitmap);
        if b.evaluate(forbidden, &mut bitmap) {
            let m: BTreeMap<_, _> = bitmap.iter().collect();
            println!("i: {} - {:?}", i, m);
        }
    }

    // controllability
    let mut rfu = forbidden;
    loop {
        let old = rfu;
        let new = relprod(&mut b, old, ub, &vars); // possible trans
        let new = replace(&mut b, new, &pairing); // to source states
        rfu = b.or(old, new);

        if old == rfu {
            break;
        }
    }

    // rfu contains all states that via uncontrollable events can reach forbidden states
    println!("Reachability to forbidden states");
    let mut bitmap = HashMap::new();
    for i in 0..16 {
        bits_to_hashmap(4, i, &mut bitmap);
        if b.evaluate(rfu, &mut bitmap) {
            let m: BTreeMap<_, _> = bitmap.iter().collect();
            println!("i: {} - {:?}", i, m);
        }
    }

    let not_forbidden = b.not(rfu);
    let nonblocking_controllable = b.and(nonblocking, not_forbidden);
    println!("Nonblocking and controllable");
    let mut bitmap = HashMap::new();
    for i in 0..16 {
        bits_to_hashmap(4, i, &mut bitmap);
        if b.evaluate(nonblocking_controllable, &mut bitmap) {
            let m: BTreeMap<_, _> = bitmap.iter().collect();
            println!("i: {} - {:?}", i, m);
        }
    }

    println!("\n");

    // find guards...
    //    for t in trans {
    let t = t4;
    println!("transition? {:?}", t);
    let f = b.from_expr(&t);
    let bt = swap(&mut b, f, &pairing, &temps);
    let x = relprod(&mut b, nonblocking_controllable, bt, &vars);
    let x = replace(&mut b, x, &pairing);
    let e = b.to_expr(x);
    println!("guard? {:?}", e);
    println!("");

    //    }

    assert!(false);
}

#[test]
fn bdd_nonblocking_controllable() {
    let vars = vec![0, 1, 2, 3];
    let destvars = vec![4, 5, 6, 7];

    let pairing: Vec<_> = vars
        .iter()
        .zip(destvars.iter())
        .map(|(x, y)| (*x, *y))
        .collect();
    let temps = vec![8, 9, 10, 11]; // hmmm...

    let is = [false, false, false, false];
    let ise = state_to_expr(&is);

    let state1 = [true, false, false, false];
    let state1e = state_to_expr(&state1);

    let state2 = [true, true, false, false];
    let state2e = state_to_expr(&state2);

    let mut b = BDD::new();

    // transition 1, flip s_0 to false, keep others
    let t1 = Expr::and(
        ise.clone(),
        Expr::and(
            (Expr::Terminal(4)),
            Expr::and(
                iff(Expr::Terminal(1), Expr::Terminal(5)),
                Expr::and(
                    iff(Expr::Terminal(2), Expr::Terminal(6)),
                    iff(Expr::Terminal(3), Expr::Terminal(7)),
                ),
            ),
        ),
    );

    // t2, flip s_1 to true, keep others
    let t2 = Expr::and(
        state1e.clone(),
        Expr::and(
            Expr::Terminal(5),
            Expr::and(
                iff(Expr::Terminal(0), Expr::Terminal(4)),
                Expr::and(
                    iff(Expr::Terminal(2), Expr::Terminal(6)),
                    iff(Expr::Terminal(3), Expr::Terminal(7)),
                ),
            ),
        ),
    );

    // t3, flip from state1 back to initial state
    let t3 = Expr::and(
        state1e.clone(),
        Expr::and(
            Expr::not(Expr::Terminal(4)),
            Expr::and(
                Expr::not(Expr::Terminal(5)),
                Expr::and(
                    iff(Expr::Terminal(2), Expr::Terminal(6)),
                    iff(Expr::Terminal(3), Expr::Terminal(7)),
                ),
            ),
        ),
    );

    // t4, flip last bit => forbidden state
    //let t4 = Expr::and(state1e.clone(), Expr::and(iff(Expr::Terminal(0), Expr::Terminal(4)), Expr::and(iff(Expr::Terminal(1), Expr::Terminal(5)), Expr::and(iff(Expr::Terminal(2), Expr::Terminal(6)), Expr::Terminal(7)))));
    // t4, flip last bit from any state...
    let t4 = Expr::and(
        Expr::not(Expr::Terminal(3)),
        Expr::and(
            iff(Expr::Terminal(0), Expr::Terminal(4)),
            Expr::and(
                iff(Expr::Terminal(1), Expr::Terminal(5)),
                Expr::and(iff(Expr::Terminal(2), Expr::Terminal(6)), Expr::Terminal(7)),
            ),
        ),
    );

    // t5, from the forbidden state back to s1
    let state3 = [true, false, false, true];
    let state3e = state_to_expr(&state3);

    let t5 = Expr::and(
        state3e.clone(),
        Expr::and(
            Expr::not(Expr::Terminal(4)),
            Expr::and(
                iff(Expr::Terminal(1), Expr::Terminal(5)),
                Expr::and(
                    iff(Expr::Terminal(2), Expr::Terminal(6)),
                    Expr::not(Expr::Terminal(7)),
                ),
            ),
        ),
    );

    // t6, from the 0001 state back to initial
    let state4 = [false, false, false, true];
    let state4e = state_to_expr(&state4);

    let t6 = Expr::and(
        state4e.clone(),
        Expr::and(
            iff(Expr::Terminal(0), Expr::Terminal(4)),
            Expr::and(
                iff(Expr::Terminal(1), Expr::Terminal(5)),
                Expr::and(
                    iff(Expr::Terminal(2), Expr::Terminal(6)),
                    Expr::not(Expr::Terminal(7)),
                ),
            ),
        ),
    );

    let trans = vec![
        t1.clone(),
        t2.clone(),
        t3.clone(),
        t4.clone(),
        t5.clone(),
        t6.clone(),
    ];

    let fi = b.from_expr(&ise);
    let state1b = b.from_expr(&state1e);
    let state2b = b.from_expr(&state2e);
    let state3b = b.from_expr(&state3e);

    let forbidden = BDD_ZERO; //b.from_expr(&state3e);
    let forbidden = b.from_expr(&state3e);

    let ft1 = b.from_expr(&t1);
    let ft2 = b.from_expr(&t2);
    let ft3 = b.from_expr(&t3);
    let ft4 = b.from_expr(&t4);
    let ft5 = b.from_expr(&t5);
    let ft6 = b.from_expr(&t6);

    let ft = b.or(ft1, ft2);
    let ft = b.or(ft, ft3);
    let ft = b.or(ft, ft4); // forbidden
    let ft = b.or(ft, ft5); // from forbidden to initial
    let ft = b.or(ft, ft6); // from forbidden to initial

    let uc = ft4; // uncontrollable forwards
    let ub = swap(&mut b, uc, &pairing, &temps); // uncontrollable backwards

    // backwards transitions
    let bt = swap(&mut b, ft, &pairing, &temps);

    // find all reachable states
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

    let not_forbidden = b.not(forbidden);
    let marked = fi; // b.or(fi, state2b); // marked is only initial
    let mut nonblock = b.and(marked, not_forbidden);

    loop {
        let old = nonblock;
        let new = relprod(&mut b, old, bt, &vars); // possible trans
        let new = replace(&mut b, new, &pairing); // to source states
        nonblock = b.or(old, new);
        nonblock = b.and(nonblock, not_forbidden);

        // controllability
        let mut rfu = b.not(nonblock); // forbidden;
        loop {
            let old = rfu;
            let new = relprod(&mut b, old, ub, &vars); // possible trans
            let new = replace(&mut b, new, &pairing); // to source states
            rfu = b.or(old, new);

            if old == rfu {
                break;
            }
        }

        rfu = b.not(rfu);
        nonblock = b.or(rfu, old);

        if old == nonblock {
            break;
        }
    }

    println!("Reachable nonblocking states");
    println!("============================");
    let mut bitmap = HashMap::new();
    for i in 0..16 {
        bits_to_hashmap(4, i, &mut bitmap);
        if b.evaluate(nonblock, &mut bitmap) {
            let m: BTreeMap<_, _> = bitmap.iter().collect();
            println!("i: {} - {:?}", i, m);
        }
    }

    println!("\n");

    // find guards...
    for t in trans {
        // println!("transition? {:?}", t);
        let f = b.from_expr(&t);
        let bt = swap(&mut b, f, &pairing, &temps);
        let x = relprod(&mut b, nonblock, bt, &vars);
        let x = replace(&mut b, x, &pairing);

        // quanity out target states from trans
        let mut f = f;
        for v in &destvars {
            let sf = b.restrict(f, *v, false);
            let st = b.restrict(f, *v, true);
            f = b.or(sf, st);
        }

        let fe = b.to_expr(f);
        let e = b.to_expr(x);
        println!("orig guard: {:?}", fe);
        println!("new guard: {:?}", e);
        println!("");
    }

    assert!(false);
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

#[test]
fn bdd_door_lock() {
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

    let destvars: Vec<_> = vars.iter().map(|i| i + vars.len() as u32).collect();
    let temps: Vec<_> = vars.iter().map(|i| i + 2 * vars.len() as u32).collect();

    let pairing: Vec<_> = vars
        .iter()
        .zip(destvars.iter())
        .map(|(x, y)| (*x, *y))
        .collect();

    println!("{:?}", vars);
    println!("{:?}", destvars);
    println!("{:?}", temps);

    // convenience
    let x = |n| Expr::Terminal(n);
    let next = |n| Expr::Terminal(n + vars.len() as u32);
    let and = |a, b| Expr::and(a, b);
    let or = |a, b| Expr::or(a, b);
    let not = |a| Expr::not(a);

    // set up transitions
    let door_open_d = (
        "door_open_d",
        and(
            and(not(x(1)), next(2)),
            iffs(&[0, 1, 3, 4, 5, 6], vars.len()),
        ),
    );

    let door_open_e = (
        "door_open_e",
        and(
            and(x(2), and(not(x(1)), and(next(1), not(next(0))))),
            iffs(&[2, 3, 4, 5, 6], vars.len()),
        ),
    );

    let door_close_d = (
        "door_close_d",
        and(
            and(not(x(0)), not(next(2))),
            iffs(&[0, 1, 3, 4, 5, 6], vars.len()),
        ),
    );

    let door_close_e = (
        "door_close_e",
        and(
            and(not(x(2)), and(not(x(0)), and(not(next(1)), next(0)))),
            iffs(&[2, 3, 4, 5, 6], vars.len()),
        ),
    );

    let lock_lock_d = (
        "lock_lock_d",
        and(
            and(
                or(x(6), not(x(5))),
                and(next(3), and(not(next(4)), and(next(5), not(next(6))))),
            ),
            iffs(&[0, 1, 2], vars.len()),
        ),
    );

    let lock_unlock_d = (
        "lock_unlock_d",
        and(
            and(
                or(x(6), x(5)),
                and(not(next(3)), and(next(4), and(not(next(5)), not(next(6))))),
            ),
            iffs(&[0, 1, 2], vars.len()),
        ),
    );

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

    let mut b: BDD<u32> = BDD::new();
    let is = [false, false, false, false, false, false, true];
    let ise = state_to_expr(&is);

    // forbid opening
    let forbidden = and(not(x(1)), and(x(2), x(5)));
    let forbidden = b.from_expr(&forbidden);

    // let forbidden = BDD_ZERO; // no forbidden states //b.from_expr(&state3e);

    let mut ft = BDD_ZERO;
    for t in transitions.values() {
        let f = b.from_expr(t);
        ft = b.or(ft, f);
    }

    let mut uc = BDD_ZERO;
    for t in uc_transitions.values() {
        let f = b.from_expr(t);
        uc = b.or(uc, f);
    }

    // let uc = b.or(ft2, ft4); // BDD_ZERO
    let ub = swap(&mut b, uc, &pairing, &temps); // uncontrollable backwards

    // backwards transitions
    let bt = swap(&mut b, ft, &pairing, &temps);

    let fi = b.from_expr(&ise);

    // find all reachable states
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

    println!("All reachable states");
    println!("============================");
    let mut bitmap = HashMap::new();
    for i in 0..128 {
        bits_to_hashmap(7, i, &mut bitmap);
        if b.evaluate(r, &mut bitmap) {
            let m: BTreeMap<_, _> = bitmap.iter().collect();
            println!("i: {} - {:?}", i, m);
        }
    }

    println!("\n");

    let mark = [true, false, false, false, false, false, false];
    let mark = state_to_expr(&mark);
    let mark = b.from_expr(&mark);

    let not_forbidden = b.not(forbidden);
    let marked = b.or(fi, mark); // fi; // b.or(fi, state2b); // marked is only initial
    let marked = BDD_ONE; // all states marked...
    let mut nonblock = b.and(marked, not_forbidden);

    loop {
        let old = nonblock;
        let new = relprod(&mut b, old, bt, &vars); // possible trans
        let new = replace(&mut b, new, &pairing); // to source states
        nonblock = b.or(old, new);
        nonblock = b.and(nonblock, not_forbidden);

        // controllability
        let mut rfu = b.not(nonblock); // forbidden;
        loop {
            let old = rfu;
            let new = relprod(&mut b, old, ub, &vars); // possible trans
            let new = replace(&mut b, new, &pairing); // to source states
            rfu = b.or(old, new);

            if old == rfu {
                break;
            }
        }

        rfu = b.not(rfu);
        nonblock = b.or(rfu, old);

        // cleanup...
        // TODO. this should not be not needed
        nonblock = b.and(nonblock, r);

        if old == nonblock {
            break;
        }
    }

    println!("Reachable nonblocking states");
    println!("============================");
    let mut bitmap = HashMap::new();
    for i in 0..128 {
        bits_to_hashmap(7, i, &mut bitmap);
        if b.evaluate(nonblock, &mut bitmap) {
            let m: BTreeMap<_, _> = bitmap.iter().collect();
            println!("i: {} - {:?}", i, m);
        }
    }

    println!("\n");

    println!("Forbidden (reachable) states");
    println!("============================");
    let notnonblock = b.not(nonblock);
    let forbidden = b.and(r, notnonblock);
    let mut bitmap = HashMap::new();
    for i in 0..128 {
        bits_to_hashmap(7, i, &mut bitmap);
        if b.evaluate(forbidden, &mut bitmap) {
            let m: BTreeMap<_, _> = bitmap.iter().collect();
            println!("i: {} - {:?}", i, m);
        }
    }

    println!("\n");

    // find guards...
    for (name, t) in transitions {
        // println!("transition? {:?}", t);
        let f = b.from_expr(&t);
        let f_orig = f;
        let bt = swap(&mut b, f, &pairing, &temps);
        let x = relprod(&mut b, nonblock, bt, &vars);
        let x = replace(&mut b, x, &pairing);

        // x is new guard. use it and compare with original trans
        let xf = b.and(f, x);
        let y = relprod(&mut b, r, f, &vars);
        let z = relprod(&mut b, r, xf, &vars);

        if y != z {
            // quanity out target states from trans to get guard
            let mut f = f;
            for v in &destvars {
                let sf = b.restrict(f, *v, false);
                let st = b.restrict(f, *v, true);
                f = b.or(sf, st);
            }

            let forbx = relprod(&mut b, forbidden, bt, &vars);
            let mut forbx = replace(&mut b, forbx, &pairing);

            let fe = b.to_expr(f);
            let tie = terms_in_expr(&fe);
            // now hack f out of x
            let mut xx = x;
            for t in tie {
                let sf = b.restrict(xx, t, false);
                let st = b.restrict(xx, t, true);
                xx = b.or(sf, st);

                let sf = b.restrict(forbx, t, false);
                let st = b.restrict(forbx, t, true);
                forbx = b.or(sf, st);
            }
            // assert that my thinking is correct...
            let tot = b.and(xx, f);
            assert_eq!(tot, x);

            // guard need to stop us from reaching forbidden
            forbx = b.not(forbx);
            let forbe = b.to_expr(forbx);

            let f_and_forb = b.and(f_orig, forbx);
            let bt = swap(&mut b, f_and_forb, &pairing, &temps);
            // assert that my thinking is correct...
            assert_eq!(relprod(&mut b, forbidden, bt, &vars), BDD_ZERO);

            let fe = b.to_expr(f);
            let e = b.to_expr(xx);

            let tie_x = terms_in_expr(&e);
            let tie_y = terms_in_expr(&forbe);

            // chose the smallest guard representation
            let mut new_guard = if tie_x.len() < tie_y.len() { e } else { forbe };

            // try to remove terms that doesnt lead us to a forbidden state
            // and doesn't over-constrain us wrt the reachable states

            let mut first = None;
            let mut disj = disj(&new_guard);
            let temp_ng = b.from_expr(&new_guard);
            let temp = b.and(f_orig, temp_ng);
            let bt = swap(&mut b, temp, &pairing, &temps);
            let z = relprod(&mut b, nonblock, bt, &vars);

            disj.push(Expr::Const(true));

            for d in disj {
                let temp = b.from_expr(&d);
                let temp = b.and(f_orig, temp);
                let bt = swap(&mut b, temp, &pairing, &temps);
                let y = relprod(&mut b, forbidden, bt, &vars);
                let zz = relprod(&mut b, nonblock, bt, &vars);

                if y == BDD_ZERO && z == zz {
                    // yay, we can eliminate the term
                    println!("yay!: {:?}", d);
                    first = Some(d);
                } else {
                    // noh!
                    println!("no luck for: {:?}", d);
                }
            }

            let disj_exprs = disj_powerset(&new_guard);
            let ok_exprs: Vec<_> = disj_exprs
                .iter()
                .filter(|e| {
                    let temp = b.from_expr(&e);
                    let temp = b.and(f_orig, temp);
                    let bt = swap(&mut b, temp, &pairing, &temps);
                    let y = relprod(&mut b, forbidden, bt, &vars);
                    let zz = relprod(&mut b, nonblock, bt, &vars);

                    y == BDD_ZERO && z == zz
                })
                .collect();
            println!("ALL OK: {:?}", ok_exprs);
            let lens: Vec<_> = ok_exprs.iter().map(|x| terms_in_expr(x).len()).collect();
            println!("TERM LENS: {:?}", lens);

            let least_terminals = ok_exprs
                .into_iter()
                .min_by(|x, y| terms_in_expr(&x).len().cmp(&terms_in_expr(&y).len()));

            if let Some(x) = least_terminals {
                //if let Some(x) = first {
                new_guard = x.clone();
            }

            // new guard!
            println!("guard added for transition {}", name);
            println!("orig guard: {:?}", fe);
            println!("new guard: {:#?}", new_guard);
            println!("");
        }
    }

    assert!(false);
}

// BDD fdd_ithvar(int var, int val)
// {
//    int n;
//    int v=1, tmp;

//    if (!bddrunning)
//    {
//       bdd_error(BDD_RUNNING);
//       return bddfalse;
//    }

//    if (var < 0  ||  var >= fdvarnum)
//    {
//       bdd_error(BDD_VAR);
//       return bddfalse;
//    }

//    if (val < 0  ||  val >= domain[var].realsize)
//    {
//       bdd_error(BDD_RANGE);
//       return bddfalse;
//    }

//    for (n=0 ; n<domain[var].binsize ; n++)
//    {
//       bdd_addref(v);

//       if (val & 0x1)
// 	 tmp = bdd_apply(bdd_ithvar(domain[var].ivar[n]), v, bddop_and);
//       else
// 	 tmp = bdd_apply(bdd_nithvar(domain[var].ivar[n]), v, bddop_and);

//       bdd_delref(v);
//       v = tmp;
//       val >>= 1;
//    }

//    return v;
// }

// BDD fdd_equals(int left, int right)
// {
//    BDD e = bddtrue, tmp1, tmp2;
//    int n;

//    if (!bddrunning)
//    {
//       bdd_error(BDD_RUNNING);
//       return bddfalse;
//    }

//    if (left < 0  ||  left >= fdvarnum  ||  right < 0  ||  right >= fdvarnum)
//    {
//       bdd_error(BDD_VAR);
//       return bddfalse;
//    }
//    if (domain[left].realsize != domain[right].realsize)
//    {
//       bdd_error(BDD_RANGE);
//       return bddfalse;
//    }

//    for (n=0 ; n<domain[left].binsize ; n++)
//    {
//       tmp1 = bdd_addref( bdd_apply(bdd_ithvar(domain[left].ivar[n]),
// 				   bdd_ithvar(domain[right].ivar[n]),
// 				   bddop_biimp) );

//       tmp2 = bdd_addref( bdd_apply(e, tmp1, bddop_and) );
//       bdd_delref(tmp1);
//       bdd_delref(e);
//       e = tmp2;
//    }

//    bdd_delref(e);
//    return e;
// }

// check if domain accepts "d"
fn bv(bdomain: &mut BDD<usize>, d: usize, binsize: usize) -> BDDFunc {
    let mut val = d;
    let mut v = BDD_ONE;
    for n in 0..binsize {
        let term = if val & 0x1 == 0x1 {
            bdomain.terminal(n)
        } else {
            let t = bdomain.terminal(n);
            bdomain.not(t)
        };
        v = bdomain.and(term, v);
        val >>= 1;
    }
    v
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

#[test]
fn test_domain() {
    let domain: Vec<String> = vec![
        "l".into(),
        "u".into(),
        "unknown".into(),
        "unknown1".into(),
        "unknown2".into(),
    ];
    let dl = domain.len();

    let mut binsize = 1;
    let mut calcsize = 2;

    while calcsize < dl {
        binsize += 1;
        calcsize *= 2;
    }

    println!("binsize: {}, calcsize: {}", binsize, calcsize);

    let mut val = 4; // unknown

    let mut bits = vec![false; binsize];

    let mut n = 0;
    while val > 0 {
        if val & 0x1 == 0x1 {
            bits[n] = true;
        }
        val >>= 1;
        n += 1;
    }

    println!("BITS: {:?}", bits);

    // higher order bit to the RIGHT

    // put them into a bdd...

    let mut bdomain = BDD::new();

    let mut val = dl - 1;
    let mut d = BDD_ONE;

    for n in 0..binsize {
        let t = bdomain.terminal(n);
        let nt = bdomain.not(t);
        let tmp = if val & 0x1 == 0x1 {
            bdomain.or(nt, d)
        } else {
            bdomain.and(nt, d)
        };

        val >>= 1;
        d = tmp;
    }

    // "d" now represents all valid assignments of the domain
    // check this...
    assert!(eval_bddfunc(&bdomain, d, &[false, false, false])); // 0
    assert!(eval_bddfunc(&bdomain, d, &[true, false, false])); // 1
    assert!(eval_bddfunc(&bdomain, d, &[false, true, false])); // 2
    assert!(eval_bddfunc(&bdomain, d, &[true, true, false])); // 3
    assert!(eval_bddfunc(&bdomain, d, &[false, false, true])); // 4

    assert!(!eval_bddfunc(&bdomain, d, &[true, false, true])); // 5
    assert!(!eval_bddfunc(&bdomain, d, &[false, true, true])); // 6

    let x = Expr::and(
        Expr::not(Expr::Terminal(0)),
        Expr::and(Expr::Terminal(1), Expr::not(Expr::Terminal(2))),
    );
    let x = Expr::Terminal(1);
    // let x = Expr::and(Expr::not(Expr::Terminal(3)), Expr::and(
    //     Expr::Terminal(1), Expr::not(Expr::Terminal(2))));
    //    let x = Expr::and(Expr::not(Expr::Terminal(2)), Expr::and(Expr::not(
    //        Expr::Terminal(4)), Expr::not(Expr::Terminal(5))));

    let mut x = bdomain.from_expr(&x);

    let xe = bdomain.to_expr(x);
    println!("has val bdd??: {:#?}", xe);

    for i in 0..7 {
        let v = bv(&mut bdomain, i, dl);
        let v = bdomain.and(v, d); // restrict to known values of the domain
        let has_val = bdomain.and(v, x) != BDD_ZERO;
        println!("has {} bdd??: {:#?}", i, has_val);
    }

    let vf = bv(&mut bdomain, 2, dl);
    let has_val = eval_bddfunc(&bdomain, vf, &[false, true, false]);
    println!("has val??: {:#?}", has_val);

    let expr = bdomain.to_expr(d);
    println!("BDD: {:#?}", expr);

    assert!(false);
}

#[test]
fn bdd_door_lock_xy() {
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
    println!("State bits: {:?}", bits);

    let destvars: Vec<_> = vars.iter().map(|i| i + vars.len() as u32).collect();
    let temps: Vec<_> = vars.iter().map(|i| i + 2 * vars.len() as u32).collect();

    let pairing: Vec<_> = vars
        .iter()
        .zip(destvars.iter())
        .map(|(x, y)| (*x, *y))
        .collect();

    println!("{:?}", vars);
    println!("{:?}", destvars);
    println!("{:?}", temps);

    // convenience
    let x = |n| Expr::Terminal(n);
    let next = |n| Expr::Terminal(n + vars.len() as u32);
    let and = |a, b| Expr::and(a, b);
    let or = |a, b| Expr::or(a, b);
    let not = |a| Expr::not(a);

    // set up transitions
    let door_open_d = (
        "door_open_d",
        and(
            and(not(x(1)), next(2)),
            iffs(&[0, 1, 3, 4, 5, 6, 7, 8], vars.len()),
        ),
    );

    let door_open_e = (
        "door_open_e",
        and(
            and(x(2), and(not(x(1)), and(next(1), not(next(0))))),
            iffs(&[2, 3, 4, 5, 6, 7, 8], vars.len()),
        ),
    );

    let door_close_d = (
        "door_close_d",
        and(
            and(not(x(0)), not(next(2))),
            iffs(&[0, 1, 3, 4, 5, 6, 7, 8], vars.len()),
        ),
    );

    let door_close_e = (
        "door_close_e",
        and(
            and(not(x(2)), and(not(x(0)), and(not(next(1)), next(0)))),
            iffs(&[2, 3, 4, 5, 6, 7, 8], vars.len()),
        ),
    );

    let lock_lock_d = (
        "lock_lock_d",
        and(
            and(
                or(x(6), not(x(5))),
                and(next(3), and(not(next(4)), and(next(5), not(next(6))))),
            ),
            iffs(&[0, 1, 2, 7, 8], vars.len()),
        ),
    );

    let lock_unlock_d = (
        "lock_unlock_d",
        and(
            and(
                or(x(6), x(5)),
                and(not(next(3)), and(next(4), and(not(next(5)), not(next(6))))),
            ),
            iffs(&[0, 1, 2, 7, 8], vars.len()),
        ),
    );

    // X
    let xm1 = (
        "x1",
        and(
            and(not(x(7)), next(7)),
            iffs(&[0, 1, 2, 3, 4, 5, 6, 8], vars.len()),
        ),
    );
    let xm2 = (
        "x2",
        and(
            and(x(7), not(next(7))),
            iffs(&[0, 1, 2, 3, 4, 5, 6, 8], vars.len()),
        ),
    );

    // Y
    let ym1 = (
        "y1",
        and(
            and(not(x(8)), next(8)),
            iffs(&[0, 1, 2, 3, 4, 5, 6, 7], vars.len()),
        ),
    );
    let ym2 = (
        "y2",
        and(
            and(x(8), not(next(8))),
            iffs(&[0, 1, 2, 3, 4, 5, 6, 7], vars.len()),
        ),
    );

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

    let mut b: BDD<u32> = BDD::new();
    let is = [false, false, false, false, false, false, true, false, false];
    let ise = state_to_expr(&is);

    // forbid opening
    let forbidden = and(not(x(1)), and(x(2), x(5)));
    let forbidden = b.from_expr(&forbidden);

    let forbidden2 = and(not(x(1)), x(7));
    let forbidden2 = b.from_expr(&forbidden2);

    let forbidden3 = and(x(7), x(8));
    let forbidden3 = b.from_expr(&forbidden3);

    let forbidden = b.or(forbidden, forbidden2);
    let forbidden = b.or(forbidden, forbidden3);

    // let forbidden = BDD_ZERO; // no forbidden states //b.from_expr(&state3e);

    let mut ft = BDD_ZERO;
    for t in transitions.values() {
        let f = b.from_expr(t);
        ft = b.or(ft, f);
    }

    let mut uc = BDD_ZERO;
    for t in uc_transitions.values() {
        let f = b.from_expr(t);
        uc = b.or(uc, f);
    }

    // let uc = b.or(ft2, ft4); // BDD_ZERO
    let ub = swap(&mut b, uc, &pairing, &temps); // uncontrollable backwards

    // backwards transitions
    let bt = swap(&mut b, ft, &pairing, &temps);

    let fi = b.from_expr(&ise);

    // find all reachable states
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

    // println!("All reachable states");
    // println!("============================");
    // let mut bitmap = HashMap::new();
    // for i in 0..bitsm {
    //     bits_to_hashmap(bits, i, &mut bitmap);
    //     if b.evaluate(r, &mut bitmap) {
    //         let m: BTreeMap<_, _> = bitmap.iter().collect();
    //         println!("i: {} - {:?}", i, m);
    //     }
    // }

    // println!("\n");

    let marked = BDD_ONE; // all states marked...

    let bad = nbc(&mut b, &vars, &pairing, bt, ub, marked, forbidden);
    let n_bad = b.not(bad);
    let nonblock = b.and(n_bad, r); // the intersection and not bad and reachable

    //    println!("Reachable nonblocking states");
    //    println!("============================");
    let mut bitmap = HashMap::new();
    let mut state_count = 0;
    for i in 0..bitsm {
        bits_to_hashmap(bits, i, &mut bitmap);
        if b.evaluate(nonblock, &mut bitmap) {
            let m: BTreeMap<_, _> = bitmap.iter().collect();
            //       println!("i: {} - {:?}", i, m);
            state_count += 1;
        }
    }

    println!("Nbr of reachable states: {}\n", state_count);

    // println!("Forbidden (reachable) states");
    // println!("============================");
    // let notnonblock = b.not(nonblock);
    // let forbidden = b.and(r, notnonblock);
    // let mut bitmap = HashMap::new();
    // for i in 0..bitsm {
    //     bits_to_hashmap(bits, i, &mut bitmap);
    //     if b.evaluate(forbidden, &mut bitmap) {
    //         let m: BTreeMap<_, _> = bitmap.iter().collect();
    //         println!("i: {} - {:?}", i, m);
    //     }
    // }

    println!("\n");

    // find guards...
    for (name, t) in transitions {
        // println!("transition? {:?}", t);
        let f = b.from_expr(&t);
        let f_orig = f;
        let bt = swap(&mut b, f, &pairing, &temps);
        let x = relprod(&mut b, nonblock, bt, &vars);
        let x = replace(&mut b, x, &pairing);

        // x is new guard. use it and compare with original trans
        let xf = b.and(f, x);
        let y = relprod(&mut b, nonblock, f, &vars);
        let z = relprod(&mut b, nonblock, xf, &vars);

        // if y != z {
        //     println!("transition {:?} got new guard...", name);
        // }
        //  else

        if y != z {
            // quanity out target states from trans to get guard
            let mut f = f;
            for v in &destvars {
                let sf = b.restrict(f, *v, false);
                let st = b.restrict(f, *v, true);
                f = b.or(sf, st);
            }

            let forbx = relprod(&mut b, bad, bt, &vars);
            let mut forbx = replace(&mut b, forbx, &pairing);

            let fe = b.to_expr(f);
            let tie = terms_in_expr(&fe);
            // now hack f out of x
            let mut xx = x;
            for t in tie {
                let sf = b.restrict(xx, t, false);
                let st = b.restrict(xx, t, true);
                xx = b.or(sf, st);

                let sf = b.restrict(forbx, t, false);
                let st = b.restrict(forbx, t, true);
                forbx = b.or(sf, st);
            }
            // assert that my thinking is correct...
            let tot = b.and(xx, f);
            assert_eq!(tot, x);

            // guard need to stop us from reaching forbidden
            forbx = b.not(forbx);
            let forbe = b.to_expr(forbx);

            let f_and_forb = b.and(f_orig, forbx);
            let bt = swap(&mut b, f_and_forb, &pairing, &temps);
            // assert that my thinking is correct...
            assert_eq!(relprod(&mut b, forbidden, bt, &vars), BDD_ZERO);

            let fe = b.to_expr(f);
            let e = b.to_expr(xx);

            let tie_x = terms_in_expr(&e);
            let tie_y = terms_in_expr(&forbe);

            // chose the smallest guard representation
            let mut new_guard = if tie_x.len() < tie_y.len() { e } else { forbe };

            // try to remove terms that doesnt lead us to a forbidden state
            // and doesn't over-constrain us wrt the reachable states
            let temp_ng = b.from_expr(&new_guard);
            let temp = b.and(f_orig, temp_ng);
            let bt = swap(&mut b, temp, &pairing, &temps);
            let z = relprod(&mut b, nonblock, bt, &vars);

            let mut new_terms = terms_in_expr(&new_guard);
            new_terms.sort();
            new_terms.dedup(); // sort + dedup to uniquify
            let ntps = powerset(&new_terms);

            let mut ng_len = new_terms.len();

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
                let te = b.to_expr(temp_ng);
                if te == Expr::Const(true) {
                    continue;
                }
                let ok = match cache.get(&temp) {
                    Some(&ok) => {
                        ok
                    },
                    None => {
                        let bt = swap(&mut b, temp, &pairing, &temps);
                        let y = relprod(&mut b, bad, bt, &vars);
                        let y = replace(&mut b, y, &pairing);
                        let y = b.and(y, nonblock);

                        if name == "x1" {
                            println!("y == zero? {} s: {:?}", y == BDD_ZERO, s);
                        }

                        let ok = if y == BDD_ZERO {
                            let zz = relprod(&mut b, nonblock, bt, &vars);

                            if name == "x1" {
                                println!("z == zz? {}", z == zz);
                            }
                            z == zz
                        } else {
                            false
                        };
                        cache.insert(temp, ok);
                        ok
                    }
                };

                // let te = b.to_expr(temp_ng);
                if ok {
                    //println!("yay2! for terms: {:?}", s);
                    //println!("new expr: {:?}", te);
                    let terms_in_te = terms_in_expr(&te);
                    if terms_in_te.len() < ng_len {
                        ng_len = terms_in_te.len();
                        new_guard = te;
                    }
                } else {
                    if name == "y1" {
                    println!("nay! for terms: {:?}", s);
                    println!("new expr: {:?}", te);
                    let te = b.to_expr(y);
                        println!("why: {:?}", te);
                    }
                }

            }

            // new guard!
            println!("guard added for transition {}", name);
            println!("orig guard: {:?}", fe);
            println!("new guard: {:?}", new_guard);
            println!("");
        }
    }

    assert!(false);
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

#[test]
fn debug_bdd_d_lock_xy() {
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
    println!("State bits: {:?}", bits);

    let destvars: Vec<_> = vars.iter().map(|i| i + vars.len() as u32).collect();
    let temps: Vec<_> = vars.iter().map(|i| i + 2 * vars.len() as u32).collect();

    let pairing: Vec<_> = vars
        .iter()
        .zip(destvars.iter())
        .map(|(x, y)| (*x, *y))
        .collect();

    println!("{:?}", vars);
    println!("{:?}", destvars);
    println!("{:?}", temps);

    // convenience
    let x = |n| Expr::Terminal(n);
    let next = |n| Expr::Terminal(n + vars.len() as u32);
    let and = |a, b| Expr::and(a, b);
    let or = |a, b| Expr::or(a, b);
    let not = |a| Expr::not(a);

    // set up transitions
    let door_open_d = (
        "door_open_d",
        and(
            and(not(x(1)), next(2)),
            iffs(&[0, 1, 3, 4, 5, 6, 7, 8], vars.len()),
        ),
    );

    let door_open_e = (
        "door_open_e",
        and(
            and(x(2), and(not(x(1)), and(next(1), not(next(0))))),
            iffs(&[2, 3, 4, 5, 6, 7, 8], vars.len()),
        ),
    );

    let door_close_d = (
        "door_close_d",
        and(
            and(not(x(0)), not(next(2))),
            iffs(&[0, 1, 3, 4, 5, 6, 7, 8], vars.len()),
        ),
    );

    let door_close_e = (
        "door_close_e",
        and(
            and(not(x(2)), and(not(x(0)), and(not(next(1)), next(0)))),
            iffs(&[2, 3, 4, 5, 6, 7, 8], vars.len()),
        ),
    );

    let lock_lock_d = (
        "lock_lock_d",
        and(
            and(
                or(x(6), not(x(5))),
                and(next(3), and(not(next(4)), and(next(5), not(next(6))))),
            ),
            iffs(&[0, 1, 2, 7, 8], vars.len()),
        ),
    );

    let lock_unlock_d = (
        "lock_unlock_d",
        and(
            and(
                or(x(6), x(5)),
                and(not(next(3)), and(next(4), and(not(next(5)), not(next(6))))),
            ),
            iffs(&[0, 1, 2, 7, 8], vars.len()),
        ),
    );

    // X
    let xm1 = (
        "x1",
        and(
            and(not(x(7)), next(7)),
            iffs(&[0, 1, 2, 3, 4, 5, 6, 8], vars.len()),
        ),
    );
    let xm2 = (
        "x2",
        and(
            and(x(7), not(next(7))),
            iffs(&[0, 1, 2, 3, 4, 5, 6, 8], vars.len()),
        ),
    );

    // Y
    let ym1 = (
        "y1",
        and(
            and(not(x(8)), next(8)),
            iffs(&[0, 1, 2, 3, 4, 5, 6, 7], vars.len()),
        ),
    );
    let ym2 = (
        "y2",
        and(
            and(x(8), not(next(8))),
            iffs(&[0, 1, 2, 3, 4, 5, 6, 7], vars.len()),
        ),
    );

    let mut transitions = HashMap::new();
    transitions.insert(door_open_d.0, door_open_d.1);
    transitions.insert(door_open_e.0, door_open_e.1.clone()); // todo
    transitions.insert(door_close_d.0, door_close_d.1);
    transitions.insert(door_close_e.0, door_close_e.1.clone());

    // transitions.insert(lock_lock_d.0, lock_lock_d.1);
    // transitions.insert(lock_unlock_d.0, lock_unlock_d.1);
    transitions.insert(xm1.0, xm1.1);
    transitions.insert(xm2.0, xm2.1);
    // transitions.insert(ym1.0, ym1.1);
    // transitions.insert(ym2.0, ym2.1);

    let mut uc_transitions = HashMap::new();
    uc_transitions.insert(door_open_e.0, door_open_e.1);
    uc_transitions.insert(door_close_e.0, door_close_e.1);

    let mut b: BDD<u32> = BDD::new();
    let is = [false, false, false, false, false, false, true, false, false];
    let ise = state_to_expr(&is);

    // forbid opening
    // let forbidden = and(not(x(1)), and(x(2), x(5)));
    // let forbidden = b.from_expr(&forbidden);

    let forbidden2 = and(not(x(1)), x(7));
    let forbidden2 = b.from_expr(&forbidden2);

    // let forbidden3 = and(x(7), x(8));
    // let forbidden3 = b.from_expr(&forbidden3);

    //    let forbidden = b.or(forbidden, forbidden2);
    //    let forbidden = b.or(forbidden, forbidden3);

    // let forbidden = BDD_ZERO; // no forbidden states //b.from_expr(&state3e);

    let forbidden = forbidden2;

    let mut ft = BDD_ZERO;
    for t in transitions.values() {
        let f = b.from_expr(t);
        ft = b.or(ft, f);
    }

    let mut uc = BDD_ZERO;
    for t in uc_transitions.values() {
        let f = b.from_expr(t);
        uc = b.or(uc, f);
    }

    // let uc = b.or(ft2, ft4); // BDD_ZERO
    let ub = swap(&mut b, uc, &pairing, &temps); // uncontrollable backwards

    // backwards transitions
    let bt = swap(&mut b, ft, &pairing, &temps);

    let fi = b.from_expr(&ise);

    // find all reachable states
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

    // println!("All reachable states");
    // println!("============================");
    // let mut bitmap = HashMap::new();
    // for i in 0..bitsm {
    //     bits_to_hashmap(bits, i, &mut bitmap);
    //     if b.evaluate(r, &mut bitmap) {
    //         let m: BTreeMap<_, _> = bitmap.iter().collect();
    //         println!("i: {} - {:?}", i, m);
    //     }
    // }

    // println!("\n");

    let mark = [true, false, false, false, false, false]; //, false];
    let mark = state_to_expr(&mark);
    let mark = b.from_expr(&mark);

    let not_forbidden = b.not(forbidden);
    let marked = b.or(fi, mark); // fi; // b.or(fi, state2b); // marked is only initial
    let marked = BDD_ONE; // all states marked...
    let mut nonblock = b.and(marked, not_forbidden);

    let nonblock2 = nbc(&mut b, &vars, &pairing, bt, ub, marked, forbidden);

    loop {
        let old = nonblock;
        let new = relprod(&mut b, old, bt, &vars); // possible trans
        let new = replace(&mut b, new, &pairing); // to source states
        nonblock = b.or(old, new);
        nonblock = b.and(nonblock, not_forbidden);

        // controllability
        let mut rfu = b.not(nonblock); // forbidden;
        loop {
            let old = rfu;
            let new = relprod(&mut b, old, ub, &vars); // possible trans
            let new = replace(&mut b, new, &pairing); // to source states
            rfu = b.or(old, new);

            if old == rfu {
                break;
            } else {
                println!("FOUND TRANS");
            }
        }

        rfu = b.not(rfu);
        nonblock = b.or(rfu, old);

        // cleanup...
        // TODO. this should not be not needed
        nonblock = b.and(nonblock, r);

        if old == nonblock {
            break;
        }
    }

    let n_nb2 = b.not(nonblock2);
    nonblock = b.and(n_nb2, r);

    println!("Reachable nonblocking states");
    println!("============================");
    let mut bitmap = HashMap::new();
    let mut state_count = 0;
    for i in 0..bitsm {
        bits_to_hashmap(bits, i, &mut bitmap);
        if b.evaluate(nonblock, &mut bitmap) {
            let m: BTreeMap<_, _> = bitmap.iter().collect();
            println!("i: {} - {:?}", i, m);
            state_count += 1;
        }
    }

    println!("Nbr of reachable states: {}\n", state_count);

    println!("Forbidden (reachable) states");
    println!("============================");
    let notnonblock = b.not(nonblock);
    let forbidden = b.and(r, notnonblock);
    let mut bitmap = HashMap::new();
    for i in 0..bitsm {
        bits_to_hashmap(bits, i, &mut bitmap);
        if b.evaluate(forbidden, &mut bitmap) {
            let m: BTreeMap<_, _> = bitmap.iter().collect();
            println!("i: {} - {:?}", i, m);
        }
    }

    println!("\n");

    // find guards...
    for (name, t) in transitions {
        // println!("transition? {:?}", t);
        let f = b.from_expr(&t);
        let f_orig = f;
        let bt = swap(&mut b, f, &pairing, &temps);
        let x = relprod(&mut b, nonblock, bt, &vars);
        let x = replace(&mut b, x, &pairing);

        // x is new guard. use it and compare with original trans
        let xf = b.and(f, x);
        let y = relprod(&mut b, nonblock, f, &vars);
        let z = relprod(&mut b, nonblock, xf, &vars);

        if y != z {
            println!("transition {:?} got new guard...", name);
        } else if y != z {
            // quanity out target states from trans to get guard
            let mut f = f;
            for v in &destvars {
                let sf = b.restrict(f, *v, false);
                let st = b.restrict(f, *v, true);
                f = b.or(sf, st);
            }

            let forbx = relprod(&mut b, forbidden, bt, &vars);
            let mut forbx = replace(&mut b, forbx, &pairing);

            let fe = b.to_expr(f);
            let tie = terms_in_expr(&fe);
            // now hack f out of x
            let mut xx = x;
            for t in tie {
                let sf = b.restrict(xx, t, false);
                let st = b.restrict(xx, t, true);
                xx = b.or(sf, st);

                let sf = b.restrict(forbx, t, false);
                let st = b.restrict(forbx, t, true);
                forbx = b.or(sf, st);
            }
            // assert that my thinking is correct...
            let tot = b.and(xx, f);
            assert_eq!(tot, x);

            // guard need to stop us from reaching forbidden
            forbx = b.not(forbx);
            let forbe = b.to_expr(forbx);

            let f_and_forb = b.and(f_orig, forbx);
            let bt = swap(&mut b, f_and_forb, &pairing, &temps);
            // assert that my thinking is correct...
            assert_eq!(relprod(&mut b, forbidden, bt, &vars), BDD_ZERO);

            let fe = b.to_expr(f);
            let e = b.to_expr(xx);

            let tie_x = terms_in_expr(&e);
            let tie_y = terms_in_expr(&forbe);

            // chose the smallest guard representation
            let mut new_guard = if tie_x.len() < tie_y.len() { e } else { forbe };

            // try to remove terms that doesnt lead us to a forbidden state
            // and doesn't over-constrain us wrt the reachable states
            let mut first = None;
            let mut disj = disj(&new_guard);
            let temp_ng = b.from_expr(&new_guard);
            let temp = b.and(f_orig, temp_ng);
            let bt = swap(&mut b, temp, &pairing, &temps);
            let z = relprod(&mut b, nonblock, bt, &vars);

            disj.push(Expr::Const(true));

            for d in disj {
                let temp = b.from_expr(&d);
                let temp = b.and(f_orig, temp);
                let bt = swap(&mut b, temp, &pairing, &temps);
                let y = relprod(&mut b, forbidden, bt, &vars);
                let zz = relprod(&mut b, nonblock, bt, &vars);

                if y == BDD_ZERO && z == zz {
                    // yay, we can eliminate the term
                    println!("yay!: {:?}", d);
                    first = Some(d);
                } else {
                    // noh!
                    println!("no luck for: {:?}", d);
                }
            }

            let disj_exprs = disj_powerset(&new_guard);
            let ok_exprs: Vec<_> = disj_exprs
                .iter()
                .filter(|e| {
                    let temp = b.from_expr(&e);
                    let temp = b.and(f_orig, temp);
                    let bt = swap(&mut b, temp, &pairing, &temps);
                    let y = relprod(&mut b, forbidden, bt, &vars);
                    let zz = relprod(&mut b, nonblock, bt, &vars);

                    y == BDD_ZERO && z == zz
                })
                .collect();
            println!("ALL OK: {:?}", ok_exprs);
            let lens: Vec<_> = ok_exprs.iter().map(|x| terms_in_expr(x).len()).collect();
            println!("TERM LENS: {:?}", lens);

            let least_terminals = ok_exprs
                .into_iter()
                .min_by(|x, y| terms_in_expr(&x).len().cmp(&terms_in_expr(&y).len()));

            if let Some(x) = least_terminals {
                //if let Some(x) = first {
                new_guard = x.clone();
            }

            // new guard!
            println!("guard added for transition {}", name);
            println!("orig guard: {:?}", fe);
            println!("new guard: {:#?}", new_guard);
            println!("");
        }
    }

    assert!(false);
}

fn main() {
    println!("Hello, world!");
}
