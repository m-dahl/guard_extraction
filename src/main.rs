use boolean_expression::*;
use std::collections::HashMap;
use std::collections::BTreeMap;
use Expr;


fn term_hashmap(vals: &[bool], h: &mut HashMap<u32, bool>) {
    h.clear();
    for (i, v) in vals.iter().enumerate() {
        h.insert(i as u32, *v);
    }
}

fn test_bdd(
    b: &BDD<u32>,
    f: BDDFunc,
    h: &mut HashMap<u32, bool>,
    inputs: &[bool],
    expected: bool,
) {
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
        b.to_expr(f_0_and_1_or_2) == Expr::or(
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

use std::fmt::Debug;
use std::cmp::Ord;
use std::hash::Hash;

fn iff<T>(a: Expr<T>, b: Expr<T>) -> Expr<T>
where T: Clone + Debug + Eq + Ord + Hash
{
    Expr::or(Expr::and(a.clone(), b.clone()), Expr::and(Expr::not(a), Expr::not(b)))
}

fn relprod<T>(b: &mut BDD<T>, states: BDDFunc, transitions: BDDFunc, variables: &Vec<T>) -> BDDFunc
where
    T: Clone + Debug + Eq + Ord + Hash + Copy {
    let mut f = b.and(states, transitions);

    for v in variables {
        let sf = b.restrict(f, *v, false);
        let st = b.restrict(f, *v, true);
        f = b.or(sf, st);
    }

    f
}

fn replace<T>(b: &mut BDD<T>, func: BDDFunc, pairing: &Vec<(T,T)>) -> BDDFunc
where
    T: Clone + Debug + Eq + Ord + Hash + Copy {

    let mut f = func;
    for (s,t) in pairing {  // set s to t
        let s = b.terminal(*s);
        let t = b.terminal(*t);
        let f1 = b.and(s, t);
        let ns = b.not(s);
        let nt = b.not(t);
        let f2 = b.and(ns, nt);
        let iff = b.or(f1,f2);
        f = b.and(iff, f);
    }

    for (_,t) in pairing { // quantify away t
        let sf = b.restrict(f, *t, false);
        let st = b.restrict(f, *t, true);
        f = b.or(sf, st);
    }
    f  // now we have "s"
}

// swap using temporary terminals
fn swap<T>(b: &mut BDD<T>, func: BDDFunc, pairing: &Vec<(T,T)>, temps: &Vec<T>) -> BDDFunc
where
    T: Clone + Debug + Eq + Ord + Hash + Copy {

    // newBDD.replaceWith(sourceToTempVariablePairing);
    // newBDD.replaceWith(destToSourceVariablePairing);
    // newBDD.replaceWith(tempToDestVariablePairing);


    // t = (8, 0)
    // r = (0, 4)
    // f = (4, 8)

    let pair1: Vec<_> = pairing.iter().zip(temps.iter()).
        map(|((x,y),z)| (*z, *x)).collect();

    let pair2: Vec<_> = pairing.iter().zip(temps.iter()).
        map(|((x,y),z)| (*y, *z)).collect();

    let nf = replace(b, func, &pair1);
    let nf = replace(b, nf, pairing);
    replace(b, nf, &pair2)
}

#[test]
fn bdd_eval2() {
    let mut b = BDD::new();
    let is = Expr::and(Expr::Terminal(0), Expr::and(Expr::not(Expr::Terminal(1)), Expr::and(Expr::not(Expr::Terminal(2)), Expr::not(Expr::Terminal(3)))));
//    let fi = b.from_expr(&is);

    let vals = vec![true, false, false, false];
    let mut h = HashMap::new();
    for (i, v) in vals.iter().enumerate() {
        h.insert(i as u32, *v);
    }
    let vars = vec![0, 1, 2, 3];
    let pairing = vec![(0,4), (1,5), (2,6), (3,7)];

    // transition 1, flip s_1 to false, keep others
    let t1 = Expr::and(is.clone(), Expr::and(Expr::not(Expr::Terminal(4)), Expr::and(iff(Expr::Terminal(1), Expr::Terminal(5)), Expr::and(iff(Expr::Terminal(2), Expr::Terminal(6)), iff(Expr::Terminal(3), Expr::Terminal(7))))));

    // state 1, all false.
    let state1 = Expr::and(Expr::not(Expr::Terminal(0)), Expr::and(Expr::not(Expr::Terminal(1)), Expr::and(Expr::not(Expr::Terminal(2)), Expr::not(Expr::Terminal(3)))));
    // t2, flib s_2 to true, keep others
    let t2 = Expr::and(state1.clone(), Expr::and(Expr::Terminal(5), Expr::and(iff(Expr::Terminal(0), Expr::Terminal(4)), Expr::and(iff(Expr::Terminal(2), Expr::Terminal(6)), iff(Expr::Terminal(3), Expr::Terminal(7))))));

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
    state.iter().enumerate().fold(Expr::Const(true), |acc, (i, v)|
                                  if *v {
                                      Expr::and(acc, Expr::Terminal(i as u32))
                                  } else {
                                      Expr::and(acc, Expr::not(Expr::Terminal(i as u32)))
                                  })
}

fn state_in_bddfunc(bdd: &BDD<u32>, f: BDDFunc, state: &[bool]) -> bool {
    let mut h = HashMap::new();
    for (i, v) in state.iter().enumerate() {
        h.insert(i as u32, *v);
    }
    bdd.evaluate(f, &h)
}

#[test]
fn bdd_test4() {
    let mut b = BDD::new();
    let is = Expr::and(Expr::Terminal(0), Expr::and(Expr::not(Expr::Terminal(1)), Expr::and(Expr::not(Expr::Terminal(2)), Expr::not(Expr::Terminal(3)))));
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
    let is = Expr::and(Expr::Terminal(0), Expr::and(Expr::not(Expr::Terminal(1)), Expr::and(Expr::not(Expr::Terminal(2)), Expr::not(Expr::Terminal(3)))));
//    let fi = b.from_expr(&is);

    let vals = vec![true, false, false, false];
    let mut h = HashMap::new();
    for (i, v) in vals.iter().enumerate() {
        h.insert(i as u32, *v);
    }
    let vars = vec![0, 1, 2, 3];
    let pairing = vec![(0,4), (1,5), (2,6), (3,7)];

    // transition 1, flip s_1 to false, keep others
    let t1 = Expr::and(is.clone(), Expr::and(Expr::not(Expr::Terminal(4)), Expr::and(iff(Expr::Terminal(1), Expr::Terminal(5)), Expr::and(iff(Expr::Terminal(2), Expr::Terminal(6)), iff(Expr::Terminal(3), Expr::Terminal(7))))));

    let state1 = Expr::and(Expr::not(Expr::Terminal(0)), Expr::and(Expr::not(Expr::Terminal(1)), Expr::and(Expr::not(Expr::Terminal(2)), Expr::not(Expr::Terminal(3)))));
    // t2, flib s_2 to true, keep others
    let t2 = Expr::and(state1.clone(), Expr::and(Expr::Terminal(5), Expr::and(iff(Expr::Terminal(0), Expr::Terminal(4)), Expr::and(iff(Expr::Terminal(2), Expr::Terminal(6)), iff(Expr::Terminal(3), Expr::Terminal(7))))));


    let fi = b.from_expr(&is);

    let ft1 = b.from_expr(&t1);
    let ft2 = b.from_expr(&t2);

    let ft = b.or(ft1, ft2);

    let mut r = fi;

    loop {
        let old = r;
        let new = relprod(&mut b, old, ft, &vars); // possible trans
        let new = replace(&mut b, new, &pairing);  // to source states
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

    let pairing = vec![(0,4), (1,5), (2,6), (3,7)];
    let temps = vec![8,9,10,11]; // hmmm...

    let is = [false, false, false, false];
    let ise = state_to_expr(&is);

    let state1 = [true, false, false, false];
    let state1e = state_to_expr(&state1);

    let state2 = [true, true, false, false];
    let state2e = state_to_expr(&state2);

    let mut b = BDD::new();

    // transition 1, flip s_0 to false, keep others
    let t1 = Expr::and(ise.clone(), Expr::and((Expr::Terminal(4)), Expr::and(iff(Expr::Terminal(1), Expr::Terminal(5)), Expr::and(iff(Expr::Terminal(2), Expr::Terminal(6)), iff(Expr::Terminal(3), Expr::Terminal(7))))));

    // t2, flip s_1 to true, keep others
    let t2 = Expr::and(state1e.clone(), Expr::and(Expr::Terminal(5), Expr::and(iff(Expr::Terminal(0), Expr::Terminal(4)), Expr::and(iff(Expr::Terminal(2), Expr::Terminal(6)), iff(Expr::Terminal(3), Expr::Terminal(7))))));

    // t3, flip from state1 back to initial state
    let t3 = Expr::and(state1e.clone(), Expr::and(Expr::not(Expr::Terminal(4)), Expr::and(Expr::not(Expr::Terminal(5)), Expr::and(iff(Expr::Terminal(2), Expr::Terminal(6)), iff(Expr::Terminal(3), Expr::Terminal(7))))));

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
        let new = replace(&mut b, new, &pairing);  // to source states
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
    println!("in bdd? {:?}", state_in_bddfunc(&b, r, &[false, true, false, false]));


    // check that some other state is NOT in bdd
    println!("in bdd? {:?}", state_in_bddfunc(&b, r, &[false, false, true, false]));

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

    let pairing: Vec<_> = vars.iter().zip(destvars.iter()).map(|(x,y)|(*x,*y)).collect();
    let temps = vec![8,9,10,11]; // hmmm...

    let is = [false, false, false, false];
    let ise = state_to_expr(&is);

    let state1 = [true, false, false, false];
    let state1e = state_to_expr(&state1);

    let state2 = [true, true, false, false];
    let state2e = state_to_expr(&state2);

    let mut b = BDD::new();

    // transition 1, flip s_0 to false, keep others
    let t1 = Expr::and(ise.clone(), Expr::and((Expr::Terminal(4)), Expr::and(iff(Expr::Terminal(1), Expr::Terminal(5)), Expr::and(iff(Expr::Terminal(2), Expr::Terminal(6)), iff(Expr::Terminal(3), Expr::Terminal(7))))));

    // t2, flip s_1 to true, keep others
    let t2 = Expr::and(state1e.clone(), Expr::and(Expr::Terminal(5), Expr::and(iff(Expr::Terminal(0), Expr::Terminal(4)), Expr::and(iff(Expr::Terminal(2), Expr::Terminal(6)), iff(Expr::Terminal(3), Expr::Terminal(7))))));

    // t3, flip from state1 back to initial state
    let t3 = Expr::and(state1e.clone(), Expr::and(Expr::not(Expr::Terminal(4)), Expr::and(Expr::not(Expr::Terminal(5)), Expr::and(iff(Expr::Terminal(2), Expr::Terminal(6)), iff(Expr::Terminal(3), Expr::Terminal(7))))));

    // t4, flip last bit => forbidden state
    //let t4 = Expr::and(state1e.clone(), Expr::and(iff(Expr::Terminal(0), Expr::Terminal(4)), Expr::and(iff(Expr::Terminal(1), Expr::Terminal(5)), Expr::and(iff(Expr::Terminal(2), Expr::Terminal(6)), Expr::Terminal(7)))));
    // t4, flip last bit from any state...
    let t4 = Expr::and(Expr::not(Expr::Terminal(3)), Expr::and(iff(Expr::Terminal(0), Expr::Terminal(4)), Expr::and(iff(Expr::Terminal(1), Expr::Terminal(5)), Expr::and(iff(Expr::Terminal(2), Expr::Terminal(6)), Expr::Terminal(7)))));

    // t5, from the forbidden state back to s1
    let state3 = [true, false, false, true];
    let state3e = state_to_expr(&state3);

    let t5 = Expr::and(state3e.clone(), Expr::and(Expr::not(Expr::Terminal(4)), Expr::and(iff(Expr::Terminal(1), Expr::Terminal(5)), Expr::and(iff(Expr::Terminal(2), Expr::Terminal(6)), Expr::not(Expr::Terminal(7))))));

    // t6, from the 0001 state back to initial
    let state4 = [false, false, false, true];
    let state4e = state_to_expr(&state4);

    let t6 = Expr::and(state4e.clone(), Expr::and(iff(Expr::Terminal(0), Expr::Terminal(4)), Expr::and(iff(Expr::Terminal(1), Expr::Terminal(5)), Expr::and(iff(Expr::Terminal(2), Expr::Terminal(6)), Expr::not(Expr::Terminal(7))))));

    let trans = vec![t1.clone(),t2.clone(),t3.clone(), t4.clone(), t5.clone(), t6.clone()];

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
            let m: BTreeMap<_,_> = bitmap.iter().collect();
            println!("i: {} - {:?}", i, m);
        }
    }


    // find all reachable states
    let mut r = fi;
    loop {
        let old = r;
        let new = relprod(&mut b, old, ft, &vars); // possible trans
        let new = replace(&mut b, new, &pairing);  // to source states
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
            let m: BTreeMap<_,_> = bitmap.iter().collect();
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
            let m: BTreeMap<_,_> = bitmap.iter().collect();
            println!("i: {} - {:?}", i, m);
        }
    }



    let not_forbidden = b.not(forbidden);
    let marked = fi; // b.or(fi, state2b); // marked is only initial
    let mut nonblock = b.and(marked, not_forbidden);

    loop {

        let old = nonblock;
        let new = relprod(&mut b, old, bt, &vars); // possible trans
        let new = replace(&mut b, new, &pairing);  // to source states
        nonblock = b.or(old, new);
        nonblock = b.and(nonblock, not_forbidden);

        // todo: uncontrollable/forbidden here

        // controllability
        let mut rfu = b.not(nonblock); // forbidden;
        loop {
            let old = rfu;
            let new = relprod(&mut b, old, ub, &vars); // possible trans
            let new = replace(&mut b, new, &pairing);  // to source states
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
            let m: BTreeMap<_,_> = bitmap.iter().collect();
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
            let m: BTreeMap<_,_> = bitmap.iter().collect();
            println!("i: {} - {:?}", i, m);
        }
    }


    println!("Forbidden states");
    let mut bitmap = HashMap::new();
    for i in 0..16 {
        bits_to_hashmap(4, i, &mut bitmap);
        if b.evaluate(forbidden, &mut bitmap) {
            let m: BTreeMap<_,_> = bitmap.iter().collect();
            println!("i: {} - {:?}", i, m);
        }
    }

    // controllability
    let mut rfu = forbidden;
    loop {
        let old = rfu;
        let new = relprod(&mut b, old, ub, &vars); // possible trans
        let new = replace(&mut b, new, &pairing);  // to source states
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
            let m: BTreeMap<_,_> = bitmap.iter().collect();
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
            let m: BTreeMap<_,_> = bitmap.iter().collect();
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

    let pairing: Vec<_> = vars.iter().zip(destvars.iter()).map(|(x,y)|(*x,*y)).collect();
    let temps = vec![8,9,10,11]; // hmmm...

    let is = [false, false, false, false];
    let ise = state_to_expr(&is);

    let state1 = [true, false, false, false];
    let state1e = state_to_expr(&state1);

    let state2 = [true, true, false, false];
    let state2e = state_to_expr(&state2);

    let mut b = BDD::new();

    // transition 1, flip s_0 to false, keep others
    let t1 = Expr::and(ise.clone(), Expr::and((Expr::Terminal(4)), Expr::and(iff(Expr::Terminal(1), Expr::Terminal(5)), Expr::and(iff(Expr::Terminal(2), Expr::Terminal(6)), iff(Expr::Terminal(3), Expr::Terminal(7))))));

    // t2, flip s_1 to true, keep others
    let t2 = Expr::and(state1e.clone(), Expr::and(Expr::Terminal(5), Expr::and(iff(Expr::Terminal(0), Expr::Terminal(4)), Expr::and(iff(Expr::Terminal(2), Expr::Terminal(6)), iff(Expr::Terminal(3), Expr::Terminal(7))))));

    // t3, flip from state1 back to initial state
    let t3 = Expr::and(state1e.clone(), Expr::and(Expr::not(Expr::Terminal(4)), Expr::and(Expr::not(Expr::Terminal(5)), Expr::and(iff(Expr::Terminal(2), Expr::Terminal(6)), iff(Expr::Terminal(3), Expr::Terminal(7))))));

    // t4, flip last bit => forbidden state
    //let t4 = Expr::and(state1e.clone(), Expr::and(iff(Expr::Terminal(0), Expr::Terminal(4)), Expr::and(iff(Expr::Terminal(1), Expr::Terminal(5)), Expr::and(iff(Expr::Terminal(2), Expr::Terminal(6)), Expr::Terminal(7)))));
    // t4, flip last bit from any state...
    let t4 = Expr::and(Expr::not(Expr::Terminal(3)), Expr::and(iff(Expr::Terminal(0), Expr::Terminal(4)), Expr::and(iff(Expr::Terminal(1), Expr::Terminal(5)), Expr::and(iff(Expr::Terminal(2), Expr::Terminal(6)), Expr::Terminal(7)))));

    // t5, from the forbidden state back to s1
    let state3 = [true, false, false, true];
    let state3e = state_to_expr(&state3);

    let t5 = Expr::and(state3e.clone(), Expr::and(Expr::not(Expr::Terminal(4)), Expr::and(iff(Expr::Terminal(1), Expr::Terminal(5)), Expr::and(iff(Expr::Terminal(2), Expr::Terminal(6)), Expr::not(Expr::Terminal(7))))));

    // t6, from the 0001 state back to initial
    let state4 = [false, false, false, true];
    let state4e = state_to_expr(&state4);

    let t6 = Expr::and(state4e.clone(), Expr::and(iff(Expr::Terminal(0), Expr::Terminal(4)), Expr::and(iff(Expr::Terminal(1), Expr::Terminal(5)), Expr::and(iff(Expr::Terminal(2), Expr::Terminal(6)), Expr::not(Expr::Terminal(7))))));

    let trans = vec![t1.clone(),t2.clone(),t3.clone(), t4.clone(), t5.clone(), t6.clone()];

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
        let new = replace(&mut b, new, &pairing);  // to source states
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
        let new = replace(&mut b, new, &pairing);  // to source states
        nonblock = b.or(old, new);
        nonblock = b.and(nonblock, not_forbidden);

        // controllability
        let mut rfu = b.not(nonblock); // forbidden;
        loop {
            let old = rfu;
            let new = relprod(&mut b, old, ub, &vars); // possible trans
            let new = replace(&mut b, new, &pairing);  // to source states
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
            let m: BTreeMap<_,_> = bitmap.iter().collect();
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
    vs.iter().fold(Expr::Const(true), |acc, i|
                   Expr::and(acc, iff(Expr::Terminal(*i as u32),
                                      Expr::Terminal(*i + offset as u32))))
}

#[test]
fn bdd_door_lock() {

    // set up variables

    let vars = vec![0,  // door_closed_m
                    1,  // door_opened_m
                    2,  // door_gs_c, false = closed, true = opened

                    3,  // lock_l_c
                    4,  // lock_u_c
                    5,  // lock_e
                    6,  // lock_e_unknown = true
    ];

    let destvars: Vec<_> = vars.iter().map(|i| i + vars.len() as u32).collect();
    let temps: Vec<_> = vars.iter().map(|i| i + 2*vars.len() as u32).collect();

    let pairing: Vec<_> = vars.iter().zip(destvars.iter()).map(|(x,y)|(*x,*y)).collect();

    println!("{:?}", vars);
    println!("{:?}", destvars);
    println!("{:?}", temps);

    // convenience
    let x    = |n| Expr::Terminal(n) ;
    let next = |n| Expr::Terminal(n + vars.len() as u32) ;
    let and  = |a,b| Expr::and(a,b) ;
    let or   = |a,b| Expr::or(a,b) ;
    let not  = |a| Expr::not(a) ;

    // set up transitions
    let door_open_d = and( and(not(x(1)), next(2)) ,
                           iffs(&[0, 1, 3, 4, 5, 6], vars.len()));
    let door_open_e = and( and(x(2), and(not(x(1)), and(next(1), not(next(0))))),
                           iffs(&[2,3,4,5,6], vars.len()));

    let door_close_d = and( and(not(x(0)), not(next(2))),
                            iffs(&[0, 1, 3, 4, 5, 6], vars.len()));
    let door_close_e = and( and(not(x(2)), and(not(x(0)), and(not(next(1)), next(0)))),
                            iffs(&[2, 3, 4, 5, 6], vars.len()));

    let lock_d = and( and( or(x(6), not(x(5))), and(next(3), and(not(next(4)), and(next(5), not(next(6)))))),
                      iffs(&[0, 1, 2], vars.len()) );

    let unlock_d = and( and(or(x(6), x(5)), and(not(next(3)), and(next(4), and(not(next(5)), not(next(6)))))),
                        iffs(&[0, 1, 2], vars.len()) );

    let mut b: BDD<u32> = BDD::new();
    let is = [true, false, false, false, false, false, true];
    let ise = state_to_expr(&is);

    // forbid opening
    let forbidden = and(not(x(1)), and(x(2), x(5)));
    let forbidden = b.from_expr(&forbidden);

    // let forbidden = BDD_ZERO; // no forbidden states //b.from_expr(&state3e);

    let ft1 = b.from_expr(&door_open_d);
    let ft2 = b.from_expr(&door_open_e);
    let ft3 = b.from_expr(&door_close_d);
    let ft4 = b.from_expr(&door_close_e);
    let ft5 = b.from_expr(&lock_d);
    let ft6 = b.from_expr(&unlock_d);

    let ft = b.or(ft1, ft2);
    let ft = b.or(ft, ft3);
    let ft = b.or(ft, ft4);
    let ft = b.or(ft, ft5);
    let ft = b.or(ft, ft6);

    let uc = b.or(ft2, ft4); // BDD_ZERO
    let ub = swap(&mut b, uc, &pairing, &temps); // uncontrollable backwards

    // backwards transitions
    let bt = swap(&mut b, ft, &pairing, &temps);


    let fi = b.from_expr(&ise);


    // find all reachable states
    let mut r = fi;
    loop {
        let old = r;
        let new = relprod(&mut b, old, ft, &vars); // possible trans
        let new = replace(&mut b, new, &pairing);  // to source states
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
            let m: BTreeMap<_,_> = bitmap.iter().collect();
            println!("i: {} - {:?}", i, m);
        }
    }

    println!("\n");



    let mark = [true, false, false, false, false, false, false];
    let mark = state_to_expr(&mark);
    let mark = b.from_expr(&mark);

    let not_forbidden = b.not(forbidden);
    let marked = b.or(fi,mark); // fi; // b.or(fi, state2b); // marked is only initial
    let marked = BDD_ONE; // all states marked...
    let mut nonblock = b.and(marked, not_forbidden);

    loop {

        let old = nonblock;
        let new = relprod(&mut b, old, bt, &vars); // possible trans
        let new = replace(&mut b, new, &pairing);  // to source states
        nonblock = b.or(old, new);
        nonblock = b.and(nonblock, not_forbidden);

        // controllability
        let mut rfu = b.not(nonblock); // forbidden;
        loop {
            let old = rfu;
            let new = relprod(&mut b, old, ub, &vars); // possible trans
            let new = replace(&mut b, new, &pairing);  // to source states
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
            let m: BTreeMap<_,_> = bitmap.iter().collect();
            println!("i: {} - {:?}", i, m);
        }
    }

    println!("\n");


    assert!(false);

}

fn main() {
    println!("Hello, world!");
}
