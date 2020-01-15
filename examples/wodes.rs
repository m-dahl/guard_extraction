use std::collections::HashMap;
use std::collections::HashSet;
use std::iter::FromIterator;
use itertools::Itertools;


use boolean_expression::*;
use guard_extraction::*;

fn main() {
    // set up variables
    let mut c = Context::new();

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

    let (reachable, bad, controllable) = bc.controllable(BDD_ONE, forbidden);

    let state_count = satcount(&mut bc.b, controllable, vars.len());
    println!("Nbr of states in supervisor: {}\n", state_count);
    let reachable_state_count = satcount(&mut bc.b, reachable, vars.len());
    println!("Nbr of reachable states: {}\n", reachable_state_count);


    let new_guards = bc.compute_guards(controllable, bad);

    for (trans, guard) in &new_guards {
        let s = c.pretty_print(&guard);
        println!("NEW GUARD FOR {}: {}", trans, s);
    }
}