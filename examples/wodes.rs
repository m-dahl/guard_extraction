use guard_extraction::*;

fn main_buddy() {
    // set up variables
    let mut c = Context::default();

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

    // convenience
    let v = |n| Ex::VAR(n);
    let _nv = |n| Ex::NOT(Box::new(Ex::VAR(n)));
    let and = |x| Ex::AND(x);
    let or = |x| Ex::OR(x);
    let not = |x| Ex::NOT(Box::new(x));
    let imp = |a, b| Ex::OR(vec![not(a), b]);
    let eq = |v, n| Ex::EQ(v, Value::InDomain(n));

    let aeq = |v, n| Ac { var: v, val: Value::InDomain(n) };
    let at = |v| Ac { var: v, val: Value::Bool(true) };
    let an = |v| Ac { var: v, val: Value::Bool(false) };


    c.add_c_trans("tool_open_d", &not(v(tool_opened_m)), &[aeq(tool_gs_c, 1)]);
    c.add_uc_trans("tool_open_e", &and(vec![eq(tool_gs_c, 1), not(v(tool_opened_m))]),
                   &[at(tool_opened_m), an(tool_closed_m)]);

    c.add_c_trans("tool_close_d", &not(v(tool_closed_m)), &[aeq(tool_gs_c, 0)]);
    c.add_uc_trans("tool_close_e", &and(vec![eq(tool_gs_c, 0), not(v(tool_closed_m))]),
                   &[at(tool_closed_m), an(tool_opened_m)]);

    c.add_c_trans("rsp_lock_d", &or(vec![eq(rsp_lock_e, 1), eq(rsp_lock_e, 2)]),
                  &[at(rsp_lock_l_c), an(rsp_lock_u_c), aeq(rsp_lock_e, 0)]);

    c.add_c_trans("rsp_unlock_d", &or(vec![eq(rsp_lock_e, 0), eq(rsp_lock_e, 2)]),
                  &[an(rsp_lock_l_c), at(rsp_lock_u_c), aeq(rsp_lock_e, 1)]);


    c.add_c_trans("robot_p0_d", &and(vec![v(robot_p_m), v(robot_p_c), v(robot_p_e)]), &[an(robot_p_c)]);
    c.add_uc_trans("robot_p0_se", &and(vec![v(robot_p_m), not(v(robot_p_c)), not(v(robot_moving_m))]), &[at(robot_moving_m)]);
    c.add_uc_trans("robot_p0_ee", &and(vec![v(robot_p_m), not(v(robot_p_c)), v(robot_moving_m)]),
                   &[an(robot_p_m), an(robot_moving_m)]);
    c.add_uc_trans("robot_p0_fa", &and(vec![not(v(robot_p_m)), not(v(robot_p_c)), not(v(robot_moving_m)), v(robot_p_e)]),
                   &[an(robot_p_e)]);

    c.add_c_trans("robot_p1_d", &and(vec![not(v(robot_p_m)), not(v(robot_p_c)), not(v(robot_p_e))]), &[at(robot_p_c)]);
    c.add_uc_trans("robot_p1_se", &and(vec![not(v(robot_p_m)), v(robot_p_c), not(v(robot_moving_m))]), &[at(robot_moving_m)]);
    c.add_uc_trans("robot_p1_ee", &and(vec![not(v(robot_p_m)), v(robot_p_c), v(robot_moving_m)]),
                   &[at(robot_p_m), an(robot_moving_m)]);
    c.add_uc_trans("robot_p1_fa", &and(vec![v(robot_p_m), v(robot_p_c), not(v(robot_moving_m)), not(v(robot_p_e))]),
                   &[at(robot_p_e)]);

    c.add_uc_trans("tool_e_home_a", &and(vec![eq(tool_e, 1), not(v(robot_p_m)), eq(rsp_lock_e, 1)]),
                   &[aeq(tool_e, 0)]);
    c.add_uc_trans("tool_e_robot_a", &and(vec![eq(tool_e, 0), not(v(robot_p_m)), eq(rsp_lock_e, 0)]),
                   &[aeq(tool_e, 1)]);

    // // let is = [false, false, false, false, false, false, true, false, false, true, false, false];
    // // let ise = state_to_expr2(&is);

    // tool cannot be closed and opened at the same time.
    let forbidden = and(vec![v(tool_closed_m), v(tool_opened_m)]);

    // spec A
    let mtop1exec = and(vec![not(v(robot_p_m)), v(robot_p_c), v(robot_moving_m)]);
    let forbidden_a = not(imp(and(vec![eq(tool_e, 1), not(v(robot_p_e)), mtop1exec]), v(tool_opened_m)));

    // spec B
    let mtop0exec = and(vec![v(robot_p_m), not(v(robot_p_c)), v(robot_moving_m)]);
    let forbidden_b = not(imp(and(vec![eq(tool_e, 1), v(robot_p_e), mtop0exec]), v(tool_opened_m)));

    // spec C
    let mtop0exec = and(vec![v(robot_p_m), not(v(robot_p_c)), v(robot_moving_m)]);
    let forbidden_c = not(imp(and(vec![eq(tool_e, 0), mtop0exec]), eq(rsp_lock_e, 1)));

    // spec D
    let forbidden_d = not(imp(and(vec![eq(tool_e, 1), eq(rsp_lock_e, 0)]),
                              and(vec![v(tool_closed_m), not(v(robot_p_m))])));

    // spec E
    let forbidden_e = not(imp(eq(tool_e, 0), not(v(tool_opened_m))));

    let forbidden = or(vec![forbidden, forbidden_a, forbidden_b, forbidden_c, forbidden_d, forbidden_e]);

    let (new_guards, _supervisor) = c.compute_guards(&Ex::TRUE, &forbidden);

    println!("\n");
    for (trans, guard) in &new_guards {
        let s = c.pretty_print(&guard);
        println!("NEW GUARD FOR {}: {}", trans, s);
        println!("\n");
    }

}



fn main_mini() {
    // set up variables
    let mut c = Context::default();

    let r1_at_m = c.add_bool("r1_at_m");
    let r1_at_c = c.add_bool("r1_at_c");

    let r1_away_m = c.add_bool("r1_away_m");
    let r1_away_c = c.add_bool("r1_away_c");

    let r2_at_m = c.add_bool("r2_at_m");
    let r2_at_c = c.add_bool("r2_at_c");

    let r2_away_m = c.add_bool("r2_away_m");
    let r2_away_c = c.add_bool("r2_away_c");

    // convenience
    let v = |n| Ex::VAR(n);
    let _nv = |n| Ex::NOT(Box::new(Ex::VAR(n)));
    let and = |x| Ex::AND(x);
    let _or = |x| Ex::OR(x);
    let not = |x| Ex::NOT(Box::new(x));
    let _imp = |a, b| Ex::OR(vec![not(a), b]);
    let _eq = |v, n| Ex::EQ(v, Value::InDomain(n));

    let _aeq = |v, n| Ac { var: v, val: Value::InDomain(n) };
    let at = |v| Ac { var: v, val: Value::Bool(true) };
    let _an = |v| Ac { var: v, val: Value::Bool(false) };

    c.add_c_trans("r1_to_at_d",
                  &not(v(r1_at_m)),
                  &[at(r1_at_c)]);
    c.add_uc_trans("r1_to_at_e",
                   &and(vec![v(r1_at_c), not(v(r1_at_m))]),
                   &[at(r1_at_m)]);

    c.add_c_trans("r1_to_away_d",
                  &not(v(r1_away_m)),
                  &[at(r1_away_c)]);
    c.add_uc_trans("r1_to_away_e",
                   &and(vec![v(r1_away_c), not(v(r1_away_m))]),
                   &[at(r1_away_m)]);

    c.add_c_trans("r2_to_at_d",
                  &not(v(r2_at_m)),
                  &[at(r2_at_c)]);
    c.add_uc_trans("r2_to_at_e",
                   &and(vec![v(r2_at_c), not(v(r2_at_m))]),
                   &[at(r2_at_m)]);

    c.add_c_trans("r2_to_away_d",
                  &not(v(r2_away_m)),
                  &[at(r2_away_c)]);
    c.add_uc_trans("r2_to_away_e",
                   &and(vec![v(r2_away_c), not(v(r2_away_m))]),
                   &[at(r2_away_m)]);

    // both cannot be at at
    let forbidden = and(vec![v(r1_at_m), v(r2_at_m)]);

    let (new_guards, _supervisor) = c.compute_guards(&Ex::TRUE, &forbidden);

    for (trans, guard) in &new_guards {
        let s = c.pretty_print(&guard);
        println!("NEW GUARD FOR {}: {}", trans, s);
    }
}

fn main() {
    main_mini();
    // test that initialization and reinitialization really works
    for _i in 1..100 {
        main_buddy();
   }
}
