
pub fn initialize_type_checker() {
    unsafe {
        let fresh_name = build_lean_name(&["_kernel_fresh"]);
        lean_mark_persistent(fresh_name);
        G_KERNEL_FRESH.store(fresh_name, Ordering::Release);
        lean_register_name_generator_prefix(fresh_name);

        let bool_true = build_lean_name(&["Bool", "true"]);
        lean_mark_persistent(bool_true);
        G_BOOL_TRUE.store(bool_true, Ordering::Release);

        let eager_reduce = build_lean_name(&["eagerReduce"]);
        lean_mark_persistent(eager_reduce);
        G_EAGER_REDUCE.store(eager_reduce, Ordering::Release);

        // dont_care expression (a const with name "dontcare").
        // lean_expr_mk_const consumes both args (obj_arg); do not dec them after.
        let dont_care_name = build_lean_name(&["dontcare"]);
        let levels_nil = lean_mk_list_nil(ptr::null_mut());
        let dont_care_expr = lean_expr_mk_const(dont_care_name, levels_nil);
        lean_mark_persistent(dont_care_expr);
        G_DONT_CARE.store(dont_care_expr, Ordering::Release);

        // Bool constants (as Expr.const, used by mk_bool for reduced Nat.beq/ble results)
        init_global_const(&G_EXPR_BOOL_TRUE, &["Bool", "true"]);
        init_global_const(&G_EXPR_BOOL_FALSE, &["Bool", "false"]);

        // Nat constants
        init_global_const(&G_NAT_ZERO, &["Nat", "zero"]);
        init_global_const(&G_NAT_SUCC, &["Nat", "succ"]);
        init_global_const(&G_NAT_ADD, &["Nat", "add"]);
        init_global_const(&G_NAT_SUB, &["Nat", "sub"]);
        init_global_const(&G_NAT_MUL, &["Nat", "mul"]);
        init_global_const(&G_NAT_POW, &["Nat", "pow"]);
        init_global_const(&G_NAT_GCD, &["Nat", "gcd"]);
        init_global_const(&G_NAT_DIV, &["Nat", "div"]);
        init_global_const(&G_NAT_MOD, &["Nat", "mod"]);
        init_global_const(&G_NAT_BEQ, &["Nat", "beq"]);
        init_global_const(&G_NAT_BLE, &["Nat", "ble"]);
        init_global_const(&G_NAT_LAND, &["Nat", "land"]);
        init_global_const(&G_NAT_LOR, &["Nat", "lor"]);
        init_global_const(&G_NAT_XOR, &["Nat", "xor"]);
        init_global_const(&G_NAT_SHIFTLEFT, &["Nat", "shiftLeft"]);
        init_global_const(&G_NAT_SHIFTRIGHT, &["Nat", "shiftRight"]);
        init_global_const(&G_STRING_MK, &["String", "ofList"]);
        init_global_const(&G_LEAN_REDUCE_BOOL, &["Lean", "reduceBool"]);
        init_global_const(&G_LEAN_REDUCE_NAT, &["Lean", "reduceNat"]);

        // Quotient eliminator/constructor names (bare Name) for quot_reduce_rec.
        init_global_name(&G_QUOT_LIFT_NAME, &["Quot", "lift"]);
        init_global_name(&G_QUOT_IND_NAME, &["Quot", "ind"]);
        init_global_name(&G_QUOT_MK_NAME, &["Quot", "mk"]);
        init_global_name(&G_NESTED_NAME, &["_nested"]);
        init_global_name(&G_NESTED_FRESH, &["_nested_fresh"]);
        lean_register_name_generator_prefix(load_global(&G_NESTED_FRESH));
        init_global_name(&G_IND_FRESH, &["_ind_fresh"]);
        lean_register_name_generator_prefix(load_global(&G_IND_FRESH));
        init_list_char_global(&G_LIST_CONS_CHAR, &["List", "cons"]);
        init_list_char_global(&G_LIST_NIL_CHAR, &["List", "nil"]);
        init_global_const(&G_CHAR_OF_NAT, &["Char", "ofNat"]);
    }
}
