// Global constants (AtomicPtr, initialized once)
// ---------------------------------------------------------------------------

use std::{
    ffi::CString,
    ptr,
    sync::atomic::{AtomicPtr, Ordering},
};

use leanh_l1::{
    datatypes::LeanObject,
    emitted::{lean_mark_persistent::lean_mark_persistent, lean_mk_string::lean_mk_string},
};

use crate::{
    kernel_type_checker::{
        lean_level_mk_zero::lean_level_mk_zero, lean_mk_list_cons::lean_mk_list_cons,
        lean_mk_list_nil::lean_mk_list_nil, lean_name_anonymous::lean_name_anonymous,
    },
    r#priv::initialize_constructions_module::lean_register_name_generator_prefix,
    todo_import_from_lean::{
        lean_expr_mk_app::lean_expr_mk_app, lean_expr_mk_const::lean_expr_mk_const,
        lean_name_mk_string::lean_name_mk_string,
    },
};

macro_rules! global_const {
    ($name:ident) => {
        static $name: AtomicPtr<LeanObject> = AtomicPtr::new(ptr::null_mut());
    };
}

global_const!(G_KERNEL_FRESH);
global_const!(G_BOOL_TRUE);
global_const!(G_EXPR_BOOL_TRUE); // `Expr.const Bool.true []`
global_const!(G_EXPR_BOOL_FALSE); // `Expr.const Bool.false []`
global_const!(G_EAGER_REDUCE);
global_const!(G_DONT_CARE);
global_const!(G_NAT_ZERO);
global_const!(G_NAT_SUCC);
global_const!(G_NAT_ADD);
global_const!(G_NAT_SUB);
global_const!(G_NAT_MUL);
global_const!(G_NAT_POW);
global_const!(G_NAT_GCD);
global_const!(G_NAT_DIV);
global_const!(G_NAT_MOD);
global_const!(G_NAT_BEQ);
global_const!(G_NAT_BLE);
global_const!(G_NAT_LAND);
global_const!(G_NAT_LOR);
global_const!(G_NAT_XOR);
global_const!(G_NAT_SHIFTLEFT);
global_const!(G_NAT_SHIFTRIGHT);
global_const!(G_STRING_MK);
global_const!(G_LEAN_REDUCE_BOOL);
global_const!(G_LEAN_REDUCE_NAT);
// Bare `Name`s (not `Expr.const`) for quotient-eliminator head matching in `quot_reduce_rec`.
global_const!(G_QUOT_LIFT_NAME);
global_const!(G_QUOT_IND_NAME);
global_const!(G_QUOT_MK_NAME);
global_const!(G_NESTED_NAME);
global_const!(G_NESTED_FRESH);
global_const!(G_IND_FRESH);
global_const!(G_LIST_CONS_CHAR);
global_const!(G_LIST_NIL_CHAR);
global_const!(G_CHAR_OF_NAT);

/// Build a Lean name from dot-separated parts.
unsafe fn build_lean_name(parts: &[&str]) -> *mut LeanObject {
    let mut cur = lean_name_anonymous();
    for &part in parts {
        let part = CString::new(part).expect("name part contains NUL");
        let s = lean_mk_string(part.as_ptr());
        // lean_name_mk_string consumes both `cur` and `s` (obj_arg). Do NOT dec
        // them afterwards — ownership is transferred into the new name.
        cur = lean_name_mk_string(cur, s);
    }
    cur
}

/// Build a persistent const expression and store in a global.
unsafe fn init_global_const(g: &AtomicPtr<LeanObject>, parts: &[&str]) {
    let name = build_lean_name(parts);
    lean_mark_persistent(name);
    let levels = lean_mk_list_nil(ptr::null_mut()); // empty list
    let expr = lean_expr_mk_const(name, levels);
    lean_mark_persistent(expr);
    g.store(expr, Ordering::Release);
}

/// Build a persistent bare `Name` and store it in a global (for name matching, not as an Expr).
unsafe fn init_global_name(g: &AtomicPtr<LeanObject>, parts: &[&str]) {
    let name = build_lean_name(parts);
    lean_mark_persistent(name);
    g.store(name, Ordering::Release);
}

/// Build `List.cons Char` or `List.nil Char`, matching inductive.cpp globals.
unsafe fn init_list_char_global(g: &AtomicPtr<LeanObject>, parts: &[&str]) {
    let level_zero = lean_level_mk_zero();
    let levels = lean_mk_list_cons(
        ptr::null_mut(),
        level_zero,
        lean_mk_list_nil(ptr::null_mut()),
    );
    let name = build_lean_name(parts);
    let list_const = lean_expr_mk_const(name, levels);
    let char_name = build_lean_name(&["Char"]);
    let char_type = lean_expr_mk_const(char_name, lean_mk_list_nil(ptr::null_mut()));
    let expr = lean_expr_mk_app(list_const, char_type);
    lean_mark_persistent(expr);
    g.store(expr, Ordering::Release);
}

unsafe fn load_global(g: &AtomicPtr<LeanObject>) -> *mut LeanObject {
    g.load(Ordering::Acquire)
}

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
