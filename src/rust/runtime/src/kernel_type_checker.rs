/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Rust port of src/kernel/type_checker.cpp (1560 lines).
All C++ `throw X` → `return Err(KernelError::X)`.
*/

#[allow(
    dead_code,
    non_snake_case,
    non_upper_case_globals,
    clippy::missing_safety_doc
)]
mod kernel_type_checker_impl {
    use crate::runtime_expr_shared::{
        BI_DEFAULT, BI_IMPLICIT, BI_INST_IMPLICIT, BI_STRICT_IMPLICIT, EXCEPT_ERROR_TAG,
        EXCEPT_OK_TAG, EXPR_APP, EXPR_BVAR, EXPR_CONST, EXPR_FVAR, EXPR_LAMBDA, EXPR_LET, EXPR_LIT,
        EXPR_MDATA, EXPR_MVAR, EXPR_PI, EXPR_PROJ, EXPR_SORT, LEVEL_IMAX, LEVEL_MAX, LEVEL_MVAR,
        LEVEL_PARAM, LEVEL_SUCC, expr_bvar_range_data,
    };
    use crate::*;
    use core::ffi::{CStr, c_char, c_int, c_long, c_uchar, c_uint, c_void};
    use core::ffi::{c_char, c_void};
    use leanh::LEAN_MAX_SMALL_NAT;
    use std::collections::{HashMap, HashSet};
    use std::ptr;
    use std::sync::atomic::{AtomicPtr, Ordering};

    // ---------------------------------------------------------------------------
    // Lean runtime C API bindings (extern "C" stubs expected from lean/lean.h)
    // lean_inc, lean_dec, lean_is_scalar, lean_box, lean_unbox, lean_ptr_tag,
    // lean_mark_persistent are Rust functions from super::* — not declared here.
    // lean_alloc_ctor / lean_ctor_get / lean_ctor_set are local shims below.
    // lean_stack_has_space, lean_memory_within_limit, check_heartbeat_exceeded,
    // check_interrupted_flag are Rust functions from super::* — not declared here.
    // ---------------------------------------------------------------------------

    #[inline(always)]
    unsafe fn lean_level_eq(
        a: *const LeanObject,
        b: *const LeanObject,
    ) -> bool {
        lean_level_eq_raw(a as *mut _, b as *mut _)
    }

    #[inline(always)]
    unsafe fn lean_expr_eqv(a: *const LeanObject, b: *const LeanObject) -> bool {
        lean_expr_eqv_raw(a as *mut _, b as *mut _)
    }

    /// Borrowing wrapper around `lean_expr_hash`. The exported `lean_expr_hash`
    /// (`@[export] def hashEx : Expr → UInt64`) takes its `Expr` argument by value and
    /// therefore **consumes** (decrements) it. All call sites here only hold borrowed
    /// references, so we `lean_inc` before handing the reference over to be consumed.
    #[inline(always)]
    unsafe fn expr_hash(e: *const LeanObject) -> u64 {
        lean_inc(e);
        lean_expr_hash(e)
    }

    /// Borrowing wrappers around the `Expr → Bool` flag exports
    /// (`@[export] def hasFVarEx : Expr → Bool`, `hasExprMVarEx`, …). Like `lean_expr_hash`
    /// these take the `Expr` by value and **consume** it, so we `lean_inc` before calling.
    #[inline(always)]
    unsafe fn expr_has_fvar(e: *const LeanObject) -> bool {
        lean_inc(e);
        lean_expr_has_fvar(e)
    }
    #[inline(always)]
    unsafe fn expr_has_expr_mvar(e: *const LeanObject) -> bool {
        lean_inc(e);
        lean_expr_has_expr_mvar(e)
    }

    // ---------------------------------------------------------------------------
    // Exported C symbols for inline C++ accessor functions
    // These were inline in the C++ runtime (lean/lean.h) and thus not exported,
    // but libleanshared.so references them as external symbols — so Rust provides them.
    // ---------------------------------------------------------------------------

    // Levels
    // Level::Succ (tag 1): field[0] = pred level
    #[no_mangle]
    pub unsafe fn lean_level_get_succ(l: *const LeanObject) -> *mut LeanObject {
        lean_ctor_get(l, 0)
    }

    // Level::Param (tag 4): field[0] = name
    #[no_mangle]
    pub unsafe fn lean_level_get_param_name(l: *const LeanObject) -> *mut LeanObject {
        lean_ctor_get(l, 0)
    }

    // Expressions
    // Expr::App (tag 5): field[0]=fn, field[1]=arg
    #[no_mangle]
    pub unsafe fn lean_expr_is_app(e: *const LeanObject) -> bool {
        !lean_is_scalar(e) && lean_ptr_tag(e) == EXPR_APP
    }

    #[no_mangle]
    pub unsafe fn lean_expr_get_app_fn(e: *const LeanObject) -> *mut LeanObject {
        lean_ctor_get(e, 0)
    }

    #[no_mangle]
    pub unsafe fn lean_expr_get_app_arg(e: *const LeanObject) -> *mut LeanObject {
        lean_ctor_get(e, 1)
    }

    // Expr::Const (tag 4): field[0]=name, field[1]=List Level
    #[no_mangle]
    pub unsafe fn lean_expr_is_const(e: *const LeanObject) -> bool {
        !lean_is_scalar(e) && lean_ptr_tag(e) == EXPR_CONST
    }

    #[no_mangle]
    pub unsafe fn lean_expr_get_const_name(e: *const LeanObject) -> *mut LeanObject {
        lean_ctor_get(e, 0)
    }

    // Expr::Proj (tag 11): field[0]=sname, field[1]=idx, field[2]=expr
    #[no_mangle]
    pub unsafe fn lean_expr_get_proj_sname(e: *const LeanObject) -> *mut LeanObject {
        lean_ctor_get(e, 0)
    }

    #[no_mangle]
    pub unsafe fn lean_expr_get_proj_idx(e: *const LeanObject) -> *mut LeanObject {
        lean_ctor_get(e, 1)
    }

    #[no_mangle]
    pub unsafe fn lean_expr_get_proj_expr(e: *const LeanObject) -> *mut LeanObject {
        lean_ctor_get(e, 2)
    }

    // Nat scalars: small Nat values are stored as tagged scalars (lean_box(n))
    #[no_mangle]
    pub unsafe fn lean_nat_is_small(n: *const LeanObject) -> bool {
        lean_is_scalar(n)
    }

    #[no_mangle]
    pub unsafe fn lean_nat_get_small_value(n: *const LeanObject) -> u32 {
        lean_unbox(n) as u32
    }

    // ConstantInfo: constant_info_kind enum {Axiom=0,Definition=1,Theorem=2,Opaque=3,Quot=4,Inductive=5,...}
    // Each variant wraps its val at field[0]
    const CONST_INFO_INDUCTIVE_TAG: u32 = 5;

    #[no_mangle]
    pub unsafe fn lean_constant_info_is_inductive(info: *const LeanObject) -> bool {
        !lean_is_scalar(info) && lean_ptr_tag(info) == CONST_INFO_INDUCTIVE_TAG
    }

    #[no_mangle]
    pub unsafe fn lean_constant_info_to_inductive_val(info: *const LeanObject) -> *mut LeanObject {
        lean_ctor_get(info, 0)
    }

    // InductiveVal: field[0]=ConstantVal, field[1]=nparams(Nat), field[2]=nindices(Nat),
    //               field[3]=all(List Name), field[4]=cnstrs(List Name), field[5]=nnested(Nat)
    #[no_mangle]
    pub unsafe fn lean_inductive_val_get_nparams(v: *const LeanObject) -> u32 {
        lean_unbox(lean_ctor_get(v, 1)) as u32
    }

    #[no_mangle]
    pub unsafe fn lean_inductive_val_get_nindices(v: *const LeanObject) -> u32 {
        lean_unbox(lean_ctor_get(v, 2)) as u32
    }

    // InductiveVal.cnstrs is the List Name at field[4]
    #[no_mangle]
    pub unsafe fn lean_inductive_val_get_cnstrs(v: *const LeanObject) -> *mut LeanObject {
        lean_ctor_get(v, 4)
    }

    #[no_mangle]
    pub unsafe fn lean_inductive_val_get_all(v: *const LeanObject) -> *mut LeanObject {
        lean_ctor_get(v, 3)
    }

    #[no_mangle]
    pub unsafe fn lean_inductive_val_get_nnested(v: *const LeanObject) -> u32 {
        lean_unbox(lean_ctor_get(v, 5)) as u32
    }

    // List.nil = scalar, List.cons h t has field[0]=h, field[1]=t
    unsafe fn lean_list_length(mut l: *const LeanObject) -> u32 {
        let mut count = 0u32;
        while !lean_is_scalar(l) {
            count += 1;
            l = lean_ctor_get(l, 1);
        }
        count
    }

    #[no_mangle]
    pub unsafe fn lean_inductive_val_get_ncnstrs(v: *const LeanObject) -> u32 {
        lean_list_length(lean_ctor_get(v, 4))
    }

    // LocalDecl: cdecl (tag 0) / ldecl (tag 1)
    //   field[0]=index(Nat), field[1]=name(Name), field[2]=userName(Name), field[3]=type(Expr)
    //   ldecl also has field[4]=value(Expr)
    #[no_mangle]
    pub unsafe fn lean_local_decl_get_type(d: *const LeanObject) -> *mut LeanObject {
        lean_ctor_get(d, 3)
    }

    // lean_local_ctx_find returns Option LocalDecl (None = scalar, Some(d) = tag-1 ctor with field[0]=d)
    // This shim extracts the FVarId from an FVar expr, calls lean_local_ctx_find, and unwraps the Option.
    #[no_mangle]
    pub unsafe fn lean_local_ctx_find_local_decl(
        lctx: *const LeanObject,
        fvar_expr: *const LeanObject,
    ) -> *mut LeanObject {
        let fvar_id = lean_ctor_get(fvar_expr, 0); // Expr::FVar field[0] = FVarId (= Name, FVarId is a single-field struct erased in ABI)
        // lean_local_ctx_find consumes both args (C++ passes them via to_obj_arg()); our lctx/fvar_id
        // are borrowed, so inc each first — otherwise every fvar lookup over-decrements the lctx.
        lean_inc(lctx as *mut _);
        lean_inc(fvar_id);
        let opt = lean_local_ctx_find(lctx as *mut _, fvar_id); // Option LocalDecl
        if lean_is_scalar(opt) {
            opt // None: return scalar
        } else {
            let decl = lean_ctor_get(opt, 0); // Some.field[0] = LocalDecl
            lean_inc(decl);
            lean_dec(opt);
            decl
        }
    }

    // ---------------------------------------------------------------------------
    // Missing shims: inline C++ functions not exported as symbols
    // ---------------------------------------------------------------------------

    // List.nil = scalar, List.cons: field[0]=head, field[1]=tail
    #[no_mangle]
    pub unsafe fn lean_list_head(l: *const LeanObject) -> *mut LeanObject {
        lean_ctor_get(l, 0)
    }

    #[no_mangle]
    pub unsafe fn lean_list_tail(l: *const LeanObject) -> *mut LeanObject {
        lean_ctor_get(l, 1)
    }

    // Expr::Const (tag 4): field[0]=name, field[1]=List Level
    #[no_mangle]
    pub unsafe fn lean_expr_get_const_levels(e: *const LeanObject) -> *mut LeanObject {
        lean_ctor_get(e, 1)
    }

    // Expr::Pi (tag 7)
    #[no_mangle]
    pub unsafe fn lean_expr_is_pi(e: *const LeanObject) -> bool {
        !lean_is_scalar(e) && lean_ptr_tag(e) == EXPR_PI
    }

    // Lambda/Pi: field[0]=name, field[1]=domain, field[2]=body
    #[no_mangle]
    pub unsafe fn lean_expr_get_binding_domain(e: *const LeanObject) -> *mut LeanObject {
        lean_ctor_get(e, 1)
    }

    #[no_mangle]
    pub unsafe fn lean_expr_get_binding_body(e: *const LeanObject) -> *mut LeanObject {
        lean_ctor_get(e, 2)
    }

    // Expr.Data u64 is stored after the header+object-fields.
    // Bits [63:44] = bvarRange. has_loose_bvars iff bvarRange > 0.
    #[no_mangle]
    pub unsafe fn lean_expr_has_loose_bvars(e: *const LeanObject) -> bool {
        if lean_is_scalar(e) {
            return false;
        }
        let num_objs = (*e).other as usize;
        let data = (e.add(1) as *const u8)
            .add(num_objs * 8)
            .cast::<u64>()
            .read();
        expr_bvar_range_data(data) > 0
    }

    // Count arguments in an App chain: App(App(f,a1),a2) has 2 args.
    #[no_mangle]
    pub unsafe fn lean_expr_get_app_num_args(e: *const LeanObject) -> u32 {
        let mut count = 0u32;
        let mut cur = e;
        while !lean_is_scalar(cur) && lean_ptr_tag(cur) == EXPR_APP {
            count += 1;
            cur = lean_ctor_get(cur, 0);
        }
        count
    }

    // Expr::Lit (tag 9): field[0]=Literal. Literal::Nat has tag 0.
    const LITERAL_NAT_TAG: u32 = 0;

    #[no_mangle]
    pub unsafe fn lean_expr_is_nat_lit(e: *const LeanObject) -> bool {
        !lean_is_scalar(e)
            && lean_ptr_tag(e) == EXPR_LIT
            && !lean_is_scalar(lean_ctor_get(e, 0))
            && lean_ptr_tag(lean_ctor_get(e, 0)) == LITERAL_NAT_TAG
    }

    // Get Nat from Expr::Lit(Literal::Nat(n))
    #[no_mangle]
    pub unsafe fn lean_expr_get_lit_nat(e: *const LeanObject) -> *mut LeanObject {
        lean_ctor_get(lean_ctor_get(e, 0), 0)
    }

    // Get String from Expr::Lit(Literal::String(s)).
    #[no_mangle]
    pub unsafe fn lean_expr_get_lit_str(e: *const LeanObject) -> *mut LeanObject {
        lean_ctor_get(lean_ctor_get(e, 0), 0)
    }

    // Create Expr::Lit(Literal::Nat(n)). Consumes n.
    #[no_mangle]
    pub unsafe fn lean_expr_mk_lit_nat(n: *mut LeanObject) -> *mut LeanObject {
        let lit = lean_alloc_ctor(LITERAL_NAT_TAG, 1, 0);
        lean_ctor_set(lit, 0, n);
        lean_expr_mk_lit(lit)
    }

    #[no_mangle]
    pub unsafe fn lean_nat_lit_to_constructor(e: *mut LeanObject) -> *mut LeanObject {
        debug_assert!(lean_expr_is_nat_lit(e));
        let n = lean_expr_get_lit_nat(e);
        if lean_nat_is_zero(n) {
            return load_global(&G_NAT_ZERO);
        }
        let pred = lean_nat_dec(n);
        let pred_lit = lean_expr_mk_lit_nat(pred);
        let succ = load_global(&G_NAT_SUCC);
        lean_expr_mk_app(succ, pred_lit)
    }

    #[no_mangle]
    pub unsafe fn lean_nat_mk_obj(n: u64) -> *mut LeanObject {
        if n <= LEAN_MAX_SMALL_NAT as u64 {
            lean_box(n as usize)
        } else {
            lean_big_uint64_to_nat(n)
        }
    }

    // For land/lor, tagged-scalar bitwise ops preserve the tag bit (bit 0 = 1 & 1 = 1 / 1 | 1 = 1).
    #[no_mangle]
    pub unsafe fn lean_nat_land(a: *mut LeanObject, b: *mut LeanObject) -> *mut LeanObject {
        if lean_is_scalar(a as *const _) && lean_is_scalar(b as *const _) {
            (a as usize & b as usize) as *mut LeanObject
        } else {
            lean_nat_big_land(a, b)
        }
    }

    #[no_mangle]
    pub unsafe fn lean_nat_lor(a: *mut LeanObject, b: *mut LeanObject) -> *mut LeanObject {
        if lean_is_scalar(a as *const _) && lean_is_scalar(b as *const _) {
            (a as usize | b as usize) as *mut LeanObject
        } else {
            lean_nat_big_lor(a, b)
        }
    }

    // lean_nat_xor (= lean_nat_lxor in lean.h): tag bit cancels on XOR so must unbox/rebox.
    #[no_mangle]
    pub unsafe fn lean_nat_xor(a: *mut LeanObject, b: *mut LeanObject) -> *mut LeanObject {
        if lean_is_scalar(a as *const _) && lean_is_scalar(b as *const _) {
            lean_box(lean_unbox(a as *const _) ^ lean_unbox(b as *const _))
        } else {
            lean_nat_big_xor(a, b)
        }
    }

    #[no_mangle]
    pub unsafe fn lean_nat_shiftr(a: *mut LeanObject, b: *mut LeanObject) -> *mut LeanObject {
        if lean_is_scalar(a as *const _) && lean_is_scalar(b as *const _) {
            let s1 = lean_unbox(a as *const _);
            let s2 = lean_unbox(b as *const _);
            lean_box(if s2 < usize::BITS as usize {
                s1 >> s2
            } else {
                0
            })
        } else {
            lean_nat_big_shiftr(a, b)
        }
    }

    // ===========================================================================
    // Real Lean/C++ exports used by the shims below.
    // These are genuine exported symbols (Lean @[export] or C++ LEAN_EXPORT), as
    // opposed to the inline C++ accessors which we re-implement as shims.
    // ===========================================================================
    unsafe extern "C" {
        // Expr binder info (Lean @[export], consumes its owned arg, returns u8).
        fn lean_expr_binder_info(e: *mut LeanObject) -> u8;
        // Environment quot-initialized flag (Lean @[export], consumes arg).
        fn lean_environment_quot_init(env: *mut LeanObject) -> bool;
        // RecursorVal flags (Lean @[export], consume arg).
        fn lean_recursor_k(v: *mut LeanObject) -> bool;
        fn lean_recursor_is_unsafe(v: *mut LeanObject) -> bool;
        // DefinitionVal safety (Lean @[export], consumes arg). 0 = unsafe, 1 = safe, 2 = partial.
        fn lean_definition_val_get_safety(v: *mut LeanObject) -> u8;
        // *_val unsafe flags (Lean @[export], consume arg).
        fn lean_axiom_val_is_unsafe(v: *mut LeanObject) -> bool;
        fn lean_opaque_val_is_unsafe(v: *mut LeanObject) -> bool;
        fn lean_inductive_val_is_unsafe_raw(v: *mut LeanObject) -> bool;
        fn lean_constructor_val_is_unsafe_raw(v: *mut LeanObject) -> bool;
        // ReducibilityHints height (Lean @[export], consumes arg).
        fn lean_reducibility_hints_get_height(h: *mut LeanObject) -> u32;
        // Native kernel reduction (C++ LEAN_EXPORT). Borrows env/opts/fn; returns Except.
        fn lean_eval_const_at_kernel_env(
            env: *mut LeanObject,
            opts: *mut LeanObject,
            fname: *mut LeanObject,
            n: usize,
            args: *const *mut LeanObject,
        ) -> *mut LeanObject;
        // Empty options (C++ LEAN_EXPORT). Consumes the unit arg, returns owned empty options.
        fn lean_options_get_empty(u: *mut LeanObject) -> *mut LeanObject;
        // Expr level-param instantiation (Lean @[export]). Borrows e/ps/ls, returns owned.
        fn lean_expr_instantiate_lparams(
            e: *mut LeanObject,
            ps: *mut LeanObject,
            ls: *mut LeanObject,
        ) -> *mut LeanObject;
        // Environment quot-init marker (Lean @[export], consumes env).
        fn lean_environment_mark_quot_init(env: *mut LeanObject) -> *mut LeanObject;
        // Real Lean LocalContext builders (return new LocalContext; consume owned args).
        fn lean_real_lctx_mk_local_decl(
            lctx: *mut LeanObject,
            fvar_id: *mut LeanObject,
            user_name: *mut LeanObject,
            ty: *mut LeanObject,
            bi: u8,
        ) -> *mut LeanObject;
        fn lean_real_lctx_mk_let_decl(
            lctx: *mut LeanObject,
            fvar_id: *mut LeanObject,
            user_name: *mut LeanObject,
            ty: *mut LeanObject,
            value: *mut LeanObject,
            nondep: bool,
        ) -> *mut LeanObject;
        fn lean_local_decl_binder_info(d: *mut LeanObject) -> u8;
    }

    // ===========================================================================
    // Shims for the remaining inline-C++ accessor functions referenced by this
    // module. Field-read accessors return BORROWED references (like C++
    // cnstr_get_ref); callers add a reference where they retain the value.
    // ===========================================================================

    // --- Literal / constant_info / hints tag constants ---
    const LITERAL_STRING_TAG: u32 = 1;
    const CI_AXIOM: u32 = 0;
    const CI_DEFINITION: u32 = 1;
    const CI_THEOREM: u32 = 2;
    const CI_OPAQUE: u32 = 3;
    const CI_QUOT: u32 = 4;
    const CI_INDUCTIVE: u32 = 5;
    const CI_CONSTRUCTOR: u32 = 6;
    const CI_RECURSOR: u32 = 7;
    const DEFINITION_SAFETY_UNSAFE: u8 = 0;
    const REDUCIBILITY_HINTS_REGULAR_TAG: u32 = 2;
    const QUOT_KIND_TYPE: u8 = 0;
    const QUOT_KIND_CTOR: u8 = 1;
    const QUOT_KIND_LIFT: u8 = 2;
    const QUOT_KIND_IND: u8 = 3;

    // --- List ---
    // List.nil is the boxed scalar 0; List.cons (tag 1) has field[0]=head, field[1]=tail.
    #[no_mangle]
    pub unsafe fn lean_list_is_nil(l: *const LeanObject) -> bool {
        lean_is_scalar(l)
    }

    // --- Levels (Max tag 2 / IMax tag 3): field[0]=lhs, field[1]=rhs ---
    #[no_mangle]
    pub unsafe fn lean_level_get_max_lhs(l: *const LeanObject) -> *mut LeanObject {
        lean_ctor_get(l, 0)
    }
    #[no_mangle]
    pub unsafe fn lean_level_get_max_rhs(l: *const LeanObject) -> *mut LeanObject {
        lean_ctor_get(l, 1)
    }
    #[no_mangle]
    pub unsafe fn lean_level_get_imax_lhs(l: *const LeanObject) -> *mut LeanObject {
        lean_ctor_get(l, 0)
    }
    #[no_mangle]
    pub unsafe fn lean_level_get_imax_rhs(l: *const LeanObject) -> *mut LeanObject {
        lean_ctor_get(l, 1)
    }

    // --- Expr kind / pointer identity ---
    // expr_kind(e) = cnstr_tag(e); Expr is never a scalar.
    #[no_mangle]
    pub unsafe fn lean_expr_kind(e: *const LeanObject) -> u32 {
        lean_ptr_tag(e)
    }

    // is_eqp = pointer equality.
    #[no_mangle]
    pub unsafe fn lean_expr_is_eqp(a: *const LeanObject, b: *const LeanObject) -> bool {
        a == b
    }

    // --- Expr predicates ---
    #[no_mangle]
    pub unsafe fn lean_expr_is_fvar(e: *const LeanObject) -> bool {
        !lean_is_scalar(e) && lean_ptr_tag(e) == EXPR_FVAR
    }
    #[no_mangle]
    pub unsafe fn lean_expr_is_sort(e: *const LeanObject) -> bool {
        !lean_is_scalar(e) && lean_ptr_tag(e) == EXPR_SORT
    }
    #[no_mangle]
    pub unsafe fn lean_expr_is_lambda(e: *const LeanObject) -> bool {
        !lean_is_scalar(e) && lean_ptr_tag(e) == EXPR_LAMBDA
    }
    #[no_mangle]
    pub unsafe fn lean_expr_is_let(e: *const LeanObject) -> bool {
        !lean_is_scalar(e) && lean_ptr_tag(e) == EXPR_LET
    }
    #[no_mangle]
    pub unsafe fn lean_expr_is_proj(e: *const LeanObject) -> bool {
        !lean_is_scalar(e) && lean_ptr_tag(e) == EXPR_PROJ
    }

    // Expr::Lit (tag 9): field[0]=Literal. Literal::String has tag 1.
    #[no_mangle]
    pub unsafe fn lean_expr_is_string_lit(e: *const LeanObject) -> bool {
        !lean_is_scalar(e)
            && lean_ptr_tag(e) == EXPR_LIT
            && !lean_is_scalar(lean_ctor_get(e, 0))
            && lean_ptr_tag(lean_ctor_get(e, 0)) == LITERAL_STRING_TAG
    }

    #[no_mangle]
    pub unsafe fn lean_string_lit_to_constructor(e: *mut LeanObject) -> *mut LeanObject {
        debug_assert!(lean_expr_is_string_lit(e));
        let s = lean_expr_get_lit_str(e);
        let bytes = core::slice::from_raw_parts(
            lean_string_cstr(s) as *const u8,
            lean_string_size(s).saturating_sub(1),
        );
        let text = core::str::from_utf8_unchecked(bytes);
        let mut r = load_global(&G_LIST_NIL_CHAR);
        for ch in text.chars().rev() {
            let char_of_nat = load_global(&G_CHAR_OF_NAT);
            let char_nat = lean_expr_mk_lit_nat(lean_box(ch as usize));
            let char_expr = lean_expr_mk_app(char_of_nat, char_nat);
            let cons = load_global(&G_LIST_CONS_CHAR);
            let cons_char = lean_expr_mk_app(cons, char_expr);
            r = lean_expr_mk_app(cons_char, r);
        }
        let string_mk = load_global(&G_STRING_MK);
        lean_expr_mk_app(string_mk, r)
    }

    // --- Expr field accessors (borrowed) ---
    // Expr::FVar (tag 1): field[0]=FVarId
    #[no_mangle]
    pub unsafe fn lean_expr_get_fvar_id(e: *const LeanObject) -> *mut LeanObject {
        lean_ctor_get(e, 0)
    }
    // Expr::Sort (tag 3): field[0]=Level
    #[no_mangle]
    pub unsafe fn lean_expr_get_sort_level(e: *const LeanObject) -> *mut LeanObject {
        lean_ctor_get(e, 0)
    }
    // Expr::MData (tag 10): field[0]=kvmap, field[1]=expr
    #[no_mangle]
    pub unsafe fn lean_expr_get_mdata_expr(e: *const LeanObject) -> *mut LeanObject {
        lean_ctor_get(e, 1)
    }
    // Lambda/Pi: field[0]=name
    #[no_mangle]
    pub unsafe fn lean_expr_get_binding_name(e: *const LeanObject) -> *mut LeanObject {
        lean_ctor_get(e, 0)
    }
    // Expr::Let (tag 8): field[0]=name, field[1]=type, field[2]=value, field[3]=body
    #[no_mangle]
    pub unsafe fn lean_expr_get_let_name(e: *const LeanObject) -> *mut LeanObject {
        lean_ctor_get(e, 0)
    }
    #[no_mangle]
    pub unsafe fn lean_expr_get_let_type(e: *const LeanObject) -> *mut LeanObject {
        lean_ctor_get(e, 1)
    }
    #[no_mangle]
    pub unsafe fn lean_expr_get_let_value(e: *const LeanObject) -> *mut LeanObject {
        lean_ctor_get(e, 2)
    }
    #[no_mangle]
    pub unsafe fn lean_expr_get_let_body(e: *const LeanObject) -> *mut LeanObject {
        lean_ctor_get(e, 3)
    }

    // binding_info: delegates to the real lean_expr_binder_info (which consumes its arg).
    #[no_mangle]
    pub unsafe fn lean_expr_get_binding_info(e: *const LeanObject) -> u8 {
        lean_inc(e as *mut _);
        lean_expr_binder_info(e as *mut _)
    }

    const BINDER_INFO_IMPLICIT: u8 = 1;

    #[inline(always)]
    fn binder_info_is_explicit(bi: u8) -> bool {
        bi != BINDER_INFO_IMPLICIT && bi != 2 && bi != 3
    }

    unsafe fn expr_has_loose_bvar(e: *const LeanObject, idx: u32) -> bool {
        lean_expr_has_loose_bvar(e, lean_box(idx as usize))
    }

    /// Port of C++ `has_loose_bvars_in_domain` from `kernel/expr.cpp`.
    unsafe fn has_loose_bvars_in_domain(b: *const LeanObject, vidx: u32, strict: bool) -> bool {
        if lean_expr_is_pi(b) {
            let domain = lean_expr_get_binding_domain(b);
            if expr_has_loose_bvar(domain, vidx) {
                let bi = lean_expr_get_binding_info(b);
                if binder_info_is_explicit(bi) {
                    return true;
                } else if has_loose_bvars_in_domain(lean_expr_get_binding_body(b), 0, strict) {
                    return true;
                }
            }
            has_loose_bvars_in_domain(lean_expr_get_binding_body(b), vidx + 1, strict)
        } else if !strict {
            expr_has_loose_bvar(b, vidx)
        } else {
            false
        }
    }

    /// Port of C++ `infer_implicit(expr const &, bool)`.
    /// Consumes `e` and returns an owned expression.
    unsafe fn lean_expr_infer_implicit(e: *mut LeanObject, strict: bool) -> *mut LeanObject {
        unsafe fn go(e: *mut LeanObject, num_params: u32, strict: bool) -> *mut LeanObject {
            if num_params == 0 || !lean_expr_is_pi(e) {
                return e;
            }
            let body = lean_expr_get_binding_body(e);
            lean_inc(body);
            let new_body = go(body, num_params - 1, strict);
            let old_bi = lean_expr_get_binding_info(e);
            let new_bi = if binder_info_is_explicit(old_bi)
                && has_loose_bvars_in_domain(new_body, 0, strict)
            {
                BINDER_INFO_IMPLICIT
            } else {
                old_bi
            };
            let name = lean_expr_get_binding_name(e);
            let domain = lean_expr_get_binding_domain(e);
            lean_inc(name);
            lean_inc(domain);
            let r = lean_expr_mk_forall(name, domain, new_body, new_bi);
            lean_dec(e);
            r
        }

        go(e, u32::MAX, strict)
    }

    // Prop = Sort 0.
    #[no_mangle]
    pub unsafe fn lean_expr_mk_prop() -> *mut LeanObject {
        let zero = lean_level_mk_zero();
        lean_expr_mk_sort(zero)
    }
    #[no_mangle]
    pub unsafe fn lean_nat_beq(a: *const LeanObject, b: *const LeanObject) -> bool {
        lean_nat_eq(a, b)
    }
    #[no_mangle]
    pub unsafe fn lean_nat_ble(a: *const LeanObject, b: *const LeanObject) -> bool {
        if lean_is_scalar(a) && lean_is_scalar(b) {
            lean_unbox(a) <= lean_unbox(b)
        } else {
            lean_nat_big_le(a as *mut LeanObject, b as *mut LeanObject)
        }
    }
    #[no_mangle]
    pub unsafe fn lean_nat_is_zero(n: *const LeanObject) -> bool {
        // Big Nat is never zero; small Nat zero is boxed scalar 0.
        lean_is_scalar(n) && lean_unbox(n) == 0
    }
    // Nat predecessor (saturating): n - 1.
    #[no_mangle]
    pub unsafe fn lean_nat_dec(n: *mut LeanObject) -> *mut LeanObject {
        lean_nat_sub(n, lean_box(1))
    }

    // --- Environment ---
    #[no_mangle]
    pub unsafe fn lean_environment_is_quot_initialized(env: *const LeanObject) -> bool {
        lean_inc(env as *mut _);
        lean_environment_quot_init(env as *mut _)
    }

    // --- ConstantInfo (info tag = kind; field[0] = inner val; val.field[0] = constant_val) ---
    // constant_val: field[0]=name, field[1]=lparams, field[2]=type
    #[inline(always)]
    unsafe fn ci_to_val(info: *const LeanObject) -> *mut LeanObject {
        lean_ctor_get(info, 0)
    }
    #[inline(always)]
    unsafe fn ci_constant_val(info: *const LeanObject) -> *mut LeanObject {
        lean_ctor_get(ci_to_val(info), 0)
    }

    #[no_mangle]
    pub unsafe fn lean_constant_info_get_name(info: *const LeanObject) -> *mut LeanObject {
        lean_ctor_get(ci_constant_val(info), 0)
    }
    #[no_mangle]
    pub unsafe fn lean_constant_info_get_lparams(info: *const LeanObject) -> *mut LeanObject {
        lean_ctor_get(ci_constant_val(info), 1)
    }
    #[no_mangle]
    pub unsafe fn lean_constant_info_get_type(info: *const LeanObject) -> *mut LeanObject {
        lean_ctor_get(ci_constant_val(info), 2)
    }
    #[no_mangle]
    pub unsafe fn lean_constant_info_get_num_lparams(info: *const LeanObject) -> u32 {
        lean_list_length(lean_ctor_get(ci_constant_val(info), 1))
    }
    #[no_mangle]
    pub unsafe fn lean_constant_info_is_definition(info: *const LeanObject) -> bool {
        !lean_is_scalar(info) && lean_ptr_tag(info) == CI_DEFINITION
    }
    #[no_mangle]
    pub unsafe fn lean_constant_info_is_constructor(info: *const LeanObject) -> bool {
        !lean_is_scalar(info) && lean_ptr_tag(info) == CI_CONSTRUCTOR
    }
    #[no_mangle]
    pub unsafe fn lean_constant_info_is_recursor(info: *const LeanObject) -> bool {
        !lean_is_scalar(info) && lean_ptr_tag(info) == CI_RECURSOR
    }
    #[no_mangle]
    pub unsafe fn lean_constant_info_to_definition_val(info: *const LeanObject) -> *mut LeanObject {
        ci_to_val(info)
    }
    #[no_mangle]
    pub unsafe fn lean_constant_info_to_constructor_val(
        info: *const LeanObject,
    ) -> *mut LeanObject {
        ci_to_val(info)
    }
    #[no_mangle]
    pub unsafe fn lean_constant_info_to_recursor_val(info: *const LeanObject) -> *mut LeanObject {
        ci_to_val(info)
    }
    // has_value: theorem or definition.
    #[no_mangle]
    pub unsafe fn lean_constant_info_has_value(info: *const LeanObject) -> bool {
        let k = lean_ptr_tag(info);
        k == CI_THEOREM || k == CI_DEFINITION
    }
    // get_safety: the argument is a definition_val (call site passes to_definition_val result).
    #[no_mangle]
    pub unsafe fn lean_constant_info_get_safety(defval: *const LeanObject) -> u8 {
        lean_inc(defval as *mut _);
        lean_definition_val_get_safety(defval as *mut _)
    }

    #[inline(always)]
    unsafe fn lean_inductive_val_is_rec(v: *const LeanObject) -> bool {
        lean_inc(v as *mut _);
        lean_inductive_val_is_rec_raw(v as *mut _)
    }

    #[inline(always)]
    unsafe fn lean_inductive_val_is_unsafe(v: *const LeanObject) -> bool {
        lean_inc(v as *mut _);
        lean_inductive_val_is_unsafe_raw(v as *mut _)
    }

    #[inline(always)]
    unsafe fn lean_inductive_val_is_reflexive(v: *const LeanObject) -> bool {
        lean_inc(v as *mut _);
        lean_inductive_val_is_reflexive_raw(v as *mut _)
    }

    #[inline(always)]
    unsafe fn lean_constructor_val_is_unsafe(v: *const LeanObject) -> bool {
        lean_inc(v as *mut _);
        lean_constructor_val_is_unsafe_raw(v as *mut _)
    }

    // is_unsafe: mirrors constant_info::is_unsafe() switch on kind.
    #[no_mangle]
    pub unsafe fn lean_constant_info_is_unsafe(info: *const LeanObject) -> bool {
        let val = ci_to_val(info);
        match lean_ptr_tag(info) {
            CI_AXIOM => {
                lean_inc(val);
                lean_axiom_val_is_unsafe(val)
            }
            CI_DEFINITION => {
                lean_inc(val);
                lean_definition_val_get_safety(val) == DEFINITION_SAFETY_UNSAFE
            }
            CI_THEOREM => false,
            CI_OPAQUE => {
                lean_inc(val);
                lean_opaque_val_is_unsafe(val)
            }
            CI_QUOT => false,
            CI_INDUCTIVE => lean_inductive_val_is_unsafe(val),
            CI_CONSTRUCTOR => lean_constructor_val_is_unsafe(val),
            CI_RECURSOR => {
                lean_inc(val);
                lean_recursor_is_unsafe(val)
            }
            _ => false,
        }
    }
    // get_hints: definitions carry reducibility hints at val.field[2]; otherwise the opaque hint (boxed 0).
    #[no_mangle]
    pub unsafe fn lean_constant_info_get_hints(info: *const LeanObject) -> *mut LeanObject {
        if lean_ptr_tag(info) == CI_DEFINITION {
            lean_ctor_get(ci_to_val(info), 2)
        } else {
            lean_box(0)
        }
    }

    // --- ConstructorVal: field[0]=cv, field[1]=induct, field[2]=cidx, field[3]=nparams, field[4]=nfields ---
    #[no_mangle]
    pub unsafe fn lean_constructor_val_get_induct(v: *const LeanObject) -> *mut LeanObject {
        lean_ctor_get(v, 1)
    }
    #[no_mangle]
    pub unsafe fn lean_constructor_val_get_cidx(v: *const LeanObject) -> u32 {
        lean_unbox(lean_ctor_get(v, 2)) as u32
    }
    #[no_mangle]
    pub unsafe fn lean_constructor_val_get_nparams(v: *const LeanObject) -> u32 {
        lean_unbox(lean_ctor_get(v, 3)) as u32
    }
    #[no_mangle]
    pub unsafe fn lean_constructor_val_get_nfields(v: *const LeanObject) -> u32 {
        lean_unbox(lean_ctor_get(v, 4)) as u32
    }

    // --- RecursorVal: field[0]=cv,1=all,2=nparams,3=nindices,4=nmotives,5=nminors,6=rules ---
    #[no_mangle]
    pub unsafe fn lean_recursor_val_get_nparams(v: *const LeanObject) -> u32 {
        lean_unbox(lean_ctor_get(v, 2)) as u32
    }
    #[no_mangle]
    pub unsafe fn lean_recursor_val_get_nindices(v: *const LeanObject) -> u32 {
        lean_unbox(lean_ctor_get(v, 3)) as u32
    }
    #[no_mangle]
    pub unsafe fn lean_recursor_val_get_nmotives(v: *const LeanObject) -> u32 {
        lean_unbox(lean_ctor_get(v, 4)) as u32
    }
    #[no_mangle]
    pub unsafe fn lean_recursor_val_get_nminors(v: *const LeanObject) -> u32 {
        lean_unbox(lean_ctor_get(v, 5)) as u32
    }
    #[no_mangle]
    pub unsafe fn lean_recursor_val_get_rules(v: *const LeanObject) -> *mut LeanObject {
        lean_ctor_get(v, 6)
    }
    #[no_mangle]
    pub unsafe fn lean_recursor_val_get_major_idx(v: *const LeanObject) -> u32 {
        let nparams = lean_unbox(lean_ctor_get(v, 2)) as u32;
        let nindices = lean_unbox(lean_ctor_get(v, 3)) as u32;
        let nmotives = lean_unbox(lean_ctor_get(v, 4)) as u32;
        let nminors = lean_unbox(lean_ctor_get(v, 5)) as u32;
        nparams + nmotives + nminors + nindices
    }
    #[no_mangle]
    pub unsafe fn lean_recursor_val_is_k(v: *const LeanObject) -> bool {
        lean_inc(v as *mut _);
        lean_recursor_k(v as *mut _)
    }
    #[no_mangle]
    pub unsafe fn lean_recursor_val_is_unsafe(v: *const LeanObject) -> bool {
        lean_inc(v as *mut _);
        lean_recursor_is_unsafe(v as *mut _)
    }
    // get_major_induct: walk the constant_val.type telescope and return the head const's name (borrowed).
    #[no_mangle]
    pub unsafe fn lean_recursor_val_get_major_induct(v: *const LeanObject) -> *mut LeanObject {
        let n = lean_recursor_val_get_major_idx(v);
        // constant_val.type = field[2] of constant_val (= field[0] of recursor_val)
        let mut t = lean_ctor_get(lean_ctor_get(v, 0), 2);
        for _ in 0..n {
            // binding_body = field[2]
            t = lean_ctor_get(t, 2);
        }
        // binding_domain = field[1]
        t = lean_ctor_get(t, 1);
        // get_app_fn: strip App spine (App field[0]=fn)
        while !lean_is_scalar(t) && lean_ptr_tag(t) == EXPR_APP {
            t = lean_ctor_get(t, 0);
        }
        // const_name = field[0] of Const
        lean_ctor_get(t, 0)
    }

    // --- RecursorRule: field[0]=cnstr, field[1]=nfields, field[2]=rhs ---
    #[no_mangle]
    pub unsafe fn lean_recursor_rule_get_cnstr(r: *const LeanObject) -> *mut LeanObject {
        lean_ctor_get(r, 0)
    }
    #[no_mangle]
    pub unsafe fn lean_recursor_rule_get_nfields(r: *const LeanObject) -> u32 {
        lean_unbox(lean_ctor_get(r, 1)) as u32
    }
    #[no_mangle]
    pub unsafe fn lean_recursor_rule_get_rhs(r: *const LeanObject) -> *mut LeanObject {
        lean_ctor_get(r, 2)
    }

    // --- LocalDecl: cdecl (tag 0) / ldecl (tag 1); ldecl field[4]=value ---
    #[no_mangle]
    pub unsafe fn lean_local_decl_has_value(d: *const LeanObject) -> bool {
        !lean_is_scalar(d) && lean_ptr_tag(d) != 0
    }
    #[no_mangle]
    pub unsafe fn lean_local_decl_get_user_name(d: *const LeanObject) -> *mut LeanObject {
        lean_ctor_get(d, 2)
    }
    unsafe fn lean_local_decl_get_info(d: *const LeanObject) -> u8 {
        lean_inc(d as *mut _);
        lean_local_decl_binder_info(d as *mut _)
    }
    // get_value returns the borrowed value expr; only valid when has_value (ldecl).
    #[no_mangle]
    pub unsafe fn lean_local_decl_get_value(d: *const LeanObject) -> *mut LeanObject {
        lean_ctor_get(d, 4)
    }

    // --- reducibility_hints compare / is_regular ---
    // kind: Opaque=boxed 0, Abbreviation=boxed 1, Regular=heap ctor (tag 2 with uint32 height).
    #[inline(always)]
    unsafe fn hints_kind(h: *const LeanObject) -> u32 {
        if lean_is_scalar(h) {
            lean_unbox(h) as u32
        } else {
            lean_ptr_tag(h)
        }
    }
    #[inline(always)]
    unsafe fn hints_height(h: *const LeanObject) -> u32 {
        lean_inc(h as *mut _);
        lean_reducibility_hints_get_height(h as *mut _)
    }
    #[no_mangle]
    pub unsafe fn lean_hints_is_regular(h: *const LeanObject) -> bool {
        hints_kind(h) == REDUCIBILITY_HINTS_REGULAR_TAG
    }
    // Mirrors C++ compare(reducibility_hints): <0 unfold h1, ==0 unfold both, >0 unfold h2.
    #[no_mangle]
    pub unsafe fn lean_hints_compare(h1: *const LeanObject, h2: *const LeanObject) -> i32 {
        const OPAQUE: u32 = 0;
        const ABBREVIATION: u32 = 1;
        const REGULAR: u32 = 2;
        let k1 = hints_kind(h1);
        let k2 = hints_kind(h2);
        if k1 == k2 {
            if k1 == REGULAR {
                let a = hints_height(h1);
                let b = hints_height(h2);
                if a == b {
                    0
                } else if a > b {
                    -1
                } else {
                    1
                }
            } else {
                0
            }
        } else if k1 == OPAQUE {
            1
        } else if k2 == OPAQUE {
            -1
        } else if k1 == ABBREVIATION {
            -1
        } else if k2 == ABBREVIATION {
            1
        } else {
            0
        }
    }

    // --- Native reduction: wrap lean_eval_const_at_kernel_env (mirrors ir::run_boxed_kernel) ---
    // Borrows env/opts/fname; returns the unwrapped result value (Except payload).
    #[no_mangle]
    pub unsafe fn lean_ir_run_boxed_kernel(
        env: *const LeanObject,
        opts: *mut LeanObject,
        name: *mut LeanObject,
        n: u32,
        args: *const *mut LeanObject,
    ) -> *mut LeanObject {
        let result = lean_eval_const_at_kernel_env(env as *mut _, opts, name, n as usize, args);
        let value = lean_ctor_get(result, 0);
        lean_inc(value);
        lean_dec(result);
        value
    }

    // --- Empty options (mirrors C++ options() default constructor) ---
    #[no_mangle]
    pub unsafe fn lean_mk_empty_options() -> *mut LeanObject {
        lean_options_get_empty(lean_box(0))
    }

    // --- LocalContext: build (fvar, new_lctx) pairs from the real Lean exports ---
    // These are NOT #[no_mangle]: `lean_local_ctx_mk_local_decl` is also a Lean stdlib
    // export (returning just the LocalContext), so an exported shim would collide.
    // As module-local fns they simply shadow the names at the call sites in this file.
    //
    // `mk_local_decl(g, un, type, bi)` in C++ does:
    //   new_lctx = lean_local_ctx_mk_local_decl(lctx, g.next(), un, type, bi); return mk_fvar(g.next())
    // The fresh fvarId is supplied by the caller as `fvar_id`.
    unsafe fn lean_local_ctx_mk_local_decl(
        lctx: *mut LeanObject,
        fvar_id: *mut LeanObject,
        user_name: *mut LeanObject,
        ty: *mut LeanObject,
        bi: u8,
    ) -> *mut LeanObject {
        // The real export consumes lctx/fvar_id/user_name/ty; preserve the caller's refs.
        lean_inc(lctx);
        lean_inc(fvar_id);
        lean_inc(user_name);
        lean_inc(ty);
        let new_lctx = lean_real_lctx_mk_local_decl(lctx, fvar_id, user_name, ty, bi);
        lean_inc(fvar_id); // lean_expr_mk_fvar consumes its arg
        let fvar = lean_expr_mk_fvar(fvar_id);
        let pair = lean_alloc_ctor(0, 2, 0);
        lean_ctor_set(pair, 0, fvar);
        lean_ctor_set(pair, 1, new_lctx);
        pair
    }

    unsafe fn lean_local_ctx_mk_local_decl_with_value(
        lctx: *mut LeanObject,
        fvar_id: *mut LeanObject,
        user_name: *mut LeanObject,
        ty: *mut LeanObject,
        value: *mut LeanObject,
    ) -> *mut LeanObject {
        // The real export consumes all owned args; preserve the caller's refs.
        lean_inc(lctx);
        lean_inc(fvar_id);
        lean_inc(user_name);
        lean_inc(ty);
        lean_inc(value);
        let new_lctx = lean_real_lctx_mk_let_decl(lctx, fvar_id, user_name, ty, value, false);
        lean_inc(fvar_id); // lean_expr_mk_fvar consumes its arg
        let fvar = lean_expr_mk_fvar(fvar_id);
        let pair = lean_alloc_ctor(0, 2, 0);
        lean_ctor_set(pair, 0, fvar);
        lean_ctor_set(pair, 1, new_lctx);
        pair
    }

    unsafe fn local_ctx_mk_binding(
        lctx: *const LeanObject,
        fvars: *const *mut LeanObject,
        n: u32,
        body: *mut LeanObject,
        remove_dead_let: bool,
        is_lambda: bool,
    ) -> *mut LeanObject {
        let mut r = lean_expr_abstract(body, n, fvars);
        let mut i = n;
        while i > 0 {
            i -= 1;
            let fvar = *fvars.add(i as usize);
            let decl = lean_local_ctx_find_local_decl(lctx, fvar);
            if lean_is_scalar(decl) {
                // Mirrors the C++ assertion path poorly, but avoids silently building malformed terms.
                lean_dec(r);
                let msg = format!("unknown free variable in local_ctx_mk_binding");
                panic!("{}", msg);
            }

            if lean_local_decl_has_value(decl) {
                if !remove_dead_let || expr_has_loose_bvar(r, 0) {
                    let decl_ty = lean_local_decl_get_type(decl);
                    let decl_val = lean_local_decl_get_value(decl);
                    let ty = lean_expr_abstract(decl_ty, i, fvars);
                    let val = lean_expr_abstract(decl_val, i, fvars);
                    let user_name = lean_local_decl_get_user_name(decl);
                    lean_inc(user_name);
                    r = lean_expr_mk_let(user_name, ty, val, r, false);
                } else {
                    let new_r = lean_expr_lower_loose_bvars(r, lean_box(1), lean_box(1));
                    lean_dec(r);
                    r = new_r;
                }
            } else {
                let decl_ty = lean_local_decl_get_type(decl);
                let ty = lean_expr_abstract(decl_ty, i, fvars);
                let user_name = lean_local_decl_get_user_name(decl);
                let bi = lean_local_decl_get_info(decl);
                lean_inc(user_name);
                r = if is_lambda {
                    lean_expr_mk_lambda(user_name, ty, r, bi)
                } else {
                    lean_expr_mk_forall(user_name, ty, r, bi)
                };
            }
            lean_dec(decl);
        }
        r
    }

    // --- local_ctx::mk_pi / mk_lambda (mk_binding<false/true>) ---
    unsafe fn lean_local_ctx_mk_pi(
        lctx: *const LeanObject,
        fvars: *const *mut LeanObject,
        n: u32,
        body: *mut LeanObject,
        remove_dead_let: bool,
    ) -> *mut LeanObject {
        local_ctx_mk_binding(lctx, fvars, n, body, remove_dead_let, false)
    }

    unsafe fn lean_local_ctx_mk_lambda(
        lctx: *const LeanObject,
        fvars: *const *mut LeanObject,
        n: u32,
        body: *mut LeanObject,
    ) -> *mut LeanObject {
        local_ctx_mk_binding(lctx, fvars, n, body, false, true)
    }

    const LEVEL_ZERO: u32 = 0; // scalar (lean_is_scalar)

    // Definition safety
    const DEF_SAFETY_UNSAFE: u8 = 0;
    const DEF_SAFETY_SAFE: u8 = 1;
    const DEF_SAFETY_PARTIAL: u8 = 2;

    // Quotient eliminator argument layout (mirrors `quot_reduce_rec` in quot.h).
    // `Quot.lift {α} (r) {β} (f) (h) (q)`: q (the Quot.mk) is arg 5, f is arg 3.
    // `Quot.ind  {α} {r} {β} (mk) (q)`:    q (the Quot.mk) is arg 4, mk is arg 3.
    // `Quot.mk   {α} (r) (a)`:             fully applied with 3 args; `a` is the last arg.
    const QUOT_LIFT_MK_POS: usize = 5;
    const QUOT_LIFT_ARG_POS: usize = 3;
    const QUOT_IND_MK_POS: usize = 4;
    const QUOT_IND_ARG_POS: usize = 3;
    const QUOT_MK_NUM_ARGS: usize = 3;

    // ---------------------------------------------------------------------------
    // LBool (three-valued boolean: true / false / undef)
    // ---------------------------------------------------------------------------

    #[derive(Clone, Copy, PartialEq, Eq)]
    enum LBool {
        True,
        False,
        Undef,
    }

    impl LBool {
        fn from_bool(b: bool) -> Self {
            if b { LBool::True } else { LBool::False }
        }
    }

    // ---------------------------------------------------------------------------
    // Level arithmetic helpers
    // ---------------------------------------------------------------------------

    unsafe fn level_kind(l: *const LeanObject) -> u32 {
        if lean_is_scalar(l) {
            LEVEL_ZERO
        } else {
            lean_ptr_tag(l)
        }
    }

    /// Strips succ chain from `l`, returns (base, offset).
    unsafe fn level_to_offset(l: *const LeanObject) -> (*const LeanObject, u32) {
        let mut cur = l;
        let mut offset: u32 = 0;
        while level_kind(cur) == LEVEL_SUCC {
            cur = lean_level_get_succ(cur);
            offset += 1;
        }
        (cur, offset)
    }

    /// Push all flattened Max arguments of `l` into `buf`.
    unsafe fn level_push_max_args(l: *const LeanObject, buf: &mut Vec<*mut LeanObject>) {
        if level_kind(l) == LEVEL_MAX {
            level_push_max_args(lean_level_get_max_lhs(l), buf);
            level_push_max_args(lean_level_get_max_rhs(l), buf);
        } else {
            lean_inc(l);
            buf.push(l as *mut LeanObject);
        }
    }

    /// Normalize a level (port of normalize(level) from level.h).
    unsafe fn normalize_level(l: *mut LeanObject) -> *mut LeanObject {
        match level_kind(l) {
            LEVEL_ZERO | LEVEL_PARAM | LEVEL_MVAR => {
                lean_inc(l);
                l
            }
            LEVEL_SUCC => {
                let inner = lean_level_get_succ(l);
                let norm = normalize_level(inner);
                // Canonical normal form pushes `succ` to the leaves: succ(max a b …) = max (succ a)(succ b)…
                // Without this distribution, `succ(max u v)` and `max (u+1)(v+1)` normalize to
                // structurally different levels and `is_equivalent_level` (normalized struct-eq) wrongly
                // reports them unequal — breaking app/pi checks over multi-universe types.
                if level_kind(norm) == LEVEL_MAX {
                    let mut margs: Vec<*mut LeanObject> = Vec::new();
                    level_push_max_args(norm, &mut margs); // owned refs
                    lean_dec(norm);
                    // mk_succ consumes each arg; fold into a raw max, then re-normalize to canonicalise.
                    let raw = margs
                        .into_iter()
                        .map(|a| lean_level_mk_succ(a))
                        .collect::<Vec<_>>()
                        .into_iter()
                        .rev()
                        .reduce(|acc, cur| lean_level_mk_max(cur, acc))
                        .unwrap();
                    let r = normalize_level(raw);
                    lean_dec(raw);
                    r
                } else {
                    // mk_succ consumes `norm` (obj_arg) — no dec afterwards.
                    lean_level_mk_succ(norm)
                }
            }
            LEVEL_MAX => {
                // Port of `normalize` (level.h): flatten max args, normalize each (re-flattening
                // since normalization may itself yield a max), sort by is_norm_lt, then drop
                // subsumed args (same base ⇒ keep only the largest offset; an explicit/numeral
                // arg is dropped when some other arg has an offset ≥ it), and rebuild the max.
                let mut todo: Vec<*mut LeanObject> = Vec::new();
                level_push_max_args(l, &mut todo);
                let mut args: Vec<*mut LeanObject> = Vec::new();
                for &a in &todo {
                    let na = normalize_level(a);
                    level_push_max_args(na, &mut args);
                    lean_dec(na);
                }
                for &a in &todo {
                    lean_dec(a);
                }

                args.sort_by(|&a, &b| {
                    if is_norm_lt(a, b) {
                        std::cmp::Ordering::Less
                    } else if is_norm_lt(b, a) {
                        std::cmp::Ordering::Greater
                    } else {
                        std::cmp::Ordering::Equal
                    }
                });

                // Select indices to keep (subsumption); dec the rest.
                let mut keep: Vec<usize> = Vec::new();
                let mut i = 0usize;
                if is_explicit_level(args[0]) {
                    while i + 1 < args.len() && is_explicit_level(args[i + 1]) {
                        i += 1;
                    }
                    let k = level_to_offset(args[i] as *const LeanObject).1;
                    let mut j = i + 1;
                    while j < args.len() && level_to_offset(args[j] as *const LeanObject).1 < k {
                        j += 1;
                    }
                    if j < args.len() {
                        i += 1;
                    } // largest explicit is subsumed by a non-explicit arg
                }
                keep.push(i);
                let (mut prev_base, mut prev_off) = level_to_offset(args[i] as *const LeanObject);
                i += 1;
                while i < args.len() {
                    let (cb, co) = level_to_offset(args[i] as *const LeanObject);
                    if lean_level_eq(prev_base, cb) {
                        if prev_off < co {
                            prev_base = cb;
                            prev_off = co;
                            keep.pop();
                            keep.push(i);
                        }
                    } else {
                        prev_base = cb;
                        prev_off = co;
                        keep.push(i);
                    }
                    i += 1;
                }

                let keep_set: HashSet<usize> = keep.iter().copied().collect();
                let mut kept: Vec<*mut LeanObject> = Vec::with_capacity(keep.len());
                for (idx, &a) in args.iter().enumerate() {
                    if keep_set.contains(&idx) {
                        kept.push(a);
                    } else {
                        lean_dec(a);
                    }
                }

                // mk_max consumes both args (obj_arg); `kept` owns each, so they flow in without dec.
                kept.iter()
                    .rev()
                    .copied()
                    .reduce(|acc, cur| lean_level_mk_max(cur, acc))
                    .unwrap_or_else(|| lean_level_mk_zero())
            }
            LEVEL_IMAX => {
                let lhs_raw = lean_level_get_imax_lhs(l);
                let rhs_raw = lean_level_get_imax_rhs(l);
                let lhs = normalize_level(lhs_raw);
                let rhs = normalize_level(rhs_raw);
                // Smart `mk_imax` (kernel level.cpp), in the same order:
                //   is_not_zero(r) ⇒ max l r      (covers IMax l (Succ r) etc.)
                //   is_zero(r)     ⇒ 0            (imax u 0 = 0)
                //   is_zero/one(l) ⇒ r            (imax 0 u = imax 1 u = u)
                //   l == r         ⇒ l            (imax u u = u)
                //   otherwise      ⇒ imax l r
                if is_not_zero_level(rhs as *const LeanObject) {
                    // mk_max is the raw constructor; normalize to canonicalise the result.
                    let m = lean_level_mk_max(lhs, rhs); // consumes lhs, rhs
                    let r = normalize_level(m);
                    lean_dec(m);
                    return r;
                }
                if level_kind(rhs) == LEVEL_ZERO {
                    lean_dec(lhs);
                    return rhs; // imax u 0 = 0 (rhs is the zero level)
                }
                if level_kind(lhs) == LEVEL_ZERO || is_one_level(lhs as *const LeanObject) {
                    lean_dec(lhs);
                    return rhs; // imax 0 u = imax 1 u = u
                }
                if lean_level_eq(lhs, rhs) {
                    lean_dec(rhs);
                    return lhs; // imax u u = u
                }
                lean_level_mk_imax(lhs, rhs) // consumes lhs, rhs
            }
            _ => {
                lean_inc(l);
                l
            }
        }
    }

    /// A level is "explicit" (a numeral) iff its succ-chain bottoms out at `zero`.
    unsafe fn is_explicit_level(l: *const LeanObject) -> bool {
        level_kind(level_to_offset(l).0) == LEVEL_ZERO
    }

    /// Map a level kind to `Level.ctorToNat`'s ordinal (zero<param<mvar<succ<max<imax).
    fn level_ctor_ord(kind: u32) -> u32 {
        match kind {
            LEVEL_ZERO => 0,
            LEVEL_PARAM => 1,
            LEVEL_MVAR => 2,
            LEVEL_SUCC => 3,
            LEVEL_MAX => 4,
            LEVEL_IMAX => 5,
            _ => 6,
        }
    }

    /// Port of `Name.cmp` (lexicographic, prefix-major). Names are BORROWED.
    /// Tags: `.str`=1, `.num`=2, `.anonymous`=scalar; ordering anonymous<num<str per `Name.cmp`.
    unsafe fn name_cmp(n1: *mut LeanObject, n2: *mut LeanObject) -> core::cmp::Ordering {
        use core::cmp::Ordering;
        let a1 = lean_is_scalar(n1);
        let a2 = lean_is_scalar(n2);
        if a1 && a2 {
            return Ordering::Equal;
        }
        if a1 {
            return Ordering::Less;
        }
        if a2 {
            return Ordering::Greater;
        }
        let t1 = lean_obj_tag(n1);
        let t2 = lean_obj_tag(n2);
        if t1 != t2 {
            return if t1 == 2 {
                Ordering::Less
            } else {
                Ordering::Greater
            };
        }
        let pc = name_cmp(lean_ctor_get(n1, 0), lean_ctor_get(n2, 0)); // compare prefix first
        if pc != Ordering::Equal {
            return pc;
        }
        if t1 == 1 {
            // `.str`: compare component strings (UTF-8 byte order == codepoint order).
            let s1 = core::ffi::CStr::from_ptr(lean_string_cstr(lean_ctor_get(n1, 1))).to_bytes();
            let s2 = core::ffi::CStr::from_ptr(lean_string_cstr(lean_ctor_get(n2, 1))).to_bytes();
            s1.cmp(s2)
        } else {
            // `.num`: compare nat indices (name numerals are small scalars in practice).
            let c1 = lean_ctor_get(n1, 1);
            let c2 = lean_ctor_get(n2, 1);
            let i1 = if lean_is_scalar(c1) {
                lean_unbox(c1) as u64
            } else {
                u64::MAX
            };
            let i2 = if lean_is_scalar(c2) {
                lean_unbox(c2) as u64
            } else {
                u64::MAX
            };
            i1.cmp(&i2)
        }
    }

    /// Faithful port of `Level.normLtAux` — the total order used to canonicalise `max` args.
    /// Levels are BORROWED; `k1`/`k2` accumulate stripped `succ` offsets. Recurses into
    /// `max`/`imax` so complex multi-universe levels get a *stable* canonical order (the previous
    /// offset-only version could not, so equal arg-multisets sorted to different sequences and
    /// `is_equivalent_level` wrongly reported them unequal). Uses `Name.cmp` (lexicographic), not a
    /// hash, matching the Lean source (hashes are unstable across shifted indices; see test 343).
    unsafe fn norm_lt_aux(l1: *const LeanObject, k1: u32, l2: *const LeanObject, k2: u32) -> bool {
        use core::cmp::Ordering;
        let kind1 = level_kind(l1);
        let kind2 = level_kind(l2);
        if kind1 == LEVEL_SUCC {
            return norm_lt_aux(lean_level_get_succ(l1), k1 + 1, l2, k2);
        }
        if kind2 == LEVEL_SUCC {
            return norm_lt_aux(l1, k1, lean_level_get_succ(l2), k2 + 1);
        }
        if kind1 == LEVEL_MAX && kind2 == LEVEL_MAX {
            if lean_level_eq(l1, l2) {
                return k1 < k2;
            }
            let a = lean_level_get_max_lhs(l1);
            let b = lean_level_get_max_lhs(l2);
            if !lean_level_eq(a, b) {
                return norm_lt_aux(a, 0, b, 0);
            }
            return norm_lt_aux(lean_level_get_max_rhs(l1), 0, lean_level_get_max_rhs(l2), 0);
        }
        if kind1 == LEVEL_IMAX && kind2 == LEVEL_IMAX {
            if lean_level_eq(l1, l2) {
                return k1 < k2;
            }
            let a = lean_level_get_imax_lhs(l1);
            let b = lean_level_get_imax_lhs(l2);
            if !lean_level_eq(a, b) {
                return norm_lt_aux(a, 0, b, 0);
            }
            return norm_lt_aux(
                lean_level_get_imax_rhs(l1),
                0,
                lean_level_get_imax_rhs(l2),
                0,
            );
        }
        if kind1 == LEVEL_PARAM && kind2 == LEVEL_PARAM {
            let n1 = lean_level_get_param_name(l1);
            let n2 = lean_level_get_param_name(l2);
            return if lean_name_eq(n1, n2) {
                k1 < k2
            } else {
                name_cmp(n1, n2) == Ordering::Less
            };
        }
        if kind1 == LEVEL_MVAR && kind2 == LEVEL_MVAR {
            // mvar holds an `LMVarId` wrapper whose field 0 is the Name.
            let n1 = lean_ctor_get(lean_level_get_param_name(l1), 0);
            let n2 = lean_ctor_get(lean_level_get_param_name(l2), 0);
            return if lean_name_eq(n1, n2) {
                k1 < k2
            } else {
                name_cmp(n1, n2) == Ordering::Less
            };
        }
        if lean_level_eq(l1, l2) {
            return k1 < k2;
        }
        level_ctor_ord(kind1) < level_ctor_ord(kind2)
    }

    /// Comparison for sorted Max-arg deduplication (`Level.normLt`).
    unsafe fn is_norm_lt(a: *const LeanObject, b: *const LeanObject) -> bool {
        norm_lt_aux(a as *mut LeanObject, 0, b as *mut LeanObject, 0)
    }

    /// Check level equivalence (modulo normalization).
    ///
    /// NOTE: do NOT call `check_system_result()` here. Level/universe comparison happens on essentially
    /// every sort defeq, and `check_system_result` increments the heartbeat counter — C++ only does so in
    /// `infer_type_core`/`whnf_core`/`is_def_eq_core`, NOT in level comparison. Incrementing here burns
    /// the heartbeat budget far faster than C++ (spurious `(kernel) deterministic timeout`) and adds
    /// stack/memory checks to a hot, shallow-recursion path. Level normalization is bounded by level depth.
    unsafe fn is_equivalent_level(
        l1: *mut LeanObject,
        l2: *mut LeanObject,
    ) -> Result<bool, KernelError> {
        if lean_level_eq(l1, l2) {
            return Ok(true);
        }
        let n1 = normalize_level(l1);
        let n2 = normalize_level(l2);
        let eq = lean_level_eq(n1, n2);
        lean_dec(n1);
        lean_dec(n2);
        Ok(eq)
    }

    /// Return true if l is the level `1` (i.e. `succ zero`).
    unsafe fn is_one_level(l: *const LeanObject) -> bool {
        level_kind(l) == LEVEL_SUCC && level_kind(lean_level_get_succ(l)) == LEVEL_ZERO
    }

    /// Return true if l is definitely not zero for any universe assignment.
    unsafe fn is_not_zero_level(l: *const LeanObject) -> bool {
        match level_kind(l) {
            LEVEL_ZERO => false,
            LEVEL_PARAM => false,
            LEVEL_MVAR => false,
            LEVEL_SUCC => true,
            LEVEL_MAX => {
                is_not_zero_level(lean_level_get_max_lhs(l))
                    || is_not_zero_level(lean_level_get_max_rhs(l))
            }
            LEVEL_IMAX => is_not_zero_level(lean_level_get_imax_rhs(l)),
            _ => false,
        }
    }

    /// Return true if l1 >= l2 (port of is_geq_core after normalizing).
    unsafe fn is_geq_level(l1: *mut LeanObject, l2: *mut LeanObject) -> Result<bool, KernelError> {
        if lean_level_eq(l1, l2) {
            return Ok(true);
        }
        let n1 = normalize_level(l1);
        let n2 = normalize_level(l2);
        let result = is_geq_normalized(n1, n2);
        lean_dec(n1);
        lean_dec(n2);
        result
    }

    unsafe fn is_geq_normalized(
        l1: *mut LeanObject,
        l2: *mut LeanObject,
    ) -> Result<bool, KernelError> {
        // No `check_system_result()` here — see the note on `is_equivalent_level` (heartbeat parity with C++).
        if lean_level_eq(l1, l2) || level_kind(l2) == LEVEL_ZERO {
            return Ok(true);
        }
        if level_kind(l2) == LEVEL_MAX {
            // l1 >= max(a, b)  iff  l1 >= a && l1 >= b
            let a = lean_level_get_max_lhs(l2);
            let b = lean_level_get_max_rhs(l2);
            return Ok(is_geq_normalized(l1, a)? && is_geq_normalized(l1, b)?);
        }
        if level_kind(l1) == LEVEL_MAX {
            // C++ only accepts the `max` LHS shortcut when one branch proves the comparison;
            // otherwise it falls through to the remaining cases such as `l2 = imax ...`.
            let a = lean_level_get_max_lhs(l1);
            let b = lean_level_get_max_rhs(l1);
            if is_geq_normalized(a, l2)? || is_geq_normalized(b, l2)? {
                return Ok(true);
            }
        }
        if level_kind(l2) == LEVEL_IMAX {
            let a = lean_level_get_imax_lhs(l2);
            let b = lean_level_get_imax_rhs(l2);
            return Ok(is_geq_normalized(l1, a)? && is_geq_normalized(l1, b)?);
        }
        if level_kind(l1) == LEVEL_IMAX {
            return is_geq_normalized(lean_level_get_imax_rhs(l1), l2);
        }

        let (base1, off1) = level_to_offset(l1 as *const LeanObject);
        let (base2, off2) = level_to_offset(l2 as *const LeanObject);
        if lean_level_eq(base1, base2) {
            return Ok(off1 >= off2);
        }
        if level_kind(base2) == LEVEL_ZERO {
            return Ok(off1 >= off2);
        }
        if off1 == off2 && off1 > 0 {
            return is_geq_normalized(base1 as *mut LeanObject, base2 as *mut LeanObject);
        }
        Ok(false)
    }

    /// Traverse level `l`; return first param name not in `lparams`, or None.
    unsafe fn get_undef_param(
        l: *const LeanObject,
        lparams: *const LeanObject,
    ) -> Option<*mut LeanObject> {
        match level_kind(l) {
            LEVEL_ZERO => None,
            LEVEL_PARAM => {
                let name = lean_level_get_param_name(l);
                let mut cur = lparams as *mut LeanObject;
                while !lean_list_is_nil(cur) {
                    let h = lean_list_head(cur);
                    if lean_name_eq(h, name) {
                        return None;
                    }
                    cur = lean_list_tail(cur);
                }
                Some(name)
            }
            LEVEL_MVAR => None, // mvars are not params
            LEVEL_SUCC => get_undef_param(lean_level_get_succ(l), lparams),
            LEVEL_MAX => get_undef_param(lean_level_get_max_lhs(l), lparams)
                .or_else(|| get_undef_param(lean_level_get_max_rhs(l), lparams)),
            LEVEL_IMAX => get_undef_param(lean_level_get_imax_lhs(l), lparams)
                .or_else(|| get_undef_param(lean_level_get_imax_rhs(l), lparams)),
            _ => None,
        }
    }

    // ---------------------------------------------------------------------------
    // KernelError — mirrors the 17 Lean.Kernel.Exception variants
    // ---------------------------------------------------------------------------

    pub enum KernelError {
        // Type-error variants (carry Lean object pointers)
        UnknownConstant {
            env: *mut LeanObject,
            name: *mut LeanObject,
        },
        AlreadyDeclared {
            env: *mut LeanObject,
            name: *mut LeanObject,
        },
        DeclTypeMismatch {
            env: *mut LeanObject,
            decl: *mut LeanObject,
            given_type: *mut LeanObject,
        },
        DeclHasMVars {
            env: *mut LeanObject,
            name: *mut LeanObject,
            expr: *mut LeanObject,
        },
        DeclHasFVars {
            env: *mut LeanObject,
            name: *mut LeanObject,
            expr: *mut LeanObject,
        },
        FunExpected {
            env: *mut LeanObject,
            lctx: *mut LeanObject,
            expr: *mut LeanObject,
        },
        TypeExpected {
            env: *mut LeanObject,
            lctx: *mut LeanObject,
            expr: *mut LeanObject,
        },
        LetTypeMismatch {
            env: *mut LeanObject,
            lctx: *mut LeanObject,
            name: *mut LeanObject,
            given: *mut LeanObject,
            expected: *mut LeanObject,
        },
        ExprTypeMismatch {
            env: *mut LeanObject,
            lctx: *mut LeanObject,
            expr: *mut LeanObject,
            expected: *mut LeanObject,
        },
        AppTypeMismatch {
            env: *mut LeanObject,
            lctx: *mut LeanObject,
            app: *mut LeanObject,
            fun_type: *mut LeanObject,
            arg_type: *mut LeanObject,
        },
        InvalidProj {
            env: *mut LeanObject,
            lctx: *mut LeanObject,
            proj: *mut LeanObject,
        },
        ThmTypeIsNotProp {
            env: *mut LeanObject,
            name: *mut LeanObject,
            ty: *mut LeanObject,
        },
        Other {
            msg: *mut LeanObject,
        },
        // Resource-limit variants (no payload; use lean_box)
        DeterministicTimeout,
        ExcessiveMemory,
        DeepRecursion,
        Interrupted,
    }

    impl Drop for KernelError {
        fn drop(&mut self) {
            unsafe {
                match self {
                    KernelError::UnknownConstant { env, name }
                    | KernelError::AlreadyDeclared { env, name } => {
                        lean_dec(*env);
                        lean_dec(*name);
                    }
                    KernelError::DeclTypeMismatch {
                        env,
                        decl,
                        given_type,
                    } => {
                        lean_dec(*env);
                        lean_dec(*decl);
                        lean_dec(*given_type);
                    }
                    KernelError::DeclHasMVars { env, name, expr }
                    | KernelError::DeclHasFVars { env, name, expr } => {
                        lean_dec(*env);
                        lean_dec(*name);
                        lean_dec(*expr);
                    }
                    KernelError::FunExpected { env, lctx, expr }
                    | KernelError::TypeExpected { env, lctx, expr }
                    | KernelError::InvalidProj {
                        env,
                        lctx,
                        proj: expr,
                    } => {
                        lean_dec(*env);
                        lean_dec(*lctx);
                        lean_dec(*expr);
                    }
                    KernelError::LetTypeMismatch {
                        env,
                        lctx,
                        name,
                        given,
                        expected,
                    } => {
                        lean_dec(*env);
                        lean_dec(*lctx);
                        lean_dec(*name);
                        lean_dec(*given);
                        lean_dec(*expected);
                    }
                    KernelError::ExprTypeMismatch {
                        env,
                        lctx,
                        expr,
                        expected,
                    } => {
                        lean_dec(*env);
                        lean_dec(*lctx);
                        lean_dec(*expr);
                        lean_dec(*expected);
                    }
                    KernelError::AppTypeMismatch {
                        env,
                        lctx,
                        app,
                        fun_type,
                        arg_type,
                    } => {
                        lean_dec(*env);
                        lean_dec(*lctx);
                        lean_dec(*app);
                        lean_dec(*fun_type);
                        lean_dec(*arg_type);
                    }
                    KernelError::ThmTypeIsNotProp { env, name, ty } => {
                        lean_dec(*env);
                        lean_dec(*name);
                        lean_dec(*ty);
                    }
                    KernelError::Other { msg } => {
                        lean_dec(*msg);
                    }
                    KernelError::DeterministicTimeout
                    | KernelError::ExcessiveMemory
                    | KernelError::DeepRecursion
                    | KernelError::Interrupted => {}
                }
            }
        }
    }

    /// Convert KernelError into a Lean `Except KernelException α` value (Except.error …).
    unsafe fn kernel_error_to_lean_except(e: KernelError) -> *mut LeanObject {
        let inner: *mut LeanObject = match e {
            KernelError::UnknownConstant { env, name } => {
                let o = lean_alloc_ctor(0, 2, 0); // tag 0
                lean_ctor_set(o, 0, env);
                lean_ctor_set(o, 1, name);
                o
            }
            KernelError::AlreadyDeclared { env, name } => {
                let o = lean_alloc_ctor(1, 2, 0);
                lean_ctor_set(o, 0, env);
                lean_ctor_set(o, 1, name);
                o
            }
            KernelError::DeclTypeMismatch {
                env,
                decl,
                given_type,
            } => {
                let o = lean_alloc_ctor(2, 3, 0);
                lean_ctor_set(o, 0, env);
                lean_ctor_set(o, 1, decl);
                lean_ctor_set(o, 2, given_type);
                o
            }
            KernelError::DeclHasMVars { env, name, expr } => {
                let o = lean_alloc_ctor(3, 3, 0);
                lean_ctor_set(o, 0, env);
                lean_ctor_set(o, 1, name);
                lean_ctor_set(o, 2, expr);
                o
            }
            KernelError::DeclHasFVars { env, name, expr } => {
                let o = lean_alloc_ctor(4, 3, 0);
                lean_ctor_set(o, 0, env);
                lean_ctor_set(o, 1, name);
                lean_ctor_set(o, 2, expr);
                o
            }
            KernelError::FunExpected { env, lctx, expr } => {
                let o = lean_alloc_ctor(5, 3, 0);
                lean_ctor_set(o, 0, env);
                lean_ctor_set(o, 1, lctx);
                lean_ctor_set(o, 2, expr);
                o
            }
            KernelError::TypeExpected { env, lctx, expr } => {
                let o = lean_alloc_ctor(6, 3, 0);
                lean_ctor_set(o, 0, env);
                lean_ctor_set(o, 1, lctx);
                lean_ctor_set(o, 2, expr);
                o
            }
            KernelError::LetTypeMismatch {
                env,
                lctx,
                name,
                given,
                expected,
            } => {
                let o = lean_alloc_ctor(7, 5, 0);
                lean_ctor_set(o, 0, env);
                lean_ctor_set(o, 1, lctx);
                lean_ctor_set(o, 2, name);
                lean_ctor_set(o, 3, given);
                lean_ctor_set(o, 4, expected);
                o
            }
            KernelError::ExprTypeMismatch {
                env,
                lctx,
                expr,
                expected,
            } => {
                let o = lean_alloc_ctor(8, 4, 0);
                lean_ctor_set(o, 0, env);
                lean_ctor_set(o, 1, lctx);
                lean_ctor_set(o, 2, expr);
                lean_ctor_set(o, 3, expected);
                o
            }
            KernelError::AppTypeMismatch {
                env,
                lctx,
                app,
                fun_type,
                arg_type,
            } => {
                let o = lean_alloc_ctor(9, 5, 0);
                lean_ctor_set(o, 0, env);
                lean_ctor_set(o, 1, lctx);
                lean_ctor_set(o, 2, app);
                lean_ctor_set(o, 3, fun_type);
                lean_ctor_set(o, 4, arg_type);
                o
            }
            KernelError::InvalidProj { env, lctx, proj } => {
                let o = lean_alloc_ctor(10, 3, 0);
                lean_ctor_set(o, 0, env);
                lean_ctor_set(o, 1, lctx);
                lean_ctor_set(o, 2, proj);
                o
            }
            KernelError::ThmTypeIsNotProp { env, name, ty } => {
                let o = lean_alloc_ctor(11, 3, 0);
                lean_ctor_set(o, 0, env);
                lean_ctor_set(o, 1, name);
                lean_ctor_set(o, 2, ty);
                o
            }
            KernelError::Other { msg } => {
                let o = lean_alloc_ctor(12, 1, 0);
                lean_ctor_set(o, 0, msg);
                o
            }
            KernelError::DeterministicTimeout => lean_box(13),
            KernelError::ExcessiveMemory => lean_box(14),
            KernelError::DeepRecursion => lean_box(15),
            KernelError::Interrupted => lean_box(16),
        };
        // Wrap: Except.error inner (Except.error is the first constructor → tag 0)
        let except_err = lean_alloc_ctor(EXCEPT_ERROR_TAG, 1, 0);
        lean_ctor_set(except_err, 0, inner);
        // The match above bound the `*mut LeanObject` fields by COPY (raw pointers are `Copy`),
        // transferring their owned refs into the Lean exception object via `lean_ctor_set` WITHOUT
        // consuming `e`. Since `KernelError` has a manual `Drop` that decrements those same fields,
        // letting `e` drop here would double-free every field (env/lctx/expr/…). Suppress it.
        core::mem::forget(e);
        except_err
    }

    // ---------------------------------------------------------------------------
    // Owned reference-counted Lean objects
    // ---------------------------------------------------------------------------

    /// RAII wrapper that increments refcount on construction and decrements on drop.
    struct OwnedLean(*mut LeanObject);

    impl OwnedLean {
        unsafe fn new(o: *mut LeanObject) -> Self {
            lean_inc(o);
            OwnedLean(o)
        }
        fn get(&self) -> *mut LeanObject {
            self.0
        }
        /// Consume without decrementing (transfer ownership to caller).
        fn into_raw(self) -> *mut LeanObject {
            let p = self.0;
            std::mem::forget(self);
            p
        }
    }

    impl Drop for OwnedLean {
        fn drop(&mut self) {
            unsafe {
                lean_dec(self.0);
            }
        }
    }

    impl Clone for OwnedLean {
        fn clone(&self) -> Self {
            unsafe { OwnedLean::new(self.0) }
        }
    }

    // ---------------------------------------------------------------------------
    // ExprKey — wrapper for HashMap/HashSet keys over expression pointers
    // ---------------------------------------------------------------------------

    struct ExprKey(*mut LeanObject);

    impl ExprKey {
        unsafe fn new(o: *mut LeanObject) -> Self {
            lean_inc(o);
            ExprKey(o)
        }
    }

    impl Drop for ExprKey {
        fn drop(&mut self) {
            unsafe {
                lean_dec(self.0);
            }
        }
    }

    impl std::hash::Hash for ExprKey {
        fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
            unsafe { expr_hash(self.0).hash(state) }
        }
    }

    impl PartialEq for ExprKey {
        fn eq(&self, other: &Self) -> bool {
            unsafe { lean_expr_eqv(self.0, other.0) }
        }
    }

    impl Eq for ExprKey {}

    type ExprCache = HashMap<ExprKey, OwnedLean>;

    // ---------------------------------------------------------------------------
    // NameGenerator
    // ---------------------------------------------------------------------------

    struct NameGenerator {
        prefix: *mut LeanObject, // owned
        counter: u64,
    }

    impl NameGenerator {
        unsafe fn new(prefix: *mut LeanObject) -> Self {
            lean_inc(prefix);
            NameGenerator { prefix, counter: 0 }
        }

        unsafe fn mk_fresh_name(&mut self) -> *mut LeanObject {
            let counter_obj = lean_nat_mk_obj(self.counter);
            lean_inc(self.prefix);
            let n = lean_name_mk_numeral(self.prefix, counter_obj);
            self.counter += 1;
            n
        }
    }

    impl Drop for NameGenerator {
        fn drop(&mut self) {
            unsafe {
                lean_dec(self.prefix);
            }
        }
    }

    /// Look up a constant, returning an owned bare `ConstantInfo`, or a boxed scalar
    /// (testable with `lean_is_scalar`) when the constant is absent.
    ///
    /// `lean_environment_find` *consumes* both of its arguments (the C++ `environment::find`
    /// passes `env`/`name` via `to_obj_arg()`) and returns an `Option ConstantInfo`. Our
    /// callers hold only borrowed references and expect the unwrapped `ConstantInfo`, so we
    /// inc both inputs and strip the `Option.some` wrapper here.
    unsafe fn env_find(env: *const LeanObject, name: *mut LeanObject) -> *mut LeanObject {
        lean_inc(env);
        lean_inc(name);
        let opt = lean_environment_find(env, name);
        if lean_is_scalar(opt) {
            opt // Option.none
        } else {
            let info = lean_ctor_get(opt, 0); // Option.some payload (borrowed)
            lean_inc(info);
            lean_dec(opt);
            info
        }
    }

    // ---------------------------------------------------------------------------
    // System check
    // ---------------------------------------------------------------------------

    unsafe fn check_system_result() -> Result<(), KernelError> {
        if !lean_stack_has_space() {
            return Err(KernelError::DeepRecursion);
        }
        if !lean_memory_within_limit() {
            return Err(KernelError::ExcessiveMemory);
        }
        if check_heartbeat_exceeded() {
            return Err(KernelError::DeterministicTimeout);
        }
        if check_interrupted_flag() {
            return Err(KernelError::Interrupted);
        }
        Ok(())
    }

    // ---------------------------------------------------------------------------
    // TypeCheckerState
    // ---------------------------------------------------------------------------

    struct TypeCheckerState {
        env: *mut LeanObject, // borrowed (inc'd by TypeChecker creator)
        ngen: NameGenerator,
        infer_cache: [ExprCache; 2], // [0]=check mode, [1]=infer-only mode
        whnf_core: ExprCache,
        whnf: ExprCache,
        unfold: ExprCache,
        eqv_manager: *mut c_void, // owned EquivManager
        failure: HashSet<(ExprKey, ExprKey)>,
    }

    impl TypeCheckerState {
        unsafe fn new(env: *mut LeanObject) -> Self {
            lean_inc(env);
            let prefix = load_global(&G_KERNEL_FRESH);
            TypeCheckerState {
                env,
                ngen: NameGenerator::new(prefix),
                infer_cache: [HashMap::new(), HashMap::new()],
                whnf_core: HashMap::new(),
                whnf: HashMap::new(),
                unfold: HashMap::new(),
                eqv_manager: lean_equiv_manager_new(),
                failure: HashSet::new(),
            }
        }
    }

    impl Drop for TypeCheckerState {
        fn drop(&mut self) {
            unsafe {
                lean_dec(self.env);
                lean_equiv_manager_free(self.eqv_manager);
            }
        }
    }

    // ---------------------------------------------------------------------------
    // TypeChecker
    // ---------------------------------------------------------------------------

    struct TypeChecker {
        st: Box<TypeCheckerState>,
        lctx: *mut LeanObject, // owned
        definition_safety: u8,
        eager_reduce: bool,
        lparams: Option<*mut LeanObject>, // borrowed, names list
        diag: *mut LeanObject,            // owned `Diagnostics`, or null when disabled
    }

    impl TypeChecker {
        unsafe fn new(env: *mut LeanObject, lctx: *mut LeanObject, definition_safety: u8) -> Self {
            lean_inc(lctx);
            TypeChecker {
                st: Box::new(TypeCheckerState::new(env)),
                lctx,
                definition_safety,
                eager_reduce: false,
                lparams: None,
                diag: ptr::null_mut(),
            }
        }

        /// Record a delta/iota unfold for kernel diagnostics. No-op when diagnostics are disabled.
        /// `name` is BORROWED. Mirrors `diagnostics::record_unfold` (type_checker.cpp).
        #[inline]
        unsafe fn record_unfold(&mut self, name: *mut LeanObject) {
            if !self.diag.is_null() {
                lean_inc(name);
                self.diag = lean_kernel_record_unfold(self.diag, name); // consumes diag + name
            }
        }

        /// Take ownership of the (possibly updated) diagnostics, leaving the field null. Used to thread
        /// the diag across the sequence of type-checkers created within one `add_*` call.
        #[inline]
        fn take_diag(&mut self) -> *mut LeanObject {
            core::mem::replace(&mut self.diag, ptr::null_mut())
        }

        fn env(&self) -> *mut LeanObject {
            self.st.env
        }

        /// Extend the type-checker's environment with `info` (pure insert; CONSUMES `info`).
        /// Mirrors C++ `environment::add_core` followed by recreating `tc()` against the mutated
        /// `m_env`: the reduction caches are cleared because results computed in the old environment
        /// may no longer hold once new declarations exist. `lctx`/`ngen` are kept so fvar ids stay
        /// unique across the whole `add_inductive`. Used by the Rust `add_inductive` port.
        unsafe fn add_core(&mut self, info: *mut LeanObject) {
            // lean_environment_add (= Kernel.Environment.add) CONSUMES both env and info.
            let new_env = lean_environment_add(self.st.env, info);
            self.st.env = new_env;
            self.st.infer_cache[0].clear();
            self.st.infer_cache[1].clear();
            self.st.whnf_core.clear();
            self.st.whnf.clear();
            self.st.unfold.clear();
            self.st.failure.clear();
        }

        unsafe fn with_saved_lctx<R, E, F>(&mut self, f: F) -> Result<R, E>
        where
            F: FnOnce(&mut Self) -> Result<R, E>,
        {
            let saved = self.lctx;
            lean_inc(saved);
            let result = f(self);
            let old = self.lctx;
            self.lctx = saved;
            lean_dec(old);
            result
        }

        /// Create a fresh local declaration in lctx. Returns the fvar expr.
        unsafe fn lctx_mk_local_decl(
            &mut self,
            name: *mut LeanObject,
            ty: *mut LeanObject,
            bi: u8,
        ) -> *mut LeanObject {
            // lean_local_ctx_mk_local_decl returns (fvar, new_lctx) as a pair
            let id = self.st.ngen.mk_fresh_name();
            let result_pair = lean_local_ctx_mk_local_decl(self.lctx, id, name, ty, bi);
            lean_dec(id);
            let fvar = lean_ctor_get(result_pair, 0);
            let new_lctx = lean_ctor_get(result_pair, 1);
            lean_inc(fvar);
            lean_inc(new_lctx);
            lean_dec(result_pair);
            lean_dec(self.lctx);
            self.lctx = new_lctx;
            fvar
        }

        unsafe fn lctx_mk_lambda(
            &self,
            fvars: &[*mut LeanObject],
            body: *mut LeanObject,
        ) -> *mut LeanObject {
            lean_local_ctx_mk_lambda(self.lctx, fvars.as_ptr(), fvars.len() as u32, body)
        }

        unsafe fn lctx_mk_pi(
            &self,
            fvars: &[*mut LeanObject],
            body: *mut LeanObject,
            remove_dead_let: bool,
        ) -> *mut LeanObject {
            lean_local_ctx_mk_pi(
                self.lctx,
                fvars.as_ptr(),
                fvars.len() as u32,
                body,
                remove_dead_let,
            )
        }

        // -----------------------------------------------------------------------
        // Level checking
        // -----------------------------------------------------------------------

        unsafe fn check_level(&self, l: *const LeanObject) -> Result<(), KernelError> {
            if let Some(lparams) = self.lparams {
                if let Some(undef) = get_undef_param(l, lparams) {
                    let msg = format_level_error_msg(undef);
                    return Err(KernelError::Other { msg });
                }
            }
            Ok(())
        }

        // -----------------------------------------------------------------------
        // ensure_sort / ensure_pi
        // -----------------------------------------------------------------------

        unsafe fn ensure_sort_core(
            &mut self,
            e: *mut LeanObject,
            s: *mut LeanObject,
        ) -> Result<*mut LeanObject, KernelError> {
            // CONSUMES `e` (owned), BORROWS `s`, returns an owned sort.
            if lean_expr_is_sort(e) {
                return Ok(e);
            }
            let new_e = self.whnf(e)?; // whnf borrows e
            lean_dec(e); // consume e
            if lean_expr_is_sort(new_e) {
                return Ok(new_e);
            }
            lean_dec(new_e);
            lean_inc(self.st.env);
            lean_inc(self.lctx);
            lean_inc(s);
            Err(KernelError::TypeExpected {
                env: self.st.env,
                lctx: self.lctx,
                expr: s,
            })
        }

        unsafe fn ensure_pi_core(
            &mut self,
            e: *mut LeanObject,
            s: *mut LeanObject,
        ) -> Result<*mut LeanObject, KernelError> {
            // CONSUMES `e` (owned), BORROWS `s`, returns an owned pi.
            if lean_expr_is_pi(e) {
                return Ok(e);
            }
            let new_e = self.whnf(e)?; // whnf borrows e
            lean_dec(e); // consume e
            if lean_expr_is_pi(new_e) {
                return Ok(new_e);
            }
            lean_dec(new_e);
            lean_inc(self.st.env);
            lean_inc(self.lctx);
            lean_inc(s);
            Err(KernelError::FunExpected {
                env: self.st.env,
                lctx: self.lctx,
                expr: s,
            })
        }

        // -----------------------------------------------------------------------
        // infer_fvar
        // -----------------------------------------------------------------------

        unsafe fn infer_fvar(&self, e: *mut LeanObject) -> Result<*mut LeanObject, KernelError> {
            let opt_decl = lean_local_ctx_find_local_decl(self.lctx, e);
            if lean_is_scalar(opt_decl) {
                // None
                lean_inc(self.st.env);
                let msg = lean_mk_string(b"unknown free variable".as_ptr(), 21);
                return Err(KernelError::Other { msg });
            }
            let ty = lean_local_decl_get_type(opt_decl);
            lean_inc(ty);
            lean_dec(opt_decl);
            Ok(ty)
        }

        // -----------------------------------------------------------------------
        // infer_constant
        // -----------------------------------------------------------------------

        unsafe fn infer_constant(
            &mut self,
            e: *mut LeanObject,
            infer_only: bool,
        ) -> Result<*mut LeanObject, KernelError> {
            let name = lean_expr_get_const_name(e);
            let info_opt = env_find(self.st.env, name);
            if lean_is_scalar(info_opt) {
                // not found
                lean_inc(self.st.env);
                lean_inc(name);
                return Err(KernelError::UnknownConstant {
                    env: self.st.env,
                    name,
                });
            }
            let info = info_opt;
            let ps = lean_constant_info_get_lparams(info);
            let ls = lean_expr_get_const_levels(e);
            let ps_len = list_length(ps);
            let ls_len = list_length(ls);
            if ps_len != ls_len {
                let msg = format_arity_error_msg(name, ps_len, ls_len);
                lean_dec(info);
                return Err(KernelError::Other { msg });
            }
            if !infer_only {
                if lean_constant_info_is_unsafe(info) && self.definition_safety != DEF_SAFETY_UNSAFE
                {
                    lean_inc(self.st.env);
                    lean_inc(name);
                    lean_dec(info);
                    let msg_str = format!(
                        "invalid declaration, it uses unsafe declaration '{}'",
                        lean_name_to_string(name)
                    );
                    let msg = lean_mk_string(msg_str.as_ptr(), msg_str.len());
                    return Err(KernelError::Other { msg });
                }
                if lean_constant_info_is_definition(info) {
                    let defval = lean_constant_info_to_definition_val(info);
                    let safety = lean_constant_info_get_safety(defval);
                    if safety == DEF_SAFETY_PARTIAL && self.definition_safety == DEF_SAFETY_SAFE {
                        // `name` is borrowed from `e` (independent of `info`); read it before dropping info.
                        let msg_str = format!(
                            "invalid declaration, safe declaration must not contain partial declaration '{}'",
                            lean_name_to_string(name)
                        );
                        lean_dec(info);
                        let msg = lean_mk_string(msg_str.as_ptr(), msg_str.len());
                        return Err(KernelError::Other { msg });
                    }
                }
                // check each level
                let mut lev = ls;
                while !lean_list_is_nil(lev) {
                    let l = lean_list_head(lev);
                    self.check_level(l)?;
                    lev = lean_list_tail(lev);
                }
            }
            let result = lean_instantiate_type_lparams(info, ls);
            lean_dec(info);
            Ok(result)
        }

        // -----------------------------------------------------------------------
        // infer_lambda
        // -----------------------------------------------------------------------

        unsafe fn infer_lambda(
            &mut self,
            e_orig: *mut LeanObject,
            infer_only: bool,
        ) -> Result<*mut LeanObject, KernelError> {
            self.with_saved_lctx(|tc| {
                let mut fvars: Vec<*mut LeanObject> = Vec::new();
                let mut e = e_orig;
                lean_inc(e);
                while lean_expr_is_lambda(e) {
                    let name = lean_expr_get_binding_name(e);
                    let domain_bv = lean_expr_get_binding_domain(e);
                    let d = if fvars.is_empty() {
                        lean_inc(domain_bv);
                        domain_bv
                    } else {
                        lean_expr_instantiate_rev(domain_bv, fvars.len() as u32, fvars.as_ptr())
                    };
                    if !infer_only {
                        let sort = tc.infer_type_core(d, infer_only)?;
                        lean_dec(tc.ensure_sort_core(sort, d)?); // consumes `sort`; result unused
                    }
                    let bi = lean_expr_get_binding_info(e);
                    let fvar = tc.lctx_mk_local_decl(name, d, bi);
                    lean_dec(d);
                    fvars.push(fvar);
                    let body = lean_expr_get_binding_body(e);
                    let new_e = lean_expr_instantiate1(body, fvar);
                    lean_dec(e);
                    e = new_e;
                }
                let inst = if fvars.is_empty() {
                    lean_inc(e);
                    e
                } else {
                    lean_expr_instantiate_rev(e, fvars.len() as u32, fvars.as_ptr())
                };
                lean_dec(e);
                let mut r = tc.infer_type_core(inst, infer_only)?;
                lean_dec(inst);
                r = lean_expr_cheap_beta_reduce(r);
                // infer_lambda builds a Pi over cdecls (remove_dead_let = false)
                let pi = tc.lctx_mk_pi(&fvars, r, false);
                lean_dec(r);
                for f in &fvars {
                    lean_dec(*f);
                }
                Ok(pi)
            })
        }

        // -----------------------------------------------------------------------
        // infer_pi
        // -----------------------------------------------------------------------

        unsafe fn infer_pi(
            &mut self,
            e_orig: *mut LeanObject,
            infer_only: bool,
        ) -> Result<*mut LeanObject, KernelError> {
            self.with_saved_lctx(|tc| {
                let mut fvars: Vec<*mut LeanObject> = Vec::new();
                let mut us: Vec<*mut LeanObject> = Vec::new(); // levels
                let mut e = e_orig;
                lean_inc(e);
                while lean_expr_is_pi(e) {
                    let domain_bv = lean_expr_get_binding_domain(e);
                    let d =
                        lean_expr_instantiate_rev(domain_bv, fvars.len() as u32, fvars.as_ptr());
                    let d_type = tc.infer_type_core(d, infer_only)?;
                    let t1 = tc.ensure_sort_core(d_type, d)?;
                    us.push(lean_expr_get_sort_level(t1));
                    lean_inc(*us.last().unwrap());
                    lean_dec(t1);
                    let name = lean_expr_get_binding_name(e);
                    let bi = lean_expr_get_binding_info(e);
                    let fvar = tc.lctx_mk_local_decl(name, d, bi);
                    lean_dec(d);
                    fvars.push(fvar);
                    let body = lean_expr_get_binding_body(e);
                    let new_e = lean_expr_instantiate1(body, fvar);
                    lean_dec(e);
                    e = new_e;
                }
                let inst = lean_expr_instantiate_rev(e, fvars.len() as u32, fvars.as_ptr());
                lean_dec(e);
                let inst_type = tc.infer_type_core(inst, infer_only)?;
                let s = tc.ensure_sort_core(inst_type, inst)?;
                lean_dec(inst);
                let mut r_level = lean_expr_get_sort_level(s);
                lean_inc(r_level);
                lean_dec(s);
                // Fold imax right to left. mk_imax/mk_sort consume their args (obj_arg);
                // `us` holds owned levels and `r_level` is owned, so they flow in without dec.
                for level in us.iter().rev() {
                    r_level = lean_level_mk_imax(*level, r_level);
                }
                // The kernel infers Pi sorts with the *smart* `mk_imax`/`mk_max` constructors, which
                // simplify e.g. `imax 1 0 → 0` and `imax 1 1 → 1`. We build with the raw `mk_imax`
                // above, so canonicalise here (normalize_level borrows, returns an owned level).
                let norm = normalize_level(r_level);
                lean_dec(r_level);
                let result = lean_expr_mk_sort(norm);
                for f in &fvars {
                    lean_dec(*f);
                }
                Ok(result)
            })
        }

        // -----------------------------------------------------------------------
        // infer_app
        // -----------------------------------------------------------------------

        unsafe fn infer_app(
            &mut self,
            e: *mut LeanObject,
            infer_only: bool,
        ) -> Result<*mut LeanObject, KernelError> {
            if !infer_only {
                let fn_type = self.infer_type_core(lean_expr_get_app_fn(e), infer_only)?;
                let f_type = self.ensure_pi_core(fn_type, e)?;
                let arg = lean_expr_get_app_arg(e);
                let a_type = self.infer_type_core(arg, infer_only)?;
                let d_type = lean_expr_get_binding_domain(f_type);

                // Detect eagerReduce argument
                let is_eager = is_eager_reduce_expr(arg);
                let saved_eager = self.eager_reduce;
                if is_eager {
                    self.eager_reduce = true;
                }

                let def_eq = self.is_def_eq(a_type, d_type)?;
                if is_eager {
                    self.eager_reduce = saved_eager;
                }

                if !def_eq {
                    lean_inc(self.st.env);
                    lean_inc(self.lctx);
                    lean_inc(e);
                    lean_inc(f_type);
                    lean_inc(a_type);
                    return Err(KernelError::AppTypeMismatch {
                        env: self.st.env,
                        lctx: self.lctx,
                        app: e,
                        fun_type: f_type,
                        arg_type: a_type,
                    });
                }
                lean_dec(a_type);
                let body = lean_expr_get_binding_body(f_type);
                let result = lean_expr_instantiate1(body, arg);
                lean_dec(f_type);
                Ok(result)
            } else {
                // infer-only fast path: collect args, infer f type, thread bindings
                let mut args: Vec<*mut LeanObject> = Vec::new();
                let mut cur = e;
                while lean_expr_is_app(cur) {
                    args.push(lean_expr_get_app_arg(cur));
                    cur = lean_expr_get_app_fn(cur);
                }
                args.reverse();
                let f = cur;
                let mut f_type = self.infer_type_core(f, true)?;
                let mut j = 0usize;
                let nargs = args.len();
                for i in 0..nargs {
                    if lean_expr_is_pi(f_type) {
                        let body = lean_expr_get_binding_body(f_type);
                        // consume binding without substituting yet
                        let old = f_type;
                        lean_inc(body);
                        lean_dec(old);
                        f_type = body;
                    } else {
                        let inst =
                            lean_expr_instantiate_rev(f_type, (i - j) as u32, args[j..i].as_ptr());
                        lean_dec(f_type);
                        f_type = self.ensure_pi_core(inst, e)?;
                        let body = lean_expr_get_binding_body(f_type);
                        lean_inc(body);
                        lean_dec(f_type);
                        f_type = body;
                        j = i;
                    }
                }
                let result =
                    lean_expr_instantiate_rev(f_type, (nargs - j) as u32, args[j..].as_ptr());
                lean_dec(f_type);
                Ok(result)
            }
        }

        // -----------------------------------------------------------------------
        // infer_let
        // -----------------------------------------------------------------------

        unsafe fn infer_let(
            &mut self,
            e_orig: *mut LeanObject,
            infer_only: bool,
        ) -> Result<*mut LeanObject, KernelError> {
            self.with_saved_lctx(|tc| {
                let mut fvars: Vec<*mut LeanObject> = Vec::new();
                let mut e = e_orig;
                lean_inc(e);
                while lean_expr_is_let(e) {
                    let name = lean_expr_get_let_name(e);
                    let ty_bv = lean_expr_get_let_type(e);
                    let val_bv = lean_expr_get_let_value(e);
                    let ty = lean_expr_instantiate_rev(ty_bv, fvars.len() as u32, fvars.as_ptr());
                    let val = lean_expr_instantiate_rev(val_bv, fvars.len() as u32, fvars.as_ptr());
                    if !infer_only {
                        let ty_type = tc.infer_type_core(ty, infer_only)?;
                        lean_dec(tc.ensure_sort_core(ty_type, ty)?); // consumes `ty_type`; result unused
                        let val_type = tc.infer_type_core(val, infer_only)?;
                        if !tc.is_def_eq(val_type, ty)? {
                            lean_inc(tc.st.env);
                            lean_inc(tc.lctx);
                            lean_inc(name);
                            lean_inc(val_type);
                            lean_inc(ty);
                            return Err(KernelError::LetTypeMismatch {
                                env: tc.st.env,
                                lctx: tc.lctx,
                                name,
                                given: val_type,
                                expected: ty,
                            });
                        }
                    }
                    // mk_local_decl_with_value
                    let id = tc.st.ngen.mk_fresh_name();
                    let pair = lean_local_ctx_mk_local_decl_with_value(tc.lctx, id, name, ty, val);
                    lean_dec(id);
                    lean_dec(ty);
                    lean_dec(val);
                    let fvar = lean_ctor_get(pair, 0);
                    let new_lctx = lean_ctor_get(pair, 1);
                    lean_inc(fvar);
                    lean_inc(new_lctx);
                    lean_dec(pair);
                    lean_dec(tc.lctx);
                    tc.lctx = new_lctx;
                    fvars.push(fvar);
                    let body = lean_expr_get_let_body(e);
                    let new_e = lean_expr_instantiate1(body, fvar);
                    lean_dec(e);
                    e = new_e;
                }
                let inst = lean_expr_instantiate_rev(e, fvars.len() as u32, fvars.as_ptr());
                lean_dec(e);
                let mut r = tc.infer_type_core(inst, infer_only)?;
                lean_dec(inst);
                r = lean_expr_cheap_beta_reduce(r);
                // mk_pi with is_let = true (remove_dead_let = true)
                let pi = tc.lctx_mk_pi(&fvars, r, true);
                lean_dec(r);
                for f in &fvars {
                    lean_dec(*f);
                }
                Ok(pi)
            })
        }

        // -----------------------------------------------------------------------
        // infer_proj
        // -----------------------------------------------------------------------

        unsafe fn infer_proj(
            &mut self,
            e: *mut LeanObject,
            infer_only: bool,
        ) -> Result<*mut LeanObject, KernelError> {
            let proj_e = lean_expr_get_proj_expr(e);
            let proj_sname = lean_expr_get_proj_sname(e);
            let proj_idx_nat = lean_expr_get_proj_idx(e);

            if !lean_nat_is_small(proj_idx_nat) {
                lean_inc(self.st.env);
                lean_inc(self.lctx);
                lean_inc(e);
                return Err(KernelError::InvalidProj {
                    env: self.st.env,
                    lctx: self.lctx,
                    proj: e,
                });
            }
            let idx = lean_nat_get_small_value(proj_idx_nat) as usize;

            let proj_e_type_uninferred = self.infer_type_core(proj_e, infer_only)?;
            let ty = self.whnf(proj_e_type_uninferred)?;
            lean_dec(proj_e_type_uninferred);

            // Collect args from the type application
            let mut type_args: Vec<*mut LeanObject> = Vec::new();
            let mut cur = ty;
            while lean_expr_is_app(cur) {
                type_args.push(lean_expr_get_app_arg(cur));
                cur = lean_expr_get_app_fn(cur);
            }
            type_args.reverse();
            let I = cur;

            if !lean_expr_is_const(I) {
                lean_dec(ty);
                lean_inc(self.st.env);
                lean_inc(self.lctx);
                lean_inc(e);
                return Err(KernelError::InvalidProj {
                    env: self.st.env,
                    lctx: self.lctx,
                    proj: e,
                });
            }
            let I_name = lean_expr_get_const_name(I);
            if !lean_name_eq(I_name, proj_sname) {
                lean_dec(ty);
                lean_inc(self.st.env);
                lean_inc(self.lctx);
                lean_inc(e);
                return Err(KernelError::InvalidProj {
                    env: self.st.env,
                    lctx: self.lctx,
                    proj: e,
                });
            }

            let I_info_opt = env_find(self.st.env, I_name);
            if lean_is_scalar(I_info_opt) || !lean_constant_info_is_inductive(I_info_opt) {
                lean_dec(ty);
                lean_inc(self.st.env);
                lean_inc(self.lctx);
                lean_inc(e);
                return Err(KernelError::InvalidProj {
                    env: self.st.env,
                    lctx: self.lctx,
                    proj: e,
                });
            }
            let I_val = lean_constant_info_to_inductive_val(I_info_opt);
            let nparams = lean_inductive_val_get_nparams(I_val) as usize;
            let nindices = lean_inductive_val_get_nindices(I_val) as usize;
            let ncnstrs = lean_inductive_val_get_ncnstrs(I_val);

            if ncnstrs != 1 || type_args.len() != nparams + nindices {
                lean_dec(ty);
                lean_dec(I_info_opt);
                lean_inc(self.st.env);
                lean_inc(self.lctx);
                lean_inc(e);
                return Err(KernelError::InvalidProj {
                    env: self.st.env,
                    lctx: self.lctx,
                    proj: e,
                });
            }

            let cnstr_names = lean_inductive_val_get_cnstrs(I_val);
            let cnstr_name = lean_list_head(cnstr_names);
            let c_info_opt = env_find(self.st.env, cnstr_name);
            let I_levels = lean_expr_get_const_levels(I);
            let mut r = lean_instantiate_type_lparams(c_info_opt, I_levels);
            lean_dec(c_info_opt);
            lean_dec(I_info_opt);

            // Apply parameters
            for i in 0..nparams {
                r = self.whnf(r)?;
                if !lean_expr_is_pi(r) {
                    lean_dec(ty);
                    lean_dec(r);
                    lean_inc(self.st.env);
                    lean_inc(self.lctx);
                    lean_inc(e);
                    return Err(KernelError::InvalidProj {
                        env: self.st.env,
                        lctx: self.lctx,
                        proj: e,
                    });
                }
                let body = lean_expr_get_binding_body(r);
                let new_r = lean_expr_instantiate1(body, type_args[i]);
                lean_dec(r);
                r = new_r;
            }

            let is_prop_type = self.is_prop(ty)?;
            lean_dec(ty);

            // Skip fields up to idx
            for i in 0..idx {
                r = self.whnf(r)?;
                if !lean_expr_is_pi(r) {
                    lean_dec(r);
                    lean_inc(self.st.env);
                    lean_inc(self.lctx);
                    lean_inc(e);
                    return Err(KernelError::InvalidProj {
                        env: self.st.env,
                        lctx: self.lctx,
                        proj: e,
                    });
                }
                if is_prop_type {
                    let dom = lean_expr_get_binding_domain(r);
                    if !self.is_prop(dom)? {
                        lean_dec(r);
                        lean_inc(self.st.env);
                        lean_inc(self.lctx);
                        lean_inc(e);
                        return Err(KernelError::InvalidProj {
                            env: self.st.env,
                            lctx: self.lctx,
                            proj: e,
                        });
                    }
                }
                let body = lean_expr_get_binding_body(r);
                if lean_expr_has_loose_bvars(body) {
                    // mk_proj CONSUMES sname/idx/expr. proj_sname/proj_e are BORROWED from `e`, so
                    // they must be inc'd BEFORE the call — incrementing after lets mk_proj decrement
                    // them to zero (freeing them) and the inc then writes to freed memory.
                    lean_inc(proj_sname);
                    lean_inc(proj_e);
                    let proj_i = lean_expr_mk_proj(proj_sname, lean_nat_mk_obj(i as u64), proj_e);
                    let new_r = lean_expr_instantiate1(body, proj_i);
                    lean_dec(proj_i);
                    lean_dec(r);
                    r = new_r;
                } else {
                    lean_inc(body);
                    lean_dec(r);
                    r = body;
                }
            }

            r = self.whnf(r)?;
            if !lean_expr_is_pi(r) {
                lean_dec(r);
                lean_inc(self.st.env);
                lean_inc(self.lctx);
                lean_inc(e);
                return Err(KernelError::InvalidProj {
                    env: self.st.env,
                    lctx: self.lctx,
                    proj: e,
                });
            }
            let dom = lean_expr_get_binding_domain(r);
            if is_prop_type && !self.is_prop(dom)? {
                lean_dec(r);
                lean_inc(self.st.env);
                lean_inc(self.lctx);
                lean_inc(e);
                return Err(KernelError::InvalidProj {
                    env: self.st.env,
                    lctx: self.lctx,
                    proj: e,
                });
            }
            lean_inc(dom);
            lean_dec(r);
            Ok(dom)
        }

        // -----------------------------------------------------------------------
        // infer_type_core — main dispatch
        // -----------------------------------------------------------------------

        unsafe fn infer_type_core(
            &mut self,
            e: *mut LeanObject,
            infer_only: bool,
        ) -> Result<*mut LeanObject, KernelError> {
            if lean_expr_has_loose_bvars(e) {
                let msg = lean_mk_string(
                    b"type checker does not support loose bound variables".as_ptr(),
                    51,
                );
                return Err(KernelError::Other { msg });
            }

            check_system_result()?;

            let cache_idx = if infer_only { 1 } else { 0 };
            let key = ExprKey::new(e);
            if let Some(v) = self.st.infer_cache[cache_idx].get(&key) {
                let r = v.get();
                lean_inc(r);
                return Ok(r);
            }

            let kind = lean_expr_kind(e);
            let r: *mut LeanObject = match kind {
                EXPR_LIT => {
                    // lit_type returns Nat or String based on literal kind
                    lean_lit_type(e)
                }
                EXPR_MDATA => self.infer_type_core(lean_expr_get_mdata_expr(e), infer_only)?,
                EXPR_PROJ => self.infer_proj(e, infer_only)?,
                EXPR_FVAR => self.infer_fvar(e)?,
                EXPR_MVAR => {
                    let msg = lean_mk_string(
                        b"kernel type checker does not support meta variables".as_ptr(),
                        51,
                    );
                    return Err(KernelError::Other { msg });
                }
                EXPR_BVAR => {
                    // should be unreachable after instantiate
                    let msg =
                        lean_mk_string(b"unexpected bound variable in type checker".as_ptr(), 41);
                    return Err(KernelError::Other { msg });
                }
                EXPR_SORT => {
                    let l = lean_expr_get_sort_level(e);
                    if !infer_only {
                        self.check_level(l)?;
                    }
                    // lean_level_mk_succ / lean_expr_mk_sort both take obj_arg (consume their
                    // argument). `l` is borrowed from `e`, so inc it once to hand an owned
                    // reference to mk_succ; the resulting `l2` is owned and consumed by mk_sort.
                    lean_inc(l);
                    let l2 = lean_level_mk_succ(l);
                    lean_expr_mk_sort(l2)
                }
                EXPR_CONST => self.infer_constant(e, infer_only)?,
                EXPR_LAMBDA => self.infer_lambda(e, infer_only)?,
                EXPR_PI => self.infer_pi(e, infer_only)?,
                EXPR_APP => self.infer_app(e, infer_only)?,
                EXPR_LET => self.infer_let(e, infer_only)?,
                _ => {
                    let msg = lean_mk_string(b"unknown expression kind".as_ptr(), 23);
                    return Err(KernelError::Other { msg });
                }
            };

            // `OwnedLean::new` inc's `r` for the cache; the original owned `r` is returned.
            self.st.infer_cache[cache_idx].insert(ExprKey::new(e), OwnedLean::new(r));
            Ok(r)
        }

        unsafe fn infer_type(
            &mut self,
            e: *mut LeanObject,
        ) -> Result<*mut LeanObject, KernelError> {
            self.infer_type_core(e, true)
        }

        pub unsafe fn infer(&mut self, e: *mut LeanObject) -> Result<*mut LeanObject, KernelError> {
            self.infer_type(e)
        }

        // -----------------------------------------------------------------------
        // is_prop
        // -----------------------------------------------------------------------

        unsafe fn is_prop(&mut self, e: *mut LeanObject) -> Result<bool, KernelError> {
            let ty = self.infer_type(e)?;
            let whnf_ty = self.whnf(ty)?;
            lean_dec(ty);
            let prop = lean_expr_mk_prop();
            let eq = lean_expr_eqv(whnf_ty, prop);
            lean_dec(prop);
            lean_dec(whnf_ty);
            Ok(eq)
        }

        // -----------------------------------------------------------------------
        // reduce_recursor  (iota + quotient reduction)
        // -----------------------------------------------------------------------

        unsafe fn reduce_recursor(
            &mut self,
            e: *mut LeanObject,
            cheap_rec: bool,
            cheap_proj: bool,
        ) -> Result<Option<*mut LeanObject>, KernelError> {
            // Try quotient reduction first (matches C++ reduce_recursor ordering).
            if lean_environment_is_quot_initialized(self.st.env) {
                if let Some(r) = self.quot_reduce_rec(e)? {
                    return Ok(Some(r));
                }
            }

            // Inductive reduction
            let result = inductive_reduce_rec_impl(self.st.env, e, cheap_rec, cheap_proj, self)?;
            Ok(result)
        }

        /// Quotient computation rule — port of `quot_reduce_rec` (quot.h). Reduces
        /// `Quot.lift f h (Quot.mk r a) ↝ f a` and `Quot.ind mk (Quot.mk r a) ↝ mk a`, re-applying any
        /// over-saturated trailing args. `e` is BORROWED; returns an OWNED reduct or `None`.
        unsafe fn quot_reduce_rec(
            &mut self,
            e: *mut LeanObject,
        ) -> Result<Option<*mut LeanObject>, KernelError> {
            // Head constant of the application spine.
            let mut head = e;
            while lean_expr_is_app(head) {
                head = lean_expr_get_app_fn(head);
            }
            if !lean_expr_is_const(head) {
                return Ok(None);
            }
            let head_name = lean_expr_get_const_name(head); // borrowed
            let mk_pos: usize;
            let arg_pos: usize;
            if lean_name_eq(head_name, load_global(&G_QUOT_LIFT_NAME)) {
                mk_pos = QUOT_LIFT_MK_POS;
                arg_pos = QUOT_LIFT_ARG_POS;
            } else if lean_name_eq(head_name, load_global(&G_QUOT_IND_NAME)) {
                mk_pos = QUOT_IND_MK_POS;
                arg_pos = QUOT_IND_ARG_POS;
            } else {
                return Ok(None);
            }

            // Collect args in application order (all borrowed, pointing inside `e`).
            let mut args: Vec<*mut LeanObject> = Vec::new();
            let mut cur = e;
            while lean_expr_is_app(cur) {
                args.push(lean_expr_get_app_arg(cur));
                cur = lean_expr_get_app_fn(cur);
            }
            args.reverse();
            if args.len() <= mk_pos {
                return Ok(None);
            }

            // whnf the major premise (the value that should be a `Quot.mk`).
            let mk_arg = args[mk_pos];
            lean_inc(mk_arg);
            let mk = self.whnf(mk_arg)?; // owned

            // Require `mk` to be exactly `Quot.mk α r a` (a constant head + 3 args).
            let mut mk_head = mk;
            let mut mk_nargs = 0usize;
            while lean_expr_is_app(mk_head) {
                mk_nargs += 1;
                mk_head = lean_expr_get_app_fn(mk_head);
            }
            if !lean_expr_is_const(mk_head)
                || !lean_name_eq(
                    lean_expr_get_const_name(mk_head),
                    load_global(&G_QUOT_MK_NAME),
                )
                || mk_nargs != QUOT_MK_NUM_ARGS
            {
                lean_dec(mk);
                return Ok(None);
            }

            // r := f a, where f = args[arg_pos] and a = last arg of `Quot.mk` (the element).
            let f = args[arg_pos];
            let elem = lean_expr_get_app_arg(mk); // borrowed (inside mk)
            lean_inc(f);
            lean_inc(elem);
            let mut r = lean_expr_mk_app(f, elem); // consumes f + elem
            lean_dec(mk);

            // Re-apply any over-saturated args beyond the eliminator's expected arity.
            let elim_arity = mk_pos + 1;
            for &a in &args[elim_arity..] {
                lean_inc(a);
                r = lean_expr_mk_app(r, a);
            }
            Ok(Some(r))
        }

        // -----------------------------------------------------------------------
        // reduce_proj_core
        // -----------------------------------------------------------------------

        unsafe fn reduce_proj_core(
            &mut self,
            c: *mut LeanObject,
            idx: usize,
        ) -> Result<Option<*mut LeanObject>, KernelError> {
            let c = if lean_expr_is_string_lit(c) {
                let ctor = lean_string_lit_to_constructor(c);
                lean_inc(ctor);
                self.whnf(ctor)?
            } else {
                lean_inc(c);
                c
            };

            let mut args: Vec<*mut LeanObject> = Vec::new();
            let mut cur = c;
            while lean_expr_is_app(cur) {
                args.push(lean_expr_get_app_arg(cur));
                cur = lean_expr_get_app_fn(cur);
            }
            args.reverse();
            let mk = cur;

            if !lean_expr_is_const(mk) {
                lean_dec(c);
                return Ok(None);
            }
            let mk_name = lean_expr_get_const_name(mk);
            let mk_info = env_find(self.st.env, mk_name);
            if lean_is_scalar(mk_info) || !lean_constant_info_is_constructor(mk_info) {
                lean_dec(mk_info);
                lean_dec(c);
                return Ok(None);
            }
            let nparams =
                lean_constructor_val_get_nparams(lean_constant_info_to_constructor_val(mk_info))
                    as usize;
            lean_dec(mk_info);
            if nparams + idx < args.len() {
                let result = args[nparams + idx];
                lean_inc(result);
                lean_dec(c);
                Ok(Some(result))
            } else {
                lean_dec(c);
                Ok(None)
            }
        }

        unsafe fn reduce_proj(
            &mut self,
            e: *mut LeanObject,
            cheap_rec: bool,
            cheap_proj: bool,
        ) -> Result<Option<*mut LeanObject>, KernelError> {
            let idx_nat = lean_expr_get_proj_idx(e);
            if !lean_nat_is_small(idx_nat) {
                return Ok(None);
            }
            let idx = lean_nat_get_small_value(idx_nat) as usize;
            let proj_e = lean_expr_get_proj_expr(e);
            let c = if cheap_proj {
                self.whnf_core(proj_e, cheap_rec, cheap_proj)?
            } else {
                self.whnf(proj_e)?
            };
            let result = self.reduce_proj_core(c, idx)?;
            lean_dec(c);
            Ok(result)
        }

        // -----------------------------------------------------------------------
        // whnf_fvar
        // -----------------------------------------------------------------------

        unsafe fn whnf_fvar(
            &mut self,
            e: *mut LeanObject,
            cheap_rec: bool,
            cheap_proj: bool,
        ) -> Result<*mut LeanObject, KernelError> {
            let opt_decl = lean_local_ctx_find_local_decl(self.lctx, e);
            if !lean_is_scalar(opt_decl) && lean_local_decl_has_value(opt_decl) {
                let val = lean_local_decl_get_value(opt_decl);
                lean_inc(val);
                lean_dec(opt_decl);
                return self.whnf_core(val, cheap_rec, cheap_proj);
            }
            lean_dec(opt_decl);
            lean_inc(e);
            Ok(e)
        }

        // -----------------------------------------------------------------------
        // whnf_core
        // -----------------------------------------------------------------------

        unsafe fn whnf_core(
            &mut self,
            e: *mut LeanObject,
            cheap_rec: bool,
            cheap_proj: bool,
        ) -> Result<*mut LeanObject, KernelError> {
            check_system_result()?;

            let kind = lean_expr_kind(e);
            // Fast path for non-reducing cases
            match kind {
                EXPR_BVAR | EXPR_SORT | EXPR_MVAR | EXPR_PI | EXPR_CONST | EXPR_LAMBDA
                | EXPR_LIT => {
                    lean_inc(e);
                    return Ok(e);
                }
                EXPR_MDATA => {
                    return self.whnf_core(lean_expr_get_mdata_expr(e), cheap_rec, cheap_proj);
                }
                EXPR_FVAR => {
                    let opt_decl = lean_local_ctx_find_local_decl(self.lctx, e);
                    let has_val = !lean_is_scalar(opt_decl) && lean_local_decl_has_value(opt_decl);
                    lean_dec(opt_decl);
                    if !has_val {
                        lean_inc(e);
                        return Ok(e);
                    }
                    // fall through to main work
                }
                EXPR_APP | EXPR_LET | EXPR_PROJ => {
                    // fall through
                }
                _ => {
                    lean_inc(e);
                    return Ok(e);
                }
            }

            // Check whnf_core cache (only when not using cheap mode)
            if !cheap_rec && !cheap_proj {
                let key = ExprKey::new(e);
                if let Some(v) = self.st.whnf_core.get(&key) {
                    let r = v.get();
                    lean_inc(r);
                    return Ok(r);
                }
            }

            let r: *mut LeanObject = match lean_expr_kind(e) {
                EXPR_FVAR => {
                    // C++ `whnf_core` does `return whnf_fvar(...)` — early return, NOT cached.
                    return self.whnf_fvar(e, cheap_rec, cheap_proj);
                }
                EXPR_PROJ => {
                    if let Some(m) = self.reduce_proj(e, cheap_rec, cheap_proj)? {
                        let result = self.whnf_core(m, cheap_rec, cheap_proj)?;
                        lean_dec(m);
                        result
                    } else {
                        lean_inc(e);
                        e
                    }
                }
                EXPR_APP => {
                    let mut args: Vec<*mut LeanObject> = Vec::new();
                    let mut cur = e;
                    while lean_expr_is_app(cur) {
                        args.push(lean_expr_get_app_arg(cur));
                        cur = lean_expr_get_app_fn(cur);
                    }
                    args.reverse();
                    // cur is now the function
                    let f0 = cur;
                    let f = self.whnf_core(f0, cheap_rec, cheap_proj)?;

                    if lean_expr_is_lambda(f) {
                        // Beta reduction
                        let mut f_cur = f;
                        let mut m = 1usize;
                        let num_args = args.len();
                        while lean_expr_is_lambda(lean_expr_get_binding_body(f_cur)) && m < num_args
                        {
                            f_cur = lean_expr_get_binding_body(f_cur);
                            m += 1;
                        }
                        let body = lean_expr_get_binding_body(f_cur);
                        // The lambda consumes the first `m` arguments (application order). C++ uses
                        // `instantiate` over a reversed buffer; the equivalent here is `instantiate_rev`
                        // over the first `m` args in application order: instantiate_rev maps
                        // bvar#i -> subst[m-1-i], so x0<-args[0] .. x_{m-1}<-args[m-1].
                        let inst = lean_expr_instantiate_rev(body, m as u32, args.as_ptr());
                        // apply the remaining args (application order). lean_expr_mk_app consumes both
                        // arguments, so inc each borrowed arg and let the previous `app` flow in.
                        let mut app = inst;
                        for &arg in &args[m..] {
                            lean_inc(arg);
                            app = lean_expr_mk_app(app, arg);
                        }
                        lean_dec(f);
                        let result = self.whnf_core(app, cheap_rec, cheap_proj)?;
                        lean_dec(app);
                        result
                    } else if lean_expr_is_eqp(f, f0) {
                        // Try recursor
                        lean_inc(e);
                        if let Some(r) = self.reduce_recursor(e, cheap_rec, cheap_proj)? {
                            // Record the iota/quot unfold for kernel diagnostics (head const of `e`).
                            if !self.diag.is_null() {
                                let mut head = e;
                                while lean_expr_is_app(head) {
                                    head = lean_expr_get_app_fn(head);
                                }
                                if lean_expr_is_const(head) {
                                    self.record_unfold(lean_expr_get_const_name(head));
                                }
                            }
                            lean_dec(e);
                            lean_dec(f);
                            let result = self.whnf_core(r, cheap_rec, cheap_proj)?;
                            lean_dec(r);
                            // C++ does `return whnf_core(*r, ...)` here — early return, NOT cached.
                            // Caching iota/recursor results diverges from C++: it suppresses re-reductions
                            // (wrong kernel-diagnostics unfold counts) and balloons the whnf_core cache on
                            // recursor-heavy proofs (bv_decide/grind) → memory pressure + slow lookups.
                            return Ok(result);
                        } else {
                            lean_dec(f);
                            lean_dec(e);
                            lean_inc(e);
                            // C++ does `return e` here (stuck recursor) — early return, NOT cached.
                            return Ok(e);
                        }
                    } else {
                        // rebuild application with reduced function. mk_app consumes both args.
                        let mut app = f;
                        for &arg in &args {
                            lean_inc(arg);
                            app = lean_expr_mk_app(app, arg);
                        }
                        let result = self.whnf_core(app, cheap_rec, cheap_proj)?;
                        lean_dec(app);
                        result
                    }
                }
                EXPR_LET => {
                    // `Expr.letE` lays out [name, type, value, body]; the body is field 3.
                    // `get_binding_body` is field 2 (Lambda/Pi layout) — for a `let` that is the
                    // *value*, so we must use `get_let_body` here, else `let g := v; body` would
                    // instantiate `v` into `v` and reduce to `v`.
                    let val = lean_expr_get_let_value(e);
                    let body = lean_expr_get_let_body(e);
                    let inst = lean_expr_instantiate1(body, val);
                    let result = self.whnf_core(inst, cheap_rec, cheap_proj)?;
                    lean_dec(inst);
                    result
                }
                _ => {
                    lean_inc(e);
                    e
                }
            };

            if !cheap_rec && !cheap_proj {
                self.st.whnf_core.insert(ExprKey::new(e), OwnedLean::new(r));
            }
            Ok(r)
        }

        // -----------------------------------------------------------------------
        // unfold_definition
        // -----------------------------------------------------------------------

        unsafe fn unfold_definition_core(
            &mut self,
            e: *const LeanObject,
        ) -> Option<*mut LeanObject> {
            if !lean_expr_is_const(e) {
                return None;
            }
            let name = lean_expr_get_const_name(e);
            let info_opt = env_find(self.st.env, name);
            if lean_is_scalar(info_opt) {
                return None;
            }
            if !lean_constant_info_has_value(info_opt) {
                lean_dec(info_opt);
                return None;
            }
            let nparams = lean_constant_info_get_num_lparams(info_opt) as usize;
            let levels = lean_expr_get_const_levels(e);
            let levels_len = list_length(levels);
            if nparams != levels_len {
                lean_dec(info_opt);
                return None;
            }

            // is_delta succeeded — record the delta unfold for kernel diagnostics (matches C++
            // unfold_definition_core, which records on every call, including cache hits).
            self.record_unfold(name);

            let levels_obj = levels;
            // Check unfold cache
            let key = ExprKey::new(e as *mut LeanObject);
            if let Some(v) = self.st.unfold.get(&key) {
                lean_dec(info_opt);
                let r = v.get();
                lean_inc(r);
                return Some(r);
            }
            let result = lean_instantiate_value_lparams(info_opt, levels_obj);
            lean_dec(info_opt);
            // `OwnedLean::new` inc's `result` for the cache; the original owned `result` is returned.
            if levels_len > 0 {
                self.st
                    .unfold
                    .insert(ExprKey::new(e as *mut LeanObject), OwnedLean::new(result));
            }
            Some(result)
        }

        unsafe fn unfold_definition(&mut self, e: *const LeanObject) -> Option<*mut LeanObject> {
            if lean_expr_is_app(e) {
                // `lean_expr_get_app_fn` strips a single application layer; walk to the spine head.
                let mut f0 = e;
                while lean_expr_is_app(f0) {
                    f0 = lean_expr_get_app_fn(f0);
                }
                if let Some(f) = self.unfold_definition_core(f0) {
                    // rebuild with args
                    let mut args: Vec<*mut LeanObject> = Vec::new();
                    let mut cur = e;
                    while lean_expr_is_app(cur) {
                        args.push(lean_expr_get_app_arg(cur));
                        cur = lean_expr_get_app_fn(cur);
                    }
                    // args are in reverse order. mk_app consumes both arguments.
                    let mut app = f;
                    for &arg in args.iter().rev() {
                        lean_inc(arg);
                        app = lean_expr_mk_app(app, arg);
                    }
                    Some(app)
                } else {
                    None
                }
            } else {
                self.unfold_definition_core(e)
            }
        }

        // -----------------------------------------------------------------------
        // reduce_nat / reduce_native
        // -----------------------------------------------------------------------

        unsafe fn reduce_nat(
            &mut self,
            e: *mut LeanObject,
        ) -> Result<Option<*mut LeanObject>, KernelError> {
            let nargs = lean_expr_get_app_num_args(e);
            if nargs == 1 {
                let f = lean_expr_get_app_fn(e);
                let nat_succ = load_global(&G_NAT_SUCC);
                if lean_expr_eqv(f, nat_succ) {
                    let arg_r = self.whnf(lean_expr_get_app_arg(e))?;
                    let result = reduce_nat_succ(arg_r);
                    lean_dec(arg_r);
                    return Ok(result);
                }
            } else if nargs == 2 {
                let f = lean_expr_get_app_fn(lean_expr_get_app_fn(e));
                if !lean_expr_is_const(f) {
                    return Ok(None);
                }
                let result = self.reduce_bin_nat_op(e, f)?;
                return Ok(result);
            }
            Ok(None)
        }

        /// True when `f` is one of the binary `Nat` operations handled by `reduce_bin_nat_op`.
        /// C++ `reduce_nat` dispatches on `f == *g_nat_*` *before* touching the arguments, so a
        /// 2-arg application whose head is not a `Nat` op (e.g. `String.ofByteArray (utf8Encode l) p`)
        /// must never have its arguments reduced — otherwise we needlessly force the `utf8Encode`
        /// (byte-encoding) reduction and blow up the kernel unfold count.
        unsafe fn is_nat_bin_op(&self, f: *const LeanObject) -> bool {
            lean_expr_eqv(f, load_global(&G_NAT_ADD))
                || lean_expr_eqv(f, load_global(&G_NAT_SUB))
                || lean_expr_eqv(f, load_global(&G_NAT_MUL))
                || lean_expr_eqv(f, load_global(&G_NAT_DIV))
                || lean_expr_eqv(f, load_global(&G_NAT_MOD))
                || lean_expr_eqv(f, load_global(&G_NAT_GCD))
                || lean_expr_eqv(f, load_global(&G_NAT_LAND))
                || lean_expr_eqv(f, load_global(&G_NAT_LOR))
                || lean_expr_eqv(f, load_global(&G_NAT_XOR))
                || lean_expr_eqv(f, load_global(&G_NAT_SHIFTLEFT))
                || lean_expr_eqv(f, load_global(&G_NAT_SHIFTRIGHT))
                || lean_expr_eqv(f, load_global(&G_NAT_POW))
                || lean_expr_eqv(f, load_global(&G_NAT_BEQ))
                || lean_expr_eqv(f, load_global(&G_NAT_BLE))
        }

        unsafe fn reduce_bin_nat_op(
            &mut self,
            e: *mut LeanObject,
            f: *mut LeanObject,
        ) -> Result<Option<*mut LeanObject>, KernelError> {
            // Match C++: bail out before reducing the arguments unless `f` is a known Nat op.
            if !self.is_nat_bin_op(f) {
                return Ok(None);
            }
            let arg1 = self.whnf(lean_expr_get_app_arg(lean_expr_get_app_fn(e)))?;
            if !is_nat_lit_ext(arg1) {
                lean_dec(arg1);
                return Ok(None);
            }
            let arg2 = self.whnf(lean_expr_get_app_arg(e))?;
            if !is_nat_lit_ext(arg2) {
                lean_dec(arg1);
                lean_dec(arg2);
                return Ok(None);
            }
            // v1/v2 are BORROWED out of arg1/arg2 (they may point inside the literals).
            // We must keep arg1/arg2 alive until we are done reading v1/v2, so the
            // decrements happen only after the computation below. lean_nat_* BORROW
            // their operands and return an owned result.
            let v1 = get_nat_val(arg1);
            let v2 = get_nat_val(arg2);

            let result: Option<*mut LeanObject> = 'compute: {
                // Nat.add, Nat.sub, Nat.mul, Nat.div, Nat.mod, Nat.gcd, Nat.land, Nat.lor, Nat.xor
                if lean_expr_eqv(f, load_global(&G_NAT_ADD)) {
                    break 'compute Some(lean_expr_mk_lit_nat(lean_nat_add(v1, v2)));
                }
                if lean_expr_eqv(f, load_global(&G_NAT_SUB)) {
                    break 'compute Some(lean_expr_mk_lit_nat(lean_nat_sub(v1, v2)));
                }
                if lean_expr_eqv(f, load_global(&G_NAT_MUL)) {
                    break 'compute Some(lean_expr_mk_lit_nat(lean_nat_mul(v1, v2)));
                }
                if lean_expr_eqv(f, load_global(&G_NAT_DIV)) {
                    break 'compute Some(lean_expr_mk_lit_nat(lean_nat_div(v1, v2)));
                }
                if lean_expr_eqv(f, load_global(&G_NAT_MOD)) {
                    break 'compute Some(lean_expr_mk_lit_nat(lean_nat_mod(v1, v2)));
                }
                if lean_expr_eqv(f, load_global(&G_NAT_GCD)) {
                    break 'compute Some(lean_expr_mk_lit_nat(lean_nat_gcd(v1, v2)));
                }
                if lean_expr_eqv(f, load_global(&G_NAT_LAND)) {
                    break 'compute Some(lean_expr_mk_lit_nat(lean_nat_land(v1, v2)));
                }
                if lean_expr_eqv(f, load_global(&G_NAT_LOR)) {
                    break 'compute Some(lean_expr_mk_lit_nat(lean_nat_lor(v1, v2)));
                }
                if lean_expr_eqv(f, load_global(&G_NAT_XOR)) {
                    break 'compute Some(lean_expr_mk_lit_nat(lean_nat_xor(v1, v2)));
                }
                if lean_expr_eqv(f, load_global(&G_NAT_SHIFTLEFT)) {
                    break 'compute Some(lean_expr_mk_lit_nat(lean_nat_shiftl(v1, v2)));
                }
                if lean_expr_eqv(f, load_global(&G_NAT_SHIFTRIGHT)) {
                    break 'compute Some(lean_expr_mk_lit_nat(lean_nat_shiftr(v1, v2)));
                }
                if lean_expr_eqv(f, load_global(&G_NAT_POW)) {
                    const MAX_EXP: u64 = 1 << 24;
                    if lean_nat_is_small(v2) && (lean_nat_get_small_value(v2) as u64) <= MAX_EXP {
                        break 'compute Some(lean_expr_mk_lit_nat(lean_nat_pow(v1, v2, MAX_EXP)));
                    } else {
                        break 'compute None;
                    }
                }
                if lean_expr_eqv(f, load_global(&G_NAT_BEQ)) {
                    break 'compute Some(mk_bool(lean_nat_beq(v1, v2)));
                }
                if lean_expr_eqv(f, load_global(&G_NAT_BLE)) {
                    break 'compute Some(mk_bool(lean_nat_ble(v1, v2)));
                }
                None
            };

            lean_dec(arg1);
            lean_dec(arg2);
            Ok(result)
        }

        unsafe fn reduce_native(&self, e: *const LeanObject) -> Option<*mut LeanObject> {
            if !lean_expr_is_app(e) {
                return None;
            }
            let arg = lean_expr_get_app_arg(e);
            if !lean_expr_is_const(arg) {
                return None;
            }
            let f = lean_expr_get_app_fn(e);
            let reduce_bool = load_global(&G_LEAN_REDUCE_BOOL);
            let reduce_nat = load_global(&G_LEAN_REDUCE_NAT);
            if lean_expr_eqv(f, reduce_bool) {
                let name = lean_expr_get_const_name(arg);
                let opts = lean_mk_empty_options();
                let r = lean_ir_run_boxed_kernel(self.st.env, opts, name, 0, ptr::null());
                lean_dec(opts);
                if lean_is_scalar(r) {
                    Some(mk_bool(lean_unbox(r) != 0))
                } else {
                    lean_dec(r);
                    None // error handled in C++ by throwing; here we just skip
                }
            } else if lean_expr_eqv(f, reduce_nat) {
                let name = lean_expr_get_const_name(arg);
                let opts = lean_mk_empty_options();
                let r = lean_ir_run_boxed_kernel(self.st.env, opts, name, 0, ptr::null());
                lean_dec(opts);
                Some(lean_expr_mk_lit_nat(r))
            } else {
                None
            }
        }

        // -----------------------------------------------------------------------
        // whnf (full)
        // -----------------------------------------------------------------------

        unsafe fn whnf(&mut self, e: *mut LeanObject) -> Result<*mut LeanObject, KernelError> {
            // Fast no-cache cases
            let kind = lean_expr_kind(e);
            match kind {
                EXPR_BVAR | EXPR_SORT | EXPR_MVAR | EXPR_PI | EXPR_LIT => {
                    lean_inc(e);
                    return Ok(e);
                }
                EXPR_MDATA => {
                    return self.whnf(lean_expr_get_mdata_expr(e));
                }
                EXPR_FVAR => {
                    let opt_decl = lean_local_ctx_find_local_decl(self.lctx, e);
                    let has_val = !lean_is_scalar(opt_decl) && lean_local_decl_has_value(opt_decl);
                    lean_dec(opt_decl);
                    if !has_val {
                        lean_inc(e);
                        return Ok(e);
                    }
                }
                _ => {}
            }

            // Check whnf cache
            let key = ExprKey::new(e);
            if let Some(v) = self.st.whnf.get(&key) {
                let r = v.get();
                lean_inc(r);
                return Ok(r);
            }

            let mut t = e;
            lean_inc(t);
            loop {
                let t1 = self.whnf_core(t, false, false)?;
                lean_dec(t);
                // In each return path `OwnedLean::new` inc's for the cache, and the original
                // owned value (`cached`/`v`/`t1`) is returned — no extra inc (that would leak).
                if let Some(v) = self.reduce_native(t1) {
                    let cached = v;
                    self.st.whnf.insert(ExprKey::new(e), OwnedLean::new(cached));
                    lean_dec(t1);
                    return Ok(cached);
                }
                if let Some(v) = self.reduce_nat(t1)? {
                    self.st.whnf.insert(ExprKey::new(e), OwnedLean::new(v));
                    lean_dec(t1);
                    return Ok(v);
                }
                if let Some(next) = self.unfold_definition(t1) {
                    lean_dec(t1);
                    t = next;
                } else {
                    let r = t1;
                    self.st.whnf.insert(ExprKey::new(e), OwnedLean::new(r));
                    return Ok(r);
                }
            }
        }

        // -----------------------------------------------------------------------
        // is_delta
        // -----------------------------------------------------------------------

        unsafe fn is_delta(&self, e: *const LeanObject) -> Option<*mut LeanObject> {
            let f = app_head(e as *mut _);
            if !lean_expr_is_const(f) {
                return None;
            }
            let name = lean_expr_get_const_name(f);
            let info_opt = env_find(self.st.env, name);
            if lean_is_scalar(info_opt) {
                return None;
            }
            if !lean_constant_info_has_value(info_opt) {
                lean_dec(info_opt);
                return None;
            }
            let ps_len = lean_constant_info_get_num_lparams(info_opt) as usize;
            let ls_len = list_length(lean_expr_get_const_levels(f));
            if ps_len != ls_len {
                lean_dec(info_opt);
                return None;
            }
            Some(info_opt) // caller must dec
        }

        // -----------------------------------------------------------------------
        // is_def_eq helpers
        // -----------------------------------------------------------------------

        unsafe fn quick_is_def_eq(
            &mut self,
            t: *mut LeanObject,
            s: *mut LeanObject,
            use_hash: bool,
        ) -> Result<LBool, KernelError> {
            if lean_equiv_manager_is_equiv(self.st.eqv_manager, t, s, use_hash) {
                return Ok(LBool::True);
            }
            let kt = lean_expr_kind(t);
            let ks = lean_expr_kind(s);
            if kt == ks {
                match kt {
                    EXPR_LAMBDA | EXPR_PI => {
                        return Ok(LBool::from_bool(self.is_def_eq_binding(t, s)?));
                    }
                    EXPR_SORT => {
                        let lt = lean_expr_get_sort_level(t);
                        let ls_l = lean_expr_get_sort_level(s);
                        return Ok(LBool::from_bool(is_equivalent_level(lt, ls_l)?));
                    }
                    EXPR_MDATA => {
                        return self.quick_is_def_eq(
                            lean_expr_get_mdata_expr(t),
                            lean_expr_get_mdata_expr(s),
                            use_hash,
                        );
                    }
                    EXPR_LIT => {
                        return Ok(LBool::from_bool(lean_expr_eqv(t, s)));
                    }
                    _ => {}
                }
            }
            Ok(LBool::Undef)
        }

        unsafe fn is_def_eq_binding(
            &mut self,
            mut t: *mut LeanObject,
            mut s: *mut LeanObject,
        ) -> Result<bool, KernelError> {
            // Both must be lambda or both pi
            let k = lean_expr_kind(t);
            let mut subst: Vec<*mut LeanObject> = Vec::new();

            self.with_saved_lctx(|tc| {
                loop {
                    let dom_t = lean_expr_get_binding_domain(t);
                    let dom_s = lean_expr_get_binding_domain(s);
                    let mut var_s_type: Option<*mut LeanObject> = None;
                    if !lean_expr_eqv(dom_t, dom_s) {
                        let inst_s =
                            lean_expr_instantiate_rev(dom_s, subst.len() as u32, subst.as_ptr());
                        let inst_t =
                            lean_expr_instantiate_rev(dom_t, subst.len() as u32, subst.as_ptr());
                        let eq = tc.is_def_eq(inst_t, inst_s)?;
                        lean_dec(inst_t);
                        if !eq {
                            lean_dec(inst_s);
                            return Ok(false);
                        }
                        var_s_type = Some(inst_s);
                    }
                    let body_t = lean_expr_get_binding_body(t);
                    let body_s = lean_expr_get_binding_body(s);
                    if lean_expr_has_loose_bvars(body_t) || lean_expr_has_loose_bvars(body_s) {
                        let s_type = if let Some(st) = var_s_type {
                            st
                        } else {
                            lean_expr_instantiate_rev(dom_s, subst.len() as u32, subst.as_ptr())
                        };
                        let bi = lean_expr_get_binding_info(s);
                        let name = lean_expr_get_binding_name(s);
                        let fvar = tc.lctx_mk_local_decl(name, s_type, bi);
                        lean_dec(s_type);
                        subst.push(fvar);
                    } else {
                        if let Some(st) = var_s_type {
                            lean_dec(st);
                        }
                        let dont_care = load_global(&G_DONT_CARE);
                        lean_inc(dont_care);
                        subst.push(dont_care);
                    }

                    t = body_t;
                    s = body_s;
                    if lean_expr_kind(t) != k || lean_expr_kind(s) != k {
                        break;
                    }
                }
                let inst_t = lean_expr_instantiate_rev(t, subst.len() as u32, subst.as_ptr());
                let inst_s = lean_expr_instantiate_rev(s, subst.len() as u32, subst.as_ptr());
                let result = tc.is_def_eq(inst_t, inst_s)?;
                lean_dec(inst_t);
                lean_dec(inst_s);
                for f in &subst {
                    lean_dec(*f);
                }
                Ok(result)
            })
        }

        unsafe fn is_def_eq_args(
            &mut self,
            mut t: *mut LeanObject,
            mut s: *mut LeanObject,
        ) -> Result<bool, KernelError> {
            while lean_expr_is_app(t) && lean_expr_is_app(s) {
                if !self.is_def_eq(lean_expr_get_app_arg(t), lean_expr_get_app_arg(s))? {
                    return Ok(false);
                }
                t = lean_expr_get_app_fn(t);
                s = lean_expr_get_app_fn(s);
            }
            Ok(!lean_expr_is_app(t) && !lean_expr_is_app(s))
        }

        unsafe fn try_eta_expansion_core(
            &mut self,
            t: *mut LeanObject,
            s: *mut LeanObject,
        ) -> Result<bool, KernelError> {
            if lean_expr_is_lambda(t) && !lean_expr_is_lambda(s) {
                let s_inferred = self.infer_type(s)?;
                let s_type = self.whnf(s_inferred)?;
                if !lean_expr_is_pi(s_type) {
                    lean_dec(s_type);
                    return Ok(false);
                }
                let name = lean_expr_get_binding_name(s_type);
                let dom = lean_expr_get_binding_domain(s_type);
                let bi = lean_expr_get_binding_info(s_type);
                // mk_app/mk_lambda consume their args (obj_arg): inc the borrowed s/name/dom,
                // and let the freshly built bvar/app flow in without dec.
                lean_inc(s);
                let app = lean_expr_mk_app(s, lean_expr_mk_bvar(lean_box(0)));
                lean_inc(name);
                lean_inc(dom);
                let new_s = lean_expr_mk_lambda(name, dom, app, bi);
                lean_dec(s_type);
                let result = self.is_def_eq(t, new_s)?;
                lean_dec(new_s);
                Ok(result)
            } else {
                Ok(false)
            }
        }

        unsafe fn try_eta_struct_core(
            &mut self,
            t: *mut LeanObject,
            s: *mut LeanObject,
        ) -> Result<bool, KernelError> {
            let f = app_head(s);
            if !lean_expr_is_const(f) {
                return Ok(false);
            }
            let f_name = lean_expr_get_const_name(f);
            let f_info_opt = env_find(self.st.env, f_name);
            if lean_is_scalar(f_info_opt) || !lean_constant_info_is_constructor(f_info_opt) {
                lean_dec(f_info_opt);
                return Ok(false);
            }
            let f_val = lean_constant_info_to_constructor_val(f_info_opt);
            let nparams = lean_constructor_val_get_nparams(f_val) as usize;
            let nfields = lean_constructor_val_get_nfields(f_val) as usize;
            let s_nargs = lean_expr_get_app_num_args(s) as usize;
            if s_nargs != nparams + nfields {
                lean_dec(f_info_opt);
                return Ok(false);
            }
            let induct_name = lean_constructor_val_get_induct(f_val);
            if !is_non_rec_structure_name(self.st.env, induct_name) {
                lean_dec(f_info_opt);
                return Ok(false);
            }
            lean_dec(f_info_opt);

            let t_type = self.infer_type(t)?;
            let s_type = self.infer_type(s)?;
            if !self.is_def_eq(t_type, s_type)? {
                lean_dec(t_type);
                lean_dec(s_type);
                return Ok(false);
            }
            lean_dec(t_type);
            lean_dec(s_type);

            // Collect s args
            let mut s_args: Vec<*mut LeanObject> = Vec::new();
            let mut cur = s;
            while lean_expr_is_app(cur) {
                s_args.push(lean_expr_get_app_arg(cur));
                cur = lean_expr_get_app_fn(cur);
            }
            s_args.reverse();

            for i in nparams..s_args.len() {
                let proj_idx = lean_nat_mk_obj((i - nparams) as u64); // owned, consumed by mk_proj
                lean_inc(induct_name);
                lean_inc(t);
                let proj = lean_expr_mk_proj(induct_name, proj_idx, t);
                if !self.is_def_eq(proj, s_args[i])? {
                    lean_dec(proj);
                    return Ok(false);
                }
                lean_dec(proj);
            }
            Ok(true)
        }

        unsafe fn is_def_eq_app(
            &mut self,
            t: *mut LeanObject,
            s: *mut LeanObject,
        ) -> Result<bool, KernelError> {
            if lean_expr_is_app(t) && lean_expr_is_app(s) {
                let mut t_args: Vec<*mut LeanObject> = Vec::new();
                let mut s_args: Vec<*mut LeanObject> = Vec::new();
                let mut tc = t;
                let mut sc = s;
                while lean_expr_is_app(tc) {
                    t_args.push(lean_expr_get_app_arg(tc));
                    tc = lean_expr_get_app_fn(tc);
                }
                while lean_expr_is_app(sc) {
                    s_args.push(lean_expr_get_app_arg(sc));
                    sc = lean_expr_get_app_fn(sc);
                }
                t_args.reverse();
                s_args.reverse();
                let t_fn = tc;
                let s_fn = sc;
                if t_args.len() == s_args.len() && self.is_def_eq(t_fn, s_fn)? {
                    for (ta, sa) in t_args.iter().zip(s_args.iter()) {
                        if !self.is_def_eq(*ta, *sa)? {
                            return Ok(false);
                        }
                    }
                    return Ok(true);
                }
            }
            Ok(false)
        }

        unsafe fn is_def_eq_proof_irrel(
            &mut self,
            t: *mut LeanObject,
            s: *mut LeanObject,
        ) -> Result<LBool, KernelError> {
            let t_type = self.infer_type(t)?;
            if !self.is_prop(t_type)? {
                lean_dec(t_type);
                return Ok(LBool::Undef);
            }
            lean_dec(t_type);
            let s_type = self.infer_type(s)?;
            let t_type2 = self.infer_type(t)?;
            let r = self.is_def_eq(t_type2, s_type)?;
            lean_dec(s_type);
            lean_dec(t_type2);
            Ok(LBool::from_bool(r))
        }

        unsafe fn is_def_eq_unit_like(
            &mut self,
            t: *mut LeanObject,
            s: *mut LeanObject,
        ) -> Result<bool, KernelError> {
            let t_type_raw = self.infer_type(t)?;
            let t_type = self.whnf(t_type_raw)?;
            lean_dec(t_type_raw);
            let I = app_head(t_type);
            if !lean_expr_is_const(I) {
                lean_dec(t_type);
                return Ok(false);
            }
            let I_name = lean_expr_get_const_name(I);
            if !is_non_rec_structure_name(self.st.env, I_name) {
                lean_dec(t_type);
                return Ok(false);
            }
            let I_info = env_find(self.st.env, I_name);
            if lean_is_scalar(I_info) {
                lean_dec(t_type);
                return Ok(false);
            }
            let I_val = lean_constant_info_to_inductive_val(I_info);
            let cnstrs = lean_inductive_val_get_cnstrs(I_val);
            let ctor_name = lean_list_head(cnstrs);
            let ctor_info = env_find(self.st.env, ctor_name);
            lean_dec(I_info);
            if lean_is_scalar(ctor_info) {
                lean_dec(t_type);
                return Ok(false);
            }
            let ctor_val = lean_constant_info_to_constructor_val(ctor_info);
            if lean_constructor_val_get_nfields(ctor_val) != 0 {
                lean_dec(ctor_info);
                lean_dec(t_type);
                return Ok(false);
            }
            lean_dec(ctor_info);
            let s_type = self.infer_type(s)?;
            let r = self.is_def_eq(t_type, s_type)?;
            lean_dec(t_type);
            lean_dec(s_type);
            Ok(r)
        }

        unsafe fn failed_before(&self, t: *const LeanObject, s: *const LeanObject) -> bool {
            let ht = expr_hash(t);
            let hs = expr_hash(s);
            let key = if ht <= hs {
                (ExprKey(t), ExprKey(s))
            } else {
                (ExprKey(s), ExprKey(t))
            };
            let result = self.st.failure.contains(&key);
            std::mem::forget(key); // Don't drop, no ownership
            result
        }

        unsafe fn cache_failure(&mut self, t: *mut LeanObject, s: *mut LeanObject) {
            let ht = expr_hash(t);
            let hs = expr_hash(s);
            if ht <= hs {
                self.st.failure.insert((ExprKey::new(t), ExprKey::new(s)));
            } else {
                self.st.failure.insert((ExprKey::new(s), ExprKey::new(t)));
            }
        }

        unsafe fn try_unfold_proj_app(
            &mut self,
            e: *mut LeanObject,
        ) -> Result<Option<*mut LeanObject>, KernelError> {
            let f = app_head(e);
            if lean_expr_is_proj(f) {
                let e_new = self.whnf_core(e, false, false)?;
                if lean_expr_eqv(e_new, e) {
                    lean_dec(e_new);
                    Ok(None)
                } else {
                    Ok(Some(e_new))
                }
            } else {
                Ok(None)
            }
        }

        unsafe fn lazy_delta_reduction_step(
            &mut self,
            t_n: &mut *mut LeanObject,
            s_n: &mut *mut LeanObject,
        ) -> Result<ReductionStatus, KernelError> {
            let d_t = self.is_delta(*t_n);
            let d_s = self.is_delta(*s_n);

            if d_t.is_none() && d_s.is_none() {
                return Ok(ReductionStatus::DefUnknown);
            }

            if d_t.is_some() && d_s.is_none() {
                if let Some(s_new) = self.try_unfold_proj_app(*s_n)? {
                    lean_dec(*s_n);
                    *s_n = s_new;
                } else {
                    let unfolded = self.unfold_definition(*t_n).unwrap();
                    let new_t = self.whnf_core(unfolded, false, true)?;
                    lean_dec(unfolded);
                    lean_dec(*t_n);
                    *t_n = new_t;
                }
            } else if d_t.is_none() && d_s.is_some() {
                if let Some(t_new) = self.try_unfold_proj_app(*t_n)? {
                    lean_dec(*t_n);
                    *t_n = t_new;
                } else {
                    let unfolded = self.unfold_definition(*s_n).unwrap();
                    let new_s = self.whnf_core(unfolded, false, true)?;
                    lean_dec(unfolded);
                    lean_dec(*s_n);
                    *s_n = new_s;
                }
            } else {
                let info_t = d_t.unwrap();
                let info_s = d_s.unwrap();
                let hints_t = lean_constant_info_get_hints(info_t);
                let hints_s = lean_constant_info_get_hints(info_s);
                let c = lean_hints_compare(hints_t, hints_s);
                lean_dec(info_t);
                lean_dec(info_s);
                if c < 0 {
                    let unfolded = self.unfold_definition(*t_n).unwrap();
                    let new_t = self.whnf_core(unfolded, false, true)?;
                    lean_dec(unfolded);
                    lean_dec(*t_n);
                    *t_n = new_t;
                } else if c > 0 {
                    let unfolded = self.unfold_definition(*s_n).unwrap();
                    let new_s = self.whnf_core(unfolded, false, true)?;
                    lean_dec(unfolded);
                    lean_dec(*s_n);
                    *s_n = new_s;
                } else {
                    let info_t2 = self.is_delta(*t_n).unwrap();
                    let info_s2 = self.is_delta(*s_n).unwrap();
                    let same_def = lean_name_eq(
                        lean_constant_info_get_name(info_t2),
                        lean_constant_info_get_name(info_s2),
                    );
                    let is_regular = lean_hints_is_regular(lean_constant_info_get_hints(info_t2));
                    lean_dec(info_t2);
                    lean_dec(info_s2);

                    if lean_expr_is_app(*t_n) && lean_expr_is_app(*s_n) && same_def && is_regular {
                        if !self.failed_before(*t_n, *s_n) {
                            let t_fn = app_head(*t_n);
                            let s_fn = app_head(*s_n);
                            let lvl_eq = is_equivalent_levels_list(
                                lean_expr_get_const_levels(t_fn),
                                lean_expr_get_const_levels(s_fn),
                            )?;
                            if lvl_eq && self.is_def_eq_args(*t_n, *s_n)? {
                                return Ok(ReductionStatus::DefEqual);
                            } else {
                                self.cache_failure(*t_n, *s_n);
                            }
                        }
                    }
                    let unf_t = self.unfold_definition(*t_n).unwrap();
                    let unf_s = self.unfold_definition(*s_n).unwrap();
                    let new_t = self.whnf_core(unf_t, false, true)?;
                    let new_s = self.whnf_core(unf_s, false, true)?;
                    lean_dec(unf_t);
                    lean_dec(unf_s);
                    lean_dec(*t_n);
                    lean_dec(*s_n);
                    *t_n = new_t;
                    *s_n = new_s;
                }
            }

            match self.quick_is_def_eq(*t_n, *s_n, false)? {
                LBool::True => Ok(ReductionStatus::DefEqual),
                LBool::False => Ok(ReductionStatus::DefDiff),
                LBool::Undef => Ok(ReductionStatus::Continue),
            }
        }

        unsafe fn is_def_eq_offset(
            &mut self,
            t: *mut LeanObject,
            s: *mut LeanObject,
        ) -> Result<LBool, KernelError> {
            if is_nat_zero_expr(t) && is_nat_zero_expr(s) {
                return Ok(LBool::True);
            }
            let pred_t = nat_pred(t);
            let pred_s = nat_pred(s);
            if let (Some(pt), Some(ps)) = (pred_t, pred_s) {
                Ok(LBool::from_bool(self.is_def_eq_core(pt, ps)?))
            } else {
                Ok(LBool::Undef)
            }
        }

        unsafe fn lazy_delta_reduction(
            &mut self,
            t_n: &mut *mut LeanObject,
            s_n: &mut *mut LeanObject,
        ) -> Result<LBool, KernelError> {
            loop {
                let r = self.is_def_eq_offset(*t_n, *s_n)?;
                if r != LBool::Undef {
                    return Ok(r);
                }

                if (!expr_has_fvar(*t_n) && !expr_has_fvar(*s_n)) || self.eager_reduce {
                    if let Some(tv) = self.reduce_nat(*t_n)? {
                        return Ok(LBool::from_bool(self.is_def_eq_core(tv, *s_n)?));
                    }
                    if let Some(sv) = self.reduce_nat(*s_n)? {
                        return Ok(LBool::from_bool(self.is_def_eq_core(*t_n, sv)?));
                    }
                }

                if let Some(tv) = self.reduce_native(*t_n) {
                    return Ok(LBool::from_bool(self.is_def_eq_core(tv, *s_n)?));
                }
                if let Some(sv) = self.reduce_native(*s_n) {
                    return Ok(LBool::from_bool(self.is_def_eq_core(*t_n, sv)?));
                }

                match self.lazy_delta_reduction_step(t_n, s_n)? {
                    ReductionStatus::Continue => continue,
                    ReductionStatus::DefUnknown => return Ok(LBool::Undef),
                    ReductionStatus::DefEqual => return Ok(LBool::True),
                    ReductionStatus::DefDiff => return Ok(LBool::False),
                }
            }
        }

        unsafe fn lazy_delta_proj_reduction(
            &mut self,
            t_n: &mut *mut LeanObject,
            s_n: &mut *mut LeanObject,
            idx: *const LeanObject,
        ) -> Result<bool, KernelError> {
            loop {
                match self.lazy_delta_reduction_step(t_n, s_n)? {
                    ReductionStatus::Continue => continue,
                    ReductionStatus::DefEqual => return Ok(true),
                    ReductionStatus::DefUnknown | ReductionStatus::DefDiff => {
                        if lean_nat_is_small(idx) {
                            let i = lean_nat_get_small_value(idx) as usize;
                            if let Some(t_proj) = self.reduce_proj_core(*t_n, i)? {
                                if let Some(s_proj) = self.reduce_proj_core(*s_n, i)? {
                                    return self.is_def_eq_core(t_proj, s_proj);
                                }
                                lean_dec(t_proj);
                            }
                        }
                        return self.is_def_eq_core(*t_n, *s_n);
                    }
                }
            }
        }

        unsafe fn try_string_lit_expansion_core(
            &mut self,
            t: *mut LeanObject,
            s: *mut LeanObject,
        ) -> Result<LBool, KernelError> {
            if lean_expr_is_string_lit(t) && lean_expr_is_app(s) {
                let string_mk = load_global(&G_STRING_MK);
                if lean_expr_eqv(lean_expr_get_app_fn(s), string_mk) {
                    let ctor = lean_string_lit_to_constructor(t);
                    let whnf_ctor = self.whnf(ctor)?;
                    lean_dec(ctor);
                    return Ok(LBool::from_bool(self.is_def_eq_core(whnf_ctor, s)?));
                }
            }
            Ok(LBool::Undef)
        }

        // -----------------------------------------------------------------------
        // is_def_eq_core — the main decision procedure
        // -----------------------------------------------------------------------

        unsafe fn is_def_eq_core(
            &mut self,
            t: *mut LeanObject,
            s: *mut LeanObject,
        ) -> Result<bool, KernelError> {
            check_system_result()?;
            let r = self.quick_is_def_eq(t, s, true)?;
            if r != LBool::Undef {
                return Ok(r == LBool::True);
            }

            // Proof by reflection: if t has no fvars and s is Bool.true, fully reduce t
            let bool_true = load_global(&G_BOOL_TRUE);
            if (!expr_has_fvar(t) || self.eager_reduce)
                && lean_expr_is_const(s)
                && lean_name_eq(lean_expr_get_const_name(s), bool_true)
            {
                let whnf_t = self.whnf(t)?;
                if lean_expr_is_const(whnf_t)
                    && lean_name_eq(lean_expr_get_const_name(whnf_t), bool_true)
                {
                    lean_dec(whnf_t);
                    return Ok(true);
                }
                lean_dec(whnf_t);
            }

            // whnf_core with cheap_proj=true (no full whnf for projections)
            let mut t_n = self.whnf_core(t, false, true)?;
            let mut s_n = self.whnf_core(s, false, true)?;

            if !lean_expr_is_eqp(t_n, t) || !lean_expr_is_eqp(s_n, s) {
                let r = self.quick_is_def_eq(t_n, s_n, false)?;
                if r != LBool::Undef {
                    lean_dec(t_n);
                    lean_dec(s_n);
                    return Ok(r == LBool::True);
                }
            }

            let r = self.is_def_eq_proof_irrel(t_n, s_n)?;
            if r != LBool::Undef {
                lean_dec(t_n);
                lean_dec(s_n);
                return Ok(r == LBool::True);
            }

            let r = self.lazy_delta_reduction(&mut t_n, &mut s_n)?;
            if r != LBool::Undef {
                lean_dec(t_n);
                lean_dec(s_n);
                return Ok(r == LBool::True);
            }

            // Constant and fvar checks
            if lean_expr_is_const(t_n) && lean_expr_is_const(s_n) {
                if lean_name_eq(lean_expr_get_const_name(t_n), lean_expr_get_const_name(s_n)) {
                    if is_equivalent_levels_list(
                        lean_expr_get_const_levels(t_n),
                        lean_expr_get_const_levels(s_n),
                    )? {
                        lean_dec(t_n);
                        lean_dec(s_n);
                        return Ok(true);
                    }
                }
            }
            if lean_expr_is_fvar(t_n) && lean_expr_is_fvar(s_n) {
                if lean_name_eq(lean_expr_get_fvar_id(t_n), lean_expr_get_fvar_id(s_n)) {
                    lean_dec(t_n);
                    lean_dec(s_n);
                    return Ok(true);
                }
            }

            // Proj-proj reduction
            if lean_expr_is_proj(t_n) && lean_expr_is_proj(s_n) {
                let ti = lean_expr_get_proj_idx(t_n);
                let si = lean_expr_get_proj_idx(s_n);
                if lean_nat_eq(ti, si) {
                    let mut t_c = lean_expr_get_proj_expr(t_n);
                    let mut s_c = lean_expr_get_proj_expr(s_n);
                    lean_inc(t_c);
                    lean_inc(s_c);
                    if self.lazy_delta_proj_reduction(&mut t_c, &mut s_c, ti)? {
                        lean_dec(t_c);
                        lean_dec(s_c);
                        lean_dec(t_n);
                        lean_dec(s_n);
                        return Ok(true);
                    }
                    lean_dec(t_c);
                    lean_dec(s_c);
                }
            }

            // Invoke whnf_core again using full whnf for projections
            let t_n_n = self.whnf_core(t_n, false, false)?;
            let s_n_n = self.whnf_core(s_n, false, false)?;
            if !lean_expr_is_eqp(t_n_n, t_n) || !lean_expr_is_eqp(s_n_n, s_n) {
                lean_dec(t_n);
                lean_dec(s_n);
                let r = self.is_def_eq_core(t_n_n, s_n_n)?;
                lean_dec(t_n_n);
                lean_dec(s_n_n);
                return Ok(r);
            }
            lean_dec(t_n_n);
            lean_dec(s_n_n);

            // App-app
            if self.is_def_eq_app(t_n, s_n)? {
                lean_dec(t_n);
                lean_dec(s_n);
                return Ok(true);
            }

            // Eta expansion
            if self.try_eta_expansion_core(t_n, s_n)? || self.try_eta_expansion_core(s_n, t_n)? {
                lean_dec(t_n);
                lean_dec(s_n);
                return Ok(true);
            }

            // Eta struct
            if self.try_eta_struct_core(t_n, s_n)? || self.try_eta_struct_core(s_n, t_n)? {
                lean_dec(t_n);
                lean_dec(s_n);
                return Ok(true);
            }

            // String literal expansion
            let r = self.try_string_lit_expansion_core(t_n, s_n)?;
            if r != LBool::Undef {
                lean_dec(t_n);
                lean_dec(s_n);
                return Ok(r == LBool::True);
            }
            let r = self.try_string_lit_expansion_core(s_n, t_n)?;
            if r != LBool::Undef {
                lean_dec(t_n);
                lean_dec(s_n);
                return Ok(r == LBool::True);
            }

            // Unit-like
            if self.is_def_eq_unit_like(t_n, s_n)? {
                lean_dec(t_n);
                lean_dec(s_n);
                return Ok(true);
            }

            lean_dec(t_n);
            lean_dec(s_n);
            Ok(false)
        }

        pub unsafe fn is_def_eq(
            &mut self,
            t: *mut LeanObject,
            s: *mut LeanObject,
        ) -> Result<bool, KernelError> {
            let r = self.is_def_eq_core(t, s)?;
            if r {
                lean_equiv_manager_add_equiv(self.st.eqv_manager, t, s);
            }
            Ok(r)
        }

        pub unsafe fn whnf_public(
            &mut self,
            e: *mut LeanObject,
        ) -> Result<*mut LeanObject, KernelError> {
            self.whnf(e)
        }

        // -----------------------------------------------------------------------
        // check (type check + return type)
        // -----------------------------------------------------------------------

        pub unsafe fn check(
            &mut self,
            e: *mut LeanObject,
            lps: *mut LeanObject,
        ) -> Result<*mut LeanObject, KernelError> {
            let saved = self.lparams;
            self.lparams = Some(lps);
            let r = self.infer_type_core(e, false);
            self.lparams = saved;
            r
        }

        pub unsafe fn check_ignore_undefined_universes(
            &mut self,
            e: *mut LeanObject,
        ) -> Result<*mut LeanObject, KernelError> {
            let saved = self.lparams;
            self.lparams = None;
            let r = self.infer_type_core(e, false);
            self.lparams = saved;
            r
        }

        pub unsafe fn ensure_sort(
            &mut self,
            e: *mut LeanObject,
        ) -> Result<*mut LeanObject, KernelError> {
            self.ensure_sort_core(e, e)
        }

        pub unsafe fn ensure_type(
            &mut self,
            e: *mut LeanObject,
        ) -> Result<*mut LeanObject, KernelError> {
            let ty = self.infer_type(e)?;
            self.ensure_sort_core(ty, e)
        }

        pub unsafe fn ensure_pi(
            &mut self,
            e: *mut LeanObject,
        ) -> Result<*mut LeanObject, KernelError> {
            self.ensure_pi_core(e, e)
        }
    }

    impl Drop for TypeChecker {
        fn drop(&mut self) {
            unsafe {
                lean_dec(self.lctx);
                if !self.diag.is_null() {
                    lean_dec(self.diag);
                }
            }
        }
    }

    // ---------------------------------------------------------------------------
    // Standalone helpers used by the type checker
    // ---------------------------------------------------------------------------

    unsafe fn lean_lit_type(e: *mut LeanObject) -> *mut LeanObject {
        // `e` is an `Expr.lit`; its field 0 is the `Literal`, whose ctor tag selects the type
        // (0 = natVal → `Nat`, 1 = strVal → `String`). Return an `Expr.const`, not a bare `Name`.
        let lit = lean_ctor_get(e, 0);
        let tag = lean_ptr_tag(lit);
        let name = if tag == LITERAL_NAT_TAG {
            build_lean_name(&["Nat"])
        } else {
            build_lean_name(&["String"])
        };
        let nil = lean_mk_list_nil(ptr::null_mut());
        // lean_expr_mk_const consumes both `name` and `nil`.
        lean_expr_mk_const(name, nil)
    }

    unsafe fn is_eager_reduce_expr(e: *const LeanObject) -> bool {
        // eagerReduce fn arg  → is_const(get_app_fn(e)) && get_app_num_args == 2
        let eager = load_global(&G_EAGER_REDUCE);
        let nargs = lean_expr_get_app_num_args(e);
        if nargs != 2 {
            return false;
        }
        let f = app_head(e);
        if !lean_expr_is_const(f) {
            return false;
        }
        lean_name_eq(lean_expr_get_const_name(f), eager)
    }

    unsafe fn is_nat_lit_ext(e: *const LeanObject) -> bool {
        let nat_zero = load_global(&G_NAT_ZERO);
        lean_expr_eqv(e, nat_zero) || lean_expr_is_nat_lit(e)
    }

    unsafe fn get_nat_val(e: *mut LeanObject) -> *mut LeanObject {
        // Returns a BORROWED nat object: for the literal case it points inside `e`'s
        // `Expr.lit`, for the `Nat.zero` constant case it is the scalar `box(0)`.
        // The caller must NOT `lean_dec` the result, and must keep `e` alive while using it.
        let nat_zero = load_global(&G_NAT_ZERO);
        if lean_expr_eqv(e, nat_zero) {
            lean_nat_mk_obj(0) // scalar box(0): no ownership, safe to treat as borrowed
        } else {
            lean_expr_get_lit_nat(e) // borrowed pointer into the literal
        }
    }

    unsafe fn reduce_nat_succ(arg: *const LeanObject) -> Option<*mut LeanObject> {
        if !is_nat_lit_ext(arg) {
            return None;
        }
        let v = get_nat_val(arg); // borrowed; do NOT dec
        let one = lean_nat_mk_obj(1); // scalar box(1)
        // lean_nat_add BORROWS both args, returns an owned result.
        let result = lean_nat_add(v, one);
        Some(lean_expr_mk_lit_nat(result))
    }

    unsafe fn mk_bool(b: bool) -> *mut LeanObject {
        // The kernel reduces Nat.beq/ble/reduceBool to the *expression* `Bool.true`/`Bool.false`
        // (a `Expr.const`), not to a raw Bool scalar.
        let e = load_global(if b {
            &G_EXPR_BOOL_TRUE
        } else {
            &G_EXPR_BOOL_FALSE
        });
        lean_inc(e);
        e
    }

    unsafe fn is_nat_zero_expr(e: *const LeanObject) -> bool {
        let nat_zero = load_global(&G_NAT_ZERO);
        if lean_expr_eqv(e, nat_zero) {
            return true;
        }
        if lean_expr_is_nat_lit(e) {
            let n = lean_expr_get_lit_nat(e);
            return lean_nat_is_zero(n);
        }
        false
    }

    unsafe fn nat_pred(e: *const LeanObject) -> Option<*mut LeanObject> {
        if lean_expr_is_nat_lit(e) {
            let n = lean_expr_get_lit_nat(e);
            if lean_nat_is_zero(n) {
                return None;
            }
            let pred = lean_nat_dec(n);
            return Some(lean_expr_mk_lit_nat(pred));
        }
        let nat_succ = load_global(&G_NAT_SUCC);
        if lean_expr_get_app_num_args(e) == 1 {
            let f = lean_expr_get_app_fn(e);
            if lean_expr_eqv(f, nat_succ) {
                let arg = lean_expr_get_app_arg(e);
                lean_inc(arg);
                return Some(arg);
            }
        }
        None
    }

    unsafe fn is_equivalent_levels_list(
        ls1: *mut LeanObject,
        ls2: *mut LeanObject,
    ) -> Result<bool, KernelError> {
        let mut l1 = ls1;
        let mut l2 = ls2;
        loop {
            let nil1 = lean_list_is_nil(l1);
            let nil2 = lean_list_is_nil(l2);
            if nil1 && nil2 {
                return Ok(true);
            }
            if nil1 || nil2 {
                return Ok(false);
            }
            if !is_equivalent_level(lean_list_head(l1), lean_list_head(l2))? {
                return Ok(false);
            }
            l1 = lean_list_tail(l1);
            l2 = lean_list_tail(l2);
        }
    }

    unsafe fn list_length(l: *const LeanObject) -> usize {
        let mut cur = l;
        let mut n = 0;
        while !lean_list_is_nil(cur) {
            n += 1;
            cur = lean_list_tail(cur);
        }
        n
    }

    /// Check if env has a non-recursive structure with this name.
    unsafe fn is_non_rec_structure_name(env: *const LeanObject, name: *const LeanObject) -> bool {
        let info_opt = env_find(env, name as *mut LeanObject);
        if lean_is_scalar(info_opt) {
            return false;
        }
        if !lean_constant_info_is_inductive(info_opt) {
            lean_dec(info_opt);
            return false;
        }
        // I_val is BORROWED (field 0 of info_opt). `lean_inductive_val_is_rec` is an @[export] owned
        // function (C++ calls it via `to_obj_arg()`), so it CONSUMES its argument — inc before calling,
        // else it frees the InductiveVal sub-object shared with the env's stored constant (env corruption).
        let I_val = lean_constant_info_to_inductive_val(info_opt);
        let result = lean_inductive_val_get_ncnstrs(I_val) == 1
            && lean_inductive_val_get_nindices(I_val) == 0
            && !lean_inductive_val_is_rec(I_val);
        lean_dec(info_opt);
        result
    }

    unsafe fn format_level_error_msg(name: *mut LeanObject) -> *mut LeanObject {
        let s = format!(
            "invalid reference to undefined universe level parameter '{}'",
            lean_name_to_string(name)
        );
        lean_mk_string(s.as_ptr(), s.len())
    }

    unsafe fn format_arity_error_msg(
        name: *mut LeanObject,
        expected: usize,
        got: usize,
    ) -> *mut LeanObject {
        let s = format!(
            "incorrect number of universe levels parameters for '{}', #{} expected, #{} provided",
            lean_name_to_string(name),
            expected,
            got
        );
        lean_mk_string(s.as_ptr(), s.len())
    }

    unsafe fn lean_name_to_string(name: *mut LeanObject) -> String {
        // Dotted string form of a `Name`: `.str`/`.num` components joined by '.', recursing into the
        // prefix first (field 0). `name` is BORROWED. Sufficient for kernel error messages over
        // ordinary identifier names (no special-char escaping, which Lean's `Name.toString` adds).
        unsafe fn go(n: *mut LeanObject, out: &mut String) {
            if lean_is_scalar(n) {
                return; // `.anonymous`: contributes nothing
            }
            let tag = lean_obj_tag(n);
            go(lean_ctor_get(n, 0), out); // prefix
            if !out.is_empty() {
                out.push('.');
            }
            if tag == 1 {
                // `.str`: field 1 is a String object.
                let bytes =
                    core::ffi::CStr::from_ptr(lean_string_cstr(lean_ctor_get(n, 1))).to_bytes();
                out.push_str(&String::from_utf8_lossy(bytes));
            } else {
                // `.num`: field 1 is a Nat (small scalar in practice).
                let c = lean_ctor_get(n, 1);
                let v = if lean_is_scalar(c) {
                    lean_unbox(c) as u64
                } else {
                    u64::MAX
                };
                out.push_str(&v.to_string());
            }
        }
        let mut s = String::new();
        go(name, &mut s);
        s
    }

    // ---------------------------------------------------------------------------
    // inductive_reduce_rec_impl  (called from TypeChecker::reduce_recursor)
    //
    // This is a Rust port of the inductive_reduce_rec template in inductive.h.
    // It calls back into `tc` for whnf/infer_type/is_def_eq.
    // ---------------------------------------------------------------------------

    unsafe fn inductive_reduce_rec_impl(
        env: *mut LeanObject,
        e: *mut LeanObject,
        cheap_rec: bool,
        cheap_proj: bool,
        tc: &mut TypeChecker,
    ) -> Result<Option<*mut LeanObject>, KernelError> {
        // Walk the whole application spine: `lean_expr_get_app_fn` strips a single layer, so we
        // must iterate to reach the head constant (the recursor). A multi-argument recursor
        // application like `Decidable.rec C m1 m2 major` has an `App` immediately under it, not the
        // const, so checking only one layer would wrongly bail and leave recursors unreduced.
        let mut rec_args: Vec<*mut LeanObject> = Vec::new();
        let mut cur = e;
        while lean_expr_is_app(cur) {
            rec_args.push(lean_expr_get_app_arg(cur));
            cur = lean_expr_get_app_fn(cur);
        }
        rec_args.reverse();
        let rec_fn = cur; // spine head
        if !lean_expr_is_const(rec_fn) {
            return Ok(None);
        }
        let rec_name = lean_expr_get_const_name(rec_fn);
        let rec_info_opt = env_find(env, rec_name);
        if lean_is_scalar(rec_info_opt) || !lean_constant_info_is_recursor(rec_info_opt) {
            lean_dec(rec_info_opt);
            return Ok(None);
        }

        let rec_val = lean_constant_info_to_recursor_val(rec_info_opt);
        let major_idx = lean_recursor_val_get_major_idx(rec_val) as usize;
        if major_idx >= rec_args.len() {
            lean_dec(rec_info_opt);
            return Ok(None);
        }

        let mut major = rec_args[major_idx];
        lean_inc(major);

        // to_cnstr_when_K
        if lean_recursor_val_is_k(rec_val) {
            major = to_cnstr_when_K_impl(env, rec_val, major, tc)?;
        }

        // whnf major
        {
            let whnf_major = if cheap_rec {
                tc.whnf_core(major, cheap_rec, cheap_proj)?
            } else {
                tc.whnf(major)?
            };
            lean_dec(major);
            major = whnf_major;
        }

        // nat/string lit to constructor
        if lean_expr_is_nat_lit(major) {
            let ctor = lean_nat_lit_to_constructor(major);
            lean_dec(major);
            major = ctor;
        } else if lean_expr_is_string_lit(major) {
            let ctor = lean_string_lit_to_constructor(major);
            let whnf = tc.whnf(ctor)?;
            lean_dec(ctor);
            lean_dec(major);
            major = whnf;
        } else {
            // to_cnstr_when_structure
            let induct_name = lean_recursor_val_get_major_induct(rec_val);
            major = to_cnstr_when_structure_impl(env, induct_name, major, tc)?;
        }

        // Find recursor rule matching major's constructor
        let rule = get_rec_rule_for_impl(rec_val, major);
        if rule.is_none() {
            lean_dec(major);
            lean_dec(rec_info_opt);
            return Ok(None);
        }
        let rule = rule.unwrap();

        let mut major_args: Vec<*mut LeanObject> = Vec::new();
        let mut mc = major;
        while lean_expr_is_app(mc) {
            major_args.push(lean_expr_get_app_arg(mc));
            mc = lean_expr_get_app_fn(mc);
        }
        major_args.reverse();

        let nfields = lean_recursor_rule_get_nfields(rule) as usize;
        if nfields > major_args.len() {
            lean_dec(rule);
            lean_dec(major);
            lean_dec(rec_info_opt);
            return Ok(None);
        }
        let rec_levels = lean_expr_get_const_levels(rec_fn);
        let rec_lparams = lean_constant_info_get_lparams(rec_info_opt);
        if list_length(rec_levels) != list_length(rec_lparams) {
            lean_dec(rule);
            lean_dec(major);
            lean_dec(rec_info_opt);
            return Ok(None);
        }
        let nparams_rec = lean_recursor_val_get_nparams(rec_val) as usize;
        let nmotives = lean_recursor_val_get_nmotives(rec_val) as usize;
        let nminors = lean_recursor_val_get_nminors(rec_val) as usize;

        let rhs_tmpl = lean_recursor_rule_get_rhs(rule);
        let mut rhs = lean_instantiate_lparams(rhs_tmpl, rec_lparams, rec_levels);

        // Apply params + motives + minors from rec_args. mk_app consumes both args (obj_arg):
        // inc the borrowed element, let `rhs` flow into the new node (no dec).
        for i in 0..(nparams_rec + nmotives + nminors) {
            if i < rec_args.len() {
                lean_inc(rec_args[i]);
                rhs = lean_expr_mk_app(rhs, rec_args[i]);
            }
        }

        // Apply fields from major
        let nparams_ctor = major_args.len() - nfields;
        for i in 0..nfields {
            lean_inc(major_args[nparams_ctor + i]);
            rhs = lean_expr_mk_app(rhs, major_args[nparams_ctor + i]);
        }

        // Apply extra rec_args after major
        if rec_args.len() > major_idx + 1 {
            for i in (major_idx + 1)..rec_args.len() {
                lean_inc(rec_args[i]);
                rhs = lean_expr_mk_app(rhs, rec_args[i]);
            }
        }

        lean_dec(rule);
        lean_dec(major);
        lean_dec(rec_info_opt);
        Ok(Some(rhs))
    }

    unsafe fn to_cnstr_when_K_impl(
        env: *mut LeanObject,
        rec_val: *mut LeanObject,
        e: *mut LeanObject,
        tc: &mut TypeChecker,
    ) -> Result<*mut LeanObject, KernelError> {
        let app_type_raw = tc.infer_type(e)?;
        let app_type = tc.whnf(app_type_raw)?;
        lean_dec(app_type_raw);
        let app_type_fn = app_head(app_type);
        if !lean_expr_is_const(app_type_fn) {
            lean_dec(app_type);
            lean_inc(e);
            return Ok(e);
        }
        let major_induct = lean_recursor_val_get_major_induct(rec_val);
        if !lean_name_eq(lean_expr_get_const_name(app_type_fn), major_induct) {
            lean_dec(app_type);
            lean_inc(e);
            return Ok(e);
        }
        // Check for metavars in indices
        if expr_has_expr_mvar(app_type) {
            let nparams = lean_recursor_val_get_nparams(rec_val) as usize;
            let mut args: Vec<*mut LeanObject> = Vec::new();
            let mut c = app_type;
            while lean_expr_is_app(c) {
                args.push(lean_expr_get_app_arg(c));
                c = lean_expr_get_app_fn(c);
            }
            args.reverse();
            for i in nparams..args.len() {
                if expr_has_expr_mvar(args[i]) {
                    lean_dec(app_type);
                    lean_inc(e);
                    return Ok(e);
                }
            }
        }
        // mk_nullary_cnstr
        let nparams = lean_recursor_val_get_nparams(rec_val) as usize;
        let cnstr_opt = mk_nullary_cnstr_impl(env, app_type, nparams);
        if let Some(cnstr) = cnstr_opt {
            let cnstr_type = tc.infer_type(cnstr)?;
            if tc.is_def_eq(app_type, cnstr_type)? {
                lean_dec(app_type);
                lean_dec(cnstr_type);
                lean_dec(e);
                return Ok(cnstr);
            }
            lean_dec(cnstr_type);
            lean_dec(cnstr);
        }
        lean_dec(app_type);
        lean_inc(e);
        Ok(e)
    }

    unsafe fn to_cnstr_when_structure_impl(
        env: *mut LeanObject,
        induct_name: *mut LeanObject,
        e: *mut LeanObject,
        tc: &mut TypeChecker,
    ) -> Result<*mut LeanObject, KernelError> {
        if !is_non_rec_structure_name(env, induct_name) {
            return Ok(e);
        }
        if is_constructor_app_impl(env, e) {
            return Ok(e);
        }
        let e_type_raw = tc.infer_type(e)?;
        let e_type = tc.whnf(e_type_raw)?;
        lean_dec(e_type_raw);
        // Check type name matches induct_name
        let e_fn = app_head(e_type);
        if !lean_expr_is_const(e_fn) || !lean_name_eq(lean_expr_get_const_name(e_fn), induct_name) {
            lean_dec(e_type);
            return Ok(e);
        }
        // Check not a Prop
        let e_type_sort_raw = tc.infer_type(e_type)?;
        let e_type_sort = tc.whnf(e_type_sort_raw)?;
        lean_dec(e_type_sort_raw);
        let prop = lean_expr_mk_prop();
        let is_prop = lean_expr_eqv(e_type_sort, prop);
        lean_dec(prop);
        lean_dec(e_type_sort);
        if is_prop {
            lean_dec(e_type);
            return Ok(e);
        }

        // Expand eta
        let result = expand_eta_struct_impl(env, e_type, e);
        lean_dec(e_type);
        lean_dec(e);
        Ok(result)
    }

    unsafe fn mk_nullary_cnstr_impl(
        env: *mut LeanObject,
        ty: *mut LeanObject,
        nparams: usize,
    ) -> Option<*mut LeanObject> {
        let mut args: Vec<*mut LeanObject> = Vec::new();
        let mut cur = ty;
        while lean_expr_is_app(cur) {
            args.push(lean_expr_get_app_arg(cur));
            cur = lean_expr_get_app_fn(cur);
        }
        args.reverse();
        let d = cur;
        if !lean_expr_is_const(d) {
            return None;
        }
        let d_name = lean_expr_get_const_name(d);
        let I_info = env_find(env, d_name);
        if lean_is_scalar(I_info) || !lean_constant_info_is_inductive(I_info) {
            lean_dec(I_info);
            return None;
        }
        let I_val = lean_constant_info_to_inductive_val(I_info);
        let cnstrs = lean_inductive_val_get_cnstrs(I_val);
        if lean_list_is_nil(cnstrs) {
            lean_dec(I_info);
            return None;
        }
        let cnstr_name = lean_list_head(cnstrs);
        lean_inc(cnstr_name); // own before freeing I_info (cnstr_name is borrowed from it)
        lean_dec(I_info);
        args.truncate(nparams);
        let levels = lean_expr_get_const_levels(d);
        lean_inc(levels);
        // mk_const/mk_app consume their args (obj_arg); cnstr_name/levels/arg are owned/inc'd here.
        let mut app = lean_expr_mk_const(cnstr_name, levels);
        for &arg in &args {
            lean_inc(arg);
            app = lean_expr_mk_app(app, arg);
        }
        Some(app)
    }

    unsafe fn expand_eta_struct_impl(
        env: *mut LeanObject,
        e_type: *mut LeanObject,
        e: *mut LeanObject,
    ) -> *mut LeanObject {
        let mut type_args: Vec<*mut LeanObject> = Vec::new();
        let mut cur = e_type;
        while lean_expr_is_app(cur) {
            type_args.push(lean_expr_get_app_arg(cur));
            cur = lean_expr_get_app_fn(cur);
        }
        type_args.reverse();
        let I = cur;
        if !lean_expr_is_const(I) {
            lean_inc(e);
            return e;
        }
        let ctor_name = {
            let I_name = lean_expr_get_const_name(I);
            let I_info = env_find(env, I_name);
            if lean_is_scalar(I_info) || !lean_constant_info_is_inductive(I_info) {
                lean_dec(I_info);
                lean_inc(e);
                return e;
            }
            let I_val = lean_constant_info_to_inductive_val(I_info);
            let cnstrs = lean_inductive_val_get_cnstrs(I_val);
            if lean_list_is_nil(cnstrs) {
                lean_dec(I_info);
                lean_inc(e);
                return e;
            }
            let n = lean_list_head(cnstrs);
            lean_inc(n);
            lean_dec(I_info);
            n
        };
        let ctor_info = env_find(env, ctor_name);
        if lean_is_scalar(ctor_info) {
            lean_dec(ctor_name);
            lean_inc(e);
            return e;
        }
        let ctor_val = lean_constant_info_to_constructor_val(ctor_info);
        let nparams = lean_constructor_val_get_nparams(ctor_val) as usize;
        let nfields = lean_constructor_val_get_nfields(ctor_val) as usize;
        lean_dec(ctor_info);

        let I_name = lean_expr_get_const_name(I);
        let I_levels = lean_expr_get_const_levels(I);
        // mk_const/mk_app/mk_proj consume their object args (obj_arg). `ctor_name` is owned;
        // `I_levels`/`I_name`/`e`/`type_args[i]` are borrowed, so inc each before handing it over.
        lean_inc(I_levels);
        let mut result = lean_expr_mk_const(ctor_name, I_levels);

        for i in 0..nparams {
            if i < type_args.len() {
                lean_inc(type_args[i]);
                result = lean_expr_mk_app(result, type_args[i]);
            }
        }
        for i in 0..nfields {
            let idx = lean_nat_mk_obj(i as u64); // owned, consumed by mk_proj
            lean_inc(I_name);
            lean_inc(e);
            let proj = lean_expr_mk_proj(I_name, idx, e);
            result = lean_expr_mk_app(result, proj);
        }
        result
    }

    unsafe fn is_constructor_app_impl(env: *const LeanObject, e: *const LeanObject) -> bool {
        let f = app_head(e);
        if !lean_expr_is_const(f) {
            return false;
        }
        let name = lean_expr_get_const_name(f);
        let info = env_find(env, name);
        if lean_is_scalar(info) {
            return false;
        }
        let is_ctor = lean_constant_info_is_constructor(info);
        lean_dec(info);
        is_ctor
    }

    /// Spine head of an application: `lean_expr_get_app_fn` strips only one `App` layer, but the
    /// kernel's C++ `get_app_fn` returns the recursive head. Walk to it.
    unsafe fn app_head(e: *const LeanObject) -> *mut LeanObject {
        let mut cur = e;
        while lean_expr_is_app(cur) {
            cur = lean_expr_get_app_fn(cur);
        }
        cur
    }

    unsafe fn get_rec_rule_for_impl(
        rec_val: *mut LeanObject,
        major: *mut LeanObject,
    ) -> Option<*mut LeanObject> {
        let fn_ = app_head(major);
        if !lean_expr_is_const(fn_) {
            return None;
        }
        let cnstr_name = lean_expr_get_const_name(fn_);
        let rules = lean_recursor_val_get_rules(rec_val);
        let mut cur = rules;
        while !lean_list_is_nil(cur) {
            let rule = lean_list_head(cur);
            let rule_cnstr = lean_recursor_rule_get_cnstr(rule);
            if lean_name_eq(rule_cnstr, cnstr_name) {
                lean_inc(rule);
                return Some(rule);
            }
            cur = lean_list_tail(cur);
        }
        None
    }

    unsafe fn lean_instantiate_lparams(
        e: *mut LeanObject,
        lparams: *mut LeanObject,
        levels: *mut LeanObject,
    ) -> *mut LeanObject {
        // Substitute lparams → levels in expression e. Delegates to the real Lean
        // export lean_expr_instantiate_lparams (borrows e/ps/ls, returns owned).
        lean_expr_instantiate_lparams(e, lparams, levels)
    }

    // ---------------------------------------------------------------------------
    // Extern "C" public entry points
    // ---------------------------------------------------------------------------

    // lean_add_decl / lean_add_decl_without_checking exported from kernel_environment.rs
    // call this Rust declaration dispatch.

    // lean_kernel_* receive elab envs; need to extract kernel env first.
    unsafe extern "C" {
        fn lean_elab_environment_to_kernel_env(env: *mut LeanObject) -> *mut LeanObject;
    }

    /// `lean_kernel_is_def_eq(env, lctx, a, b) -> Except KernelException Bool`
    #[no_mangle]
    pub unsafe fn lean_kernel_is_def_eq(
        env: *mut LeanObject,
        lctx: *mut LeanObject,
        a: *mut LeanObject,
        b: *mut LeanObject,
    ) -> *mut LeanObject {
        let kernel_env = lean_elab_environment_to_kernel_env(env);
        let mut tc = TypeChecker::new(kernel_env, lctx, DEF_SAFETY_SAFE);
        lean_dec(kernel_env);
        let result = match tc.is_def_eq(a, b) {
            Ok(r) => mk_except_ok(lean_box(if r { 1 } else { 0 })),
            Err(e) => kernel_error_to_lean_except(e),
        };
        // The opaque @[extern] passes `lctx`/`a`/`b` owned; tc only borrowed them, so consume here.
        lean_dec(lctx);
        lean_dec(a);
        lean_dec(b);
        result
    }

    /// `lean_kernel_whnf(env, lctx, a) -> Except KernelException Expr`
    #[no_mangle]
    pub unsafe fn lean_kernel_whnf(
        env: *mut LeanObject,
        lctx: *mut LeanObject,
        a: *mut LeanObject,
    ) -> *mut LeanObject {
        let kernel_env = lean_elab_environment_to_kernel_env(env);
        let mut tc = TypeChecker::new(kernel_env, lctx, DEF_SAFETY_SAFE);
        lean_dec(kernel_env);
        let result = match tc.whnf(a) {
            Ok(r) => mk_except_ok(r),
            Err(e) => kernel_error_to_lean_except(e),
        };
        // The opaque @[extern] passes `lctx`/`a` owned; tc only borrowed them, so consume here.
        lean_dec(lctx);
        lean_dec(a);
        result
    }

    /// `lean_kernel_check(env, lctx, a) -> Except KernelException Expr`
    #[no_mangle]
    pub unsafe fn lean_kernel_check(
        env: *mut LeanObject,
        lctx: *mut LeanObject,
        a: *mut LeanObject,
    ) -> *mut LeanObject {
        let kernel_env = lean_elab_environment_to_kernel_env(env);
        let mut tc = TypeChecker::new(kernel_env, lctx, DEF_SAFETY_SAFE);
        lean_dec(kernel_env);
        // The `Kernel.check` debugging API matches C++ `check(expr)` (one arg), which is
        // `check_ignore_undefined_universes` (m_lparams = null). Passing an empty lparam list
        // instead would wrongly reject any term containing universe-level parameters.
        let result = match tc.check_ignore_undefined_universes(a) {
            Ok(r) => mk_except_ok(r),
            Err(e) => kernel_error_to_lean_except(e),
        };
        // The opaque @[extern] passes `lctx`/`a` owned; tc only borrowed them, so consume here.
        lean_dec(lctx);
        lean_dec(a);
        result
    }

    use self::kernel_type_checker_lean_level_eq as lean_level_eq;
    use self::kernel_type_checker_level_to_offset as level_to_offset;
    /// Build `Except.ok value` (a single-field constructor). `Except` declares `error`
    /// first (tag 0) and `ok` second (tag 1), so `ok` uses tag `EXCEPT_OK_TAG`.
    use crate::runtime_exception::{mk_except_err, mk_except_ok};

    // ---------------------------------------------------------------------------
    // add-declaration path (Rust port of environment::add_axiom/add_definition/
    // add_theorem/add_opaque from type_checker.cpp). All C++ `throw` become
    // `Err(KernelError::...)`. For declaration kinds Axiom/Definition/Theorem/Opaque
    // (tags 0-3) a `Declaration` IS layout-identical to a `ConstantInfo` (the C++
    // `constant_info(declaration)` ctor just reuses `d.raw()`), so we treat `decl`
    // directly as a `ConstantInfo` for the field accessors and for `add`.
    // ---------------------------------------------------------------------------

    unsafe extern "C" {
        // LocalContext.mkEmpty : Unit → LocalContext (returns an owned empty local ctx).
        fn lean_mk_empty_local_ctx(u: *mut LeanObject) -> *mut LeanObject;
        // Kernel.Environment.add (env cinfo) : Environment — pure insert (no dup check);
        // CONSUMES env + cinfo, returns the new env (owned). Matches C++ `environment::add`.
        fn lean_environment_add(env: *mut LeanObject, info: *mut LeanObject) -> *mut LeanObject;
        // Kernel diagnostics (Kernel.Environment / Diagnostics in Environment.lean). All take their
        // arguments OWNED (no `@&`); record_unfold/set_diag return owned results.
        fn lean_kernel_diag_is_enabled(d: *mut LeanObject) -> bool;
        fn lean_kernel_record_unfold(d: *mut LeanObject, name: *mut LeanObject) -> *mut LeanObject;
        fn lean_kernel_get_diag(env: *mut LeanObject) -> *mut LeanObject;
        fn lean_kernel_set_diag(env: *mut LeanObject, diag: *mut LeanObject) -> *mut LeanObject;
    }

    #[inline(always)]
    unsafe fn mk_empty_lctx() -> *mut LeanObject {
        lean_mk_empty_local_ctx(lean_box(0))
    }

    /// Begin a `scoped_diagnostics` (type_checker.cpp): if the env's diagnostics are enabled, return an
    /// owned copy of the `Diagnostics` to accumulate unfolds into; otherwise return null. `env` BORROWED.
    ///
    unsafe fn diag_begin(env: *mut LeanObject) -> *mut LeanObject {
        lean_inc(env);
        let d = lean_kernel_get_diag(env); // consumes the inc'd env, returns owned Diagnostics
        lean_inc(d);
        let enabled = lean_kernel_diag_is_enabled(d); // consumes the inc'd copy
        if enabled {
            d
        } else {
            lean_dec(d);
            ptr::null_mut()
        }
    }

    /// Write an accumulated `Diagnostics` back into the env (`scoped_diagnostics::update`). CONSUMES
    /// `env` and `diag` (when non-null); returns the (possibly updated) env.
    unsafe fn diag_update(env: *mut LeanObject, diag: *mut LeanObject) -> *mut LeanObject {
        if diag.is_null() {
            env
        } else {
            lean_kernel_set_diag(env, diag)
        }
    }

    /// Value of a def/thm/opaque declaration (BORROWED). `val` is field 0 of the
    /// `Declaration`/`ConstantInfo`; the val nests its `constant_val` at field 0 and stores the
    /// value at field 1 (matching C++ `definition_val::get_value() = cnstr_get_ref(*this, 1)`).
    #[inline(always)]
    unsafe fn decl_value(decl: *mut LeanObject) -> *mut LeanObject {
        lean_ctor_get(ci_to_val(decl), 1)
    }

    /// Port of `check_no_metavar_no_fvar`: declarations may not contain mvars/fvars.
    unsafe fn check_no_metavar_no_fvar(
        env: *mut LeanObject,
        name: *mut LeanObject,
        e: *mut LeanObject,
    ) -> Result<(), KernelError> {
        if expr_has_expr_mvar(e) {
            lean_inc(env);
            lean_inc(name);
            lean_inc(e);
            return Err(KernelError::DeclHasMVars { env, name, expr: e });
        }
        if expr_has_fvar(e) {
            lean_inc(env);
            lean_inc(name);
            lean_inc(e);
            return Err(KernelError::DeclHasFVars { env, name, expr: e });
        }
        Ok(())
    }

    /// Port of `check_name` (errors if `name` is already declared). `env`/`name` borrowed.
    unsafe fn check_name_dup(
        env: *mut LeanObject,
        name: *mut LeanObject,
    ) -> Result<(), KernelError> {
        let info = env_find(env, name); // owned ConstantInfo, or boxed scalar when absent
        if lean_is_scalar(info) {
            return Ok(());
        }
        lean_dec(info);
        lean_inc(env);
        lean_inc(name);
        Err(KernelError::AlreadyDeclared { env, name })
    }

    /// Port of `check_duplicated_univ_params`: error if a level param repeats.
    unsafe fn check_duplicated_univ_params(
        env: *mut LeanObject,
        lparams: *mut LeanObject,
    ) -> Result<(), KernelError> {
        let mut l = lparams;
        while !lean_list_is_nil(l) {
            let p = lean_list_head(l);
            let mut rest = lean_list_tail(l);
            while !lean_list_is_nil(rest) {
                if lean_name_eq(p, lean_list_head(rest)) {
                    let _ = env;
                    let msg = lean_mk_string_from_bytes(
                    b"failed to add declaration to environment, duplicate universe level parameter".as_ptr().cast(),
                    78);
                    return Err(KernelError::Other { msg });
                }
                rest = lean_list_tail(rest);
            }
            l = lean_list_tail(l);
        }
        Ok(())
    }

    /// Port of `check_constant_val`: name not duplicated, no duplicate univ params, the type is
    /// metavar/fvar-free, and the type is itself a sort. `tc`'s env is borrowed.
    unsafe fn check_constant_val(
        tc: &mut TypeChecker,
        decl: *mut LeanObject,
    ) -> Result<(), KernelError> {
        let env = tc.env();
        let name = lean_constant_info_get_name(decl);
        let lparams = lean_constant_info_get_lparams(decl);
        let ty = lean_constant_info_get_type(decl);
        check_name_dup(env, name)?;
        check_duplicated_univ_params(env, lparams)?;
        check_no_metavar_no_fvar(env, name, ty)?;
        let sort = tc.check(ty, lparams)?;
        // ensure_sort_core CONSUMES `sort` and returns an owned sort; do not dec `sort` again.
        let s2 = tc.ensure_sort_core(sort, ty)?;
        lean_dec(s2);
        Ok(())
    }

    /// Check the value of a def/thm/opaque against its declared type. `tc`'s env is borrowed.
    unsafe fn check_decl_value(
        tc: &mut TypeChecker,
        decl: *mut LeanObject,
    ) -> Result<(), KernelError> {
        let env = tc.env();
        let name = lean_constant_info_get_name(decl);
        let lparams = lean_constant_info_get_lparams(decl);
        let ty = lean_constant_info_get_type(decl);
        let val = decl_value(decl);
        check_no_metavar_no_fvar(env, name, val)?;
        let val_type = tc.check(val, lparams)?;
        let ok = tc.is_def_eq(val_type, ty)?;
        if !ok {
            // `givenType` in the error is the INFERRED type of the value (val_type), and the message's
            // "expected to have type" is `decl.type` (Message.lean: declTypeMismatch). val_type is owned
            // and moves into the error — do NOT dec it here.
            lean_inc(env);
            lean_inc(decl);
            return Err(KernelError::DeclTypeMismatch {
                env,
                decl,
                given_type: val_type,
            });
        }
        lean_dec(val_type);
        Ok(())
    }

    /// Port of `environment::add_axiom/add_definition/add_theorem/add_opaque`.
    /// CONSUMES `env`, BORROWS `decl`. `kind` ∈ {0=axiom,1=def,2=thm,3=opaque}.
    unsafe fn add_decl_impl(
        env: *mut LeanObject,
        decl: *mut LeanObject,
        do_check: bool,
    ) -> Result<*mut LeanObject, KernelError> {
        let kind = lean_ptr_tag(decl);
        let is_unsafe = lean_constant_info_is_unsafe(decl);

        // Unsafe definitions: check the type, ADD, then check the value in the new env
        // (so the definition may reference itself). Mirrors add_definition's unsafe branch.
        if kind == 1 && is_unsafe {
            // scoped_diagnostics: accumulate unfolds across both passes, then write back.
            let mut diag = if do_check {
                diag_begin(env)
            } else {
                ptr::null_mut()
            };
            if do_check {
                let lctx = mk_empty_lctx();
                let mut tc = TypeChecker::new(env, lctx, DEF_SAFETY_UNSAFE);
                lean_dec(lctx); // tc took its own inc; release the owned ref from mk_empty_lctx
                tc.diag = diag;
                let r = check_constant_val(&mut tc, decl);
                diag = tc.take_diag();
                drop(tc);
                if let Err(e) = r {
                    if !diag.is_null() {
                        lean_dec(diag);
                    }
                    lean_dec(env);
                    return Err(e);
                }
            }
            lean_inc(decl);
            let new_env = lean_environment_add(env, decl); // consumes env + inc'd decl
            if do_check {
                let lctx = mk_empty_lctx();
                let mut tc = TypeChecker::new(new_env, lctx, DEF_SAFETY_UNSAFE);
                lean_dec(lctx); // tc took its own inc; release the owned ref from mk_empty_lctx
                tc.diag = diag;
                let r = check_decl_value(&mut tc, decl);
                diag = tc.take_diag();
                drop(tc);
                if let Err(e) = r {
                    if !diag.is_null() {
                        lean_dec(diag);
                    }
                    lean_dec(new_env);
                    return Err(e);
                }
            }
            return Ok(diag_update(new_env, diag));
        }

        // Axiom / safe(+partial) definition / theorem / opaque: check everything in the
        // current env, then add.
        let mut diag: *mut LeanObject = ptr::null_mut();
        if do_check {
            diag = diag_begin(env);
            // Axiom uses unsafe-mode iff the axiom is unsafe; the others use safe mode.
            let ds = if kind == 0 && is_unsafe {
                DEF_SAFETY_UNSAFE
            } else {
                DEF_SAFETY_SAFE
            };
            let lctx = mk_empty_lctx();
            let mut tc = TypeChecker::new(env, lctx, ds);
            lean_dec(lctx); // tc took its own inc; release the owned ref from mk_empty_lctx
            tc.diag = diag;
            let r: Result<(), KernelError> = (|| {
                check_constant_val(&mut tc, decl)?;
                if kind == 2 {
                    // theorem: the type must be a proposition (C++ add_theorem: is_prop(type))
                    let ty = lean_constant_info_get_type(decl);
                    if !tc.is_prop(ty)? {
                        let env2 = tc.env();
                        let name = lean_constant_info_get_name(decl);
                        lean_inc(env2);
                        lean_inc(name);
                        lean_inc(ty);
                        return Err(KernelError::ThmTypeIsNotProp {
                            env: env2,
                            name,
                            ty,
                        });
                    }
                }
                if kind != 0 {
                    // def/thm/opaque carry a value
                    check_decl_value(&mut tc, decl)?;
                }
                Ok(())
            })();
            diag = tc.take_diag();
            drop(tc);
            if let Err(e) = r {
                if !diag.is_null() {
                    lean_dec(diag);
                }
                lean_dec(env);
                return Err(e);
            }
        }

        lean_inc(decl);
        let new_env = lean_environment_add(env, decl); // consumes env + inc'd decl
        Ok(diag_update(new_env, diag))
    }

    /// Wrap a `DefinitionVal` (BORROWED) as a `ConstantInfo.defnInfo` (tag 1). Returns an OWNED ctor.
    #[inline]
    unsafe fn wrap_defn_info(v: *mut LeanObject) -> *mut LeanObject {
        let w = lean_alloc_ctor(CI_DEFINITION, 1, 0);
        lean_inc(v);
        lean_ctor_set(w, 0, v);
        w
    }

    /// Port of `environment::add_mutual` (type_checker.cpp). CONSUMES `env`, BORROWS `decl`
    /// (= `Declaration.mutualDefnDecl`, field 0 = `List DefinitionVal`). The definitions must all be
    /// unsafe/partial with the same safety. Checks each constant-val, adds all (so they may reference
    /// each other), then checks each value against its type in the extended env.
    unsafe fn add_mutual_impl(
        env: *mut LeanObject,
        decl: *mut LeanObject,
        do_check: bool,
    ) -> Result<*mut LeanObject, KernelError> {
        let defns = lean_ctor_get(decl, 0); // List DefinitionVal (borrowed)
        if lean_list_is_nil(defns) {
            lean_dec(env);
            let msg =
                lean_mk_string_from_bytes(b"invalid empty mutual definition".as_ptr().cast(), 31);
            return Err(KernelError::Other { msg });
        }
        let safety = lean_constant_info_get_safety(lean_list_head(defns));
        if safety == DEF_SAFETY_SAFE {
            lean_dec(env);
            let msg = lean_mk_string_from_bytes(
                b"invalid mutual definition, declaration is not tagged as unsafe/partial"
                    .as_ptr()
                    .cast(),
                69,
            );
            return Err(KernelError::Other { msg });
        }

        // scoped_diagnostics: shared across both passes (matches C++ add_mutual).
        let mut diag = if do_check {
            diag_begin(env)
        } else {
            ptr::null_mut()
        };

        // Pass 1: check each constant-val in the current env.
        if do_check {
            let lctx = mk_empty_lctx();
            let mut tc = TypeChecker::new(env, lctx, safety);
            lean_dec(lctx);
            tc.diag = diag;
            let r: Result<(), KernelError> = (|| {
                let mut cur = defns;
                while !lean_list_is_nil(cur) {
                    let v = lean_list_head(cur);
                    if lean_constant_info_get_safety(v) != safety {
                        let msg = lean_mk_string_from_bytes(
                        b"invalid mutual definition, declarations must have the same safety annotation".as_ptr().cast(), 75);
                        return Err(KernelError::Other { msg });
                    }
                    let wrapped = wrap_defn_info(v);
                    let res = check_constant_val(&mut tc, wrapped);
                    lean_dec(wrapped);
                    res?;
                    cur = lean_list_tail(cur);
                }
                Ok(())
            })();
            diag = tc.take_diag();
            drop(tc);
            if let Err(e) = r {
                if !diag.is_null() {
                    lean_dec(diag);
                }
                lean_dec(env);
                return Err(e);
            }
        }

        // Add all definitions to the env (each as a ConstantInfo.defnInfo).
        let mut new_env = env;
        let mut cur = defns;
        while !lean_list_is_nil(cur) {
            let wrapped = wrap_defn_info(lean_list_head(cur));
            new_env = lean_environment_add(new_env, wrapped); // consumes new_env + wrapped
            cur = lean_list_tail(cur);
        }

        // Pass 2: check each value against its type in the extended env.
        if do_check {
            let lctx = mk_empty_lctx();
            let mut tc = TypeChecker::new(new_env, lctx, safety);
            lean_dec(lctx);
            tc.diag = diag;
            let r: Result<(), KernelError> = (|| {
                let mut cur = defns;
                while !lean_list_is_nil(cur) {
                    let wrapped = wrap_defn_info(lean_list_head(cur));
                    let res = check_decl_value(&mut tc, wrapped);
                    lean_dec(wrapped);
                    res?;
                    cur = lean_list_tail(cur);
                }
                Ok(())
            })();
            diag = tc.take_diag();
            drop(tc);
            if let Err(e) = r {
                if !diag.is_null() {
                    lean_dec(diag);
                }
                lean_dec(new_env);
                return Err(e);
            }
        }

        Ok(diag_update(new_env, diag))
    }

    #[inline]
    unsafe fn lean_string_name(s: &str) -> *mut LeanObject {
        build_lean_name(&[s])
    }

    unsafe fn lean_list_from_borrowed(items: &[*mut LeanObject]) -> *mut LeanObject {
        let mut result = lean_mk_list_nil(ptr::null_mut());
        for &item in items.iter().rev() {
            lean_inc(item);
            result = lean_mk_list_cons(ptr::null_mut(), item, result);
        }
        result
    }

    #[inline]
    unsafe fn level_param_borrowed(name: *mut LeanObject) -> *mut LeanObject {
        lean_inc(name);
        lean_level_mk_param(name)
    }

    #[inline]
    unsafe fn sort_borrowed(level: *mut LeanObject) -> *mut LeanObject {
        lean_inc(level);
        lean_expr_mk_sort(level)
    }

    #[inline]
    unsafe fn const_borrowed(name: *mut LeanObject, levels: &[*mut LeanObject]) -> *mut LeanObject {
        lean_inc(name);
        let ls = lean_list_from_borrowed(levels);
        lean_expr_mk_const(name, ls)
    }

    unsafe fn app_borrowed(mut f: *mut LeanObject, args: &[*mut LeanObject]) -> *mut LeanObject {
        for &arg in args {
            lean_inc(arg);
            f = lean_expr_mk_app(f, arg);
        }
        f
    }

    unsafe fn arrow_borrowed(domain: *mut LeanObject, body: *mut LeanObject) -> *mut LeanObject {
        let n = lean_name_anonymous();
        lean_inc(domain);
        lean_inc(body);
        lean_expr_mk_forall(n, domain, body, BI_DEFAULT)
    }

    unsafe fn local_decl(
        tc: &mut TypeChecker,
        name: &str,
        ty: *mut LeanObject,
        bi: u8,
    ) -> *mut LeanObject {
        let n = lean_string_name(name);
        let fvar = tc.lctx_mk_local_decl(n, ty, bi);
        lean_dec(n);
        fvar
    }

    unsafe fn pi_named(
        name: &str,
        domain: *mut LeanObject,
        body: *mut LeanObject,
    ) -> *mut LeanObject {
        let n = lean_string_name(name);
        lean_expr_mk_forall(n, domain, body, BI_DEFAULT)
    }

    unsafe fn wrap_quot_info(v: *mut LeanObject) -> *mut LeanObject {
        let w = lean_alloc_ctor(CI_QUOT, 1, 0);
        lean_ctor_set(w, 0, v);
        w
    }

    unsafe fn add_quot_const(
        env: *mut LeanObject,
        name: *mut LeanObject,
        lparams: &[*mut LeanObject],
        ty: *mut LeanObject,
        kind: u8,
    ) -> *mut LeanObject {
        lean_inc(name);
        let ps = lean_list_from_borrowed(lparams);
        let qv = lean_mk_quot_val(name, ps, ty, kind);
        let info = wrap_quot_info(qv);
        lean_environment_add(env, info)
    }

    unsafe fn quot_error(msg: &'static [u8]) -> KernelError {
        KernelError::Other {
            msg: lean_mk_string(msg.as_ptr(), msg.len()),
        }
    }

    /// Port of `quot_detail::check_eq_type` (kernel/quot.cpp). `env` is BORROWED.
    unsafe fn check_eq_type_for_quot(env: *mut LeanObject) -> Result<(), KernelError> {
        let eq_name = build_lean_name(&["Eq"]);
        let eq_info = env_find(env, eq_name);
        if lean_is_scalar(eq_info) {
            lean_dec(eq_name);
            return Err(quot_error(
                b"failed to initialize quot module, environment does not have 'Eq' type",
            ));
        }
        if !lean_constant_info_is_inductive(eq_info) {
            lean_dec(eq_name);
            lean_dec(eq_info);
            return Err(quot_error(
                b"failed to initialize quot module, environment does not have 'Eq' type",
            ));
        }
        let eq_lparams = lean_constant_info_get_lparams(eq_info);
        let eq_val = lean_constant_info_to_inductive_val(eq_info);
        if lean_list_length(eq_lparams) != 1 {
            lean_dec(eq_name);
            lean_dec(eq_info);
            return Err(quot_error(b"failed to initialize quot module, unexpected number of universe params at 'Eq' type"));
        }
        let eq_cnstrs = lean_inductive_val_get_cnstrs(eq_val);
        if lean_list_length(eq_cnstrs) != 1 {
            lean_dec(eq_name);
            lean_dec(eq_info);
            return Err(quot_error(b"failed to initialize quot module, unexpected number of constructors for 'Eq' type"));
        }

        let lctx = mk_empty_lctx();
        let mut tc = TypeChecker::new(env, lctx, DEF_SAFETY_SAFE);
        lean_dec(lctx);

        let u = level_param_borrowed(lean_list_head(eq_lparams));
        let sort_u = sort_borrowed(u);
        let alpha = local_decl(&mut tc, "α", sort_u, BI_IMPLICIT);
        let alpha_to_prop = arrow_borrowed(alpha, lean_expr_mk_prop());
        let alpha_to_alpha_to_prop = arrow_borrowed(alpha, alpha_to_prop);
        let expected_eq_type = tc.lctx_mk_pi(&[alpha], alpha_to_alpha_to_prop, false);
        if !lean_expr_eqv(expected_eq_type, lean_constant_info_get_type(eq_info)) {
            lean_dec(u);
            lean_dec(sort_u);
            lean_dec(alpha);
            lean_dec(alpha_to_prop);
            lean_dec(alpha_to_alpha_to_prop);
            lean_dec(expected_eq_type);
            drop(tc);
            lean_dec(eq_name);
            lean_dec(eq_info);
            return Err(quot_error(
                b"failed to initialize quot module, 'Eq' has an expected type",
            ));
        }
        lean_dec(u);
        lean_dec(sort_u);
        lean_dec(alpha);
        lean_dec(alpha_to_prop);
        lean_dec(alpha_to_alpha_to_prop);
        lean_dec(expected_eq_type);

        let eq_refl_info = env_find(env, lean_list_head(eq_cnstrs));
        if lean_is_scalar(eq_refl_info) {
            drop(tc);
            lean_dec(eq_name);
            lean_dec(eq_info);
            return Err(quot_error(
                b"failed to initialize quot module, unexpected type for 'Eq' type constructor",
            ));
        }
        let u2 = level_param_borrowed(lean_list_head(lean_constant_info_get_lparams(eq_refl_info)));
        let sort_u2 = sort_borrowed(u2);
        let alpha2 = local_decl(&mut tc, "α", sort_u2, BI_IMPLICIT);
        let a = local_decl(&mut tc, "a", alpha2, BI_DEFAULT);
        let eq_const = const_borrowed(eq_name, &[u2]);
        let eq_refl_body = app_borrowed(eq_const, &[alpha2, a, a]);
        let expected_eq_refl_type = tc.lctx_mk_pi(&[alpha2, a], eq_refl_body, false);
        if !lean_expr_eqv(
            expected_eq_refl_type,
            lean_constant_info_get_type(eq_refl_info),
        ) {
            lean_dec(u2);
            lean_dec(sort_u2);
            lean_dec(alpha2);
            lean_dec(a);
            lean_dec(eq_refl_body);
            lean_dec(expected_eq_refl_type);
            lean_dec(eq_refl_info);
            drop(tc);
            lean_dec(eq_name);
            lean_dec(eq_info);
            return Err(quot_error(
                b"failed to initialize quot module, unexpected type for 'Eq' type constructor",
            ));
        }
        lean_dec(u2);
        lean_dec(sort_u2);
        lean_dec(alpha2);
        lean_dec(a);
        lean_dec(eq_refl_body);
        lean_dec(expected_eq_refl_type);
        lean_dec(eq_refl_info);
        drop(tc);
        lean_dec(eq_name);
        lean_dec(eq_info);
        Ok(())
    }

    /// Port of `environment::add_quot` (kernel/quot.cpp). CONSUMES `env`.
    unsafe fn add_quot_impl(env: *mut LeanObject) -> Result<*mut LeanObject, KernelError> {
        if lean_environment_is_quot_initialized(env) {
            return Ok(env);
        }
        check_eq_type_for_quot(env)?;

        let lctx = mk_empty_lctx();
        let mut tc = TypeChecker::new(env, lctx, DEF_SAFETY_SAFE);
        lean_dec(lctx);

        let u_name = lean_string_name("u");
        let u = level_param_borrowed(u_name);
        let sort_u = sort_borrowed(u);
        let alpha = local_decl(&mut tc, "α", sort_u, BI_IMPLICIT);
        let alpha_to_prop = arrow_borrowed(alpha, lean_expr_mk_prop());
        let r_ty = arrow_borrowed(alpha, alpha_to_prop);
        let r = local_decl(&mut tc, "r", r_ty, BI_DEFAULT);

        let quot_ty = tc.lctx_mk_pi(&[alpha, r], sort_u, false);
        let quot_name = build_lean_name(&["Quot"]);
        let mut new_env = add_quot_const(env, quot_name, &[u_name], quot_ty, QUOT_KIND_TYPE);

        let quot_const = const_borrowed(quot_name, &[u]);
        let quot_r = app_borrowed(quot_const, &[alpha, r]);
        let a = local_decl(&mut tc, "a", alpha, BI_DEFAULT);
        let quot_mk_ty = tc.lctx_mk_pi(&[alpha, r, a], quot_r, false);
        let quot_mk_name = load_global(&G_QUOT_MK_NAME);
        new_env = add_quot_const(new_env, quot_mk_name, &[u_name], quot_mk_ty, QUOT_KIND_CTOR);

        drop(tc);

        let lctx2 = mk_empty_lctx();
        let mut tc = TypeChecker::new(new_env, lctx2, DEF_SAFETY_SAFE);
        lean_dec(lctx2);
        let alpha2 = local_decl(&mut tc, "α", sort_u, BI_IMPLICIT);
        let alpha2_to_prop = arrow_borrowed(alpha2, lean_expr_mk_prop());
        let r2_ty = arrow_borrowed(alpha2, alpha2_to_prop);
        let r2 = local_decl(&mut tc, "r", r2_ty, BI_IMPLICIT);
        let quot_const2 = const_borrowed(quot_name, &[u]);
        let quot_r2 = app_borrowed(quot_const2, &[alpha2, r2]);
        let a2 = local_decl(&mut tc, "a", alpha2, BI_DEFAULT);
        let v_name = lean_string_name("v");
        let v = level_param_borrowed(v_name);
        let sort_v = sort_borrowed(v);
        let beta = local_decl(&mut tc, "β", sort_v, BI_IMPLICIT);
        let alpha2_to_beta = arrow_borrowed(alpha2, beta);
        let f = local_decl(&mut tc, "f", alpha2_to_beta, BI_DEFAULT);
        let b = local_decl(&mut tc, "b", alpha2, BI_DEFAULT);
        let r_a_b = app_borrowed(r2, &[a2, b]);
        let eq_const_v = const_borrowed(build_lean_name(&["Eq"]), &[v]);
        let f_a = app_borrowed(f, &[a2]);
        let f_b = app_borrowed(f, &[b]);
        let f_a_eq_f_b = app_borrowed(eq_const_v, &[beta, f_a, f_b]);
        let r_to_eq = arrow_borrowed(r_a_b, f_a_eq_f_b);
        let sanity = tc.lctx_mk_pi(&[a2, b], r_to_eq, false);
        let quot_r_to_beta = arrow_borrowed(quot_r2, beta);
        let lift_tail = arrow_borrowed(sanity, quot_r_to_beta);
        let lift_ty = tc.lctx_mk_pi(&[alpha2, r2, beta, f], lift_tail, false);
        new_env = add_quot_const(
            new_env,
            load_global(&G_QUOT_LIFT_NAME),
            &[u_name, v_name],
            lift_ty,
            QUOT_KIND_LIFT,
        );

        let quot_r2_to_prop = arrow_borrowed(quot_r2, lean_expr_mk_prop());
        let beta2 = local_decl(&mut tc, "β", quot_r2_to_prop, BI_IMPLICIT);
        let quot_mk_const = const_borrowed(quot_mk_name, &[u]);
        let quot_mk_a = app_borrowed(quot_mk_const, &[alpha2, r2, a2]);
        let beta_quot_mk_a = app_borrowed(beta2, &[quot_mk_a]);
        let all_quot = tc.lctx_mk_pi(&[a2], beta_quot_mk_a, false);
        let q = local_decl(&mut tc, "q", quot_r2, BI_DEFAULT);
        let beta_q = app_borrowed(beta2, &[q]);
        let ind_q_tail = tc.lctx_mk_pi(&[q], beta_q, false);
        let ind_mk_tail = pi_named("mk", all_quot, ind_q_tail);
        let ind_ty = tc.lctx_mk_pi(&[alpha2, r2, beta2], ind_mk_tail, false);
        new_env = add_quot_const(
            new_env,
            load_global(&G_QUOT_IND_NAME),
            &[u_name],
            ind_ty,
            QUOT_KIND_IND,
        );

        drop(tc);
        // These quotient declarations are built once per kernel environment. Releasing the local
        // construction temporaries here currently corrupts `Environment.replay`/`Quot.sound`; keep the
        // objects alive until the exact C++ RAII ownership pattern is mirrored.

        Ok(lean_environment_mark_quot_init(new_env))
    }

    // ===========================================================================
    // add_inductive — port of kernel/inductive.cpp
    //
    // Refcount discipline mirrors `add_quot_impl`/`add_decl_impl`: construction
    // temporaries (fvars, intermediate exprs) are intentionally leaked; only the
    // VALUES handed to the environment builders need correct ownership (the
    // `lean_mk_*_val` builders CONSUME their object args, like C++ `obj_arg`).
    // ===========================================================================

    unsafe extern "C" {
        // @[export] builders from Lean's Declaration (declaration.cpp wraps these). All object args
        // are CONSUMED; trailing u8 args are plain scalars.
        fn lean_mk_inductive_val(
            n: *mut LeanObject,
            lparams: *mut LeanObject,
            type_: *mut LeanObject,
            nparams: *mut LeanObject,
            nindices: *mut LeanObject,
            all: *mut LeanObject,
            cnstrs: *mut LeanObject,
            nnested: *mut LeanObject,
            rec: bool,
            is_unsafe: bool,
            is_refl: bool,
        ) -> *mut LeanObject;
        fn lean_mk_constructor_val(
            n: *mut LeanObject,
            lparams: *mut LeanObject,
            type_: *mut LeanObject,
            induct: *mut LeanObject,
            cidx: *mut LeanObject,
            nparams: *mut LeanObject,
            nfields: *mut LeanObject,
            is_unsafe: bool,
        ) -> *mut LeanObject;
        fn lean_mk_recursor_val(
            n: *mut LeanObject,
            lparams: *mut LeanObject,
            type_: *mut LeanObject,
            all: *mut LeanObject,
            nparams: *mut LeanObject,
            nindices: *mut LeanObject,
            nmotives: *mut LeanObject,
            nminors: *mut LeanObject,
            rules: *mut LeanObject,
            k: bool,
            is_unsafe: bool,
        ) -> *mut LeanObject;
        fn lean_mk_inductive_decl(
            lparams: *mut LeanObject,
            nparams: *mut LeanObject,
            types: *mut LeanObject,
            is_unsafe: bool,
        ) -> *mut LeanObject;
        fn lean_is_unsafe_inductive_decl(d: *mut LeanObject) -> bool;
        // Name ops (obj_arg → owned).
        fn lean_name_append_index_after(n: *mut LeanObject, i: *mut LeanObject) -> *mut LeanObject;
        fn lean_name_replace_prefix(
            n: *mut LeanObject,
            pre: *mut LeanObject,
            new_pre: *mut LeanObject,
        ) -> *mut LeanObject;
        // Expr traversal callbacks (from kernel_for_each_fn.rs / kernel_replace_fn.rs).
        fn lean_for_each_expr_with_callback(
            e: *mut LeanObject,
            ctx: *mut c_void,
            cb: unsafe fn(*mut c_void, *mut LeanObject, u32) -> bool,
        );
        fn lean_replace_expr_with_callback(
            e: *mut LeanObject,
            ctx: *mut c_void,
            cb: unsafe fn(*mut c_void, *mut LeanObject, u32) -> *mut LeanObject,
            use_cache: bool,
        ) -> *mut LeanObject;
    }

    #[inline]
    unsafe fn nat_box(n: usize) -> *mut LeanObject {
        lean_usize_to_nat(n)
    }

    /// Wrap a `*Val` in a `ConstantInfo` constructor (tag = CI kind, one object field).
    unsafe fn wrap_ci(tag: u32, v: *mut LeanObject) -> *mut LeanObject {
        let w = lean_alloc_ctor(tag, 1, 0);
        lean_ctor_set(w, 0, v);
        w
    }

    /// Collect a Lean `List` into a Vec of BORROWED element pointers (list order).
    unsafe fn list_to_vec(mut l: *mut LeanObject) -> Vec<*mut LeanObject> {
        let mut v = Vec::new();
        while !lean_list_is_nil(l) {
            v.push(lean_list_head(l));
            l = lean_list_tail(l);
        }
        v
    }

    /// `is_constant(e)` — true iff `e` is an `Expr.const`.
    #[inline]
    unsafe fn ind_is_constant(e: *const LeanObject) -> bool {
        !lean_is_scalar(e) && lean_ptr_tag(e) == EXPR_CONST
    }

    /// Strip the application spine: returns `(fn, args)` with `args` in application order,
    /// all BORROWED (sub-references of `e`).
    unsafe fn ind_get_app_args(e: *const LeanObject) -> (*mut LeanObject, Vec<*mut LeanObject>) {
        let mut args = Vec::new();
        let mut cur = e;
        while !lean_is_scalar(cur) && lean_ptr_tag(cur) == EXPR_APP {
            args.push(lean_expr_get_app_arg(cur));
            cur = lean_expr_get_app_fn(cur);
        }
        args.reverse();
        (cur, args)
    }

    /// `mk_rec_name(I) = I.str "rec"`. BORROWS `i`, returns owned name.
    unsafe fn mk_rec_name(i: *const LeanObject) -> *mut LeanObject {
        lean_inc(i);
        let s = lean_mk_string(b"rec".as_ptr(), 3);
        lean_name_mk_string(i as *mut LeanObject, s)
    }

    /// `name.append_after(i)` (`Name.appendIndexAfter`). BORROWS `n`, returns owned name.
    unsafe fn name_append_index(n: *const LeanObject, idx: usize) -> *mut LeanObject {
        lean_inc(n);
        lean_name_append_index_after(n as *mut LeanObject, nat_box(idx))
    }

    /// `name.append_after(s)` (`Name.appendAfter` with a string). BORROWS `n`, returns owned name.
    unsafe fn name_append_str(n: *const LeanObject, s: &str) -> *mut LeanObject {
        lean_inc(n);
        // Build the suffix Name (`Name.str anonymous s`) then append its single string component.
        let str_obj = lean_mk_string(s.as_ptr(), s.len());
        // `lean_name_append_after` takes the suffix as a Lean String, not a Name.
        name_append_after_string(n as *mut LeanObject, str_obj)
    }

    /// `name.replace_prefix(pre, new)`. BORROWS all three, returns owned name.
    unsafe fn name_replace_prefix(
        n: *const LeanObject,
        pre: *const LeanObject,
        new_pre: *const LeanObject,
    ) -> *mut LeanObject {
        lean_inc(n);
        lean_inc(pre);
        lean_inc(new_pre);
        lean_name_replace_prefix(
            n as *mut LeanObject,
            pre as *mut LeanObject,
            new_pre as *mut LeanObject,
        )
    }

    /// `n1 + n2` for Lean names. BORROWS both, returns owned.
    unsafe fn name_append_name(n1: *const LeanObject, n2: *const LeanObject) -> *mut LeanObject {
        enum NamePart {
            Str(*mut LeanObject),
            Num(*mut LeanObject),
        }
        let mut parts = Vec::new();
        let mut cur = n2;
        while !lean_is_scalar(cur) {
            let tag = lean_ptr_tag(cur);
            let part = lean_ctor_get(cur, 1);
            parts.push(if tag == 1 {
                NamePart::Str(part)
            } else {
                NamePart::Num(part)
            });
            cur = lean_ctor_get(cur, 0);
        }
        lean_inc(n1);
        let mut r = n1 as *mut LeanObject;
        for part in parts.iter().rev() {
            match *part {
                NamePart::Str(s) => {
                    lean_inc(s);
                    r = lean_name_mk_string(r, s);
                }
                NamePart::Num(n) => {
                    lean_inc(n);
                    r = lean_name_mk_numeral(r, n);
                }
            }
        }
        r
    }

    /// `lparams_to_levels(ps)` — map `List Name` to `List Level` of `Level.param`. BORROWS `ps`.
    unsafe fn lparams_to_levels(ps: *const LeanObject) -> *mut LeanObject {
        let names = list_to_vec(ps as *mut LeanObject);
        let levels: Vec<*mut LeanObject> = names.iter().map(|&n| level_param_borrowed(n)).collect();
        let r = lean_list_from_borrowed(&levels);
        for l in levels {
            lean_dec(l);
        }
        r
    }

    // `lean_name_append_after(n, str)` — append a String component. CONSUMES n + str.
    unsafe fn name_append_after_string(n: *mut LeanObject, s: *mut LeanObject) -> *mut LeanObject {
        lean_name_append_after_extern(n, s)
    }

    unsafe extern "C" {
        fn lean_name_append_after_extern(n: *mut LeanObject, s: *mut LeanObject)
        -> *mut LeanObject;
    }

    /// Does `e` contain a subterm `Expr.const c` with `c` ∈ `names`?  (`find` + `is_ind_occ`).
    struct FindConstCtx<'a> {
        names: &'a [*mut LeanObject],
        found: bool,
    }
    unsafe fn find_const_cb(ctx: *mut c_void, e: *mut LeanObject, _depth: u32) -> bool {
        let c = &mut *(ctx as *mut FindConstCtx);
        if c.found {
            return false;
        }
        if ind_is_constant(e) {
            let nm = lean_expr_get_const_name(e);
            for &n in c.names {
                if lean_name_eq(nm, n) {
                    c.found = true;
                    return false;
                }
            }
        }
        true
    }
    unsafe fn expr_contains_const(e: *const LeanObject, names: &[*mut LeanObject]) -> bool {
        let mut ctx = FindConstCtx {
            names,
            found: false,
        };
        lean_for_each_expr_with_callback(
            e,
            &mut ctx as *mut FindConstCtx as *mut c_void,
            find_const_cb,
        );
        ctx.found
    }

    unsafe fn kernel_exc(msg: &str) -> KernelError {
        KernelError::Other {
            msg: lean_mk_string(msg.as_ptr(), msg.len()),
        }
    }

    unsafe fn some_expr(e: *mut LeanObject) -> *mut LeanObject {
        let r = lean_alloc_ctor(1, 1, 0);
        lean_ctor_set(r, 0, e);
        r
    }

    unsafe extern "C" {
        fn lean_expr_consume_type_annotations(e: *mut LeanObject) -> *mut LeanObject;
    }

    /// Per-recursor working data (mirrors C++ `add_inductive_fn::rec_info`).
    struct RecInfo {
        c: *mut LeanObject, // motive fvar
        minors: Vec<*mut LeanObject>,
        indices: Vec<*mut LeanObject>,
        major: *mut LeanObject,
    }

    /// Port of C++ `add_inductive_fn`. Holds one persistent `TypeChecker` for the whole add (so its
    /// name generator + local context evolve continuously, giving unique fvar ids); `tc.add_core`
    /// extends the env as declarations are added. Construction temporaries are leaked, matching
    /// `add_quot_impl`/`add_decl_impl`; only env-bound values are refcount-correct.
    struct AddInductiveFn {
        tc: TypeChecker,
        lparams: *mut LeanObject, // borrowed (List Name) from the decl
        nparams: usize,
        is_unsafe: bool,
        ind_types: Vec<*mut LeanObject>, // borrowed InductiveType objects
        ind_names: Vec<*mut LeanObject>, // borrowed Name of each inductive type
        nindices: Vec<usize>,
        result_level: *mut LeanObject, // owned Level (null until set)
        levels: *mut LeanObject,       // owned List Level (null until set)
        is_not_zero: bool,
        params: Vec<*mut LeanObject>,      // parameter fvars (owned)
        param_types: Vec<*mut LeanObject>, // type of each parameter (owned, consume-annotated)
        ind_cnsts: Vec<*mut LeanObject>,   // `Expr.const I levels` for each inductive type (owned)
        elim_level: *mut LeanObject,       // owned Level (null until set)
        k_target: bool,
        nnested: usize,
        rec_infos: Vec<RecInfo>,
    }

    impl AddInductiveFn {
        /// CONSUMES `env`; BORROWS `decl` (an `inductive_decl` = `Declaration.inductDecl`).
        unsafe fn new(env: *mut LeanObject, decl: *mut LeanObject, nnested: usize) -> Self {
            let lparams = lean_ctor_get(decl, 0); // List Name (borrowed)
            let nparams_nat = lean_ctor_get(decl, 1); // Nat
            let nparams = lean_unbox(nparams_nat); // small (kernel guarantees)
            let types = lean_ctor_get(decl, 2); // List InductiveType (borrowed)
            lean_inc(decl);
            let is_unsafe = lean_is_unsafe_inductive_decl(decl);
            let ind_types = list_to_vec(types);
            let ind_names: Vec<*mut LeanObject> =
                ind_types.iter().map(|&it| lean_ctor_get(it, 0)).collect();
            let safety = if is_unsafe {
                DEF_SAFETY_UNSAFE
            } else {
                DEF_SAFETY_SAFE
            };
            let lctx = mk_empty_lctx();
            let mut tc = TypeChecker::new(env, lctx, safety);
            tc.st.ngen = NameGenerator::new(load_global(&G_IND_FRESH));
            lean_dec(lctx);
            lean_dec(env); // TypeChecker::new inc'd env; drop the consumed caller ref.
            AddInductiveFn {
                tc,
                lparams,
                nparams,
                is_unsafe,
                ind_types,
                ind_names,
                nindices: Vec::new(),
                result_level: ptr::null_mut(),
                levels: ptr::null_mut(),
                is_not_zero: false,
                params: Vec::new(),
                param_types: Vec::new(),
                ind_cnsts: Vec::new(),
                elim_level: ptr::null_mut(),
                k_target: false,
                nnested,
                rec_infos: Vec::new(),
            }
        }

        #[inline]
        unsafe fn env(&self) -> *mut LeanObject {
            self.tc.env()
        }

        /// `m_lctx.mk_local_decl(m_ngen, name, consume_type_annotations(ty), bi)`. BORROWS name + ty.
        unsafe fn mk_local_decl(
            &mut self,
            name_obj: *mut LeanObject,
            ty: *mut LeanObject,
            bi: u8,
        ) -> *mut LeanObject {
            lean_inc(ty);
            let ty2 = lean_expr_consume_type_annotations(ty); // owned, stripped
            let fvar = self.tc.lctx_mk_local_decl(name_obj, ty2, bi); // borrows name + ty2
            lean_dec(ty2);
            fvar
        }

        /// `mk_local_decl` for the binder at the head of Pi `t`. BORROWS `t`.
        unsafe fn mk_local_decl_for(&mut self, t: *mut LeanObject) -> *mut LeanObject {
            let name = lean_expr_get_binding_name(t);
            let domain = lean_expr_get_binding_domain(t);
            let bi = lean_expr_get_binding_info(t);
            self.mk_local_decl(name, domain, bi)
        }

        /// `instantiate(binding_body(t), v)`. BORROWS `t` and `v`; returns owned.
        #[inline]
        unsafe fn inst_body(&self, t: *mut LeanObject, v: *mut LeanObject) -> *mut LeanObject {
            let body = lean_expr_get_binding_body(t);
            lean_expr_instantiate1(body, v)
        }

        /// `check_inductive_types` (inductive.cpp): every datatype's type is well-typed with no
        /// mvars/fvars, all share the same parameters and result universe; initializes `levels`,
        /// `result_level`, `nindices`, `ind_cnsts`, `params`.
        unsafe fn check_inductive_types(&mut self) -> Result<(), KernelError> {
            self.levels = lparams_to_levels(self.lparams);
            let mut first = true;
            let ind_types = self.ind_types.clone();
            for &ind_type in &ind_types {
                let name = lean_ctor_get(ind_type, 0);
                let ty0 = lean_ctor_get(ind_type, 1);
                check_name_dup(self.env(), name)?;
                let rn = mk_rec_name(name);
                let rn_dup = check_name_dup(self.env(), rn);
                lean_dec(rn);
                rn_dup?;
                check_no_metavar_no_fvar(self.env(), name, ty0)?;
                let sort = self.tc.check(ty0, self.lparams)?;
                lean_dec(sort);
                self.nindices.push(0);
                let mut i: usize = 0;
                let mut ty = self.tc.whnf(ty0)?;
                while lean_expr_is_pi(ty) {
                    if i < self.nparams {
                        if first {
                            let param = self.mk_local_decl_for(ty);
                            let dom = lean_expr_get_binding_domain(ty);
                            lean_inc(dom);
                            let dom2 = lean_expr_consume_type_annotations(dom);
                            self.params.push(param);
                            self.param_types.push(dom2);
                            let nty = self.inst_body(ty, param);
                            lean_dec(ty);
                            ty = nty;
                        } else {
                            let dom = lean_expr_get_binding_domain(ty);
                            let pt = self.param_types[i];
                            if !self.tc.is_def_eq(dom, pt)? {
                                return Err(kernel_exc(
                                    "parameters of all inductive datatypes must match",
                                ));
                            }
                            let nty = self.inst_body(ty, self.params[i]);
                            lean_dec(ty);
                            ty = nty;
                        }
                        i += 1;
                    } else {
                        let local = self.mk_local_decl_for(ty);
                        let nty = self.inst_body(ty, local);
                        lean_dec(local);
                        lean_dec(ty);
                        ty = nty;
                        *self.nindices.last_mut().unwrap() += 1;
                    }
                    let w = self.tc.whnf(ty)?;
                    lean_dec(ty);
                    ty = w;
                }
                if i != self.nparams {
                    return Err(kernel_exc(
                        "number of parameters mismatch in inductive datatype declaration",
                    ));
                }
                let s = self.tc.ensure_sort(ty)?; // consumes ty
                let lvl = lean_expr_get_sort_level(s);
                if first {
                    lean_inc(lvl);
                    self.result_level = lvl;
                    self.is_not_zero = is_not_zero_level(self.result_level);
                } else if !is_equivalent_level(lvl, self.result_level)? {
                    lean_dec(s);
                    return Err(kernel_exc(
                        "mutually inductive types must live in the same universe",
                    ));
                }
                lean_dec(s);
                let levels_vec = list_to_vec(self.levels);
                let cnst = const_borrowed(name, &levels_vec);
                self.ind_cnsts.push(cnst);
                first = false;
            }
            Ok(())
        }
    }

    #[inline]
    unsafe fn level_is_zero(l: *const LeanObject) -> bool {
        level_kind(l) == LEVEL_ZERO
    }

    unsafe fn kernel_exc_string(s: String) -> KernelError {
        KernelError::Other {
            msg: lean_mk_string(s.as_ptr(), s.len()),
        }
    }

    impl AddInductiveFn {
        /// True iff the declaration is recursive (a constructor argument mentions a datatype being
        /// declared). Structural walk over the constructor types (no fvars introduced).
        unsafe fn is_rec(&self) -> bool {
            for &ind_type in &self.ind_types {
                for &cnstr in &list_to_vec(lean_ctor_get(ind_type, 2)) {
                    let mut t = lean_ctor_get(cnstr, 1);
                    while lean_expr_is_pi(t) {
                        if expr_contains_const(lean_expr_get_binding_domain(t), &self.ind_names) {
                            return true;
                        }
                        t = lean_expr_get_binding_body(t);
                    }
                }
            }
            false
        }

        /// True iff reflexive (a constructor takes a function argument returning a datatype being
        /// declared). Introduces fvars via `mk_local_decl_for` like C++.
        unsafe fn is_reflexive(&mut self) -> bool {
            let ind_types = self.ind_types.clone();
            for &ind_type in &ind_types {
                for &cnstr in &list_to_vec(lean_ctor_get(ind_type, 2)) {
                    let mut t = lean_ctor_get(cnstr, 1);
                    lean_inc(t);
                    while lean_expr_is_pi(t) {
                        let arg_type = lean_expr_get_binding_domain(t);
                        if lean_expr_is_pi(arg_type)
                            && expr_contains_const(arg_type, &self.ind_names)
                        {
                            lean_dec(t);
                            return true;
                        }
                        let local = self.mk_local_decl_for(t);
                        let nt = self.inst_body(t, local);
                        lean_dec(local);
                        lean_dec(t);
                        t = nt;
                    }
                    lean_dec(t);
                }
            }
            false
        }

        /// Add all inductive type declarations to the environment.
        unsafe fn declare_inductive_types(&mut self) -> Result<(), KernelError> {
            let rec = self.is_rec();
            let reflexive = self.is_reflexive();
            let all = lean_list_from_borrowed(&self.ind_names);
            for idx in 0..self.ind_types.len() {
                let ind_type = self.ind_types[idx];
                let n = lean_ctor_get(ind_type, 0);
                let ty = lean_ctor_get(ind_type, 1);
                let cnstr_names: Vec<*mut LeanObject> = list_to_vec(lean_ctor_get(ind_type, 2))
                    .iter()
                    .map(|&c| lean_ctor_get(c, 0))
                    .collect();
                check_name_dup(self.env(), n)?;
                lean_inc(n);
                lean_inc(self.lparams);
                lean_inc(ty);
                lean_inc(all);
                let cnstr_list = lean_list_from_borrowed(&cnstr_names);
                let v = lean_mk_inductive_val(
                    n,
                    self.lparams,
                    ty,
                    nat_box(self.nparams),
                    nat_box(self.nindices[idx]),
                    all,
                    cnstr_list,
                    nat_box(self.nnested),
                    rec,
                    self.is_unsafe,
                    reflexive,
                );
                let info = wrap_ci(CI_INDUCTIVE, v);
                self.tc.add_core(info);
            }
            lean_dec(all);
            Ok(())
        }

        /// `is_valid_ind_app(t, i)` — `t` is `I_i params indices` with no occurrence of a datatype
        /// being declared in the indices.
        unsafe fn is_valid_ind_app_i(&self, t: *const LeanObject, i: usize) -> bool {
            let (head, args) = ind_get_app_args(t);
            if !lean_expr_eqv(head, self.ind_cnsts[i])
                || args.len() != self.nparams + self.nindices[i]
            {
                return false;
            }
            for k in 0..self.nparams {
                if !lean_expr_eqv(self.params[k], args[k]) {
                    return false;
                }
            }
            for k in self.nparams..args.len() {
                if expr_contains_const(args[k], &self.ind_names) {
                    return false;
                }
            }
            true
        }

        unsafe fn is_valid_ind_app(&self, t: *const LeanObject) -> Option<usize> {
            (0..self.ind_types.len()).find(|&i| self.is_valid_ind_app_i(t, i))
        }

        /// `is_rec_argument(t)` — `Some(d_idx)` iff `t` is a recursive argument.
        unsafe fn is_rec_argument(
            &mut self,
            t: *mut LeanObject,
        ) -> Result<Option<usize>, KernelError> {
            let mut t = self.tc.whnf(t)?;
            while lean_expr_is_pi(t) {
                let local = self.mk_local_decl_for(t);
                let inst = self.inst_body(t, local);
                lean_dec(local);
                let w = self.tc.whnf(inst)?;
                lean_dec(inst);
                lean_dec(t);
                t = w;
            }
            let r = self.is_valid_ind_app(t);
            lean_dec(t);
            Ok(r)
        }

        /// Check that `t` contains only positive occurrences of the datatypes being declared.
        unsafe fn check_positivity(
            &mut self,
            t: *mut LeanObject,
            cnstr_name: *mut LeanObject,
            arg_idx: usize,
        ) -> Result<(), KernelError> {
            let t = self.tc.whnf(t)?;
            if !expr_contains_const(t, &self.ind_names) {
                // nonrecursive argument
            } else if lean_expr_is_pi(t) {
                if expr_contains_const(lean_expr_get_binding_domain(t), &self.ind_names) {
                    lean_dec(t);
                    return Err(kernel_exc_string(format!(
                        "arg #{} of '{}' has a non positive occurrence of the datatypes being declared",
                        arg_idx + 1,
                        lean_name_to_string(cnstr_name)
                    )));
                }
                let local = self.mk_local_decl_for(t);
                let body = self.inst_body(t, local);
                lean_dec(local);
                let r = self.check_positivity(body, cnstr_name, arg_idx);
                lean_dec(body);
                lean_dec(t);
                return r;
            } else if self.is_valid_ind_app(t).is_some() {
                // recursive argument
            } else {
                lean_dec(t);
                return Err(kernel_exc_string(format!(
                    "arg #{} of '{}' contains a non valid occurrence of the datatypes being declared",
                    arg_idx + 1,
                    lean_name_to_string(cnstr_name)
                )));
            }
            lean_dec(t);
            Ok(())
        }

        /// Check that every constructor is type-correct: parameters match, fields live in acceptable
        /// universes, positivity holds, and the return type is the right datatype application.
        unsafe fn check_constructors(&mut self) -> Result<(), KernelError> {
            let ind_types = self.ind_types.clone();
            for idx in 0..ind_types.len() {
                let mut seen: Vec<*mut LeanObject> = Vec::new();
                for &cnstr in &list_to_vec(lean_ctor_get(ind_types[idx], 2)) {
                    let n = lean_ctor_get(cnstr, 0);
                    if seen.iter().any(|&s| lean_name_eq(s, n)) {
                        return Err(kernel_exc_string(format!(
                            "duplicate constructor name '{}'",
                            lean_name_to_string(n)
                        )));
                    }
                    seen.push(n);
                    let t0 = lean_ctor_get(cnstr, 1);
                    check_name_dup(self.env(), n)?;
                    check_no_metavar_no_fvar(self.env(), n, t0)?;
                    let sort = self.tc.check(t0, self.lparams)?;
                    lean_dec(sort);
                    let mut i: usize = 0;
                    let mut t = t0;
                    lean_inc(t);
                    while lean_expr_is_pi(t) {
                        if i < self.nparams {
                            let dom = lean_expr_get_binding_domain(t);
                            if !self.tc.is_def_eq(dom, self.param_types[i])? {
                                lean_dec(t);
                                return Err(kernel_exc_string(format!(
                                    "arg #{} of '{}' does not match inductive datatypes parameters'",
                                    i + 1,
                                    lean_name_to_string(n)
                                )));
                            }
                            let nt = self.inst_body(t, self.params[i]);
                            lean_dec(t);
                            t = nt;
                        } else {
                            let dom = lean_expr_get_binding_domain(t);
                            let s = self.tc.ensure_type(dom)?;
                            let s_lvl = lean_expr_get_sort_level(s);
                            let geq = is_geq_level(self.result_level, s_lvl)?;
                            lean_dec(s);
                            if !(geq || level_is_zero(self.result_level)) {
                                lean_dec(t);
                                return Err(kernel_exc_string(format!(
                                    "universe level of type_of(arg #{}) of '{}' is too big for the corresponding inductive datatype",
                                    i + 1,
                                    lean_name_to_string(n)
                                )));
                            }
                            if !self.is_unsafe {
                                let dom2 = lean_expr_get_binding_domain(t);
                                lean_inc(dom2);
                                let r = self.check_positivity(dom2, n, i);
                                lean_dec(dom2);
                                r?;
                            }
                            let local = self.mk_local_decl_for(t);
                            let nt = self.inst_body(t, local);
                            lean_dec(local);
                            lean_dec(t);
                            t = nt;
                        }
                        i += 1;
                    }
                    let valid = self.is_valid_ind_app_i(t, idx);
                    lean_dec(t);
                    if !valid {
                        return Err(kernel_exc_string(format!(
                            "invalid return type for '{}'",
                            lean_name_to_string(n)
                        )));
                    }
                }
            }
            Ok(())
        }

        /// Add all constructor declarations to the environment.
        unsafe fn declare_constructors(&mut self) -> Result<(), KernelError> {
            for idx in 0..self.ind_types.len() {
                let ind_type = self.ind_types[idx];
                let ind_name = lean_ctor_get(ind_type, 0);
                let mut cidx: usize = 0;
                for &cnstr in &list_to_vec(lean_ctor_get(ind_type, 2)) {
                    let n = lean_ctor_get(cnstr, 0);
                    let t = lean_ctor_get(cnstr, 1);
                    // arity = number of leading Pis; nfields = arity - nparams.
                    let mut arity: usize = 0;
                    let mut it = t;
                    while lean_expr_is_pi(it) {
                        it = lean_expr_get_binding_body(it);
                        arity += 1;
                    }
                    let nfields = arity - self.nparams;
                    check_name_dup(self.env(), n)?;
                    lean_inc(n);
                    lean_inc(self.lparams);
                    lean_inc(t);
                    lean_inc(ind_name);
                    let v = lean_mk_constructor_val(
                        n,
                        self.lparams,
                        t,
                        ind_name,
                        nat_box(cidx),
                        nat_box(self.nparams),
                        nat_box(nfields),
                        self.is_unsafe,
                    );
                    let info = wrap_ci(CI_CONSTRUCTOR, v);
                    self.tc.add_core(info);
                    cidx += 1;
                }
            }
            Ok(())
        }
    }

    impl AddInductiveFn {
        /// Build a local decl with a string user-name. BORROWS `ty`.
        unsafe fn mk_local_decl_str(
            &mut self,
            s: &str,
            ty: *mut LeanObject,
            bi: u8,
        ) -> *mut LeanObject {
            let n = lean_string_name(s);
            let fvar = self.mk_local_decl(n, ty, bi);
            lean_dec(n);
            fvar
        }

        /// `mk_constant(name, m_levels)`. BORROWS `name`; returns owned.
        unsafe fn mk_const_levels(&self, name: *mut LeanObject) -> *mut LeanObject {
            let lv = list_to_vec(self.levels);
            const_borrowed(name, &lv)
        }

        /// `mk_app(mk_app(base, xs), ys)` where `base` is OWNED (consumed); `xs`/`ys` BORROWED.
        unsafe fn app2(
            &self,
            base: *mut LeanObject,
            xs: &[*mut LeanObject],
            ys: &[*mut LeanObject],
        ) -> *mut LeanObject {
            app_borrowed(app_borrowed(base, xs), ys)
        }

        #[inline]
        unsafe fn mk_pi(
            &self,
            fvars: &[*mut LeanObject],
            body: *mut LeanObject,
        ) -> *mut LeanObject {
            self.tc.lctx_mk_pi(fvars, body, false)
        }
        #[inline]
        unsafe fn mk_lambda(
            &self,
            fvars: &[*mut LeanObject],
            body: *mut LeanObject,
        ) -> *mut LeanObject {
            self.tc.lctx_mk_lambda(fvars, body)
        }

        /// `get_I_indices(t, indices)` — push the index args of `I params indices` into `indices`,
        /// return the inductive index. BORROWS `t`.
        unsafe fn get_i_indices(
            &self,
            t: *mut LeanObject,
            indices: &mut Vec<*mut LeanObject>,
        ) -> usize {
            let r = self
                .is_valid_ind_app(t)
                .expect("get_i_indices: not a valid ind app");
            let (_, all_args) = ind_get_app_args(t);
            for k in self.nparams..all_args.len() {
                indices.push(all_args[k]);
            }
            r
        }

        /// `elim_only_at_universe_zero` — true iff the recursor can only eliminate into `Prop`.
        unsafe fn elim_only_at_universe_zero(&mut self) -> Result<bool, KernelError> {
            if self.is_not_zero {
                return Ok(false);
            }
            if self.ind_types.len() > 1 {
                return Ok(true);
            }
            let cnstrs = list_to_vec(lean_ctor_get(self.ind_types[0], 2));
            let num_intros = cnstrs.len();
            if num_intros > 1 {
                return Ok(true);
            }
            if num_intros == 0 {
                return Ok(false);
            }
            let mut t = lean_ctor_get(cnstrs[0], 1);
            lean_inc(t);
            let mut i: usize = 0;
            let mut to_check: Vec<*mut LeanObject> = Vec::new();
            while lean_expr_is_pi(t) {
                let fvar = self.mk_local_decl_for(t);
                if i >= self.nparams {
                    let s = self.tc.ensure_type(lean_expr_get_binding_domain(t))?;
                    let is_zero = level_is_zero(lean_expr_get_sort_level(s));
                    lean_dec(s);
                    if !is_zero {
                        to_check.push(fvar);
                    }
                }
                let nt = self.inst_body(t, fvar);
                lean_dec(t);
                t = nt;
                i += 1;
            }
            let (_, result_args) = ind_get_app_args(t);
            lean_dec(t);
            for arg in to_check {
                if !result_args.iter().any(|&ra| lean_expr_eqv(arg, ra)) {
                    return Ok(true);
                }
            }
            Ok(false)
        }

        /// Initialize `elim_level`.
        unsafe fn init_elim_level(&mut self) -> Result<(), KernelError> {
            if self.elim_only_at_universe_zero()? {
                self.elim_level = lean_level_mk_zero();
            } else {
                let lparam_names = list_to_vec(self.lparams);
                let mut u = lean_string_name("u");
                let mut idx = 1usize;
                while lparam_names.iter().any(|&p| lean_name_eq(p, u)) {
                    let base = lean_string_name("u");
                    u = name_append_index(base, idx);
                    lean_dec(base);
                    idx += 1;
                }
                self.elim_level = level_param_borrowed(u);
                lean_dec(u);
            }
            Ok(())
        }

        /// Initialize `k_target` (K-like reduction is available).
        unsafe fn init_k_target(&mut self) {
            let cnstrs = list_to_vec(lean_ctor_get(self.ind_types[0], 2));
            self.k_target =
                self.ind_types.len() == 1 && level_is_zero(self.result_level) && cnstrs.len() == 1;
            if !self.k_target {
                return;
            }
            let mut it = lean_ctor_get(cnstrs[0], 1);
            let mut i: usize = 0;
            while lean_expr_is_pi(it) {
                if i < self.nparams {
                    it = lean_expr_get_binding_body(it);
                } else {
                    self.k_target = false;
                    break;
                }
                i += 1;
            }
        }

        /// Populate `rec_infos` (motives, indices, major premises, minor premises).
        unsafe fn mk_rec_infos(&mut self) -> Result<(), KernelError> {
            // Pass 1: motives, indices, major premise.
            for d_idx in 0..self.ind_types.len() {
                let mut indices: Vec<*mut LeanObject> = Vec::new();
                let mut t = self.tc.whnf(lean_ctor_get(self.ind_types[d_idx], 1))?;
                let mut i: usize = 0;
                while lean_expr_is_pi(t) {
                    let nt = if i < self.nparams {
                        self.inst_body(t, self.params[i])
                    } else {
                        let idx = self.mk_local_decl_for(t);
                        indices.push(idx);
                        self.inst_body(t, idx)
                    };
                    lean_dec(t);
                    let w = self.tc.whnf(nt)?;
                    lean_dec(nt);
                    t = w;
                    i += 1;
                }
                lean_dec(t);
                let base = self.ind_cnsts[d_idx];
                lean_inc(base);
                let major_ty = self.app2(base, &self.params.clone(), &indices);
                let major = self.mk_local_decl_str("t", major_ty, BI_DEFAULT);
                let mut c_ty = sort_borrowed(self.elim_level);
                c_ty = self.mk_pi(&[major], c_ty);
                c_ty = self.mk_pi(&indices, c_ty);
                let c_name = if self.ind_types.len() > 1 {
                    let m = lean_string_name("motive");
                    let r = name_append_index(m, d_idx + 1);
                    lean_dec(m);
                    r
                } else {
                    lean_string_name("motive")
                };
                let c = self.mk_local_decl(c_name, c_ty, BI_DEFAULT);
                lean_dec(c_name);
                self.rec_infos.push(RecInfo {
                    c,
                    minors: Vec::new(),
                    indices,
                    major,
                });
            }
            // Pass 2: minor premises.
            for d_idx in 0..self.ind_types.len() {
                let ind_type_name = self.ind_names[d_idx];
                let cnstrs = list_to_vec(lean_ctor_get(self.ind_types[d_idx], 2));
                for &cnstr in &cnstrs {
                    let mut b_u: Vec<*mut LeanObject> = Vec::new();
                    let mut u: Vec<*mut LeanObject> = Vec::new();
                    let cnstr_name = lean_ctor_get(cnstr, 0);
                    let mut t = lean_ctor_get(cnstr, 1);
                    lean_inc(t);
                    let mut i: usize = 0;
                    while lean_expr_is_pi(t) {
                        let nt = if i < self.nparams {
                            self.inst_body(t, self.params[i])
                        } else {
                            let l = self.mk_local_decl_for(t);
                            b_u.push(l);
                            if self
                                .is_rec_argument(lean_expr_get_binding_domain(t))?
                                .is_some()
                            {
                                u.push(l);
                            }
                            self.inst_body(t, l)
                        };
                        lean_dec(t);
                        t = nt;
                        i += 1;
                    }
                    let mut it_indices: Vec<*mut LeanObject> = Vec::new();
                    let it_idx = self.get_i_indices(t, &mut it_indices);
                    let mut c_app = app_borrowed(
                        {
                            let c = self.rec_infos[it_idx].c;
                            lean_inc(c);
                            c
                        },
                        &it_indices,
                    );
                    let intro_base = self.mk_const_levels(cnstr_name);
                    let intro_app = self.app2(intro_base, &self.params.clone(), &b_u);
                    c_app = app_borrowed(c_app, &[intro_app]);
                    lean_dec(t);
                    // populate v using u
                    let mut v: Vec<*mut LeanObject> = Vec::new();
                    for &u_i in &u {
                        let inferred = self.tc.infer_type(u_i)?;
                        let mut u_i_ty = self.tc.whnf(inferred)?;
                        lean_dec(inferred);
                        let mut xs: Vec<*mut LeanObject> = Vec::new();
                        while lean_expr_is_pi(u_i_ty) {
                            let x = self.mk_local_decl_for(u_i_ty);
                            xs.push(x);
                            let inst = self.inst_body(u_i_ty, x);
                            let w = self.tc.whnf(inst)?;
                            lean_dec(inst);
                            lean_dec(u_i_ty);
                            u_i_ty = w;
                        }
                        let mut it_indices2: Vec<*mut LeanObject> = Vec::new();
                        let it_idx2 = self.get_i_indices(u_i_ty, &mut it_indices2);
                        lean_dec(u_i_ty);
                        let mut c_app2 = app_borrowed(
                            {
                                let c = self.rec_infos[it_idx2].c;
                                lean_inc(c);
                                c
                            },
                            &it_indices2,
                        );
                        let u_app = app_borrowed(
                            {
                                lean_inc(u_i);
                                u_i
                            },
                            &xs,
                        );
                        c_app2 = app_borrowed(c_app2, &[u_app]);
                        let v_i_ty = self.mk_pi(&xs, c_app2);
                        let u_decl = lean_local_ctx_find_local_decl(self.tc.lctx, u_i);
                        let user_name = lean_local_decl_get_user_name(u_decl);
                        let ih_name = name_append_str(user_name, "_ih");
                        lean_dec(u_decl);
                        let v_i = self.mk_local_decl(ih_name, v_i_ty, BI_DEFAULT);
                        lean_dec(ih_name);
                        v.push(v_i);
                    }
                    let inner = self.mk_pi(&v, c_app);
                    let minor_ty = self.mk_pi(&b_u, inner);
                    let anon = lean_name_anonymous();
                    let minor_name = name_replace_prefix(cnstr_name, ind_type_name, anon);
                    let minor = self.mk_local_decl(minor_name, minor_ty, BI_DEFAULT);
                    lean_dec(minor_name);
                    self.rec_infos[d_idx].minors.push(minor);
                }
            }
            Ok(())
        }

        /// Recursor universe levels (prepend the elim level param if it is a parameter).
        unsafe fn get_rec_levels(&self) -> *mut LeanObject {
            if level_kind(self.elim_level) == LEVEL_PARAM {
                lean_inc(self.elim_level);
                lean_inc(self.levels);
                lean_mk_list_cons(ptr::null_mut(), self.elim_level, self.levels)
            } else {
                lean_inc(self.levels);
                self.levels
            }
        }

        /// Recursor level parameter names (prepend the elim level's param name if it is a parameter).
        unsafe fn get_rec_lparams(&self) -> *mut LeanObject {
            if level_kind(self.elim_level) == LEVEL_PARAM {
                let pid = lean_ctor_get(self.elim_level, 0);
                lean_inc(pid);
                lean_inc(self.lparams);
                lean_mk_list_cons(ptr::null_mut(), pid, self.lparams)
            } else {
                lean_inc(self.lparams);
                self.lparams
            }
        }

        unsafe fn collect_cs(&self) -> Vec<*mut LeanObject> {
            self.rec_infos.iter().map(|r| r.c).collect()
        }
        unsafe fn collect_minors(&self) -> Vec<*mut LeanObject> {
            let mut ms = Vec::new();
            for r in &self.rec_infos {
                ms.extend_from_slice(&r.minors);
            }
            ms
        }

        /// Build the computation rules for inductive type `d_idx`.
        unsafe fn mk_rec_rules(
            &mut self,
            d_idx: usize,
            cs: &[*mut LeanObject],
            minors: &[*mut LeanObject],
            minor_idx: &mut usize,
        ) -> Result<*mut LeanObject, KernelError> {
            let lvls = self.get_rec_levels();
            let cnstrs = list_to_vec(lean_ctor_get(self.ind_types[d_idx], 2));
            let mut rules: Vec<*mut LeanObject> = Vec::new();
            for &cnstr in &cnstrs {
                let mut b_u: Vec<*mut LeanObject> = Vec::new();
                let mut u: Vec<*mut LeanObject> = Vec::new();
                let mut t = lean_ctor_get(cnstr, 1);
                lean_inc(t);
                let mut i: usize = 0;
                while lean_expr_is_pi(t) {
                    let nt = if i < self.nparams {
                        self.inst_body(t, self.params[i])
                    } else {
                        let l = self.mk_local_decl_for(t);
                        b_u.push(l);
                        if self
                            .is_rec_argument(lean_expr_get_binding_domain(t))?
                            .is_some()
                        {
                            u.push(l);
                        }
                        self.inst_body(t, l)
                    };
                    lean_dec(t);
                    t = nt;
                    i += 1;
                }
                lean_dec(t);
                let mut v: Vec<*mut LeanObject> = Vec::new();
                for &u_i in &u {
                    let inferred = self.tc.infer_type(u_i)?;
                    let mut u_i_ty = self.tc.whnf(inferred)?;
                    lean_dec(inferred);
                    let mut xs: Vec<*mut LeanObject> = Vec::new();
                    while lean_expr_is_pi(u_i_ty) {
                        let x = self.mk_local_decl_for(u_i_ty);
                        xs.push(x);
                        let inst = self.inst_body(u_i_ty, x);
                        let w = self.tc.whnf(inst)?;
                        lean_dec(inst);
                        lean_dec(u_i_ty);
                        u_i_ty = w;
                    }
                    let mut it_indices: Vec<*mut LeanObject> = Vec::new();
                    let it_idx = self.get_i_indices(u_i_ty, &mut it_indices);
                    lean_dec(u_i_ty);
                    let rec_name = mk_rec_name(self.ind_names[it_idx]);
                    lean_inc(lvls);
                    let lv = list_to_vec(lvls);
                    let rec_app0 = const_borrowed(rec_name, &lv);
                    lean_dec(rec_name);
                    // rec_app = rec params Cs minors it_indices (u_i xs)
                    let u_app = app_borrowed(
                        {
                            lean_inc(u_i);
                            u_i
                        },
                        &xs,
                    );
                    let rec_app = app_borrowed(
                        app_borrowed(
                            app_borrowed(
                                app_borrowed(app_borrowed(rec_app0, &self.params.clone()), cs),
                                minors,
                            ),
                            &it_indices,
                        ),
                        &[u_app],
                    );
                    v.push(self.mk_lambda(&xs, rec_app));
                }
                let e_app = app_borrowed(
                    app_borrowed(
                        {
                            let m = minors[*minor_idx];
                            lean_inc(m);
                            m
                        },
                        &b_u,
                    ),
                    &v,
                );
                let comp_rhs = self.mk_lambda(
                    &self.params.clone(),
                    self.mk_lambda(cs, self.mk_lambda(minors, self.mk_lambda(&b_u, e_app))),
                );
                let cnstr_name = lean_ctor_get(cnstr, 0);
                let rule = lean_alloc_ctor(0, 3, 0);
                lean_inc(cnstr_name);
                lean_ctor_set(rule, 0, cnstr_name);
                lean_ctor_set(rule, 1, nat_box(b_u.len()));
                lean_ctor_set(rule, 2, comp_rhs);
                rules.push(rule);
                *minor_idx += 1;
            }
            lean_dec(lvls);
            let r = lean_list_from_borrowed(&rules);
            for rule in rules {
                lean_dec(rule);
            }
            Ok(r)
        }

        /// Declare the recursors.
        unsafe fn declare_recursors(&mut self) -> Result<(), KernelError> {
            let cs = self.collect_cs();
            let minors = self.collect_minors();
            let nminors = minors.len();
            let nmotives = cs.len();
            let all = lean_list_from_borrowed(&self.ind_names);
            let mut minor_idx: usize = 0;
            for d_idx in 0..self.ind_types.len() {
                let (c, indices, major) = {
                    let info = &self.rec_infos[d_idx];
                    (info.c, info.indices.clone(), info.major)
                };
                lean_inc(c);
                let c_app = self.app2(c, &indices, &[major]);
                let mut rec_ty = self.mk_pi(&[major], c_app);
                rec_ty = self.mk_pi(&indices, rec_ty);
                rec_ty = self.mk_pi(&minors, rec_ty);
                rec_ty = self.mk_pi(&cs, rec_ty);
                rec_ty = self.mk_pi(&self.params.clone(), rec_ty);
                rec_ty = lean_expr_infer_implicit(rec_ty, true);
                let rules = self.mk_rec_rules(d_idx, &cs, &minors, &mut minor_idx)?;
                let rec_name = mk_rec_name(self.ind_names[d_idx]);
                let rec_lparams = self.get_rec_lparams();
                check_name_dup(self.env(), rec_name)?;
                lean_inc(all);
                let v = lean_mk_recursor_val(
                    rec_name,
                    rec_lparams,
                    rec_ty,
                    all,
                    nat_box(self.nparams),
                    nat_box(self.nindices[d_idx]),
                    nat_box(nmotives),
                    nat_box(nminors),
                    rules,
                    self.k_target,
                    self.is_unsafe,
                );
                let info = wrap_ci(CI_RECURSOR, v);
                self.tc.add_core(info);
            }
            lean_dec(all);
            Ok(())
        }

        /// Run the full add (mirrors C++ `add_inductive_fn::operator()`). Returns the extended env
        /// (OWNED). On error, the caller drops `self` which decs the partially-built env.
        unsafe fn run(&mut self) -> Result<*mut LeanObject, KernelError> {
            check_duplicated_univ_params(self.env(), self.lparams)?;
            self.check_inductive_types()?;
            self.declare_inductive_types()?;
            self.check_constructors()?;
            self.declare_constructors()?;
            self.init_elim_level()?;
            self.init_k_target();
            self.mk_rec_infos()?;
            self.declare_recursors()?;
            let env = self.tc.env();
            lean_inc(env);
            Ok(env)
        }
    }

    struct NestedLocalCtx {
        lctx: *mut LeanObject,
    }

    impl NestedLocalCtx {
        unsafe fn new() -> Self {
            Self {
                lctx: mk_empty_lctx(),
            }
        }

        unsafe fn mk_local_decl(
            &mut self,
            ngen: &mut NameGenerator,
            name: *mut LeanObject,
            ty: *mut LeanObject,
            bi: u8,
        ) -> *mut LeanObject {
            let id = ngen.mk_fresh_name();
            let pair = lean_local_ctx_mk_local_decl(self.lctx, id, name, ty, bi);
            lean_dec(id);
            let fvar = lean_ctor_get(pair, 0);
            let new_lctx = lean_ctor_get(pair, 1);
            lean_inc(fvar);
            lean_inc(new_lctx);
            lean_dec(pair);
            lean_dec(self.lctx);
            self.lctx = new_lctx;
            fvar
        }

        unsafe fn mk_local_decl_for(
            &mut self,
            ngen: &mut NameGenerator,
            t: *mut LeanObject,
        ) -> *mut LeanObject {
            self.mk_local_decl(
                ngen,
                lean_expr_get_binding_name(t),
                lean_expr_get_binding_domain(t),
                lean_expr_get_binding_info(t),
            )
        }

        unsafe fn mk_pi(
            &self,
            fvars: &[*mut LeanObject],
            body: *mut LeanObject,
        ) -> *mut LeanObject {
            lean_local_ctx_mk_pi(self.lctx, fvars.as_ptr(), fvars.len() as u32, body, false)
        }

        unsafe fn mk_lambda(
            &self,
            fvars: &[*mut LeanObject],
            body: *mut LeanObject,
        ) -> *mut LeanObject {
            lean_local_ctx_mk_lambda(self.lctx, fvars.as_ptr(), fvars.len() as u32, body)
        }
    }

    impl Drop for NestedLocalCtx {
        fn drop(&mut self) {
            unsafe {
                lean_dec(self.lctx);
            }
        }
    }

    unsafe fn mk_constructor(name: *mut LeanObject, ty: *mut LeanObject) -> *mut LeanObject {
        let r = lean_alloc_ctor(0, 2, 0);
        lean_ctor_set(r, 0, name);
        lean_ctor_set(r, 1, ty);
        r
    }

    unsafe fn mk_inductive_type(
        name: *mut LeanObject,
        ty: *mut LeanObject,
        ctors: *mut LeanObject,
    ) -> *mut LeanObject {
        let r = lean_alloc_ctor(0, 3, 0);
        lean_ctor_set(r, 0, name);
        lean_ctor_set(r, 1, ty);
        lean_ctor_set(r, 2, ctors);
        r
    }

    unsafe fn instantiate_pi_params(
        env: *mut LeanObject,
        mut e: *mut LeanObject,
        params: &[*mut LeanObject],
    ) -> Result<*mut LeanObject, KernelError> {
        lean_inc(e);
        for _ in params {
            if !lean_expr_is_pi(e) {
                lean_dec(e);
                return Err(kernel_exc(
                    "invalid nested inductive datatype, ill-formed declaration",
                ));
            }
            let body = lean_expr_get_binding_body(e);
            lean_inc(body);
            lean_dec(e);
            e = body;
        }
        let r = lean_expr_instantiate_rev(e, params.len() as u32, params.as_ptr());
        lean_dec(e);
        let _ = env;
        Ok(r)
    }

    unsafe fn abstract_instantiate_params(
        e: *mut LeanObject,
        old_params: &[*mut LeanObject],
        new_params: &[*mut LeanObject],
    ) -> *mut LeanObject {
        let abs = lean_expr_abstract(e, old_params.len() as u32, old_params.as_ptr());
        let r = lean_expr_instantiate_rev(abs, new_params.len() as u32, new_params.as_ptr());
        lean_dec(abs);
        r
    }

    struct ElimNestedInductiveResult {
        ngen: NameGenerator,
        params: Vec<*mut LeanObject>,
        aux2nested: Vec<(*mut LeanObject, *mut LeanObject)>,
        aux_decl: *mut LeanObject,
    }

    impl ElimNestedInductiveResult {
        unsafe fn get_nested_if_aux_constructor(
            &self,
            aux_env: *mut LeanObject,
            c: *mut LeanObject,
        ) -> Option<(*mut LeanObject, *mut LeanObject)> {
            let info = env_find(aux_env, c);
            if lean_is_scalar(info) {
                return None;
            }
            if !lean_constant_info_is_constructor(info) {
                lean_dec(info);
                return None;
            }
            let cval = lean_constant_info_to_constructor_val(info);
            let aux_i_name = lean_constructor_val_get_induct(cval);
            for &(nested, aux_name) in &self.aux2nested {
                if lean_name_eq(aux_i_name, aux_name) {
                    lean_dec(info);
                    return Some((nested, aux_name));
                }
            }
            lean_dec(info);
            None
        }

        unsafe fn restore_constructor_name(
            &self,
            aux_env: *mut LeanObject,
            cnstr_name: *mut LeanObject,
        ) -> *mut LeanObject {
            let (nested, aux_i_name) = self
                .get_nested_if_aux_constructor(aux_env, cnstr_name)
                .expect("restore_constructor_name: auxiliary constructor expected");
            let (i, _) = ind_get_app_args(nested);
            name_replace_prefix(cnstr_name, aux_i_name, lean_expr_get_const_name(i))
        }

        unsafe fn restore_nested(
            &mut self,
            mut e: *mut LeanObject,
            aux_env: *mut LeanObject,
            aux_rec_name_map: &[(*mut LeanObject, *mut LeanObject)],
        ) -> *mut LeanObject {
            let mut lctx = NestedLocalCtx::new();
            let mut actual_params = Vec::new();
            let pi = lean_expr_is_pi(e);
            lean_inc(e);
            for _ in 0..self.params.len() {
                let fvar = lctx.mk_local_decl_for(&mut self.ngen, e);
                actual_params.push(fvar);
                let body = lean_expr_get_binding_body(e);
                let new_e = lean_expr_instantiate1(body, fvar);
                lean_dec(e);
                e = new_e;
            }
            struct RestoreCtx<'a> {
                res: &'a ElimNestedInductiveResult,
                aux_env: *mut LeanObject,
                aux_rec_name_map: &'a [(*mut LeanObject, *mut LeanObject)],
                decl_params: &'a [*mut LeanObject],
                actual_params: &'a [*mut LeanObject],
            }
            unsafe fn restore_cb(
                ctx: *mut c_void,
                t: *mut LeanObject,
                _offset: u32,
            ) -> *mut LeanObject {
                let c = &*(ctx as *const RestoreCtx);
                if ind_is_constant(t) {
                    let n = lean_expr_get_const_name(t);
                    for &(old_rec, new_rec) in c.aux_rec_name_map {
                        if lean_name_eq(n, old_rec) {
                            let levels = list_to_vec(lean_expr_get_const_levels(t));
                            return some_expr(const_borrowed(new_rec, &levels));
                        }
                    }
                }
                let (head, args) = ind_get_app_args(t);
                if ind_is_constant(head) {
                    let head_name = lean_expr_get_const_name(head);
                    for &(nested, aux_name) in &c.res.aux2nested {
                        if lean_name_eq(head_name, aux_name) {
                            let new_t =
                                abstract_instantiate_params(nested, c.decl_params, c.actual_params);
                            let app = if args.len() >= c.decl_params.len() {
                                app_borrowed(new_t, &args[c.decl_params.len()..])
                            } else {
                                new_t
                            };
                            return some_expr(app);
                        }
                    }
                    if let Some((nested, aux_i_name)) =
                        c.res.get_nested_if_aux_constructor(c.aux_env, head_name)
                    {
                        let new_nested =
                            abstract_instantiate_params(nested, c.decl_params, c.actual_params);
                        let (i, i_args) = ind_get_app_args(new_nested);
                        let new_fn_name =
                            name_replace_prefix(head_name, aux_i_name, lean_expr_get_const_name(i));
                        let levels = list_to_vec(lean_expr_get_const_levels(i));
                        let new_fn = const_borrowed(new_fn_name, &levels);
                        lean_dec(new_fn_name);
                        let new_t = if args.len() >= c.decl_params.len() {
                            app_borrowed(
                                app_borrowed(new_fn, &i_args),
                                &args[c.decl_params.len()..],
                            )
                        } else {
                            app_borrowed(new_fn, &i_args)
                        };
                        lean_dec(new_nested);
                        return some_expr(new_t);
                    }
                }
                lean_box(0)
            }
            let ctx = RestoreCtx {
                res: self,
                aux_env,
                aux_rec_name_map,
                decl_params: &self.params,
                actual_params: &actual_params,
            };
            let new_e = lean_replace_expr_with_callback(
                e,
                &ctx as *const RestoreCtx as *mut c_void,
                restore_cb,
                1,
            );
            lean_dec(e);
            if pi {
                lctx.mk_pi(&actual_params, new_e)
            } else {
                lctx.mk_lambda(&actual_params, new_e)
            }
        }
    }

    struct ElimNestedInductiveFn {
        env: *mut LeanObject,
        decl: *mut LeanObject,
        ngen: NameGenerator,
        params_lctx: NestedLocalCtx,
        params: Vec<*mut LeanObject>,
        nested_aux: Vec<(*mut LeanObject, *mut LeanObject)>,
        lvls: *mut LeanObject,
        new_types: Vec<*mut LeanObject>,
        next_idx: usize,
    }

    impl ElimNestedInductiveFn {
        unsafe fn new(env: *mut LeanObject, decl: *mut LeanObject) -> Self {
            Self {
                env,
                decl,
                ngen: NameGenerator::new(load_global(&G_NESTED_FRESH)),
                params_lctx: NestedLocalCtx::new(),
                params: Vec::new(),
                nested_aux: Vec::new(),
                lvls: lparams_to_levels(lean_ctor_get(decl, 0)),
                new_types: list_to_vec(lean_ctor_get(decl, 2)),
                next_idx: 1,
            }
        }

        unsafe fn mk_unique_name(&mut self, n: *mut LeanObject) -> *mut LeanObject {
            loop {
                let r = name_append_index(n, self.next_idx);
                self.next_idx += 1;
                let info = env_find(self.env, r);
                if lean_is_scalar(info) {
                    return r;
                }
                lean_dec(info);
                lean_dec(r);
            }
        }

        unsafe fn replace_params(
            &self,
            e: *mut LeanObject,
            params: &[*mut LeanObject],
        ) -> *mut LeanObject {
            abstract_instantiate_params(e, params, &self.params)
        }

        unsafe fn is_nested_inductive_app(
            &self,
            e: *mut LeanObject,
        ) -> Result<Option<*mut LeanObject>, KernelError> {
            if !lean_expr_is_app(e) {
                return Ok(None);
            }
            let (head, args) = ind_get_app_args(e);
            if !ind_is_constant(head) {
                return Ok(None);
            }
            let info = env_find(self.env, lean_expr_get_const_name(head));
            if lean_is_scalar(info) {
                return Ok(None);
            }
            if !lean_constant_info_is_inductive(info) {
                lean_dec(info);
                return Ok(None);
            }
            let ival = lean_constant_info_to_inductive_val(info);
            let nparams = lean_inductive_val_get_nparams(ival) as usize;
            if nparams > args.len() {
                lean_dec(info);
                return Ok(None);
            }
            let mut is_nested = false;
            let mut loose_bvars = false;
            let new_type_names: Vec<*mut LeanObject> = self
                .new_types
                .iter()
                .map(|&it| lean_ctor_get(it, 0))
                .collect();
            for &arg in args.iter().take(nparams) {
                if lean_expr_has_loose_bvars(arg) {
                    loose_bvars = true;
                }
                if expr_contains_const(arg, &new_type_names) {
                    is_nested = true;
                }
            }
            if !is_nested {
                lean_dec(info);
                return Ok(None);
            }
            if loose_bvars {
                let msg = format!(
                    "invalid nested inductive datatype '{}', nested inductive datatypes parameters cannot contain local variables.",
                    lean_name_to_string(lean_expr_get_const_name(head))
                );
                lean_dec(info);
                return Err(kernel_exc_string(msg));
            }
            lean_inc(ival);
            lean_dec(info);
            Ok(Some(ival))
        }

        unsafe fn replace_if_nested(
            &mut self,
            lctx: &NestedLocalCtx,
            params: &[*mut LeanObject],
            e: *mut LeanObject,
        ) -> Result<Option<*mut LeanObject>, KernelError> {
            let Some(i_val) = self.is_nested_inductive_app(e)? else {
                return Ok(None);
            };
            let (head, args) = ind_get_app_args(e);
            let i_name = lean_expr_get_const_name(head);
            let i_lvls = lean_expr_get_const_levels(head);
            let i_nparams = lean_inductive_val_get_nparams(i_val) as usize;
            let i_as = app_borrowed(
                {
                    lean_inc(head);
                    head
                },
                &args[..i_nparams],
            );
            let i_params = self.replace_params(i_as, params);
            lean_dec(i_as);
            for &(nested, aux_name) in &self.nested_aux {
                if lean_expr_eqv(nested, i_params) {
                    lean_dec(i_params);
                    lean_dec(i_val);
                    let aux_i = const_borrowed(aux_name, &list_to_vec(self.lvls));
                    let aux_i = app_borrowed(aux_i, params);
                    return Ok(Some(app_borrowed(aux_i, &args[i_nparams..])));
                }
            }
            lean_dec(i_params);

            let mut result = ptr::null_mut();
            for j_name in list_to_vec(lean_inductive_val_get_all(i_val)) {
                let j_info = env_find(self.env, j_name);
                let nested_prefix = name_append_name(load_global(&G_NESTED_NAME), j_name);
                let aux_j_name = self.mk_unique_name(nested_prefix);
                lean_dec(nested_prefix);

                let j = const_borrowed(j_name, &list_to_vec(i_lvls));
                let j_as = app_borrowed(j, &args[..i_nparams]);
                let mut aux_j_type = lean_instantiate_lparams(
                    lean_constant_info_get_type(j_info),
                    lean_constant_info_get_lparams(j_info),
                    i_lvls,
                );
                aux_j_type = instantiate_pi_params(self.env, aux_j_type, &args[..i_nparams])?;
                aux_j_type = lctx.mk_pi(params, aux_j_type);
                let nested_j = self.replace_params(j_as, params);
                lean_dec(j_as);
                self.nested_aux.push((nested_j, aux_j_name));

                if lean_name_eq(j_name, i_name) {
                    let aux_i = const_borrowed(aux_j_name, &list_to_vec(self.lvls));
                    let aux_i = app_borrowed(aux_i, params);
                    result = app_borrowed(aux_i, &args[i_nparams..]);
                }

                let j_ind_val = lean_constant_info_to_inductive_val(j_info);
                let mut aux_ctors = Vec::new();
                for j_cnstr_name in list_to_vec(lean_inductive_val_get_cnstrs(j_ind_val)) {
                    let j_cnstr_info = env_find(self.env, j_cnstr_name);
                    let aux_j_cnstr_name = name_replace_prefix(j_cnstr_name, j_name, aux_j_name);
                    let mut aux_j_cnstr_type = lean_instantiate_lparams(
                        lean_constant_info_get_type(j_cnstr_info),
                        lean_constant_info_get_lparams(j_cnstr_info),
                        i_lvls,
                    );
                    aux_j_cnstr_type =
                        instantiate_pi_params(self.env, aux_j_cnstr_type, &args[..i_nparams])?;
                    aux_j_cnstr_type = lctx.mk_pi(params, aux_j_cnstr_type);
                    aux_ctors.push(mk_constructor(aux_j_cnstr_name, aux_j_cnstr_type));
                    lean_dec(j_cnstr_info);
                }
                let aux_ctors_list = lean_list_from_borrowed(&aux_ctors);
                for c in aux_ctors {
                    lean_dec(c);
                }
                lean_inc(aux_j_name);
                self.new_types
                    .push(mk_inductive_type(aux_j_name, aux_j_type, aux_ctors_list));
                lean_dec(j_info);
            }
            lean_dec(i_val);
            Ok(Some(result))
        }

        unsafe fn replace_all_nested(
            &mut self,
            lctx: &NestedLocalCtx,
            params: &[*mut LeanObject],
            e: *mut LeanObject,
        ) -> Result<*mut LeanObject, KernelError> {
            struct ReplaceCtx {
                this: *mut ElimNestedInductiveFn,
                lctx: *const NestedLocalCtx,
                params_ptr: *const *mut LeanObject,
                params_len: usize,
                error: Option<KernelError>,
            }
            unsafe fn cb(ctx: *mut c_void, e: *mut LeanObject, _offset: u32) -> *mut LeanObject {
                let c = &mut *(ctx as *mut ReplaceCtx);
                if c.error.is_some() {
                    return lean_box(0);
                }
                let this = &mut *c.this;
                let lctx = &*c.lctx;
                let params = core::slice::from_raw_parts(c.params_ptr, c.params_len);
                match this.replace_if_nested(lctx, params, e) {
                    Ok(Some(r)) => some_expr(r),
                    Ok(None) => lean_box(0),
                    Err(err) => {
                        c.error = Some(err);
                        lean_box(0)
                    }
                }
            }
            let mut ctx = ReplaceCtx {
                this: self as *mut ElimNestedInductiveFn,
                lctx: lctx as *const NestedLocalCtx,
                params_ptr: params.as_ptr(),
                params_len: params.len(),
                error: None,
            };
            let r = lean_replace_expr_with_callback(
                e,
                &mut ctx as *mut ReplaceCtx as *mut c_void,
                cb,
                1,
            );
            if let Some(err) = ctx.error {
                lean_dec(r);
                Err(err)
            } else {
                Ok(r)
            }
        }

        unsafe fn get_params(
            ngen: &mut NameGenerator,
            mut ty: *mut LeanObject,
            nparams: usize,
            lctx: &mut NestedLocalCtx,
            params: &mut Vec<*mut LeanObject>,
        ) -> Result<*mut LeanObject, KernelError> {
            lean_inc(ty);
            for _ in 0..nparams {
                if !lean_expr_is_pi(ty) {
                    lean_dec(ty);
                    return Err(kernel_exc(
                        "invalid inductive datatype declaration, incorrect number of parameters",
                    ));
                }
                let fvar = lctx.mk_local_decl_for(ngen, ty);
                params.push(fvar);
                let new_ty = lean_expr_instantiate1(lean_expr_get_binding_body(ty), fvar);
                lean_dec(ty);
                ty = new_ty;
            }
            Ok(ty)
        }

        unsafe fn run(mut self) -> Result<ElimNestedInductiveResult, KernelError> {
            let nparams = lean_unbox(lean_ctor_get(self.decl, 1));
            if self.new_types.is_empty() {
                return Err(kernel_exc(
                    "invalid empty (mutual) inductive datatype declaration, it must contain at least one inductive type.",
                ));
            }
            let first_ty = lean_ctor_get(self.new_types[0], 1);
            let mut params = Vec::new();
            let mut params_lctx = core::mem::replace(&mut self.params_lctx, NestedLocalCtx::new());
            let rest = Self::get_params(
                &mut self.ngen,
                first_ty,
                nparams,
                &mut params_lctx,
                &mut params,
            )?;
            lean_dec(rest);
            self.params = params;
            self.params_lctx = params_lctx;

            let mut qhead = 0usize;
            while qhead < self.new_types.len() {
                let ind_type = self.new_types[qhead];
                let mut new_ctors = Vec::new();
                for cnstr in list_to_vec(lean_ctor_get(ind_type, 2)) {
                    let mut lctx = NestedLocalCtx::new();
                    let mut actual_params = Vec::new();
                    let cnstr_ty = Self::get_params(
                        &mut self.ngen,
                        lean_ctor_get(cnstr, 1),
                        nparams,
                        &mut lctx,
                        &mut actual_params,
                    )?;
                    let mut new_cnstr_ty =
                        self.replace_all_nested(&lctx, &actual_params, cnstr_ty)?;
                    lean_dec(cnstr_ty);
                    new_cnstr_ty = lctx.mk_pi(&actual_params, new_cnstr_ty);
                    let cnstr_name = lean_ctor_get(cnstr, 0);
                    lean_inc(cnstr_name);
                    new_ctors.push(mk_constructor(cnstr_name, new_cnstr_ty));
                }
                let new_ctors_list = lean_list_from_borrowed(&new_ctors);
                for c in new_ctors {
                    lean_dec(c);
                }
                let ind_name = lean_ctor_get(ind_type, 0);
                let ind_ty = lean_ctor_get(ind_type, 1);
                lean_inc(ind_name);
                lean_inc(ind_ty);
                self.new_types[qhead] = mk_inductive_type(ind_name, ind_ty, new_ctors_list);
                qhead += 1;
            }
            let new_types_list = lean_list_from_borrowed(&self.new_types);
            let lparams = lean_ctor_get(self.decl, 0);
            let nparams_obj = lean_ctor_get(self.decl, 1);
            lean_inc(lparams);
            lean_inc(nparams_obj);
            let is_unsafe = lean_is_unsafe_inductive_decl({
                lean_inc(self.decl);
                self.decl
            });
            let aux_decl = lean_mk_inductive_decl(lparams, nparams_obj, new_types_list, is_unsafe);
            Ok(ElimNestedInductiveResult {
                ngen: self.ngen,
                params: self.params,
                aux2nested: self.nested_aux,
                aux_decl,
            })
        }
    }

    unsafe fn get_all_inductive_names_from_decl(decl: *mut LeanObject) -> *mut LeanObject {
        let names: Vec<*mut LeanObject> = list_to_vec(lean_ctor_get(decl, 2))
            .iter()
            .map(|&it| lean_ctor_get(it, 0))
            .collect();
        lean_list_from_borrowed(&names)
    }

    unsafe fn mk_aux_rec_name_map(
        aux_env: *mut LeanObject,
        decl: *mut LeanObject,
    ) -> (
        Vec<*mut LeanObject>,
        Vec<(*mut LeanObject, *mut LeanObject)>,
    ) {
        let types = list_to_vec(lean_ctor_get(decl, 2));
        let ntypes = types.len();
        let main_name = lean_ctor_get(types[0], 0);
        let main_info = env_find(aux_env, main_name);
        let all_names = list_to_vec(lean_inductive_val_get_all(
            lean_constant_info_to_inductive_val(main_info),
        ));
        let mut old_rec_names = Vec::new();
        let mut rec_map = Vec::new();
        let mut next_idx = 1usize;
        for (i, ind_name) in all_names.into_iter().enumerate() {
            if i >= ntypes {
                let old_rec = mk_rec_name(ind_name);
                let main_rec = mk_rec_name(main_name);
                let new_rec = name_append_index(main_rec, next_idx);
                lean_dec(main_rec);
                next_idx += 1;
                old_rec_names.push(old_rec);
                rec_map.push((old_rec, new_rec));
            }
        }
        lean_dec(main_info);
        (old_rec_names, rec_map)
    }

    /// Port of `environment::add_inductive`. CONSUMES `env`, BORROWS `decl`.
    unsafe fn add_inductive_impl(
        env: *mut LeanObject,
        decl: *mut LeanObject,
    ) -> Result<*mut LeanObject, KernelError> {
        let mut res = ElimNestedInductiveFn::new(env, decl).run()?;
        let nnested = res.aux2nested.len();
        let diag = diag_begin(env);
        lean_inc(env);
        let mut f = AddInductiveFn::new(env, res.aux_decl, nnested);
        let aux_env = f.run()?;
        if nnested == 0 {
            lean_dec(env);
            return Ok(diag_update(aux_env, diag));
        }

        let all_ind_names = get_all_inductive_names_from_decl(decl);
        let (aux_rec_names, aux_rec_name_map) = mk_aux_rec_name_map(aux_env, decl);
        let mut new_env = env;

        unsafe fn process_rec(
            mut new_env: *mut LeanObject,
            aux_env: *mut LeanObject,
            res: &mut ElimNestedInductiveResult,
            all_ind_names: *mut LeanObject,
            aux_rec_name_map: &[(*mut LeanObject, *mut LeanObject)],
            rec_name: *mut LeanObject,
        ) -> Result<*mut LeanObject, KernelError> {
            let mut new_rec_name = rec_name;
            for &(old, new_) in aux_rec_name_map {
                if lean_name_eq(old, rec_name) {
                    new_rec_name = new_;
                    break;
                }
            }
            let rec_info = env_find(aux_env, rec_name);
            let new_rec_type = res.restore_nested(
                lean_constant_info_get_type(rec_info),
                aux_env,
                aux_rec_name_map,
            );
            let rec_val = lean_constant_info_to_recursor_val(rec_info);
            let mut new_rules = Vec::new();
            for rule in list_to_vec(lean_recursor_val_get_rules(rec_val)) {
                let new_rhs =
                    res.restore_nested(lean_recursor_rule_get_rhs(rule), aux_env, aux_rec_name_map);
                let cnstr_name = lean_recursor_rule_get_cnstr(rule);
                let new_cnstr_name = if !lean_name_eq(new_rec_name, rec_name) {
                    res.restore_constructor_name(aux_env, cnstr_name)
                } else {
                    lean_inc(cnstr_name);
                    cnstr_name
                };
                let new_rule = lean_alloc_ctor(0, 3, 0);
                lean_ctor_set(new_rule, 0, new_cnstr_name);
                lean_ctor_set(
                    new_rule,
                    1,
                    nat_box(lean_recursor_rule_get_nfields(rule) as usize),
                );
                lean_ctor_set(new_rule, 2, new_rhs);
                new_rules.push(new_rule);
            }
            let new_rules_list = lean_list_from_borrowed(&new_rules);
            for r in new_rules {
                lean_dec(r);
            }
            check_name_dup(new_env, new_rec_name)?;
            lean_inc(new_rec_name);
            let lparams = lean_constant_info_get_lparams(rec_info);
            lean_inc(lparams);
            lean_inc(all_ind_names);
            let v = lean_mk_recursor_val(
                new_rec_name,
                lparams,
                new_rec_type,
                all_ind_names,
                nat_box(lean_recursor_val_get_nparams(rec_val) as usize),
                nat_box(lean_recursor_val_get_nindices(rec_val) as usize),
                nat_box(lean_recursor_val_get_nmotives(rec_val) as usize),
                nat_box(lean_recursor_val_get_nminors(rec_val) as usize),
                new_rules_list,
                lean_recursor_val_is_k(rec_val),
                lean_recursor_val_is_unsafe(rec_val),
            );
            let info = wrap_ci(CI_RECURSOR, v);
            new_env = lean_environment_add(new_env, info);
            lean_dec(rec_info);
            Ok(new_env)
        }

        for ind_type in list_to_vec(lean_ctor_get(decl, 2)) {
            let ind_name = lean_ctor_get(ind_type, 0);
            let ind_info = env_find(aux_env, ind_name);
            let ind_val = lean_constant_info_to_inductive_val(ind_info);
            check_name_dup(new_env, lean_constant_info_get_name(ind_info))?;
            let info_name = lean_constant_info_get_name(ind_info);
            let lparams = lean_constant_info_get_lparams(ind_info);
            let ind_ty = lean_constant_info_get_type(ind_info);
            let cnstrs = lean_inductive_val_get_cnstrs(ind_val);
            lean_inc(info_name);
            lean_inc(lparams);
            lean_inc(ind_ty);
            lean_inc(all_ind_names);
            lean_inc(cnstrs);
            let new_ind_val = lean_mk_inductive_val(
                info_name,
                lparams,
                ind_ty,
                nat_box(lean_inductive_val_get_nparams(ind_val) as usize),
                nat_box(lean_inductive_val_get_nindices(ind_val) as usize),
                all_ind_names,
                cnstrs,
                nat_box(lean_inductive_val_get_nnested(ind_val) as usize),
                lean_inductive_val_is_rec(ind_val),
                lean_inductive_val_is_unsafe(ind_val),
                lean_inductive_val_is_reflexive(ind_val),
            );
            new_env = lean_environment_add(new_env, wrap_ci(CI_INDUCTIVE, new_ind_val));

            for cnstr_name in list_to_vec(lean_inductive_val_get_cnstrs(ind_val)) {
                let cnstr_info = env_find(aux_env, cnstr_name);
                let cnstr_val = lean_constant_info_to_constructor_val(cnstr_info);
                let new_type =
                    res.restore_nested(lean_constant_info_get_type(cnstr_info), aux_env, &[]);
                check_name_dup(new_env, lean_constant_info_get_name(cnstr_info))?;
                let info_name = lean_constant_info_get_name(cnstr_info);
                let lparams = lean_constant_info_get_lparams(cnstr_info);
                let induct = lean_constructor_val_get_induct(cnstr_val);
                lean_inc(info_name);
                lean_inc(lparams);
                lean_inc(induct);
                let new_cnstr_val = lean_mk_constructor_val(
                    info_name,
                    lparams,
                    new_type,
                    induct,
                    nat_box(lean_constructor_val_get_cidx(cnstr_val) as usize),
                    nat_box(lean_constructor_val_get_nparams(cnstr_val) as usize),
                    nat_box(lean_constructor_val_get_nfields(cnstr_val) as usize),
                    lean_constructor_val_is_unsafe(cnstr_val),
                );
                new_env = lean_environment_add(new_env, wrap_ci(CI_CONSTRUCTOR, new_cnstr_val));
                lean_dec(cnstr_info);
            }
            let rec_name = mk_rec_name(ind_name);
            new_env = process_rec(
                new_env,
                aux_env,
                &mut res,
                all_ind_names,
                &aux_rec_name_map,
                rec_name,
            )?;
            lean_dec(rec_name);
            lean_dec(ind_info);
        }
        for &aux_rec in &aux_rec_names {
            new_env = process_rec(
                new_env,
                aux_env,
                &mut res,
                all_ind_names,
                &aux_rec_name_map,
                aux_rec,
            )?;
        }
        lean_dec(all_ind_names);
        lean_dec(aux_env);
        Ok(diag_update(new_env, diag))
    }

    /// Dispatch a kernel declaration add. CONSUMES `env`, BORROWS `decl`; returns
    /// `Except KernelException Environment`. Kinds 0-3 use the Rust `add_decl_impl`, kind 5 (mutual)
    /// uses `add_mutual_impl`; quot uses `add_quot_impl`; inductive is gated while the port is
    /// incomplete.
    #[no_mangle]
    pub unsafe fn lean_rust_add_decl(
        env: *mut LeanObject,
        decl: *mut LeanObject,
        check: bool,
    ) -> *mut LeanObject {
        match lean_ptr_tag(decl) {
            0 | 1 | 2 | 3 => match add_decl_impl(env, decl, check) {
                Ok(new_env) => mk_except_ok(new_env),
                Err(e) => kernel_error_to_lean_except(e),
            },
            5 => match add_mutual_impl(env, decl, check) {
                Ok(new_env) => mk_except_ok(new_env),
                Err(e) => kernel_error_to_lean_except(e),
            },
            4 => match add_quot_impl(env) {
                Ok(new_env) => mk_except_ok(new_env),
                Err(e) => {
                    lean_dec(env);
                    kernel_error_to_lean_except(e)
                }
            },
            6 => match add_inductive_impl(env, decl) {
                Ok(new_env) => mk_except_ok(new_env),
                Err(e) => kernel_error_to_lean_except(e),
            },
            _ => {
                lean_dec(env);
                let msg =
                    lean_mk_string_from_bytes(b"unknown declaration kind".as_ptr().cast(), 24);
                kernel_error_to_lean_except(KernelError::Other { msg })
            }
        }
    }

    // ---------------------------------------------------------------------------
    // Init / Finalize
    // ---------------------------------------------------------------------------

    pub fn finalize_type_checker() {
        // All globals were marked persistent; the runtime will free them.
        // Reset pointers to null for cleanliness.
        let ptrs: &[&AtomicPtr<LeanObject>] = &[
            &G_KERNEL_FRESH,
            &G_BOOL_TRUE,
            &G_EXPR_BOOL_TRUE,
            &G_EXPR_BOOL_FALSE,
            &G_EAGER_REDUCE,
            &G_DONT_CARE,
            &G_NAT_ZERO,
            &G_NAT_SUCC,
            &G_NAT_ADD,
            &G_NAT_SUB,
            &G_NAT_MUL,
            &G_NAT_POW,
            &G_NAT_GCD,
            &G_NAT_DIV,
            &G_NAT_MOD,
            &G_NAT_BEQ,
            &G_NAT_BLE,
            &G_NAT_LAND,
            &G_NAT_LOR,
            &G_NAT_XOR,
            &G_NAT_SHIFTLEFT,
            &G_NAT_SHIFTRIGHT,
            &G_STRING_MK,
            &G_LEAN_REDUCE_BOOL,
            &G_LEAN_REDUCE_NAT,
            &G_QUOT_LIFT_NAME,
            &G_QUOT_IND_NAME,
            &G_QUOT_MK_NAME,
            &G_NESTED_NAME,
            &G_NESTED_FRESH,
            &G_IND_FRESH,
            &G_LIST_CONS_CHAR,
            &G_LIST_NIL_CHAR,
            &G_CHAR_OF_NAT,
        ];
        for p in ptrs {
            p.store(ptr::null_mut(), Ordering::Release);
        }
    }

    #[export_name = "_ZN4lean22initialize_environmentEv"]
    pub fn initialize_environment() {
        // No per-environment globals needed; all state is per-instance.
    }

    #[export_name = "_ZN4lean20finalize_environmentEv"]
    pub fn finalize_environment() {}

    // The ReductionStatus type needs to be accessible from the TypeChecker impl.
    // Rust doesn't allow nested enums in impls cleanly, so we define it at module level:
    #[derive(PartialEq)]
    enum ReductionStatus {
        Continue,
        DefUnknown,
        DefEqual,
        DefDiff,
    }
} // end kernel_type_checker_impl
pub use kernel_type_checker_impl::*;
