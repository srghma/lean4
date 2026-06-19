/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Full Rust implementations of kernel/instantiate.cpp LEAN_EXPORT functions:
  lean_expr_instantiate1
  lean_expr_instantiate
  lean_expr_instantiate_range
  lean_expr_instantiate_rev
  lean_expr_instantiate_rev_range
  lean_expr_instantiate_at
  lean_expr_instantiate_rev_ptr
  lean_expr_cheap_beta_reduce
  lean_expr_instantiate_lparams
  lean_instantiate_type_lparams
  lean_instantiate_value_lparams

Algorithm: recursive expression traversal (mirrors replace_rec_fn) with an
(expr*, offset) cache for shared sub-expressions.

Expression kind tags:
  BVar=0  FVar=1  MVar=2  Sort=3  Const=4  App=5
  Lambda=6  Pi=7  Let=8  Lit=9  MData=10  Proj=11

Scalar field layout:
  All ctors: [0] Expr.Data (u64, bits 0-63)
    Bits [63:44] = bvarRange (20-bit, loose BVar count)
  Lambda/Pi (3 obj fields): uint8 BinderInfo after data u64
  Let      (4 obj fields): uint8 nondep after data u64
*/

#[cfg(feature = "export-runtime-ffi")]
mod kernel_instantiate_impl {
    use super::*;
    use super::runtime_object_panic_impl::lean_internal_panic;
    use super::runtime_object_name_impl::lean_name_eq;
    use std::collections::HashMap;

    extern "C" {
        fn lean_level_mk_succ(l: *mut LeanObject) -> *mut LeanObject;
        fn lean_level_mk_max(l1: *mut LeanObject, l2: *mut LeanObject) -> *mut LeanObject;
        fn lean_level_mk_imax(l1: *mut LeanObject, l2: *mut LeanObject) -> *mut LeanObject;
        fn lean_level_eq(l1: *mut LeanObject, l2: *mut LeanObject) -> u8;
        fn lean_expr_lift_loose_bvars(e: *mut LeanObject, s: *mut LeanObject, d: *mut LeanObject) -> *mut LeanObject;
        fn lean_expr_mk_bvar(idx: *mut LeanObject) -> *mut LeanObject;
        fn lean_expr_mk_sort(l: *mut LeanObject) -> *mut LeanObject;
        fn lean_expr_mk_const(n: *mut LeanObject, us: *mut LeanObject) -> *mut LeanObject;
        fn lean_expr_mk_app(f: *mut LeanObject, a: *mut LeanObject) -> *mut LeanObject;
        fn lean_expr_mk_lambda(n: *mut LeanObject, d: *mut LeanObject, b: *mut LeanObject, bi: u8) -> *mut LeanObject;
        fn lean_expr_mk_forall(n: *mut LeanObject, d: *mut LeanObject, b: *mut LeanObject, bi: u8) -> *mut LeanObject;
        fn lean_expr_mk_let(n: *mut LeanObject, t: *mut LeanObject, v: *mut LeanObject, b: *mut LeanObject, nondep: u8) -> *mut LeanObject;
        fn lean_expr_mk_mdata(data: *mut LeanObject, expr: *mut LeanObject) -> *mut LeanObject;
        fn lean_expr_mk_proj(sname: *mut LeanObject, idx: *mut LeanObject, expr: *mut LeanObject) -> *mut LeanObject;
    }

    const LEVEL_DATA_HAS_PARAM_BIT: u64 = 1u64 << 33;
    const LEVEL_DATA_DEPTH_SHIFT: u32 = 40;

    const LEVEL_SUCC:  u8 = 1;
    const LEVEL_MAX:   u8 = 2;
    const LEVEL_IMAX:  u8 = 3;
    const LEVEL_PARAM: u8 = 4;

    const EXPR_BVAR:   u8 = 0;
    const EXPR_SORT:   u8 = 3;
    const EXPR_CONST:  u8 = 4;
    const EXPR_APP:    u8 = 5;
    const EXPR_LAMBDA: u8 = 6;
    const EXPR_PI:     u8 = 7;
    const EXPR_LET:    u8 = 8;
    const EXPR_MDATA:  u8 = 10;
    const EXPR_PROJ:   u8 = 11;

    const EXPR_DATA_HAS_LEVEL_PARAM_BIT: u64 = 1u64 << 43;

    const CONSTANT_INFO_DEFINITION: u8 = 1;
    const CONSTANT_INFO_THEOREM: u8 = 2;

    const LIST_CONS_TAG: u32 = 1;
    const LIST_CONS_FIELDS: usize = 2;

    const TYPE_LPARAMS_MISMATCH: &[u8] = b"#universes mismatch at instantiateTypeLevelParams\0";
    const VALUE_LPARAMS_MISMATCH: &[u8] = b"#universes mismatch at instantiateValueLevelParams\0";
    const VALUE_LPARAMS_EXPECTED_VALUE: &[u8] = b"definition/theorem expected at instantiateValueLevelParams\0";

    #[inline(always)]
    unsafe fn ctor_set(obj: *mut LeanObject, idx: usize, val: *mut LeanObject) {
        (obj.add(1) as *mut *mut LeanObject).add(idx).write(val);
    }

    unsafe fn alloc_ctor(tag: u32, num_objs: usize, scalar_size: usize) -> *mut LeanObject {
        lean_runtime_alloc_ctor(
            tag as core::ffi::c_uint,
            num_objs as core::ffi::c_uint,
            scalar_size as core::ffi::c_uint,
        )
    }

    // bvarRange = bits [63:44] of the Expr.Data u64.
    #[inline(always)]
    unsafe fn expr_bvar_range(e: *mut LeanObject) -> u64 {
        expr_data(e) >> 44
    }

    #[inline(always)]
    unsafe fn expr_data(e: *mut LeanObject) -> u64 {
        let num_objs = (*e).other as usize;
        lean_ctor_get_uint64(e, num_objs * core::mem::size_of::<*mut LeanObject>())
    }

    #[inline(always)]
    unsafe fn expr_has_level_param(e: *mut LeanObject) -> bool {
        (expr_data(e) & EXPR_DATA_HAS_LEVEL_PARAM_BIT) != 0
    }

    // BinderInfo byte for Lambda/Pi (stored after data u64, num_objs=3).
    #[inline(always)]
    unsafe fn expr_binder_info_raw(e: *mut LeanObject) -> u8 {
        let num_objs = (*e).other as usize;
        lean_ctor_get_uint8(e, num_objs * 8 + 8)
    }

    // nondep byte for Let (4 obj fields, stored after data u64).
    #[inline(always)]
    unsafe fn expr_let_nondep(e: *mut LeanObject) -> u8 {
        lean_ctor_get_uint8(e, 4 * 8 + 8)
    }

    #[inline(always)]
    unsafe fn level_data(l: *mut LeanObject) -> u64 {
        if lean_is_scalar(l) {
            0
        } else {
            let num_objs = (*l).other as usize;
            lean_ctor_get_uint64(l, num_objs * core::mem::size_of::<*mut LeanObject>())
        }
    }

    #[inline(always)]
    unsafe fn level_depth(l: *mut LeanObject) -> u32 {
        (level_data(l) >> LEVEL_DATA_DEPTH_SHIFT) as u32
    }

    #[inline(always)]
    unsafe fn level_has_param(l: *mut LeanObject) -> bool {
        (level_data(l) & LEVEL_DATA_HAS_PARAM_BIT) != 0
    }

    unsafe fn level_is_zero(l: *mut LeanObject) -> bool {
        lean_is_scalar(l) && lean_unbox(l) == 0
    }

    unsafe fn level_is_one(l: *mut LeanObject) -> bool {
        !lean_is_scalar(l) && lean_obj_tag(l) == LEVEL_SUCC && level_is_zero(lean_ctor_get(l, 0))
    }

    unsafe fn level_is_explicit(l: *mut LeanObject) -> bool {
        lean_is_scalar(l) || (!lean_is_scalar(l) && lean_obj_tag(l) == LEVEL_SUCC && level_is_explicit(lean_ctor_get(l, 0)))
    }

    unsafe fn level_is_not_zero(l: *mut LeanObject) -> bool {
        if lean_is_scalar(l) {
            return false;
        }
        match lean_obj_tag(l) {
            LEVEL_SUCC => true,
            LEVEL_MAX => level_is_not_zero(lean_ctor_get(l, 0)) || level_is_not_zero(lean_ctor_get(l, 1)),
            LEVEL_IMAX => level_is_not_zero(lean_ctor_get(l, 1)),
            _ => false,
        }
    }

    unsafe fn level_to_offset(mut l: *mut LeanObject) -> (*mut LeanObject, u32) {
        let mut offset = 0;
        while !lean_is_scalar(l) && lean_obj_tag(l) == LEVEL_SUCC {
            l = lean_ctor_get(l, 0);
            offset += 1;
        }
        (l, offset)
    }

    unsafe fn level_eq(lhs: *mut LeanObject, rhs: *mut LeanObject) -> bool {
        lean_level_eq(lhs, rhs) != 0
    }

    unsafe fn mk_max_simplified(lhs: *mut LeanObject, rhs: *mut LeanObject) -> *mut LeanObject {
        if level_is_explicit(lhs) && level_is_explicit(rhs) {
            if level_depth(lhs) >= level_depth(rhs) {
                lean_dec(rhs);
                return lhs;
            } else {
                lean_dec(lhs);
                return rhs;
            }
        }
        if level_eq(lhs, rhs) {
            lean_dec(rhs);
            return lhs;
        }
        if level_is_zero(lhs) {
            lean_dec(lhs);
            return rhs;
        }
        if level_is_zero(rhs) {
            lean_dec(rhs);
            return lhs;
        }
        if !lean_is_scalar(rhs) && lean_obj_tag(rhs) == LEVEL_MAX
            && (level_eq(lean_ctor_get(rhs, 0), lhs) || level_eq(lean_ctor_get(rhs, 1), lhs))
        {
            lean_dec(lhs);
            return rhs;
        }
        if !lean_is_scalar(lhs) && lean_obj_tag(lhs) == LEVEL_MAX
            && (level_eq(lean_ctor_get(lhs, 0), rhs) || level_eq(lean_ctor_get(lhs, 1), rhs))
        {
            lean_dec(rhs);
            return lhs;
        }
        let (base_lhs, offset_lhs) = level_to_offset(lhs);
        let (base_rhs, offset_rhs) = level_to_offset(rhs);
        if level_eq(base_lhs, base_rhs) {
            if offset_lhs > offset_rhs {
                lean_dec(rhs);
                return lhs;
            } else {
                lean_dec(lhs);
                return rhs;
            }
        }
        lean_level_mk_max(lhs, rhs)
    }

    unsafe fn mk_imax_simplified(lhs: *mut LeanObject, rhs: *mut LeanObject) -> *mut LeanObject {
        if level_is_not_zero(rhs) {
            return mk_max_simplified(lhs, rhs);
        }
        if level_is_zero(rhs) {
            lean_dec(lhs);
            return rhs;
        }
        if level_is_zero(lhs) || level_is_one(lhs) {
            lean_dec(lhs);
            return rhs;
        }
        if level_eq(lhs, rhs) {
            lean_dec(rhs);
            return lhs;
        }
        lean_level_mk_imax(lhs, rhs)
    }

    // (expr*, offset) → owned result cache — mirrors replace_rec_fn's cache.
    struct InstFn {
        n: usize,                           // number of substitution expressions
        start: usize,                       // first loose BVar index to instantiate at offset 0
        base: *const *mut LeanObject,       // pointer to first subst element (borrowed)
        rev: bool,                          // if true, index as subst[n-1-rel_idx] (instantiateRev)
        cache: HashMap<(usize, u32), *mut LeanObject>,
    }

    impl Drop for InstFn {
        fn drop(&mut self) {
            unsafe {
                for (_, v) in &self.cache {
                    lean_dec(*v);
                }
            }
        }
    }

    impl InstFn {
        // Returns an owned reference to the instantiation of `e` at De Bruijn `offset`.
        // `e` is borrowed.
        unsafe fn apply(&mut self, e: *mut LeanObject, offset: u32) -> *mut LeanObject {
            // Early exit: no loose bvars at or above offset in this subtree.
            if expr_bvar_range(e) <= offset as u64 {
                lean_inc(e);
                return e;
            }

            // Cache check for shared nodes.
            let shared = (*e).rc != 1;
            if shared {
                if let Some(&cached) = self.cache.get(&(e as usize, offset)) {
                    lean_inc(cached);
                    return cached;
                }
            }

            let tag = lean_obj_tag(e);
            let result: *mut LeanObject = match tag {
                EXPR_BVAR => {
                    let idx_obj = lean_ctor_get(e, 0);
                    if lean_is_scalar(idx_obj) {
                        let idx = lean_unbox(idx_obj);
                        let Some(first_idx) = self.start.checked_add(offset as usize) else {
                            lean_inc(e);
                            return e;
                        };
                        if idx >= first_idx {
                            let rel_idx = idx - first_idx;
                            let (_, ovf) = first_idx.overflowing_add(self.n);
                            if ovf || rel_idx < self.n {
                                // In substitution range: look up substitution and lift.
                                let subst_idx = if self.rev { self.n - rel_idx - 1 } else { rel_idx };
                                let v = *self.base.add(subst_idx);
                                // lift_loose_bvars(v, 0, offset): lift all loose bvars by offset.
                                lean_expr_lift_loose_bvars(v, lean_box(0), lean_box(offset as usize))
                            } else {
                                // Beyond substitution range: lower BVar index by n.
                                let new_idx = idx - self.n;
                                lean_expr_mk_bvar(lean_box(new_idx))
                            }
                        } else {
                            lean_inc(e);
                            e
                        }
                    } else {
                        // Bignum BVar: bvarRange is ≤ 20-bit; bignum indices can't appear.
                        lean_inc(e);
                        e
                    }
                }
                EXPR_APP => {
                    let fn_e  = lean_ctor_get(e, 0);
                    let arg_e = lean_ctor_get(e, 1);
                    let new_fn  = self.apply(fn_e,  offset);
                    let new_arg = self.apply(arg_e, offset);
                    if new_fn == fn_e && new_arg == arg_e {
                        lean_dec(new_fn);
                        lean_dec(new_arg);
                        lean_inc(e);
                        e
                    } else {
                        lean_expr_mk_app(new_fn, new_arg)
                    }
                }
                EXPR_LAMBDA | EXPR_PI => {
                    let dom  = lean_ctor_get(e, 1);
                    let body = lean_ctor_get(e, 2);
                    let new_dom  = self.apply(dom,  offset);
                    let new_body = self.apply(body, offset + 1);
                    if new_dom == dom && new_body == body {
                        lean_dec(new_dom);
                        lean_dec(new_body);
                        lean_inc(e);
                        e
                    } else {
                        let name = lean_ctor_get(e, 0);
                        lean_inc(name);
                        let bi = expr_binder_info_raw(e);
                        if tag == EXPR_LAMBDA {
                            lean_expr_mk_lambda(name, new_dom, new_body, bi)
                        } else {
                            lean_expr_mk_forall(name, new_dom, new_body, bi)
                        }
                    }
                }
                EXPR_LET => {
                    let ty   = lean_ctor_get(e, 1);
                    let val  = lean_ctor_get(e, 2);
                    let body = lean_ctor_get(e, 3);
                    let new_ty   = self.apply(ty,   offset);
                    let new_val  = self.apply(val,  offset);
                    let new_body = self.apply(body, offset + 1);
                    if new_ty == ty && new_val == val && new_body == body {
                        lean_dec(new_ty);
                        lean_dec(new_val);
                        lean_dec(new_body);
                        lean_inc(e);
                        e
                    } else {
                        let name   = lean_ctor_get(e, 0);
                        lean_inc(name);
                        let nondep = expr_let_nondep(e);
                        lean_expr_mk_let(name, new_ty, new_val, new_body, nondep)
                    }
                }
                EXPR_MDATA => {
                    let child = lean_ctor_get(e, 1);
                    let new_child = self.apply(child, offset);
                    if new_child == child {
                        lean_dec(new_child);
                        lean_inc(e);
                        e
                    } else {
                        let md = lean_ctor_get(e, 0);
                        lean_inc(md);
                        lean_expr_mk_mdata(md, new_child)
                    }
                }
                EXPR_PROJ => {
                    let child = lean_ctor_get(e, 2);
                    let new_child = self.apply(child, offset);
                    if new_child == child {
                        lean_dec(new_child);
                        lean_inc(e);
                        e
                    } else {
                        let sname = lean_ctor_get(e, 0);
                        let idx   = lean_ctor_get(e, 1);
                        lean_inc(sname);
                        lean_inc(idx);
                        lean_expr_mk_proj(sname, idx, new_child)
                    }
                }
                _ => {
                    // FVar, MVar, Sort, Const, Lit: leaves without loose bvars.
                    lean_inc(e);
                    e
                }
            };

            if shared {
                lean_inc(result);
                self.cache.insert((e as usize, offset), result);
            }
            result
        }
    }

    // Shared entry point for instantiate variants.
    // `a` is borrowed; returns owned.
    unsafe fn instantiate_core(
        a: *mut LeanObject,
        start: usize,
        n: usize,
        base: *const *mut LeanObject,
        rev: bool,
    ) -> *mut LeanObject {
        if n == 0 || start >= expr_bvar_range(a) as usize {
            lean_inc(a);
            return a;
        }
        let mut inst = InstFn { n, start, base, rev, cache: HashMap::new() };
        inst.apply(a, 0)
    }

    // C++ compatibility entry point for `lean::instantiate(a, start, n, subst)`.
    // `subst` points to `n` borrowed Expr object pointers.
    #[no_mangle]
    pub unsafe extern "C" fn lean_expr_instantiate_at(
        a: *mut LeanObject,
        start: usize,
        n: usize,
        subst: *const *mut LeanObject,
    ) -> *mut LeanObject {
        instantiate_core(a, start, n, subst, false)
    }

    // C++ compatibility entry point for `lean::instantiate_rev(a, n, subst)`.
    // `subst` points to `n` borrowed Expr object pointers.
    #[no_mangle]
    pub unsafe extern "C" fn lean_expr_instantiate_rev_ptr(
        a: *mut LeanObject,
        n: usize,
        subst: *const *mut LeanObject,
    ) -> *mut LeanObject {
        instantiate_core(a, 0, n, subst, true)
    }

    unsafe fn mk_app_from_borrowed(mut f: *mut LeanObject, args: &[*mut LeanObject]) -> *mut LeanObject {
        lean_inc(f);
        for &arg in args {
            lean_inc(arg);
            f = lean_expr_mk_app(f, arg);
        }
        f
    }

    // C++ compatibility entry point for `lean::cheap_beta_reduce`.
    #[no_mangle]
    pub unsafe extern "C" fn lean_expr_cheap_beta_reduce(e: *mut LeanObject) -> *mut LeanObject {
        if lean_obj_tag(e) != EXPR_APP {
            lean_inc(e);
            return e;
        }

        let mut rev_args: Vec<*mut LeanObject> = Vec::new();
        let mut head = e;
        while lean_obj_tag(head) == EXPR_APP {
            rev_args.push(lean_ctor_get(head, 1));
            head = lean_ctor_get(head, 0);
        }
        if lean_obj_tag(head) != EXPR_LAMBDA {
            lean_inc(e);
            return e;
        }
        rev_args.reverse();

        let mut consumed_lambdas = 0usize;
        let mut fn_body = head;
        while lean_obj_tag(fn_body) == EXPR_LAMBDA && consumed_lambdas < rev_args.len() {
            consumed_lambdas += 1;
            fn_body = lean_ctor_get(fn_body, 2);
        }

        if expr_bvar_range(fn_body) == 0 {
            return mk_app_from_borrowed(fn_body, &rev_args[consumed_lambdas..]);
        }

        if lean_obj_tag(fn_body) == EXPR_BVAR {
            let idx_obj = lean_ctor_get(fn_body, 0);
            if lean_is_scalar(idx_obj) {
                let idx = lean_unbox(idx_obj);
                if idx < consumed_lambdas {
                    let arg_idx = consumed_lambdas - idx - 1;
                    return mk_app_from_borrowed(rev_args[arg_idx], &rev_args[consumed_lambdas..]);
                }
            }
        }

        lean_inc(e);
        e
    }

    unsafe fn list_len(mut xs: *mut LeanObject) -> usize {
        let mut n = 0;
        while !lean_is_scalar(xs) {
            n += 1;
            xs = lean_ctor_get(xs, 1);
        }
        n
    }

    unsafe fn list_is_nil(xs: *mut LeanObject) -> bool {
        lean_is_scalar(xs)
    }

    unsafe fn find_level_param(
        name: *mut LeanObject,
        mut params: *mut LeanObject,
        mut levels: *mut LeanObject,
    ) -> Option<*mut LeanObject> {
        while !lean_is_scalar(params) && !lean_is_scalar(levels) {
            let param = lean_ctor_get(params, 0);
            if lean_name_eq(param, name) != 0 {
                let level = lean_ctor_get(levels, 0);
                lean_inc(level);
                return Some(level);
            }
            params = lean_ctor_get(params, 1);
            levels = lean_ctor_get(levels, 1);
        }
        None
    }

    unsafe fn instantiate_level_lparams(
        level: *mut LeanObject,
        params: *mut LeanObject,
        levels: *mut LeanObject,
    ) -> *mut LeanObject {
        if !level_has_param(level) {
            lean_inc(level);
            return level;
        }
        if lean_is_scalar(level) {
            lean_inc(level);
            return level;
        }
        match lean_obj_tag(level) {
            LEVEL_SUCC => {
                let child = lean_ctor_get(level, 0);
                let new_child = instantiate_level_lparams(child, params, levels);
                if new_child == child {
                    lean_dec(new_child);
                    lean_inc(level);
                    level
                } else {
                    lean_level_mk_succ(new_child)
                }
            }
            LEVEL_MAX | LEVEL_IMAX => {
                let lhs = lean_ctor_get(level, 0);
                let rhs = lean_ctor_get(level, 1);
                let new_lhs = instantiate_level_lparams(lhs, params, levels);
                let new_rhs = instantiate_level_lparams(rhs, params, levels);
                if new_lhs == lhs && new_rhs == rhs {
                    lean_dec(new_lhs);
                    lean_dec(new_rhs);
                    lean_inc(level);
                    level
                } else if lean_obj_tag(level) == LEVEL_MAX {
                    mk_max_simplified(new_lhs, new_rhs)
                } else {
                    mk_imax_simplified(new_lhs, new_rhs)
                }
            }
            LEVEL_PARAM => {
                if let Some(replacement) = find_level_param(lean_ctor_get(level, 0), params, levels) {
                    replacement
                } else {
                    lean_inc(level);
                    level
                }
            }
            _ => {
                lean_inc(level);
                level
            }
        }
    }

    unsafe fn instantiate_levels_lparams(
        list: *mut LeanObject,
        params: *mut LeanObject,
        levels: *mut LeanObject,
    ) -> *mut LeanObject {
        let mut curr = list;
        let mut new_levels = Vec::new();
        let mut changed = false;
        while !lean_is_scalar(curr) {
            let head = lean_ctor_get(curr, 0);
            let new_head = instantiate_level_lparams(head, params, levels);
            changed |= new_head != head;
            new_levels.push(new_head);
            curr = lean_ctor_get(curr, 1);
        }
        if !changed {
            for level in new_levels {
                lean_dec(level);
            }
            lean_inc(list);
            return list;
        }
        let mut result = lean_box(0);
        for level in new_levels.into_iter().rev() {
            let cons = alloc_ctor(LIST_CONS_TAG, LIST_CONS_FIELDS, 0);
            ctor_set(cons, 0, level);
            ctor_set(cons, 1, result);
            result = cons;
        }
        result
    }

    unsafe fn instantiate_expr_lparams_impl(
        e: *mut LeanObject,
        params: *mut LeanObject,
        levels: *mut LeanObject,
    ) -> *mut LeanObject {
        if !expr_has_level_param(e) {
            lean_inc(e);
            return e;
        }
        match lean_obj_tag(e) {
            EXPR_SORT => {
                let level = lean_ctor_get(e, 0);
                let new_level = instantiate_level_lparams(level, params, levels);
                if new_level == level {
                    lean_dec(new_level);
                    lean_inc(e);
                    e
                } else {
                    lean_expr_mk_sort(new_level)
                }
            }
            EXPR_CONST => {
                let old_levels = lean_ctor_get(e, 1);
                let new_levels = instantiate_levels_lparams(old_levels, params, levels);
                if new_levels == old_levels {
                    lean_dec(new_levels);
                    lean_inc(e);
                    e
                } else {
                    let name = lean_ctor_get(e, 0);
                    lean_inc(name);
                    lean_expr_mk_const(name, new_levels)
                }
            }
            EXPR_APP => {
                let f = lean_ctor_get(e, 0);
                let a = lean_ctor_get(e, 1);
                let new_f = instantiate_expr_lparams_impl(f, params, levels);
                let new_a = instantiate_expr_lparams_impl(a, params, levels);
                if new_f == f && new_a == a {
                    lean_dec(new_f);
                    lean_dec(new_a);
                    lean_inc(e);
                    e
                } else {
                    lean_expr_mk_app(new_f, new_a)
                }
            }
            EXPR_LAMBDA | EXPR_PI => {
                let domain = lean_ctor_get(e, 1);
                let body = lean_ctor_get(e, 2);
                let new_domain = instantiate_expr_lparams_impl(domain, params, levels);
                let new_body = instantiate_expr_lparams_impl(body, params, levels);
                if new_domain == domain && new_body == body {
                    lean_dec(new_domain);
                    lean_dec(new_body);
                    lean_inc(e);
                    e
                } else {
                    let name = lean_ctor_get(e, 0);
                    lean_inc(name);
                    let bi = expr_binder_info_raw(e);
                    if lean_obj_tag(e) == EXPR_LAMBDA {
                        lean_expr_mk_lambda(name, new_domain, new_body, bi)
                    } else {
                        lean_expr_mk_forall(name, new_domain, new_body, bi)
                    }
                }
            }
            EXPR_LET => {
                let ty = lean_ctor_get(e, 1);
                let val = lean_ctor_get(e, 2);
                let body = lean_ctor_get(e, 3);
                let new_ty = instantiate_expr_lparams_impl(ty, params, levels);
                let new_val = instantiate_expr_lparams_impl(val, params, levels);
                let new_body = instantiate_expr_lparams_impl(body, params, levels);
                if new_ty == ty && new_val == val && new_body == body {
                    lean_dec(new_ty);
                    lean_dec(new_val);
                    lean_dec(new_body);
                    lean_inc(e);
                    e
                } else {
                    let name = lean_ctor_get(e, 0);
                    lean_inc(name);
                    lean_expr_mk_let(name, new_ty, new_val, new_body, expr_let_nondep(e))
                }
            }
            EXPR_MDATA => {
                let child = lean_ctor_get(e, 1);
                let new_child = instantiate_expr_lparams_impl(child, params, levels);
                if new_child == child {
                    lean_dec(new_child);
                    lean_inc(e);
                    e
                } else {
                    let data = lean_ctor_get(e, 0);
                    lean_inc(data);
                    lean_expr_mk_mdata(data, new_child)
                }
            }
            EXPR_PROJ => {
                let child = lean_ctor_get(e, 2);
                let new_child = instantiate_expr_lparams_impl(child, params, levels);
                if new_child == child {
                    lean_dec(new_child);
                    lean_inc(e);
                    e
                } else {
                    let struct_name = lean_ctor_get(e, 0);
                    let idx = lean_ctor_get(e, 1);
                    lean_inc(struct_name);
                    lean_inc(idx);
                    lean_expr_mk_proj(struct_name, idx, new_child)
                }
            }
            _ => {
                lean_inc(e);
                e
            }
        }
    }

    #[inline(always)]
    unsafe fn constant_info_val(info: *mut LeanObject) -> *mut LeanObject {
        lean_ctor_get(info, 0)
    }

    #[inline(always)]
    unsafe fn constant_info_constant_val(info: *mut LeanObject) -> *mut LeanObject {
        lean_ctor_get(constant_info_val(info), 0)
    }

    #[inline(always)]
    unsafe fn constant_info_lparams(info: *mut LeanObject) -> *mut LeanObject {
        lean_ctor_get(constant_info_constant_val(info), 1)
    }

    #[inline(always)]
    unsafe fn constant_info_type(info: *mut LeanObject) -> *mut LeanObject {
        lean_ctor_get(constant_info_constant_val(info), 2)
    }

    #[inline(always)]
    unsafe fn constant_info_has_value(info: *mut LeanObject) -> bool {
        let tag = lean_obj_tag(info);
        tag == CONSTANT_INFO_DEFINITION || tag == CONSTANT_INFO_THEOREM
    }

    #[inline(always)]
    unsafe fn constant_info_value(info: *mut LeanObject) -> *mut LeanObject {
        lean_ctor_get(constant_info_val(info), 1)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_expr_instantiate_lparams(
        e: *mut LeanObject,
        params: *mut LeanObject,
        levels: *mut LeanObject,
    ) -> *mut LeanObject {
        instantiate_expr_lparams_impl(e, params, levels)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_instantiate_type_lparams(
        info: *mut LeanObject,
        levels: *mut LeanObject,
    ) -> *mut LeanObject {
        let params = constant_info_lparams(info);
        if list_len(params) != list_len(levels) {
            lean_internal_panic(TYPE_LPARAMS_MISMATCH.as_ptr() as *const i8);
        }
        let ty = constant_info_type(info);
        if list_is_nil(levels) || !expr_has_level_param(ty) {
            lean_inc(ty);
            return ty;
        }
        instantiate_expr_lparams_impl(ty, params, levels)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_instantiate_value_lparams(
        info: *mut LeanObject,
        levels: *mut LeanObject,
    ) -> *mut LeanObject {
        let params = constant_info_lparams(info);
        if list_len(params) != list_len(levels) {
            lean_internal_panic(VALUE_LPARAMS_MISMATCH.as_ptr() as *const i8);
        }
        if !constant_info_has_value(info) {
            lean_internal_panic(VALUE_LPARAMS_EXPECTED_VALUE.as_ptr() as *const i8);
        }
        let value = constant_info_value(info);
        if list_is_nil(levels) || !expr_has_level_param(value) {
            lean_inc(value);
            return value;
        }
        instantiate_expr_lparams_impl(value, params, levels)
    }

    // lean_expr_instantiate1 (a e : @& Expr) : Expr
    // Instantiates BVar(0) with e and lowers all remaining loose BVars by 1.
    #[no_mangle]
    pub unsafe extern "C" fn lean_expr_instantiate1(
        a: *mut LeanObject,
        e: *mut LeanObject,
    ) -> *mut LeanObject {
        let subst = [e as *mut LeanObject];
        instantiate_core(a, 0, 1, subst.as_ptr(), false)
    }

    // Compute pointer to start of Lean array data (byte offset 24 from object header).
    // Does NOT dereference; safe to call on empty arrays.
    #[inline(always)]
    unsafe fn lean_array_data_ptr(obj: *mut LeanObject) -> *const *mut LeanObject {
        (obj as *const u8).add(24) as *const *mut LeanObject
    }

    // lean_expr_instantiate (a : @& Expr) (subst : @& Array Expr) : Expr
    // Instantiates BVar(i) with subst[i] for all i < subst.size.
    #[no_mangle]
    pub unsafe extern "C" fn lean_expr_instantiate(
        a: *mut LeanObject,
        subst: *mut LeanObject,
    ) -> *mut LeanObject {
        let n    = lean_array_size(subst);
        let base = lean_array_data_ptr(subst);
        instantiate_core(a, 0, n, base, false)
    }

    // lean_expr_instantiate_range (a : @& Expr) (begin end : @& Nat) (subst : @& Array Expr) : Expr
    // Instantiates using subst[begin..end].
    #[no_mangle]
    pub unsafe extern "C" fn lean_expr_instantiate_range(
        a: *mut LeanObject,
        begin: *mut LeanObject,
        end: *mut LeanObject,
        subst: *mut LeanObject,
    ) -> *mut LeanObject {
        if !lean_is_scalar(begin) || !lean_is_scalar(end) {
            lean_internal_panic(b"invalid range for Expr.instantiateRange\0".as_ptr() as *const i8);
        }
        let sz = lean_array_size(subst);
        let b  = lean_unbox(begin);
        let e  = lean_unbox(end);
        if b > e || e > sz {
            lean_internal_panic(b"invalid range for Expr.instantiateRange\0".as_ptr() as *const i8);
        }
        let n    = e - b;
        let base = lean_array_data_ptr(subst).add(b);
        instantiate_core(a, 0, n, base, false)
    }

    // lean_expr_instantiate_rev (a : @& Expr) (subst : @& Array Expr) : Expr
    // Like instantiate but uses reversed indexing: BVar(i) → subst[n-1-i].
    #[no_mangle]
    pub unsafe extern "C" fn lean_expr_instantiate_rev(
        a: *mut LeanObject,
        subst: *mut LeanObject,
    ) -> *mut LeanObject {
        let n    = lean_array_size(subst);
        let base = lean_array_data_ptr(subst);
        instantiate_core(a, 0, n, base, true)
    }

    // lean_expr_instantiate_rev_range (a : @& Expr) (begin end : @& Nat) (subst : @& Array Expr) : Expr
    // Like instantiate_rev but uses subst[begin..end].
    #[no_mangle]
    pub unsafe extern "C" fn lean_expr_instantiate_rev_range(
        a: *mut LeanObject,
        begin: *mut LeanObject,
        end: *mut LeanObject,
        subst: *mut LeanObject,
    ) -> *mut LeanObject {
        if !lean_is_scalar(begin) || !lean_is_scalar(end) {
            lean_internal_panic(b"invalid range for Expr.instantiateRevRange\0".as_ptr() as *const i8);
        }
        let sz = lean_array_size(subst);
        let b  = lean_unbox(begin);
        let e  = lean_unbox(end);
        if b > e || e > sz {
            lean_internal_panic(b"invalid range for Expr.instantiateRevRange\0".as_ptr() as *const i8);
        }
        let n    = e - b;
        let base = lean_array_data_ptr(subst).add(b);
        instantiate_core(a, 0, n, base, true)
    }
}
