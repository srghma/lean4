use core::ffi::{CStr, c_char, c_int, c_long, c_uchar, c_uint, c_void};
/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Full Rust implementations of kernel/abstract.cpp LEAN_EXPORT functions:
  lean_expr_abstract       — replaces lean_cxx_expr_abstract
  lean_expr_abstract_range — replaces lean_cxx_expr_abstract_range

Algorithm: recursive expression traversal using replace_rec_fn pattern.
For each node m at De Bruijn offset:
  - If m has no FVar or MVar: stop recursing (no free/meta vars in subtree)
  - If m is FVar or MVar: search backward through subst for matching name;
    if found at position i, replace with BVar(offset + n - i - 1)
  - Otherwise: recurse into children

Bit layout of Expr.Data:
  bit 40 = hasFVar
  bit 41 = hasExprMVar
  bit 42 = hasLevelMVar (hasMVar = hasExprMVar || hasLevelMVar)

Expression kind tags:
  BVar=0  FVar=1  MVar=2  Sort=3  Const=4  App=5
  Lambda=6  Pi=7  Let=8  Lit=9  MData=10  Proj=11
*/

mod kernel_abstract_impl {
    use crate::*;
    use core::ffi::{CStr, c_char, c_int, c_long, c_uchar, c_uint, c_void};
    use std::collections::HashMap;

    unsafe extern "C" {
        fn lean_expr_mk_bvar(idx: *mut LeanObject) -> *mut LeanObject;
        fn lean_expr_mk_app(f: *mut LeanObject, a: *mut LeanObject) -> *mut LeanObject;
        fn lean_expr_mk_lambda(
            n: *mut LeanObject,
            d: *mut LeanObject,
            b: *mut LeanObject,
            bi: u8,
        ) -> *mut LeanObject;
        fn lean_expr_mk_forall(
            n: *mut LeanObject,
            d: *mut LeanObject,
            b: *mut LeanObject,
            bi: u8,
        ) -> *mut LeanObject;
        fn lean_expr_mk_let(
            n: *mut LeanObject,
            t: *mut LeanObject,
            v: *mut LeanObject,
            b: *mut LeanObject,
            nondep: u8,
        ) -> *mut LeanObject;
        fn lean_expr_mk_mdata(data: *mut LeanObject, expr: *mut LeanObject) -> *mut LeanObject;
        fn lean_expr_mk_proj(
            sname: *mut LeanObject,
            idx: *mut LeanObject,
            expr: *mut LeanObject,
        ) -> *mut LeanObject;
    }

    const EXPR_FVAR: u8 = 1;
    const EXPR_MVAR: u8 = 2;
    const EXPR_APP: u8 = 5;
    const EXPR_LAMBDA: u8 = 6;
    const EXPR_PI: u8 = 7;
    const EXPR_LET: u8 = 8;
    const EXPR_MDATA: u8 = 10;
    const EXPR_PROJ: u8 = 11;

    // Read the Expr.Data u64 stored right after the object pointer fields.
    #[inline(always)]
    unsafe fn expr_data(e: *mut LeanObject) -> u64 {
        let num_objs = (*e).other as usize;
        lean_ctor_get_uint64(e, num_objs * core::mem::size_of::<*mut LeanObject>())
    }

    #[inline(always)]
    unsafe fn has_fvar(e: *mut LeanObject) -> bool {
        (expr_data(e) >> 40) & 1 == 1
    }

    #[inline(always)]
    unsafe fn has_expr_mvar(e: *mut LeanObject) -> bool {
        (expr_data(e) >> 41) & 1 == 1
    }

    #[inline(always)]
    unsafe fn has_level_mvar(e: *mut LeanObject) -> bool {
        (expr_data(e) >> 42) & 1 == 1
    }

    #[inline(always)]
    unsafe fn has_mvar(e: *mut LeanObject) -> bool {
        has_expr_mvar(e) || has_level_mvar(e)
    }

    // BinderInfo byte for Lambda/Pi.
    #[inline(always)]
    unsafe fn expr_binder_info_raw(e: *mut LeanObject) -> u8 {
        let num_objs = (*e).other as usize;
        lean_ctor_get_uint8(e, num_objs * 8 + 8)
    }

    // nondep byte for Let.
    #[inline(always)]
    unsafe fn expr_let_nondep(e: *mut LeanObject) -> u8 {
        lean_ctor_get_uint8(e, 4 * 8 + 8)
    }

    // Get pointer to start of array data without dereferencing.
    #[inline(always)]
    unsafe fn lean_array_data_ptr(obj: *mut LeanObject) -> *const *mut LeanObject {
        (obj as *const u8).add(24) as *const *mut LeanObject
    }

    struct AbstractFn {
        n: usize,                      // number of substitution expressions
        subst: *const *mut LeanObject, // borrowed substitution slice
        cache: HashMap<(usize, u32), *mut LeanObject>,
    }

    impl Drop for AbstractFn {
        fn drop(&mut self) {
            unsafe {
                for (_, v) in &self.cache {
                    lean_dec(*v);
                }
            }
        }
    }

    impl AbstractFn {
        // Returns owned reference to the abstraction of `e` at De Bruijn `offset`.
        // `e` is borrowed.
        unsafe fn apply(&mut self, e: *mut LeanObject, offset: u32) -> *mut LeanObject {
            // Early exit: node has no free or meta variables.
            if !has_fvar(e) && !has_mvar(e) {
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
                EXPR_FVAR | EXPR_MVAR => {
                    // Search backward through subst for a matching FVar/MVar name.
                    let e_name = lean_ctor_get(e, 0); // field[0] = name
                    let mut i = self.n;
                    let mut found = false;
                    let mut bvar_idx = 0usize;
                    while i > 0 {
                        i -= 1;
                        let v = *self.subst.add(i);
                        let v_tag = lean_obj_tag(v);
                        if (tag == EXPR_FVAR && v_tag == EXPR_FVAR)
                            || (tag == EXPR_MVAR && v_tag == EXPR_MVAR)
                        {
                            let v_name = lean_ctor_get(v, 0);
                            if lean_name_eq(v_name, e_name) != 0 {
                                // Match: replace with BVar(offset + n - i - 1)
                                bvar_idx = offset as usize + self.n - i - 1;
                                found = true;
                                break;
                            }
                        }
                    }
                    if found {
                        lean_expr_mk_bvar(lean_box(bvar_idx))
                    } else {
                        // No match in subst: return e unchanged (leaf).
                        lean_inc(e);
                        e
                    }
                }
                EXPR_APP => {
                    let fn_e = lean_ctor_get(e, 0);
                    let arg_e = lean_ctor_get(e, 1);
                    let new_fn = self.apply(fn_e, offset);
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
                    let dom = lean_ctor_get(e, 1);
                    let body = lean_ctor_get(e, 2);
                    let new_dom = self.apply(dom, offset);
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
                    let ty = lean_ctor_get(e, 1);
                    let val = lean_ctor_get(e, 2);
                    let body = lean_ctor_get(e, 3);
                    let new_ty = self.apply(ty, offset);
                    let new_val = self.apply(val, offset);
                    let new_body = self.apply(body, offset + 1);
                    if new_ty == ty && new_val == val && new_body == body {
                        lean_dec(new_ty);
                        lean_dec(new_val);
                        lean_dec(new_body);
                        lean_inc(e);
                        e
                    } else {
                        let name = lean_ctor_get(e, 0);
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
                        let idx = lean_ctor_get(e, 1);
                        lean_inc(sname);
                        lean_inc(idx);
                        lean_expr_mk_proj(sname, idx, new_child)
                    }
                }
                _ => {
                    // BVar, Sort, Const, Lit: leaves. has_fvar/has_mvar check above
                    // should have handled the early exit. Return unchanged.
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

    unsafe fn abstract_core(
        e: *mut LeanObject,
        n: usize,
        subst: *const *mut LeanObject,
    ) -> *mut LeanObject {
        if n == 0 || (!has_fvar(e) && !has_mvar(e)) {
            lean_inc(e);
            return e;
        }
        let mut abs_fn = AbstractFn {
            n,
            subst,
            cache: HashMap::new(),
        };
        abs_fn.apply(e, 0)
    }

    // lean_expr_abstract (e : @& Expr) (xs : @& Array Expr) : Expr
    #[no_mangle]
    pub unsafe fn lean_expr_abstract(
        e: *mut LeanObject,
        subst: *mut LeanObject,
    ) -> *mut LeanObject {
        let n = lean_array_size(subst);
        abstract_core(e, n, lean_array_data_ptr(subst))
    }

    // lean_expr_abstract_range (e : @& Expr) (n : @& Nat) (xs : @& Array Expr) : Expr
    // Uses at most min(n, xs.size) entries.
    #[no_mangle]
    pub unsafe fn lean_expr_abstract_range(
        e: *mut LeanObject,
        n: *mut LeanObject,
        subst: *mut LeanObject,
    ) -> *mut LeanObject {
        let sz = lean_array_size(subst);
        let count = if !lean_is_scalar(n) {
            sz
        } else {
            lean_unbox(n).min(sz)
        };
        abstract_core(e, count, lean_array_data_ptr(subst))
    }

    #[no_mangle]
    pub unsafe fn lean_expr_abstract_ptr(
        e: *mut LeanObject,
        n: usize,
        subst: *const *mut LeanObject,
    ) -> *mut LeanObject {
        abstract_core(e, n, subst)
    }
}
