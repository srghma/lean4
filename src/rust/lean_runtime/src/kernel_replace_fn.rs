#[cfg(feature = "export-runtime-ffi")]
use crate::*;

/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Full Rust implementation of lean_replace_expr (replace_fn in replace_fn.cpp).
Replaces the thin C++ shim lean_cxx_replace_expr.

Algorithm: replace_fn — applies a Lean closure f : Expr → Option Expr
to each sub-expression bottom-up. If f returns Some(e'), use e'. If None,
recurse into children and rebuild. Caches results for shared (multi-ref) nodes.

Expression kind tags:
  BVar=0  FVar=1  MVar=2  Sort=3  Const=4  App=5
  Lambda=6  Pi=7  Let=8  Lit=9  MData=10  Proj=11

Field layout (from expr.h):
  App:       [0]=fn,   [1]=arg
  Lambda/Pi: [0]=name, [1]=domain, [2]=body  | uint8 BinderInfo after data u64
  Let:       [0]=name, [1]=type, [2]=value, [3]=body | uint8 nondep after data u64
  MData:     [0]=kvmap, [1]=expr
  Proj:      [0]=sname, [1]=idx,  [2]=expr
*/

#[cfg(feature = "export-runtime-ffi")]
mod kernel_replace_fn_impl {
    use super::*;
    use core::ffi::c_void;
    use std::collections::HashMap;

    extern "C" {
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

    type ReplaceCallback =
        unsafe extern "C" fn(*mut c_void, *mut LeanObject, u32) -> *mut LeanObject;

    struct ReplaceCallbackFn {
        ctx: *mut c_void,
        callback: ReplaceCallback,
        use_cache: bool,
        cache: HashMap<(usize, u32), *mut LeanObject>,
    }

    impl Drop for ReplaceCallbackFn {
        fn drop(&mut self) {
            unsafe {
                for (_, v) in &self.cache {
                    lean_dec(*v);
                }
            }
        }
    }

    impl ReplaceCallbackFn {
        fn new(ctx: *mut c_void, callback: ReplaceCallback, use_cache: bool) -> Self {
            Self {
                ctx,
                callback,
                use_cache,
                cache: HashMap::new(),
            }
        }

        unsafe fn apply(&mut self, e: *mut LeanObject, offset: u32) -> *mut LeanObject {
            let shared = self.use_cache && (*e).rc != 1;
            if shared {
                if let Some(&cached) = self.cache.get(&(e as usize, offset)) {
                    lean_inc(cached);
                    return cached;
                }
            }

            let r = (self.callback)(self.ctx, e, offset);
            if !lean_is_scalar(r) {
                let inner = lean_ctor_get(r, 0);
                lean_inc(inner);
                lean_dec(r);
                if shared {
                    lean_inc(inner);
                    self.cache.insert((e as usize, offset), inner);
                }
                return inner;
            }

            const EXPR_APP: u8 = 5;
            const EXPR_LAMBDA: u8 = 6;
            const EXPR_PI: u8 = 7;
            const EXPR_LET: u8 = 8;
            const EXPR_MDATA: u8 = 10;
            const EXPR_PROJ: u8 = 11;

            let tag = lean_obj_tag(e);
            let result: *mut LeanObject = match tag {
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

    // Read BinderInfo uint8 stored right after the data u64 in Lambda/Pi (3 obj fields).
    #[inline(always)]
    unsafe fn expr_binder_info_raw(e: *mut LeanObject) -> u8 {
        let num_objs = (*e).other as usize; // 3 for Lambda/Pi
        lean_ctor_get_uint8(e, num_objs * 8 + 8)
    }

    // Read nondep uint8 stored right after the data u64 in Let (4 obj fields).
    #[inline(always)]
    unsafe fn expr_let_nondep(e: *mut LeanObject) -> u8 {
        lean_ctor_get_uint8(e, 4 * 8 + 8)
    }

    // Cache maps expression pointer → owned result reference.
    // On drop, all cached values are released.
    struct ReplaceFn {
        f: *mut LeanObject,
        cache: HashMap<usize, *mut LeanObject>,
    }

    impl Drop for ReplaceFn {
        fn drop(&mut self) {
            unsafe {
                for (_, v) in &self.cache {
                    lean_dec(*v);
                }
            }
        }
    }

    impl ReplaceFn {
        fn new(f: *mut LeanObject) -> Self {
            ReplaceFn {
                f,
                cache: HashMap::new(),
            }
        }

        // Returns an owned reference to the replacement of `e`.
        // `e` is borrowed (b_obj_arg); caller keeps ownership.
        unsafe fn apply(&mut self, e: *mut LeanObject) -> *mut LeanObject {
            // is_shared = refcount != 1 (handles both ST shared and MT objects)
            let shared = (*e).rc != 1;
            if shared {
                if let Some(&cached) = self.cache.get(&(e as usize)) {
                    lean_inc(cached);
                    return cached;
                }
            }

            // Call the closure: consume owned copies of f and e.
            lean_inc(e);
            lean_inc_ref(self.f);
            let r = lean_apply_1(self.f, e);

            if !lean_is_scalar(r) {
                // r = Some(inner): extract inner, release wrapper.
                let inner = lean_ctor_get(r, 0);
                lean_inc(inner); // take ownership of inner
                lean_dec(r); // release Some wrapper (also dec's inner, net +1-1=0 for inner)
                if shared {
                    lean_inc(inner);
                    self.cache.insert(e as usize, inner);
                }
                return inner;
            }
            // r = lean_box(0) = None (scalar): recurse into children.

            const EXPR_APP: u8 = 5;
            const EXPR_LAMBDA: u8 = 6;
            const EXPR_PI: u8 = 7;
            const EXPR_LET: u8 = 8;
            const EXPR_MDATA: u8 = 10;
            const EXPR_PROJ: u8 = 11;

            let tag = lean_obj_tag(e);
            let result: *mut LeanObject = match tag {
                EXPR_APP => {
                    let fn_e = lean_ctor_get(e, 0);
                    let arg_e = lean_ctor_get(e, 1);
                    let new_fn = self.apply(fn_e);
                    let new_arg = self.apply(arg_e);
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
                    let new_dom = self.apply(dom);
                    let new_body = self.apply(body);
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
                    let new_ty = self.apply(ty);
                    let new_val = self.apply(val);
                    let new_body = self.apply(body);
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
                    let new_child = self.apply(child);
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
                    let new_child = self.apply(child);
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
                // BVar=0, FVar=1, MVar=2, Sort=3, Const=4, Lit=9: leaf — return unchanged.
                _ => {
                    lean_inc(e);
                    e
                }
            };

            if shared {
                lean_inc(result);
                self.cache.insert(e as usize, result);
            }
            result
        }
    }

    // lean_replace_expr (f : Expr → Option Expr) (e : Expr) : Expr
    // Both f and e are borrowed (b_obj_arg); returns owned result.
    #[no_mangle]
    pub unsafe extern "C" fn lean_replace_expr(
        f: *mut LeanObject,
        e: *mut LeanObject,
    ) -> *mut LeanObject {
        ReplaceFn::new(f).apply(e)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_replace_expr_with_callback(
        e: *mut LeanObject,
        ctx: *mut c_void,
        callback: ReplaceCallback,
        use_cache: u8,
    ) -> *mut LeanObject {
        ReplaceCallbackFn::new(ctx, callback, use_cache != 0).apply(e, 0)
    }
}
