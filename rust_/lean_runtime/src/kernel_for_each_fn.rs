// Port of kernel/for_each_fn.cpp
// Copyright (c) 2013 Microsoft Corporation. All rights reserved.
// Released under Apache 2.0 license as described in the file LICENSE.
// Author: Leonardo de Moura
// Ported to Rust.
//
mod kernel_for_each_fn_impl {
    use super::*;
    use std::collections::HashSet;

    unsafe fn mk_option_some(value: *mut LeanObject) -> *mut LeanObject {
        lean_inc(value);
        let r = lean_alloc_ctor(1, 1, 0);
        lean_ctor_set(r, 0, value);
        r
    }

    unsafe fn should_visit_bool(p: *mut LeanObject, e: *mut LeanObject) -> bool {
        lean_inc(p);
        lean_inc(e);
        let r = lean_apply_1(p, e);
        lean_unbox(r) != 0
    }

    unsafe fn find_step(p: *mut LeanObject, e: *mut LeanObject) -> usize {
        lean_inc(p);
        lean_inc(e);
        let r = lean_apply_1(p, e);
        lean_unbox(r)
    }

    unsafe fn mark_visited(cache: &mut HashSet<usize>, e: *mut LeanObject) -> bool {
        !cache.insert(e as usize)
    }

    unsafe fn find_expr_go(
        p: *mut LeanObject,
        e: *mut LeanObject,
        cache: &mut HashSet<usize>,
        partial_apps: bool,
        ext: bool,
    ) -> Option<*mut LeanObject> {
        let tag = lean_obj_tag(e);
        match tag {
            0 | 3 | 4 => {
                if ext {
                    return (find_step(p, e) == 0).then_some(e);
                }
                return should_visit_bool(p, e).then_some(e);
            }
            _ => {}
        }

        if mark_visited(cache, e) {
            return None;
        }

        if ext {
            match find_step(p, e) {
                0 => return Some(e),
                1 => {}
                2 => return None,
                _ => lean_internal_panic(c"invalid FindStep value".as_ptr()),
            }
        } else if should_visit_bool(p, e) {
            return Some(e);
        }

        match tag {
            0 | 1 | 2 | 3 | 4 | 9 => None,
            5 => {
                let f = lean_ctor_get(e, 0);
                let a = lean_ctor_get(e, 1);
                if partial_apps {
                    find_expr_go(p, f, cache, partial_apps, ext)
                        .or_else(|| find_expr_go(p, a, cache, partial_apps, ext))
                } else {
                    find_expr_app_fn(p, f, cache, ext)
                        .or_else(|| find_expr_go(p, a, cache, partial_apps, ext))
                }
            }
            6 | 7 => {
                find_expr_go(p, lean_ctor_get(e, 1), cache, partial_apps, ext)
                    .or_else(|| find_expr_go(p, lean_ctor_get(e, 2), cache, partial_apps, ext))
            }
            8 => {
                find_expr_go(p, lean_ctor_get(e, 1), cache, partial_apps, ext)
                    .or_else(|| find_expr_go(p, lean_ctor_get(e, 2), cache, partial_apps, ext))
                    .or_else(|| find_expr_go(p, lean_ctor_get(e, 3), cache, partial_apps, ext))
            }
            10 => find_expr_go(p, lean_ctor_get(e, 1), cache, partial_apps, ext),
            11 => find_expr_go(p, lean_ctor_get(e, 2), cache, partial_apps, ext),
            _ => None,
        }
    }

    unsafe fn find_expr_app_fn(
        p: *mut LeanObject,
        e: *mut LeanObject,
        cache: &mut HashSet<usize>,
        ext: bool,
    ) -> Option<*mut LeanObject> {
        if lean_obj_tag(e) == 5 {
            find_expr_app_fn(p, lean_ctor_get(e, 0), cache, ext)
                .or_else(|| find_expr_go(p, lean_ctor_get(e, 1), cache, false, ext))
        } else {
            find_expr_go(p, e, cache, false, ext)
        }
    }

    /// `findExpr? (p : Expr → Bool) (e : Expr) : Option Expr`
    ///
    /// Returns the first subexpression (including partial applications) for
    /// which `p` returns true, or `none`.
    #[no_mangle]
    pub unsafe extern "C" fn lean_find_expr(
        p: *mut LeanObject,
        e: *mut LeanObject,
    ) -> *mut LeanObject {
        let mut cache = HashSet::new();
        if let Some(found) = find_expr_go(p, e, &mut cache, true, false) {
            mk_option_some(found)
        } else {
            lean_box(0)
        }
    }

    /// `findExtExpr? (p : Expr → FindStep) (e : Expr) : Option Expr`
    ///
    /// Like `lean_find_expr` but `p` returns a three-valued `FindStep`:
    ///   0 = found (stop, return this node)
    ///   1 = visit  (continue into children)
    ///   2 = done   (skip children)
    /// Does NOT visit partial applications.
    #[no_mangle]
    pub unsafe extern "C" fn lean_find_ext_expr(
        p: *mut LeanObject,
        e: *mut LeanObject,
    ) -> *mut LeanObject {
        let mut cache = HashSet::new();
        if let Some(found) = find_expr_go(p, e, &mut cache, false, true) {
            mk_option_some(found)
        } else {
            lean_box(0)
        }
    }

}
