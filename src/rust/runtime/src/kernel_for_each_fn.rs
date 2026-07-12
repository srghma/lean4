/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Full Rust implementation of:
  - lean_for_each_expr_with_callback: C++ for_each traversal via callback (for_each_fn.cpp)
  - lean_find_expr / lean_find_ext_expr: predicate search (lean_find_expr)

Expression kind tags (enum class expr_kind { BVar, FVar, MVar, Sort, Const, App, Lambda, Pi, Let, Lit, MData, Proj }):
  BVar=0  FVar=1  MVar=2  Sort=3  Const=4  App=5  Lambda=6  Pi=7  Let=8  Lit=9  MData=10  Proj=11

Field layout (from expr.h):
  App:       [0]=fn, [1]=arg
  Lambda/Pi: [0]=name, [1]=domain, [2]=body
  Let:       [0]=name, [1]=type, [2]=value, [3]=body
  MData:     [0]=kvmap, [1]=expr
  Proj:      [0]=sname, [1]=idx, [2]=expr
*/

mod kernel_for_each_fn_impl {
    use crate::runtime_expr_shared::{
        LeanExprKind, expr_kind,
    };
    use crate::*;
    use core::ffi::c_void;
    use core::ffi::{CStr, c_char, c_int, c_long, c_uchar, c_uint, c_void};
    use std::collections::HashSet;

    // Callback: ctx, expr_ptr, binder_offset → true to recurse into children, false to stop.
    // For BVar/Sort/Const (pure leaves), the return value is ignored.
    type ForEachCallback = unsafe fn(*mut c_void, *mut LeanObject, u32) -> bool;

    struct ForEachState {
        ctx: *mut c_void,
        callback: ForEachCallback,
        // Cache of (ptr, offset) pairs already visited. Only used for shared (rc != 1) nodes.
        cache: HashSet<(usize, u32)>,
    }

    impl ForEachState {
        fn new(ctx: *mut c_void, callback: ForEachCallback) -> Self {
            Self {
                ctx,
                callback,
                cache: HashSet::new(),
            }
        }

        // Returns true if the node was already visited (should be skipped).
        // Unshared nodes (rc == 1) are never cached — they can only be reached once.
        unsafe fn visited(&mut self, e: *const LeanObject, offset: u32) -> bool {
            if (*e).rc == 1 {
                return false;
            }
            !self.cache.insert((e as usize, offset))
        }

        unsafe fn apply(&mut self, e: *mut LeanObject, offset: u32) {
            match expr_kind(e) {
                LeanExprKind::BVar | LeanExprKind::Sort | LeanExprKind::Const => {
                    (self.callback)(self.ctx, e, offset);
                    return;
                }
                _ => {}
            }

            if self.visited(e, offset) {
                return;
            }

            if !(self.callback)(self.ctx, e, offset) {
                return;
            }

            match expr_kind(e) {
                LeanExprKind::FVar | LeanExprKind::MVar | LeanExprKind::Lit => {}
                LeanExprKind::App => {
                    self.apply(lean_ctor_get(e, 0), offset);
                    self.apply(lean_ctor_get(e, 1), offset);
                }
                LeanExprKind::Lambda | LeanExprKind::Pi => {
                    self.apply(lean_ctor_get(e, 1), offset);
                    self.apply(lean_ctor_get(e, 2), offset + 1);
                }
                LeanExprKind::Let => {
                    self.apply(lean_ctor_get(e, 1), offset);
                    self.apply(lean_ctor_get(e, 2), offset);
                    self.apply(lean_ctor_get(e, 3), offset + 1);
                }
                LeanExprKind::MData => {
                    self.apply(lean_ctor_get(e, 1), offset);
                }
                LeanExprKind::Proj => {
                    self.apply(lean_ctor_get(e, 2), offset);
                }
                _ => {}
            }
        }
    }

    /// C-callable for_each traversal used by the for_each_fn.h C++ adapter.
    /// Mirrors for_each_offset_fn::apply from for_each_fn.cpp.
    #[no_mangle]
    pub unsafe fn lean_for_each_expr_with_callback(
        e: *mut LeanObject,
        ctx: *mut c_void,
        callback: ForEachCallback,
    ) {
        ForEachState::new(ctx, callback).apply(e, 0);
    }

    unsafe fn lean_ctor_set_local(obj: *mut LeanObject, idx: usize, val: *mut LeanObject) {
        (obj.add(1) as *mut *mut LeanObject).add(idx).write(val);
    }

    unsafe fn lean_alloc_ctor_local(
        tag: u32,
        num_objs: usize,
        scalar_size: usize,
    ) -> *mut LeanObject {
        lean_alloc_ctor(
            tag as core::ffi::c_uint,
            num_objs as core::ffi::c_uint,
            scalar_size as core::ffi::c_uint,
        )
    }

    // Wrap an optional found pointer into a Lean Option<Expr>.
    // None -> lean_box(0); Some(e) -> Some constructor with lean_inc'd e.
    unsafe fn make_option(found: Option<*mut LeanObject>) -> *mut LeanObject {
        match found {
            None => lean_box(0),
            Some(e) => {
                lean_inc(e);
                let r = lean_alloc_ctor_local(1, 1, 0);
                lean_ctor_set_local(r, 0, e);
                r
            }
        }
    }

    struct ExprFindState {
        found: Option<*mut LeanObject>,
        cache: HashSet<usize>,
    }

    impl ExprFindState {
        fn new() -> Self {
            ExprFindState {
                found: None,
                cache: HashSet::new(),
            }
        }

        // for_each_fn<true> (partial_apps = true): App nodes visit fn via apply_find.
        // Predicate p(e) -> bool: nonzero = found, zero = continue searching.
        unsafe fn apply_find(&mut self, p: *mut LeanObject, e: *mut LeanObject) {
            if self.found.is_some() {
                return;
            }
            match expr_kind(e) {
                LeanExprKind::BVar | LeanExprKind::Const | LeanExprKind::Sort => {
                    lean_inc(p);
                    lean_inc(e);
                    if lean_unbox(lean_apply_1(p, e)) != 0 {
                        self.found = Some(e);
                    }
                    return;
                }
                _ => {}
            }

            if !self.cache.insert(e as usize) {
                return;
            }

            lean_inc(p);
            lean_inc(e);
            if lean_unbox(lean_apply_1(p, e)) != 0 {
                self.found = Some(e);
                return;
            }

            match expr_kind(e) {
                LeanExprKind::MData => {
                    self.apply_find(p, lean_ctor_get(e, 1));
                }
                LeanExprKind::Proj => {
                    self.apply_find(p, lean_ctor_get(e, 2));
                }
                LeanExprKind::App => {
                    self.apply_find(p, lean_ctor_get(e, 0));
                    if self.found.is_none() {
                        self.apply_find(p, lean_ctor_get(e, 1));
                    }
                }
                LeanExprKind::Lambda | LeanExprKind::Pi => {
                    self.apply_find(p, lean_ctor_get(e, 1));
                    if self.found.is_none() {
                        self.apply_find(p, lean_ctor_get(e, 2));
                    }
                }
                LeanExprKind::Let => {
                    self.apply_find(p, lean_ctor_get(e, 1));
                    if self.found.is_none() {
                        self.apply_find(p, lean_ctor_get(e, 2));
                    }
                    if self.found.is_none() {
                        self.apply_find(p, lean_ctor_get(e, 3));
                    }
                }
                _ => {}
            }
        }

        // apply_fn for partial_apps=false: unpack the left App spine without calling predicate
        // on intermediate App nodes; only calls apply_ext on the head and each argument.
        unsafe fn apply_fn_ext(&mut self, p: *mut LeanObject, e: *mut LeanObject) {
            if self.found.is_some() {
                return;
            }
            if matches!(expr_kind(e), LeanExprKind::App) {
                self.apply_fn_ext(p, lean_ctor_get(e, 0)); // unpack fn recursively
                if self.found.is_none() {
                    self.apply_ext(p, lean_ctor_get(e, 1)); // visit arg
                }
            } else {
                self.apply_ext(p, e); // reached non-App head
            }
        }

        // for_each_fn<false> (partial_apps = false): App nodes use apply_fn_ext for fn.
        // Predicate p(e) -> FindStep: 0=found, 1=visit, 2=done(skip children).
        unsafe fn apply_ext(&mut self, p: *mut LeanObject, e: *mut LeanObject) {
            if self.found.is_some() {
                return;
            }
            match expr_kind(e) {
                LeanExprKind::BVar | LeanExprKind::Const | LeanExprKind::Sort => {
                    lean_inc(p);
                    lean_inc(e);
                    if lean_unbox(lean_apply_1(p, e)) == 0 {
                        self.found = Some(e);
                    }
                    return;
                }
                _ => {}
            }

            if !self.cache.insert(e as usize) {
                return;
            }

            lean_inc(p);
            lean_inc(e);
            match lean_unbox(lean_apply_1(p, e)) {
                0 => {
                    self.found = Some(e);
                    return;
                }
                1 => {}
                _ => return,
            }

            match expr_kind(e) {
                LeanExprKind::MData => {
                    self.apply_ext(p, lean_ctor_get(e, 1));
                }
                LeanExprKind::Proj => {
                    self.apply_ext(p, lean_ctor_get(e, 2));
                }
                LeanExprKind::App => {
                    self.apply_fn_ext(p, lean_ctor_get(e, 0));
                    if self.found.is_none() {
                        self.apply_ext(p, lean_ctor_get(e, 1));
                    }
                }
                LeanExprKind::Lambda | LeanExprKind::Pi => {
                    self.apply_ext(p, lean_ctor_get(e, 1));
                    if self.found.is_none() {
                        self.apply_ext(p, lean_ctor_get(e, 2));
                    }
                }
                LeanExprKind::Let => {
                    self.apply_ext(p, lean_ctor_get(e, 1));
                    if self.found.is_none() {
                        self.apply_ext(p, lean_ctor_get(e, 2));
                    }
                    if self.found.is_none() {
                        self.apply_ext(p, lean_ctor_get(e, 3));
                    }
                }
                _ => {}
            }
        }
    }

    // find? (p : Expr → Bool) (e : Expr) : Option Expr
    #[no_mangle]
    pub unsafe fn lean_find_expr(p: *mut LeanObject, e: *mut LeanObject) -> *mut LeanObject {
        let mut state = ExprFindState::new();
        state.apply_find(p, e);
        make_option(state.found)
    }

    // findExt? (p : Expr → FindStep) (e : Expr) : Option Expr
    #[no_mangle]
    pub unsafe fn lean_find_ext_expr(p: *mut LeanObject, e: *mut LeanObject) -> *mut LeanObject {
        let mut state = ExprFindState::new();
        state.apply_ext(p, e);
        make_option(state.found)
    }
}
