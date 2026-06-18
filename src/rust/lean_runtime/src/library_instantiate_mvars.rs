/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Full Rust port of src/library/instantiate_mvars.cpp.
  lean_instantiate_level_mvars — level-MVar instantiation
  lean_instantiate_expr_mvars  — two-pass expr-MVar instantiation
*/

#[cfg(feature = "export-runtime-ffi")]
mod library_instantiate_mvars_impl {
    use super::*;
    use std::collections::{HashMap, HashSet};

    extern "C" {
        fn lean_get_lmvar_assignment(mctx: *mut LeanObject, mid: *mut LeanObject) -> *mut LeanObject;
        fn lean_assign_lmvar(mctx: *mut LeanObject, mid: *mut LeanObject, val: *mut LeanObject) -> *mut LeanObject;
        fn lean_level_eq(l1: *mut LeanObject, l2: *mut LeanObject) -> u8;
        fn lean_cxx_instantiate_expr_mvars(mctx: *mut LeanObject, e: *mut LeanObject) -> *mut LeanObject;

        fn lean_get_mvar_assignment(mctx: *mut LeanObject, mid: *mut LeanObject) -> *mut LeanObject;
        fn lean_get_delayed_mvar_assignment(mctx: *mut LeanObject, mid: *mut LeanObject) -> *mut LeanObject;
        fn lean_delayed_mvar_assignment_fvars(d: *mut LeanObject) -> *mut LeanObject;
        fn lean_delayed_mvar_assignment_mvar_id_pending(d: *mut LeanObject) -> *mut LeanObject;
        fn lean_assign_mvar(mctx: *mut LeanObject, mid: *mut LeanObject, val: *mut LeanObject) -> *mut LeanObject;

        fn lean_name_eq(n1: *mut LeanObject, n2: *mut LeanObject) -> u8;

        fn lean_level_mk_succ(l: *mut LeanObject) -> *mut LeanObject;
        fn lean_level_mk_max(l1: *mut LeanObject, l2: *mut LeanObject) -> *mut LeanObject;
        fn lean_level_mk_imax(l1: *mut LeanObject, l2: *mut LeanObject) -> *mut LeanObject;

        fn lean_expr_lift_loose_bvars(
            e: *mut LeanObject,
            s: *mut LeanObject,
            d: *mut LeanObject,
        ) -> *mut LeanObject;
        fn lean_expr_instantiate(e: *mut LeanObject, subst: *mut LeanObject) -> *mut LeanObject;
        fn lean_expr_mk_sort(l: *mut LeanObject) -> *mut LeanObject;
        fn lean_expr_mk_const(n: *mut LeanObject, us: *mut LeanObject) -> *mut LeanObject;
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
        fn lean_expr_mk_mdata(m: *mut LeanObject, e: *mut LeanObject) -> *mut LeanObject;
        fn lean_expr_mk_proj(
            struct_name: *mut LeanObject,
            idx: *mut LeanObject,
            structure: *mut LeanObject,
        ) -> *mut LeanObject;

        fn lean_array_push(array: *mut LeanObject, value: *mut LeanObject) -> *mut LeanObject;
    }

    // Level data bit 32 = hasMVar.
    const LEVEL_DATA_HAS_MVAR: u64 = 1 << 32;
    // Level.Data.depth is stored in bits [63:40] of the packed u64.
    const LEVEL_DATA_DEPTH_SHIFT: u64 = 40;

    const LEVEL_SUCC_TAG:  u8 = 1;
    const LEVEL_MAX_TAG:   u8 = 2;
    const LEVEL_IMAX_TAG:  u8 = 3;

    const EXPR_FVAR_TAG:   u8 = 1;
    const EXPR_MVAR_TAG:   u8 = 2;
    const EXPR_SORT_TAG:   u8 = 3;
    const EXPR_CONST_TAG:  u8 = 4;
    const EXPR_APP_TAG:    u8 = 5;
    const EXPR_LAMBDA_TAG: u8 = 6;
    const EXPR_PI_TAG:     u8 = 7;
    const EXPR_LET_TAG:    u8 = 8;
    const EXPR_MDATA_TAG:  u8 = 10;
    const EXPR_PROJ_TAG:   u8 = 11;

    unsafe fn is_zero_level(l: *mut LeanObject) -> bool {
        // Level.zero = lean_box(0) = the tagged scalar 0.
        lean_is_scalar(l) && lean_unbox(l) == 0
    }

    unsafe fn is_one_level(l: *mut LeanObject) -> bool {
        !lean_is_scalar(l) && lean_obj_tag(l) == LEVEL_SUCC_TAG
            && is_zero_level(lean_ctor_get(l, 0))
    }

    // A level is "explicit" iff it is a chain of succs ending at zero (no params/mvars/max/imax).
    unsafe fn is_explicit_level(l: *mut LeanObject) -> bool {
        if lean_is_scalar(l) {
            return true; // zero
        }
        if lean_obj_tag(l) == LEVEL_SUCC_TAG {
            is_explicit_level(lean_ctor_get(l, 0))
        } else {
            false
        }
    }

    // Read the packed Level.Data u64 from a level ctor object.
    unsafe fn get_level_data(l: *mut LeanObject) -> u64 {
        if lean_is_scalar(l) {
            return 0; // zero: depth = 0
        }
        let num_objs = (*l).other as usize;
        lean_ctor_get_uint64(l, num_objs * core::mem::size_of::<*mut LeanObject>())
    }

    unsafe fn get_level_depth(l: *mut LeanObject) -> u32 {
        (get_level_data(l) >> LEVEL_DATA_DEPTH_SHIFT) as u32
    }

    // True iff the level is syntactically guaranteed to be > 0 (e.g., succ of anything).
    unsafe fn is_not_zero_level(l: *mut LeanObject) -> bool {
        if lean_is_scalar(l) { return false; }
        match lean_obj_tag(l) {
            LEVEL_SUCC_TAG => true,
            LEVEL_MAX_TAG  => {
                is_not_zero_level(lean_ctor_get(l, 0))
                    || is_not_zero_level(lean_ctor_get(l, 1))
            }
            LEVEL_IMAX_TAG => is_not_zero_level(lean_ctor_get(l, 1)),
            _ => false, // param, mvar — unknown sign
        }
    }

    // Simplified mk_max that mirrors the C++ mk_max() simplifications.
    // Consumes ownership of both lhs and rhs; returns a new owned result.
    unsafe extern "C" fn mk_max_simplified(
        lhs: *mut LeanObject,
        rhs: *mut LeanObject,
    ) -> *mut LeanObject {
        // Both explicit (succ chains): return the deeper (= numerically larger) one.
        if is_explicit_level(lhs) && is_explicit_level(rhs) {
            if get_level_depth(lhs) >= get_level_depth(rhs) {
                lean_dec(rhs);
                return lhs;
            } else {
                lean_dec(lhs);
                return rhs;
            }
        }
        // Pointer equality: l1 == l2.
        if lhs == rhs {
            lean_dec(rhs);
            return lhs;
        }
        // max(0, u) = u.
        if is_zero_level(lhs) {
            lean_dec(lhs);
            return rhs;
        }
        // max(u, 0) = u.
        if is_zero_level(rhs) {
            lean_dec(rhs);
            return lhs;
        }
        // max(u, max(u, v)) = max(u, v)  (rhs already contains lhs as a child).
        if !lean_is_scalar(rhs) && lean_obj_tag(rhs) == LEVEL_MAX_TAG
            && (lean_ctor_get(rhs, 0) == lhs || lean_ctor_get(rhs, 1) == lhs)
        {
            lean_dec(lhs);
            return rhs;
        }
        // max(max(u, v), u) = max(u, v)  (lhs already contains rhs as a child).
        if !lean_is_scalar(lhs) && lean_obj_tag(lhs) == LEVEL_MAX_TAG
            && (lean_ctor_get(lhs, 0) == rhs || lean_ctor_get(lhs, 1) == rhs)
        {
            lean_dec(rhs);
            return lhs;
        }
        lean_level_mk_max(lhs, rhs)
    }

    // Simplified mk_imax that mirrors the C++ mk_imax() simplifications.
    // Consumes ownership of both lhs and rhs; returns a new owned result.
    unsafe extern "C" fn mk_imax_simplified(
        lhs: *mut LeanObject,
        rhs: *mut LeanObject,
    ) -> *mut LeanObject {
        // imax(u, v) where v is not zero = max(u, v).
        if is_not_zero_level(rhs) {
            return mk_max_simplified(lhs, rhs);
        }
        // imax(u, 0) = 0.
        if is_zero_level(rhs) {
            lean_dec(lhs);
            return rhs;
        }
        // imax(0, v) = v  and  imax(1, v) = v.
        if is_zero_level(lhs) || is_one_level(lhs) {
            lean_dec(lhs);
            return rhs;
        }
        // imax(u, u) = u.
        if lhs == rhs {
            lean_dec(rhs);
            return lhs;
        }
        lean_level_mk_imax(lhs, rhs)
    }

    unsafe fn lean_ctor_set(obj: *mut LeanObject, idx: usize, val: *mut LeanObject) {
        (obj.add(1) as *mut *mut LeanObject).add(idx).write(val);
    }

    unsafe fn lean_alloc_ctor(tag: u32, num_objs: usize, scalar_size: usize) -> *mut LeanObject {
        lean_runtime_alloc_ctor(tag as core::ffi::c_uint, num_objs as core::ffi::c_uint, scalar_size as core::ffi::c_uint)
    }

    // rc > 0 means single-threaded object (not atomic refcount).
    unsafe fn lean_is_st(o: *mut LeanObject) -> bool {
        (*o).rc > 0
    }

    unsafe fn has_level_mvar(l: *mut LeanObject) -> bool {
        if lean_is_scalar(l) {
            false
        } else {
            let num_objs = (*l).other as usize;
            let data = lean_ctor_get_uint64(l, num_objs * core::mem::size_of::<*mut LeanObject>());
            (data & LEVEL_DATA_HAS_MVAR) != 0
        }
    }

    unsafe fn is_shared_object(o: *mut LeanObject) -> bool {
        !lean_is_scalar(o) && lean_is_st(o) && (*o).rc > 1
    }

    unsafe fn mk_pair(a: *mut LeanObject, b: *mut LeanObject) -> *mut LeanObject {
        let r = lean_alloc_ctor(0, 2, 0);
        lean_ctor_set(r, 0, a);
        lean_ctor_set(r, 1, b);
        r
    }

    struct LevelMVarInstantiator {
        mctx: *mut LeanObject,
        cache: HashMap<*mut LeanObject, *mut LeanObject>,
        saved_assignments: Vec<*mut LeanObject>,
    }

    impl LevelMVarInstantiator {
        unsafe fn new(mctx: *mut LeanObject) -> Self {
            Self { mctx, cache: HashMap::new(), saved_assignments: Vec::new() }
        }

        unsafe fn cache_result(&mut self, original: *mut LeanObject, result: *mut LeanObject, shared: bool) -> *mut LeanObject {
            if shared {
                lean_inc(result);
                self.cache.insert(original, result);
            }
            result
        }

        unsafe fn rebuild_unary(
            &mut self,
            original: *mut LeanObject,
            child: *mut LeanObject,
            mk: unsafe extern "C" fn(*mut LeanObject) -> *mut LeanObject,
            shared: bool,
        ) -> *mut LeanObject {
            let old_child = lean_ctor_get(original, 0);
            if child == old_child {
                lean_inc(original);
                lean_dec(child);
                self.cache_result(original, original, shared)
            } else {
                self.cache_result(original, mk(child), shared)
            }
        }

        unsafe fn rebuild_binary(
            &mut self,
            original: *mut LeanObject,
            lhs: *mut LeanObject,
            rhs: *mut LeanObject,
            mk: unsafe extern "C" fn(*mut LeanObject, *mut LeanObject) -> *mut LeanObject,
            shared: bool,
        ) -> *mut LeanObject {
            let old_lhs = lean_ctor_get(original, 0);
            let old_rhs = lean_ctor_get(original, 1);
            if lhs == old_lhs && rhs == old_rhs {
                lean_inc(original);
                lean_dec(lhs);
                lean_dec(rhs);
                self.cache_result(original, original, shared)
            } else {
                self.cache_result(original, mk(lhs, rhs), shared)
            }
        }

        unsafe fn get_assignment(&mut self, mid: *mut LeanObject) -> Option<*mut LeanObject> {
            lean_inc_ref(self.mctx);
            lean_inc(mid);
            let opt = lean_get_lmvar_assignment(self.mctx, mid);
            if lean_is_scalar(opt) {
                None
            } else {
                let value = lean_ctor_get(opt, 0);
                lean_inc(value);
                lean_dec(opt);
                Some(value)
            }
        }

        unsafe fn assign(&mut self, mid: *mut LeanObject, value: *mut LeanObject) {
            lean_inc(mid);
            lean_inc(value);
            self.mctx = lean_assign_lmvar(self.mctx, mid, value);
        }

        unsafe fn visit(&mut self, l: *mut LeanObject) -> *mut LeanObject {
            if !has_level_mvar(l) {
                lean_inc(l);
                return l;
            }
            let shared = is_shared_object(l);
            if shared {
                if let Some(&cached) = self.cache.get(&l) {
                    lean_inc(cached);
                    return cached;
                }
            }
            // Level kind tags: 0=Zero(scalar) 1=Succ 2=Max 3=IMax 4=Param 5=MVar
            match lean_obj_tag(l) {
                1 => {
                    let child = self.visit(lean_ctor_get(l, 0));
                    self.rebuild_unary(l, child, lean_level_mk_succ, shared)
                }
                2 => {
                    let lhs = self.visit(lean_ctor_get(l, 0));
                    let rhs = self.visit(lean_ctor_get(l, 1));
                    self.rebuild_binary(l, lhs, rhs, mk_max_simplified, shared)
                }
                3 => {
                    let lhs = self.visit(lean_ctor_get(l, 0));
                    let rhs = self.visit(lean_ctor_get(l, 1));
                    self.rebuild_binary(l, lhs, rhs, mk_imax_simplified, shared)
                }
                5 => {
                    // LevelMVar: field 0 = LevelMVarId (a Name)
                    let mid = lean_ctor_get(l, 0);
                    let Some(assignment) = self.get_assignment(mid) else {
                        lean_inc(l);
                        return l;
                    };
                    if !has_level_mvar(assignment) {
                        assignment
                    } else {
                        let assignment_new = self.visit(assignment);
                        if lean_level_eq(assignment, assignment_new) == 0 {
                            lean_inc(assignment);
                            self.saved_assignments.push(assignment);
                            self.assign(mid, assignment_new);
                        }
                        lean_dec(assignment);
                        assignment_new
                    }
                }
                _ => {
                    lean_inc(l);
                    l
                }
            }
        }
    }

    impl Drop for LevelMVarInstantiator {
        fn drop(&mut self) {
            unsafe {
                for &v in self.cache.values() {
                    lean_dec(v);
                }
                for v in self.saved_assignments.drain(..) {
                    lean_dec(v);
                }
            }
        }
    }

    /// `instantiateLevelMVars (mctx : MetavarContext) (l : Level) : MetavarContext × Level`
    #[no_mangle]
    pub unsafe extern "C" fn lean_instantiate_level_mvars(
        mctx: *mut LeanObject,
        l: *mut LeanObject,
    ) -> *mut LeanObject {
        let mut inst = LevelMVarInstantiator::new(mctx);
        let level = inst.visit(l);
        let mctx = inst.mctx;
        inst.mctx = core::ptr::null_mut();
        lean_dec(l);
        mk_pair(mctx, level)
    }

    unsafe fn expr_data(e: *mut LeanObject) -> u64 {
        let num_objs = (*e).other as usize;
        lean_ctor_get_uint64(e, num_objs * core::mem::size_of::<*mut LeanObject>())
    }

    unsafe fn has_fvar(e: *mut LeanObject) -> bool {
        if lean_is_scalar(e) {
            false
        } else {
            (expr_data(e) >> 40) & 1 == 1
        }
    }

    unsafe fn has_expr_mvar(e: *mut LeanObject) -> bool {
        if lean_is_scalar(e) {
            false
        } else {
            (expr_data(e) >> 41) & 1 == 1
        }
    }

    unsafe fn has_level_mvar_expr(e: *mut LeanObject) -> bool {
        if lean_is_scalar(e) {
            false
        } else {
            (expr_data(e) >> 42) & 1 == 1
        }
    }

    unsafe fn expr_needs_instantiation(e: *mut LeanObject) -> bool {
        has_expr_mvar(e) || has_level_mvar_expr(e)
    }

    unsafe fn expr_binder_info_raw(e: *mut LeanObject) -> u8 {
        let num_objs = (*e).other as usize;
        lean_ctor_get_uint8(e, num_objs * 8 + 8)
    }

    unsafe fn expr_let_nondep(e: *mut LeanObject) -> u8 {
        lean_ctor_get_uint8(e, 4 * 8 + 8)
    }

    unsafe fn fvar_name(e: *mut LeanObject) -> *mut LeanObject {
        lean_ctor_get(e, 0)
    }

    unsafe fn mvar_name(e: *mut LeanObject) -> *mut LeanObject {
        lean_ctor_get(e, 0)
    }

    unsafe fn delayed_assignment_fvars_array(d: *mut LeanObject) -> *mut LeanObject {
        lean_delayed_mvar_assignment_fvars(d)
    }

    unsafe fn delayed_assignment_mvar_id_pending(d: *mut LeanObject) -> *mut LeanObject {
        lean_delayed_mvar_assignment_mvar_id_pending(d)
    }

    unsafe fn instantiate_with_slice(
        e: *mut LeanObject,
        n: usize,
        base: *const *mut LeanObject,
    ) -> *mut LeanObject {
        if n == 0 {
            lean_inc(e);
            return e;
        }
        let mut subst = lean_alloc_array(0, n);
        for i in 0..n {
            let v = *base.add(i);
            lean_inc(v);
            subst = lean_array_push(subst, v);
        }
        let r = lean_expr_instantiate(e, subst);
        lean_dec(subst);
        r
    }

    unsafe fn mk_rev_app(mut f: *mut LeanObject, num_args: usize, args: *const *mut LeanObject) -> *mut LeanObject {
        let mut i = num_args;
        while i > 0 {
            i -= 1;
            f = lean_expr_mk_app(f, *args.add(i));
        }
        f
    }

    unsafe fn apply_beta_rec(
        f: *mut LeanObject,
        i: usize,
        num_rev_args: usize,
        rev_args: *const *mut LeanObject,
        preserve_data: bool,
        zeta: bool,
    ) -> *mut LeanObject {
        match lean_obj_tag(f) {
            EXPR_LAMBDA_TAG => {
                if i + 1 < num_rev_args {
                    apply_beta_rec(lean_ctor_get(f, 2), i + 1, num_rev_args, rev_args, preserve_data, zeta)
                } else {
                    instantiate_with_slice(lean_ctor_get(f, 2), num_rev_args, rev_args)
                }
            }
            EXPR_LET_TAG => {
                if zeta && i < num_rev_args {
                    let value = lean_ctor_get(f, 2);
                    let body = instantiate_with_slice(lean_ctor_get(f, 3), 1, &value);
                    apply_beta_rec(body, i, num_rev_args, rev_args, preserve_data, zeta)
                } else {
                    let n = num_rev_args - i;
                    let r = instantiate_with_slice(f, i, rev_args.add(n));
                    mk_rev_app(r, n, rev_args)
                }
            }
            EXPR_MDATA_TAG => {
                if preserve_data {
                    let n = num_rev_args - i;
                    let r = instantiate_with_slice(f, i, rev_args.add(n));
                    mk_rev_app(r, n, rev_args)
                } else {
                    apply_beta_rec(lean_ctor_get(f, 1), i, num_rev_args, rev_args, preserve_data, zeta)
                }
            }
            _ => {
                let n = num_rev_args - i;
                let r = instantiate_with_slice(f, i, rev_args.add(n));
                mk_rev_app(r, n, rev_args)
            }
        }
    }

    unsafe fn apply_beta(
        f: *mut LeanObject,
        num_rev_args: usize,
        rev_args: *const *mut LeanObject,
        preserve_data: bool,
        zeta: bool,
    ) -> *mut LeanObject {
        if num_rev_args == 0 {
            lean_inc(f);
            return f;
        }
        apply_beta_rec(f, 0, num_rev_args, rev_args, preserve_data, zeta)
    }

    struct ScopeGenNode {
        gen: u32,
        tail: Option<usize>,
    }

    struct ScopeCacheEntry {
        result: *mut LeanObject,
        scope_level: u32,
        scope_gen: usize,
        result_scope: u32,
    }

    struct ExprScopeCache {
        cache: HashMap<(usize, u32), Vec<ScopeCacheEntry>>,
        gens: Vec<ScopeGenNode>,
        current_gen: usize,
        gen_counter: u32,
        scope: u32,
    }

    impl ExprScopeCache {
        fn new() -> Self {
            Self {
                cache: HashMap::new(),
                gens: vec![ScopeGenNode { gen: 0, tail: None }],
                current_gen: 0,
                gen_counter: 0,
                scope: 0,
            }
        }

        fn scope(&self) -> u32 {
            self.scope
        }

        fn push(&mut self) {
            self.scope += 1;
            self.gen_counter += 1;
            self.gens.push(ScopeGenNode { gen: self.gen_counter, tail: Some(self.current_gen) });
            self.current_gen = self.gens.len() - 1;
        }

        fn pop(&mut self) {
            self.scope -= 1;
            self.current_gen = self.gens[self.current_gen].tail.expect("cache scope underflow");
        }

        fn node_at_level(
            gens: &[ScopeGenNode],
            mut node: usize,
            current_scope: u32,
            level: u32,
        ) -> usize {
            let mut current_level = current_scope;
            while current_level > level {
                node = gens[node].tail.expect("cache scope rewind underflow");
                current_level -= 1;
            }
            node
        }

        fn rewind(
            stack: &mut Vec<ScopeCacheEntry>,
            current_scope: u32,
            current_gen: usize,
            gens: &[ScopeGenNode],
        ) {
            while let Some(top) = stack.last_mut() {
                if top.result_scope > current_scope {
                    stack.pop();
                    continue;
                }
                while top.scope_level > current_scope {
                    top.scope_gen = gens[top.scope_gen].tail.expect("cache rewind underflow");
                    top.scope_level -= 1;
                }
                let mut current = Self::node_at_level(gens, current_gen, current_scope, top.scope_level);
                if gens[top.scope_gen].gen == gens[current].gen {
                    return;
                }
                let mut entry = top.scope_gen;
                let mut level = top.scope_level;
                while level > top.result_scope {
                    entry = gens[entry].tail.expect("cache rewind tail underflow");
                    current = gens[current].tail.expect("cache rewind tail underflow");
                    level -= 1;
                    if gens[entry].gen == gens[current].gen {
                        top.scope_level = level;
                        top.scope_gen = entry;
                        return;
                    }
                }
                stack.pop();
            }
        }

        fn lookup(&mut self, key: (usize, u32), result_scope: &mut u32) -> Option<*mut LeanObject> {
            let stack = self.cache.get_mut(&key)?;
            Self::rewind(stack, self.scope, self.current_gen, &self.gens);
            let top = stack.last()?;
            if top.scope_level != self.scope {
                return None;
            }
            *result_scope = (*result_scope).max(top.result_scope);
            unsafe {
                lean_inc(top.result);
            }
            Some(top.result)
        }

        unsafe fn insert(
            &mut self,
            key: (usize, u32),
            result: *mut LeanObject,
            result_scope: u32,
        ) -> *mut LeanObject {
            let stack = self.cache.entry(key).or_default();
            Self::rewind(stack, self.scope, self.current_gen, &self.gens);
            let mut shared = result;
            let mut reused = false;
            if let Some(top) = stack.last() {
                if top.result_scope == result_scope {
                    shared = top.result;
                    reused = true;
                }
            }
            if reused && shared != result {
                lean_inc(shared);
            }
            while let Some(top) = stack.last() {
                if top.scope_level < result_scope {
                    break;
                }
                let old = stack.pop().unwrap();
                lean_dec(old.result);
            }
            if reused {
                if shared != result {
                    lean_dec(result);
                }
                lean_inc(shared);
            } else {
                lean_inc(shared);
            }
            stack.push(ScopeCacheEntry {
                result: shared,
                scope_level: self.scope,
                scope_gen: self.current_gen,
                result_scope,
            });
            shared
        }
    }

    struct ExprMVarInstantiator {
        level_inst: LevelMVarInstantiator,
        mctx: *mut LeanObject,
        cache: ExprScopeCache,
        fvar_subst: HashMap<*mut LeanObject, (u32, *mut LeanObject)>,
        already_normalized: HashSet<*mut LeanObject>,
        saved_assignments: Vec<*mut LeanObject>,
        resolvable_expr_cache: HashMap<usize, bool>,
        resolvable_pending_cache: HashMap<*mut LeanObject, u8>,
        depth: u32,
        result_scope: u32,
    }

    impl ExprMVarInstantiator {
        unsafe fn new(mctx: *mut LeanObject) -> Self {
            Self {
                level_inst: LevelMVarInstantiator::new(mctx),
                mctx,
                cache: ExprScopeCache::new(),
                fvar_subst: HashMap::new(),
                already_normalized: HashSet::new(),
                saved_assignments: Vec::new(),
                resolvable_expr_cache: HashMap::new(),
                resolvable_pending_cache: HashMap::new(),
                depth: 0,
                result_scope: 0,
            }
        }

        fn in_outer_mode(&self) -> bool {
            self.fvar_subst.is_empty()
        }

        unsafe fn lookup_fvar(&mut self, fid: *mut LeanObject) -> Option<*mut LeanObject> {
            if let Some(&(depth, value)) = self.fvar_subst.get(&fid) {
                let d = self.depth.checked_sub(depth)?;
                if d == 0 {
                    lean_inc(value);
                    Some(value)
                } else {
                    Some(lean_expr_lift_loose_bvars(value, lean_box(0), lean_box(d as usize)))
                }
            } else {
                None
            }
        }

        unsafe fn get_lmvar_assignment(&mut self, mid: *mut LeanObject) -> Option<*mut LeanObject> {
            lean_inc_ref(self.mctx);
            lean_inc(mid);
            let opt = lean_get_lmvar_assignment(self.mctx, mid);
            if lean_is_scalar(opt) {
                None
            } else {
                let value = lean_ctor_get(opt, 0);
                lean_inc(value);
                lean_dec(opt);
                Some(value)
            }
        }

        unsafe fn assign_lmvar(&mut self, mid: *mut LeanObject, value: *mut LeanObject) {
            lean_inc(mid);
            lean_inc(value);
            self.mctx = lean_assign_lmvar(self.mctx, mid, value);
            self.resolvable_expr_cache.clear();
            self.resolvable_pending_cache.clear();
        }

        unsafe fn get_mvar_assignment(&mut self, mid: *mut LeanObject) -> Option<*mut LeanObject> {
            lean_inc_ref(self.mctx);
            lean_inc(mid);
            let opt = lean_get_mvar_assignment(self.mctx, mid);
            if lean_is_scalar(opt) {
                None
            } else {
                let value = lean_ctor_get(opt, 0);
                lean_inc(value);
                lean_dec(opt);
                Some(value)
            }
        }

        unsafe fn assign_mvar(&mut self, mid: *mut LeanObject, value: *mut LeanObject) {
            lean_inc(mid);
            lean_inc(value);
            self.mctx = lean_assign_mvar(self.mctx, mid, value);
            self.resolvable_expr_cache.clear();
            self.resolvable_pending_cache.clear();
        }

        unsafe fn get_assignment(&mut self, mid: *mut LeanObject) -> Option<*mut LeanObject> {
            let opt = self.get_mvar_assignment(mid)?;
            if self.in_outer_mode() {
                if self.already_normalized.contains(&mid) {
                    return Some(opt);
                }
                self.already_normalized.insert(mid);
                let a_new = self.visit(opt);
                if a_new != opt {
                    lean_inc(opt);
                    self.saved_assignments.push(opt);
                    self.assign_mvar(mid, a_new);
                }
                lean_dec(opt);
                Some(a_new)
            } else {
                let a_new = self.visit(opt);
                lean_dec(opt);
                Some(a_new)
            }
        }

        unsafe fn is_resolvable_pending(&mut self, pending: *mut LeanObject) -> bool {
            if let Some(&state) = self.resolvable_pending_cache.get(&pending) {
                return state == 1;
            }
            self.resolvable_pending_cache.insert(pending, 0);
            let Some(a) = self.get_mvar_assignment(pending) else {
                self.resolvable_pending_cache.insert(pending, 2);
                return false;
            };
            let ok = self.is_resolvable_expr(a);
            self.resolvable_pending_cache.insert(pending, if ok { 1 } else { 2 });
            lean_dec(a);
            ok
        }

        unsafe fn is_resolvable_expr(&mut self, e: *mut LeanObject) -> bool {
            if !has_expr_mvar(e) {
                return true;
            }
            let key = e as usize;
            if let Some(&cached) = self.resolvable_expr_cache.get(&key) {
                return cached;
            }
            let r = self.is_resolvable_expr_core(e);
            self.resolvable_expr_cache.insert(key, r);
            r
        }

        unsafe fn is_resolvable_expr_core(&mut self, e: *mut LeanObject) -> bool {
            match lean_obj_tag(e) {
                EXPR_MVAR_TAG => false,
                EXPR_APP_TAG => {
                    let f = lean_ctor_get(e, 0);
                    if lean_obj_tag(f) == EXPR_MVAR_TAG {
                        let d = lean_get_delayed_mvar_assignment(self.mctx, lean_ctor_get(f, 0));
                        if lean_is_scalar(d) {
                            return false;
                        }
                        let fvars = delayed_assignment_fvars_array(d);
                        if lean_array_size(fvars) > self.app_num_args(e) {
                            lean_dec(d);
                            return false;
                        }
                        let pending = delayed_assignment_mvar_id_pending(d);
                        if !self.is_resolvable_pending(pending) {
                            lean_dec(d);
                            return false;
                        }
                        let mut curr = e;
                        while lean_obj_tag(curr) == EXPR_APP_TAG {
                            if !self.is_resolvable_expr(lean_ctor_get(curr, 1)) {
                                lean_dec(d);
                                return false;
                            }
                            curr = lean_ctor_get(curr, 0);
                        }
                        lean_dec(d);
                        true
                    } else {
                        self.is_resolvable_expr(lean_ctor_get(e, 0)) && self.is_resolvable_expr(lean_ctor_get(e, 1))
                    }
                }
                EXPR_LAMBDA_TAG | EXPR_PI_TAG => {
                    self.is_resolvable_expr(lean_ctor_get(e, 1)) && self.is_resolvable_expr(lean_ctor_get(e, 2))
                }
                EXPR_LET_TAG => {
                    self.is_resolvable_expr(lean_ctor_get(e, 1))
                        && self.is_resolvable_expr(lean_ctor_get(e, 2))
                        && self.is_resolvable_expr(lean_ctor_get(e, 3))
                }
                EXPR_MDATA_TAG => self.is_resolvable_expr(lean_ctor_get(e, 1)),
                EXPR_PROJ_TAG => self.is_resolvable_expr(lean_ctor_get(e, 2)),
                _ => true,
            }
        }

        unsafe fn app_num_args(&self, e: *mut LeanObject) -> usize {
            let mut curr = e;
            let mut n = 0;
            while lean_obj_tag(curr) == EXPR_APP_TAG {
                n += 1;
                curr = lean_ctor_get(curr, 0);
            }
            n
        }

        unsafe fn map_level_list(&mut self, list: *mut LeanObject) -> *mut LeanObject {
            let mut curr = list;
            let mut levels = Vec::new();
            let mut changed = false;
            while !lean_is_scalar(curr) {
                let head = lean_ctor_get(curr, 0);
                let new_head = self.visit_level(head);
                changed |= new_head != head;
                levels.push(new_head);
                curr = lean_ctor_get(curr, 1);
            }
            if !changed {
                for level in levels {
                    lean_dec(level);
                }
                lean_inc(list);
                return list;
            }
            let mut result = lean_box(0);
            for level in levels.into_iter().rev() {
                let cons = lean_alloc_ctor(1, 2, 0);
                lean_ctor_set(cons, 0, level);
                lean_ctor_set(cons, 1, result);
                result = cons;
            }
            result
        }

        unsafe fn visit_level(&mut self, l: *mut LeanObject) -> *mut LeanObject {
            if !has_level_mvar(l) {
                lean_inc(l);
                return l;
            }
            let shared = is_shared_object(l);
            if shared {
                if let Some(cached) = self.level_inst.cache.get(&l) {
                    lean_inc(*cached);
                    return *cached;
                }
            }
            match lean_obj_tag(l) {
                LEVEL_SUCC_TAG => {
                    let child = self.visit_level(lean_ctor_get(l, 0));
                    self.level_inst.rebuild_unary(l, child, lean_level_mk_succ, shared)
                }
                LEVEL_MAX_TAG => {
                    let lhs = self.visit_level(lean_ctor_get(l, 0));
                    let rhs = self.visit_level(lean_ctor_get(l, 1));
                    self.level_inst.rebuild_binary(l, lhs, rhs, mk_max_simplified, shared)
                }
                LEVEL_IMAX_TAG => {
                    let lhs = self.visit_level(lean_ctor_get(l, 0));
                    let rhs = self.visit_level(lean_ctor_get(l, 1));
                    self.level_inst.rebuild_binary(l, lhs, rhs, mk_imax_simplified, shared)
                }
                5 => {
                    let mid = lean_ctor_get(l, 0);
                    let Some(assignment) = self.get_lmvar_assignment(mid) else {
                        lean_inc(l);
                        return l;
                    };
                    if !has_level_mvar(assignment) {
                        assignment
                    } else {
                        let assignment_new = self.visit_level(assignment);
                        if lean_level_eq(assignment, assignment_new) == 0 {
                            lean_inc(assignment);
                            self.saved_assignments.push(assignment);
                            self.assign_lmvar(mid, assignment_new);
                        }
                        lean_dec(assignment);
                        assignment_new
                    }
                }
                _ => {
                    lean_inc(l);
                    l
                }
            }
        }

        unsafe fn visit_nonmvar_app(&mut self, e: *mut LeanObject) -> *mut LeanObject {
            let new_a = self.visit(lean_ctor_get(e, 1));
            let fn_e = lean_ctor_get(e, 0);
            let new_f = if lean_obj_tag(fn_e) == EXPR_APP_TAG {
                self.visit_nonmvar_app(fn_e)
            } else {
                self.visit(fn_e)
            };
            if new_f == fn_e && new_a == lean_ctor_get(e, 1) {
                lean_dec(new_f);
                lean_dec(new_a);
                lean_inc(e);
                e
            } else {
                lean_expr_mk_app(new_f, new_a)
            }
        }

        unsafe fn visit_app_beta(&mut self, f_new: *mut LeanObject, e: *mut LeanObject) -> *mut LeanObject {
            let mut args: Vec<*mut LeanObject> = Vec::new();
            let mut curr = e;
            while lean_obj_tag(curr) == EXPR_APP_TAG {
                args.push(self.visit(lean_ctor_get(curr, 1)));
                curr = lean_ctor_get(curr, 0);
            }
            apply_beta(f_new, args.len(), args.as_ptr(), false, true)
        }

        unsafe fn visit_app(&mut self, e: *mut LeanObject) -> *mut LeanObject {
            let f = lean_ctor_get(e, 0);
            if lean_obj_tag(f) != EXPR_MVAR_TAG {
                return self.visit_nonmvar_app(e);
            }
            let mid = mvar_name(f);
            if let Some(f_new) = self.get_assignment(mid) {
                return self.visit_app_beta(f_new, e);
            }
            let d = lean_get_delayed_mvar_assignment(self.mctx, mid);
            if !lean_is_scalar(d) {
                let fvars = delayed_assignment_fvars_array(d);
                if lean_array_size(fvars) > self.app_num_args(e) {
                    lean_dec(d);
                    return self.visit_nonmvar_app(e);
                }
                let pending = delayed_assignment_mvar_id_pending(d);
                if self.is_resolvable_pending(pending) {
                    let r = self.visit_delayed(fvars, pending, e);
                    lean_dec(d);
                    return r;
                } else {
                    debug_assert!(self.in_outer_mode());
                    let _ = self.get_assignment(pending);
                    lean_dec(d);
                    return self.visit_nonmvar_app(e);
                }
            }
            self.visit_nonmvar_app(e)
        }

        unsafe fn visit_fvar(&mut self, e: *mut LeanObject) -> *mut LeanObject {
            if let Some(r) = self.lookup_fvar(fvar_name(e)) {
                r
            } else {
                lean_inc(e);
                e
            }
        }

        unsafe fn visit_delayed(
            &mut self,
            fvars: *mut LeanObject,
            mid_pending: *mut LeanObject,
            e: *mut LeanObject,
        ) -> *mut LeanObject {
            let mut args: Vec<*mut LeanObject> = Vec::new();
            let mut curr = e;
            while lean_obj_tag(curr) == EXPR_APP_TAG {
                args.push(self.visit(lean_ctor_get(curr, 1)));
                curr = lean_ctor_get(curr, 0);
            }
            let fvar_count = lean_array_size(fvars);
            let Some(extra_count) = args.len().checked_sub(fvar_count) else {
                for arg in args {
                    lean_dec(arg);
                }
                return self.visit_nonmvar_app(e);
            };
            let args_ptr = args.as_ptr();

            self.cache.push();
            let saved_scope = self.result_scope;
            self.result_scope = 0;

            let mut saved_entries: Vec<(*mut LeanObject, Option<(u32, *mut LeanObject)>)> = Vec::with_capacity(fvar_count);
            for i in 0..fvar_count {
                let fid = fvar_name(lean_array_get(fvars, i));
                let arg = args[args.len() - 1 - i];
                lean_inc(arg);
                let old = self.fvar_subst.insert(fid, (self.depth, arg));
                saved_entries.push((fid, old));
            }

            let pending_val = self.get_mvar_assignment(mid_pending).expect("delayed assignment must be assigned");
            let val_new = self.visit(pending_val);
            lean_dec(pending_val);

            self.cache.pop();
            self.result_scope = self.result_scope.max(saved_scope);
            self.result_scope = self.result_scope.min(self.cache.scope());

            for (fid, old) in saved_entries {
                if let Some((_, current)) = self.fvar_subst.remove(&fid) {
                    lean_dec(current);
                }
                if let Some(v) = old {
                    self.fvar_subst.insert(fid, v);
                }
            }

            let result = apply_beta(val_new, extra_count, args_ptr, false, true);
            for arg in args {
                lean_dec(arg);
            }
            result
        }

        unsafe fn visit(&mut self, e: *mut LeanObject) -> *mut LeanObject {
            if (!has_fvar(e) || self.in_outer_mode()) && !expr_needs_instantiation(e) {
                lean_inc(e);
                return e;
            }

            let shared = is_shared_object(e);
            if shared {
                if let Some(cached) = self.cache.lookup((e as usize, self.depth), &mut self.result_scope) {
                    return cached;
                }
            }

            let saved_result_scope = self.result_scope;
            self.result_scope = 0;

            let r = match lean_obj_tag(e) {
                EXPR_FVAR_TAG => self.visit_fvar(e),
                EXPR_MVAR_TAG => {
                    let mid = mvar_name(e);
                    if let Some(r) = self.get_assignment(mid) {
                        r
                    } else {
                        lean_inc(e);
                        e
                    }
                }
                EXPR_SORT_TAG => {
                    let old = lean_ctor_get(e, 0);
                    let level = self.visit_level(old);
                    lean_expr_mk_sort(level)
                }
                EXPR_CONST_TAG => {
                    let old_levels = lean_ctor_get(e, 1);
                    let levels = self.map_level_list(old_levels);
                    let name = lean_ctor_get(e, 0);
                    lean_inc(name);
                    lean_expr_mk_const(name, levels)
                }
                EXPR_APP_TAG => self.visit_app(e),
                EXPR_LAMBDA_TAG | EXPR_PI_TAG => {
                    let dom = self.visit(lean_ctor_get(e, 1));
                    self.depth += 1;
                    let body = self.visit(lean_ctor_get(e, 2));
                    self.depth -= 1;
                    let name = lean_ctor_get(e, 0);
                    lean_inc(name);
                    let bi = expr_binder_info_raw(e);
                    if lean_obj_tag(e) == EXPR_LAMBDA_TAG {
                        lean_expr_mk_lambda(name, dom, body, bi)
                    } else {
                        lean_expr_mk_forall(name, dom, body, bi)
                    }
                }
                EXPR_LET_TAG => {
                    let typ = self.visit(lean_ctor_get(e, 1));
                    let value = self.visit(lean_ctor_get(e, 2));
                    self.depth += 1;
                    let body = self.visit(lean_ctor_get(e, 3));
                    self.depth -= 1;
                    let name = lean_ctor_get(e, 0);
                    lean_inc(name);
                    let nondep = expr_let_nondep(e);
                    lean_expr_mk_let(name, typ, value, body, nondep)
                }
                EXPR_MDATA_TAG => {
                    let md = lean_ctor_get(e, 0);
                    let expr = self.visit(lean_ctor_get(e, 1));
                    lean_inc(md);
                    lean_expr_mk_mdata(md, expr)
                }
                EXPR_PROJ_TAG => {
                    let sname = lean_ctor_get(e, 0);
                    let idx = lean_ctor_get(e, 1);
                    let expr = self.visit(lean_ctor_get(e, 2));
                    lean_inc(sname);
                    lean_inc(idx);
                    lean_expr_mk_proj(sname, idx, expr)
                }
                _ => {
                    lean_inc(e);
                    e
                }
            };

            if shared {
                let r = self.cache.insert((e as usize, self.depth), r, self.result_scope);
                self.result_scope = self.result_scope.max(saved_result_scope);
                r
            } else {
                self.result_scope = self.result_scope.max(saved_result_scope);
                r
            }
        }
    }

    impl Drop for ExprMVarInstantiator {
        fn drop(&mut self) {
            unsafe {
                for v in self.saved_assignments.drain(..) {
                    lean_dec(v);
                }
                for (_, (_, v)) in self.fvar_subst.drain() {
                    lean_dec(v);
                }
            }
        }
    }

    /// `instantiateExprMVars (mctx : MetavarContext) (e : Expr) : MetavarContext × Expr`
    #[no_mangle]
    pub unsafe extern "C" fn lean_instantiate_expr_mvars(
        mctx: *mut LeanObject,
        e: *mut LeanObject,
    ) -> *mut LeanObject {
        lean_cxx_instantiate_expr_mvars(mctx, e)
    }
}
