/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Rust implementation of src/library/instantiate_mvars.cpp entry points.
  lean_instantiate_level_mvars — level-MVar instantiation
  lean_instantiate_expr_mvars  — expr-MVar instantiation
*/

mod library_instantiate_mvars_impl {
    use crate::runtime_expr_shared::{
        BI_DEFAULT, BI_IMPLICIT, BI_INST_IMPLICIT, BI_STRICT_IMPLICIT, EXPR_APP as EXPR_APP_TAG,
        EXPR_BVAR as EXPR_BVAR_TAG, EXPR_CONST as EXPR_CONST_TAG, EXPR_FVAR as EXPR_FVAR_TAG,
        EXPR_LAMBDA as EXPR_LAMBDA_TAG, EXPR_LET as EXPR_LET_TAG, EXPR_MDATA as EXPR_MDATA_TAG,
        EXPR_MVAR as EXPR_MVAR_TAG, EXPR_PI as EXPR_PI_TAG, EXPR_PROJ as EXPR_PROJ_TAG,
        EXPR_SORT as EXPR_SORT_TAG, LEVEL_DATA_DEPTH_SHIFT, LEVEL_DATA_HAS_MVAR,
        LEVEL_IMAX as LEVEL_IMAX_TAG, LEVEL_MAX as LEVEL_MAX_TAG, LEVEL_PARAM as LEVEL_PARAM_TAG,
        LEVEL_SUCC as LEVEL_SUCC_TAG, LeanBinderInfo,
    };
    use crate::runtime_object_name_impl::lean_name_eq;
    use crate::*;
    use core::ffi::{CStr, c_char, c_int, c_long, c_uchar, c_uint, c_void};
    use std::collections::HashMap;

    unsafe extern "C" {
        fn lean_get_lmvar_assignment(
            mctx: *mut LeanObject,
            mid: *mut LeanObject,
        ) -> *mut LeanObject;
        fn lean_assign_lmvar(
            mctx: *mut LeanObject,
            mid: *mut LeanObject,
            val: *mut LeanObject,
        ) -> *mut LeanObject;
        fn lean_level_eq(l1: *mut LeanObject, l2: *mut LeanObject) -> bool;
        fn lean_get_mvar_assignment(mctx: *mut LeanObject, mid: *mut LeanObject)
        -> *mut LeanObject;
        fn lean_get_delayed_mvar_assignment(
            mctx: *mut LeanObject,
            mid: *mut LeanObject,
        ) -> *mut LeanObject;
        fn lean_delayed_mvar_assignment_fvars(d: *mut LeanObject) -> *mut LeanObject;
        fn lean_delayed_mvar_assignment_mvar_id_pending(d: *mut LeanObject) -> *mut LeanObject;
        fn lean_assign_mvar(
            mctx: *mut LeanObject,
            mid: *mut LeanObject,
            val: *mut LeanObject,
        ) -> *mut LeanObject;

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
        fn lean_expr_mk_lambda(
            n: *mut LeanObject,
            d: *mut LeanObject,
            b: *mut LeanObject,
            bi: LeanBinderInfo,
        ) -> *mut LeanObject;
        fn lean_expr_mk_forall(
            n: *mut LeanObject,
            d: *mut LeanObject,
            b: *mut LeanObject,
            bi: LeanBinderInfo,
        ) -> *mut LeanObject;
        fn lean_expr_mk_let(
            n: *mut LeanObject,
            t: *mut LeanObject,
            v: *mut LeanObject,
            b: *mut LeanObject,
            nondep: bool,
        ) -> *mut LeanObject;
        fn lean_expr_mk_mdata(m: *mut LeanObject, e: *mut LeanObject) -> *mut LeanObject;
        fn lean_expr_mk_proj(
            struct_name: *mut LeanObject,
            idx: *mut LeanObject,
            structure: *mut LeanObject,
        ) -> *mut LeanObject;
    }

    unsafe fn is_zero_level(l: *const LeanObject) -> bool {
        // Level.zero = lean_box(0) = the tagged scalar 0.
        lean_is_scalar(l) && lean_unbox(l) == 0
    }

    unsafe fn is_one_level(l: *const LeanObject) -> bool {
        !lean_is_scalar(l)
            && lean_obj_tag(l) == LEVEL_SUCC_TAG
            && is_zero_level(lean_ctor_get(l, 0))
    }

    // A level is "explicit" iff it is a chain of succs ending at zero (no params/mvars/max/imax).
    unsafe fn is_explicit_level(l: *const LeanObject) -> bool {
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
    unsafe fn get_level_data(l: *const LeanObject) -> u64 {
        if lean_is_scalar(l) {
            return 0; // zero: depth = 0
        }
        let num_objs = (*l).other as usize;
        lean_ctor_get_uint64(l, num_objs * core::mem::size_of::<*mut LeanObject>())
    }

    unsafe fn get_level_depth(l: *const LeanObject) -> u32 {
        (get_level_data(l) >> LEVEL_DATA_DEPTH_SHIFT) as u32
    }

    // True iff the level is syntactically guaranteed to be > 0 (e.g., succ of anything).
    unsafe fn is_not_zero_level(l: *const LeanObject) -> bool {
        if lean_is_scalar(l) {
            return false;
        }
        match lean_obj_tag(l) {
            LEVEL_SUCC_TAG => true,
            LEVEL_MAX_TAG => {
                is_not_zero_level(lean_ctor_get(l, 0)) || is_not_zero_level(lean_ctor_get(l, 1))
            }
            LEVEL_IMAX_TAG => is_not_zero_level(lean_ctor_get(l, 1)),
            _ => false, // param, mvar — unknown sign
        }
    }

    // Simplified mk_max that mirrors the C++ mk_max() simplifications.
    // Consumes ownership of both lhs and rhs; returns a new owned result.
    unsafe fn mk_max_simplified(lhs: *mut LeanObject, rhs: *mut LeanObject) -> *mut LeanObject {
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
        if !lean_is_scalar(rhs)
            && lean_obj_tag(rhs) == LEVEL_MAX_TAG
            && (lean_ctor_get(rhs, 0) == lhs || lean_ctor_get(rhs, 1) == lhs)
        {
            lean_dec(lhs);
            return rhs;
        }
        // max(max(u, v), u) = max(u, v)  (lhs already contains rhs as a child).
        if !lean_is_scalar(lhs)
            && lean_obj_tag(lhs) == LEVEL_MAX_TAG
            && (lean_ctor_get(lhs, 0) == rhs || lean_ctor_get(lhs, 1) == rhs)
        {
            lean_dec(rhs);
            return lhs;
        }
        lean_level_mk_max(lhs, rhs)
    }

    // Simplified mk_imax that mirrors the C++ mk_imax() simplifications.
    // Consumes ownership of both lhs and rhs; returns a new owned result.
    unsafe fn mk_imax_simplified(lhs: *mut LeanObject, rhs: *mut LeanObject) -> *mut LeanObject {
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

    unsafe fn has_level_mvar(l: *const LeanObject) -> bool {
        if lean_is_scalar(l) {
            false
        } else {
            let num_objs = (*l).other as usize;
            let data = lean_ctor_get_uint64(l, num_objs * core::mem::size_of::<*mut LeanObject>());
            (data & LEVEL_DATA_HAS_MVAR) != 0
        }
    }

    unsafe fn is_shared_object(o: *const LeanObject) -> bool {
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
            Self {
                mctx,
                cache: HashMap::new(),
                saved_assignments: Vec::new(),
            }
        }

        unsafe fn cache_result(
            &mut self,
            original: *mut LeanObject,
            result: *mut LeanObject,
            shared: bool,
        ) -> *mut LeanObject {
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
            mk: unsafe fn(*mut LeanObject) -> *mut LeanObject,
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
            mk: unsafe fn(*mut LeanObject, *mut LeanObject) -> *mut LeanObject,
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

        unsafe fn get_assignment(&mut self, mid: *const LeanObject) -> Option<*mut LeanObject> {
            lean_inc_ref(self.mctx);
            lean_inc(mid);
            let opt = lean_get_lmvar_assignment(self.mctx, mid as *mut LeanObject);
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
                        if !lean_level_eq(assignment, assignment_new) {
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
    pub unsafe fn lean_instantiate_level_mvars(
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

    unsafe fn expr_data(e: *const LeanObject) -> u64 {
        let num_objs = (*e).other as usize;
        lean_ctor_get_uint64(e, num_objs * core::mem::size_of::<*mut LeanObject>())
    }

    unsafe fn has_fvar(e: *const LeanObject) -> bool {
        if lean_is_scalar(e) {
            false
        } else {
            (expr_data(e) >> 40) & 1 == 1
        }
    }

    unsafe fn has_expr_mvar(e: *const LeanObject) -> bool {
        if lean_is_scalar(e) {
            false
        } else {
            (expr_data(e) >> 41) & 1 == 1
        }
    }

    unsafe fn has_level_mvar_expr(e: *const LeanObject) -> bool {
        if lean_is_scalar(e) {
            false
        } else {
            (expr_data(e) >> 42) & 1 == 1
        }
    }

    unsafe fn expr_needs_instantiation(e: *const LeanObject) -> bool {
        has_expr_mvar(e) || has_level_mvar_expr(e)
    }

    unsafe fn expr_binder_info_raw(e: *const LeanObject) -> LeanBinderInfo {
        let num_objs = (*e).other as usize;
        match lean_ctor_get_uint8(e, num_objs * 8 + 8) {
            0 => LeanBinderInfo::Default,
            1 => LeanBinderInfo::Implicit,
            2 => LeanBinderInfo::StrictImplicit,
            3 => LeanBinderInfo::InstImplicit,
            _ => LeanBinderInfo::Default,
        }
    }

    unsafe fn expr_let_nondep(e: *const LeanObject) -> bool {
        lean_ctor_get_uint8(e, 4 * 8 + 8) != 0
    }

    unsafe fn fvar_name(e: *mut LeanObject) -> *mut LeanObject {
        lean_ctor_get(e, 0)
    }

    unsafe fn mvar_name(e: *mut LeanObject) -> *mut LeanObject {
        lean_ctor_get(e, 0)
    }

    unsafe fn get_delayed_assignment(
        mctx: *mut LeanObject,
        mid: *mut LeanObject,
    ) -> *mut LeanObject {
        lean_inc_ref(mctx);
        lean_inc(mid);
        lean_get_delayed_mvar_assignment(mctx, mid)
    }

    unsafe fn app_head(mut e: *mut LeanObject) -> *mut LeanObject {
        while !lean_is_scalar(e) && lean_obj_tag(e) == EXPR_APP_TAG {
            e = lean_ctor_get(e, 0);
        }
        e
    }

    unsafe fn app_num_args(mut e: *const LeanObject) -> usize {
        let mut n = 0;
        while !lean_is_scalar(e) && lean_obj_tag(e) == EXPR_APP_TAG {
            n += 1;
            e = lean_ctor_get(e, 0);
        }
        n
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

    unsafe fn mk_rev_app(
        mut f: *mut LeanObject,
        num_args: usize,
        args: *const *mut LeanObject,
    ) -> *mut LeanObject {
        let mut i = num_args;
        while i > 0 {
            i -= 1;
            let arg = *args.add(i);
            lean_inc(arg);
            f = lean_expr_mk_app(f, arg);
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
                    apply_beta_rec(
                        lean_ctor_get(f, 2),
                        i + 1,
                        num_rev_args,
                        rev_args,
                        preserve_data,
                        zeta,
                    )
                } else {
                    instantiate_with_slice(lean_ctor_get(f, 2), num_rev_args, rev_args)
                }
            }
            EXPR_LET_TAG => {
                if zeta && i < num_rev_args {
                    let value = lean_ctor_get(f, 2);
                    let body = instantiate_with_slice(lean_ctor_get(f, 3), 1, &value);
                    let result =
                        apply_beta_rec(body, i, num_rev_args, rev_args, preserve_data, zeta);
                    lean_dec(body);
                    result
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
                    apply_beta_rec(
                        lean_ctor_get(f, 1),
                        i,
                        num_rev_args,
                        rev_args,
                        preserve_data,
                        zeta,
                    )
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

    unsafe fn map_level_list(
        level_inst: &mut LevelMVarInstantiator,
        list: *mut LeanObject,
    ) -> *mut LeanObject {
        let mut curr = list;
        let mut levels = Vec::new();
        let mut changed = false;
        while !lean_is_scalar(curr) {
            let head = lean_ctor_get(curr, 0);
            let new_head = level_inst.visit(head);
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

    unsafe fn name_vec_contains(names: &[*mut LeanObject], name: *const LeanObject) -> bool {
        names.iter().any(|&entry| lean_name_eq(entry, name))
    }

    unsafe fn name_vec_insert(names: &mut Vec<*mut LeanObject>, name: *mut LeanObject) {
        if !name_vec_contains(names, name) {
            lean_inc(name);
            names.push(name);
        }
    }

    unsafe fn name_state_find(
        states: &[(*mut LeanObject, u8)],
        name: *const LeanObject,
    ) -> Option<usize> {
        states
            .iter()
            .position(|(entry, _)| lean_name_eq(*entry, name))
    }

    unsafe fn name_state_get(
        states: &[(*mut LeanObject, u8)],
        name: *mut LeanObject,
    ) -> Option<u8> {
        name_state_find(states, name).map(|idx| states[idx].1)
    }

    unsafe fn name_state_set(
        states: &mut Vec<(*mut LeanObject, u8)>,
        name: *mut LeanObject,
        state: u8,
    ) {
        if let Some(idx) = name_state_find(states, name) {
            states[idx].1 = state;
        } else {
            lean_inc(name);
            states.push((name, state));
        }
    }

    unsafe fn name_state_clear(states: &mut Vec<(*mut LeanObject, u8)>) {
        for (name, _) in states.drain(..) {
            lean_dec(name);
        }
    }

    struct InstantiateDirect {
        level_inst: LevelMVarInstantiator,
        cache: HashMap<*mut LeanObject, *mut LeanObject>,
        saved_assignments: Vec<*mut LeanObject>,
        already_normalized: Vec<*mut LeanObject>,
        has_updateable_delayed: bool,
    }

    impl InstantiateDirect {
        unsafe fn new(mctx: *mut LeanObject) -> Self {
            Self {
                level_inst: LevelMVarInstantiator::new(mctx),
                cache: HashMap::new(),
                saved_assignments: Vec::new(),
                already_normalized: Vec::new(),
                has_updateable_delayed: false,
            }
        }

        unsafe fn cache_result(
            &mut self,
            original: *mut LeanObject,
            result: *mut LeanObject,
            shared: bool,
        ) -> *mut LeanObject {
            if shared {
                lean_inc(result);
                self.cache.insert(original, result);
            }
            result
        }

        unsafe fn get_assignment(&mut self, mid: *const LeanObject) -> Option<*mut LeanObject> {
            let mctx = self.level_inst.mctx;
            lean_inc_ref(mctx);
            lean_inc(mid);
            let opt = lean_get_mvar_assignment(mctx, mid as *mut LeanObject);
            if lean_is_scalar(opt) {
                None
            } else {
                let value = lean_ctor_get(opt, 0);
                lean_inc(value);
                lean_dec(opt);
                if !expr_needs_instantiation(value)
                    || name_vec_contains(&self.already_normalized, mid)
                {
                    return Some(value);
                }
                name_vec_insert(&mut self.already_normalized, mid);
                let value_new = self.visit(value);
                if value_new != value {
                    lean_inc(value);
                    self.saved_assignments.push(value);
                    self.assign(mid, value_new);
                }
                lean_dec(value);
                Some(value_new)
            }
        }

        unsafe fn assign(&mut self, mid: *mut LeanObject, value: *mut LeanObject) {
            lean_inc(mid);
            lean_inc(value);
            let mctx = self.level_inst.mctx;
            self.level_inst.mctx = lean_assign_mvar(mctx, mid, value);
        }

        unsafe fn reuse_or(
            &mut self,
            original: *mut LeanObject,
            changed: bool,
            new_fields: &[*mut LeanObject],
            mk: impl FnOnce() -> *mut LeanObject,
            shared: bool,
        ) -> *mut LeanObject {
            if changed {
                self.cache_result(original, mk(), shared)
            } else {
                for &field in new_fields {
                    lean_dec(field);
                }
                lean_inc(original);
                self.cache_result(original, original, shared)
            }
        }

        unsafe fn visit_nonmvar_app(&mut self, e: *mut LeanObject) -> *mut LeanObject {
            let old_a = lean_ctor_get(e, 1);
            let new_a = self.visit(old_a);
            let old_f = lean_ctor_get(e, 0);
            let new_f = if lean_obj_tag(old_f) == EXPR_APP_TAG {
                self.visit_nonmvar_app(old_f)
            } else {
                self.visit(old_f)
            };
            if new_f == old_f && new_a == old_a {
                lean_dec(new_f);
                lean_dec(new_a);
                lean_inc(e);
                e
            } else {
                lean_expr_mk_app(new_f, new_a)
            }
        }

        unsafe fn visit_app_beta(
            &mut self,
            f_new: *mut LeanObject,
            e: *mut LeanObject,
        ) -> *mut LeanObject {
            let mut args = Vec::new();
            let mut curr = e;
            while lean_obj_tag(curr) == EXPR_APP_TAG {
                args.push(self.visit(lean_ctor_get(curr, 1)));
                curr = lean_ctor_get(curr, 0);
            }
            let result = apply_beta(f_new, args.len(), args.as_ptr(), false, true);
            lean_dec(f_new);
            for &arg in &args {
                lean_dec(arg);
            }
            result
        }

        unsafe fn visit_app(&mut self, e: *mut LeanObject) -> *mut LeanObject {
            let f = app_head(e);
            if lean_obj_tag(f) != EXPR_MVAR_TAG {
                return self.visit_nonmvar_app(e);
            }
            let mid = mvar_name(f);
            if let Some(f_new) = self.get_assignment(mid) {
                return self.visit_app_beta(f_new, e);
            }
            let d_opt = get_delayed_assignment(self.level_inst.mctx, mid);
            if !lean_is_scalar(d_opt) {
                let d = lean_ctor_get(d_opt, 0);
                lean_inc(d);
                let pending = lean_delayed_mvar_assignment_mvar_id_pending(d);
                if self.get_assignment(pending).is_some() {
                    self.has_updateable_delayed = true;
                }
                lean_dec(pending);
                lean_dec(d_opt);
            }
            self.visit_nonmvar_app(e)
        }

        unsafe fn visit_mvar(&mut self, e: *mut LeanObject) -> *mut LeanObject {
            let mid = mvar_name(e);
            if let Some(r) = self.get_assignment(mid) {
                return r;
            }
            let d_opt = get_delayed_assignment(self.level_inst.mctx, mid);
            if !lean_is_scalar(d_opt) {
                let d = lean_ctor_get(d_opt, 0);
                lean_inc(d);
                let pending = lean_delayed_mvar_assignment_mvar_id_pending(d);
                if self.get_assignment(pending).is_some() {
                    self.has_updateable_delayed = true;
                }
                lean_dec(pending);
                lean_dec(d_opt);
            }
            lean_inc(e);
            e
        }

        unsafe fn visit(&mut self, e: *mut LeanObject) -> *mut LeanObject {
            if !expr_needs_instantiation(e) {
                lean_inc(e);
                return e;
            }
            let shared = is_shared_object(e);
            if shared {
                if let Some(&cached) = self.cache.get(&e) {
                    lean_inc(cached);
                    return cached;
                }
            }
            match lean_obj_tag(e) {
                EXPR_SORT_TAG => {
                    let old = lean_ctor_get(e, 0);
                    let level = self.level_inst.visit(old);
                    self.reuse_or(
                        e,
                        level != old,
                        &[level],
                        || lean_expr_mk_sort(level),
                        shared,
                    )
                }
                EXPR_CONST_TAG => {
                    let old_levels = lean_ctor_get(e, 1);
                    let levels = map_level_list(&mut self.level_inst, old_levels);
                    self.reuse_or(
                        e,
                        levels != old_levels,
                        &[levels],
                        || {
                            let name = lean_ctor_get(e, 0);
                            lean_inc(name);
                            lean_expr_mk_const(name, levels)
                        },
                        shared,
                    )
                }
                EXPR_MVAR_TAG => self.visit_mvar(e),
                EXPR_MDATA_TAG => {
                    let old = lean_ctor_get(e, 1);
                    let expr = self.visit(old);
                    self.reuse_or(
                        e,
                        expr != old,
                        &[expr],
                        || {
                            let md = lean_ctor_get(e, 0);
                            lean_inc(md);
                            lean_expr_mk_mdata(md, expr)
                        },
                        shared,
                    )
                }
                EXPR_PROJ_TAG => {
                    let old = lean_ctor_get(e, 2);
                    let expr = self.visit(old);
                    self.reuse_or(
                        e,
                        expr != old,
                        &[expr],
                        || {
                            let sname = lean_ctor_get(e, 0);
                            let idx = lean_ctor_get(e, 1);
                            lean_inc(sname);
                            lean_inc(idx);
                            lean_expr_mk_proj(sname, idx, expr)
                        },
                        shared,
                    )
                }
                EXPR_APP_TAG => {
                    let r = self.visit_app(e);
                    self.cache_result(e, r, shared)
                }
                EXPR_LAMBDA_TAG | EXPR_PI_TAG => {
                    let old_dom = lean_ctor_get(e, 1);
                    let old_body = lean_ctor_get(e, 2);
                    let dom = self.visit(old_dom);
                    let body = self.visit(old_body);
                    self.reuse_or(
                        e,
                        dom != old_dom || body != old_body,
                        &[dom, body],
                        || {
                            let name = lean_ctor_get(e, 0);
                            lean_inc(name);
                            let bi = expr_binder_info_raw(e);
                            if lean_obj_tag(e) == EXPR_LAMBDA_TAG {
                                lean_expr_mk_lambda(name, dom, body, bi)
                            } else {
                                lean_expr_mk_forall(name, dom, body, bi)
                            }
                        },
                        shared,
                    )
                }
                EXPR_LET_TAG => {
                    let old_typ = lean_ctor_get(e, 1);
                    let old_val = lean_ctor_get(e, 2);
                    let old_body = lean_ctor_get(e, 3);
                    let typ = self.visit(old_typ);
                    let val = self.visit(old_val);
                    let body = self.visit(old_body);
                    self.reuse_or(
                        e,
                        typ != old_typ || val != old_val || body != old_body,
                        &[typ, val, body],
                        || {
                            let name = lean_ctor_get(e, 0);
                            lean_inc(name);
                            lean_expr_mk_let(name, typ, val, body, expr_let_nondep(e))
                        },
                        shared,
                    )
                }
                _ => {
                    lean_inc(e);
                    e
                }
            }
        }
    }

    impl Drop for InstantiateDirect {
        fn drop(&mut self) {
            unsafe {
                for &v in self.cache.values() {
                    lean_dec(v);
                }
                for v in self.saved_assignments.drain(..) {
                    lean_dec(v);
                }
                for name in self.already_normalized.drain(..) {
                    lean_dec(name);
                }
            }
        }
    }

    struct FvarSubstEntry {
        depth: u32,
        scope: u32,
        value: *mut LeanObject,
    }

    struct ScopeGenNode {
        r#gen: u64,
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
        gen_counter: u64,
        scope: u32,
    }

    impl ExprScopeCache {
        fn new() -> Self {
            Self {
                cache: HashMap::new(),
                gens: vec![ScopeGenNode {
                    r#gen: 0,
                    tail: None,
                }],
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
            self.gens.push(ScopeGenNode {
                r#gen: self.gen_counter,
                tail: Some(self.current_gen),
            });
            self.current_gen = self.gens.len() - 1;
        }

        fn pop(&mut self) {
            self.scope -= 1;
            self.current_gen = self.gens[self.current_gen]
                .tail
                .expect("scope cache underflow");
        }

        fn node_at_level(
            gens: &[ScopeGenNode],
            mut node: usize,
            current_scope: u32,
            level: u32,
        ) -> usize {
            let mut current_level = current_scope;
            while current_level > level {
                node = gens[node].tail.expect("scope cache rewind underflow");
                current_level -= 1;
            }
            node
        }

        fn rewind(
            gens: &[ScopeGenNode],
            current_gen: usize,
            scope: u32,
            stack: &mut Vec<ScopeCacheEntry>,
        ) {
            while let Some(top) = stack.last_mut() {
                if top.result_scope > scope {
                    let old = stack.pop().unwrap();
                    unsafe {
                        lean_dec(old.result);
                    }
                    continue;
                }

                while top.scope_level > scope {
                    top.scope_gen = gens[top.scope_gen]
                        .tail
                        .expect("scope cache rewind underflow");
                    top.scope_level -= 1;
                }

                let mut current = Self::node_at_level(gens, current_gen, scope, top.scope_level);
                if gens[top.scope_gen].r#gen == gens[current].r#gen {
                    return;
                }

                let mut entry = top.scope_gen;
                let mut level = top.scope_level;
                while level > top.result_scope {
                    entry = gens[entry].tail.expect("scope cache rewind tail underflow");
                    current = gens[current]
                        .tail
                        .expect("scope cache rewind tail underflow");
                    level -= 1;
                    if gens[entry].r#gen == gens[current].r#gen {
                        top.scope_level = level;
                        top.scope_gen = entry;
                        return;
                    }
                }

                let old = stack.pop().unwrap();
                unsafe {
                    lean_dec(old.result);
                }
            }
        }

        fn lookup(&mut self, key: (usize, u32), result_scope: &mut u32) -> Option<*mut LeanObject> {
            let stack = self.cache.get_mut(&key)?;
            Self::rewind(&self.gens, self.current_gen, self.scope, stack);
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
            Self::rewind(&self.gens, self.current_gen, self.scope, stack);
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

    impl Drop for ExprScopeCache {
        fn drop(&mut self) {
            unsafe {
                for stack in self.cache.values_mut() {
                    for entry in stack.drain(..) {
                        lean_dec(entry.result);
                    }
                }
            }
        }
    }

    struct InstantiateDelayed {
        mctx: *mut LeanObject,
        fvar_subst: Vec<(*mut LeanObject, FvarSubstEntry)>,
        depth: u32,
        cache: ExprScopeCache,
        result_scope: u32,
        already_normalized: Vec<*mut LeanObject>,
        saved_assignments: Vec<*mut LeanObject>,
        resolvable_expr_cache: HashMap<usize, bool>,
        resolvable_pending_cache: Vec<(*mut LeanObject, u8)>,
    }

    impl InstantiateDelayed {
        unsafe fn new(mctx: *mut LeanObject) -> Self {
            Self {
                mctx,
                fvar_subst: Vec::new(),
                depth: 0,
                cache: ExprScopeCache::new(),
                result_scope: 0,
                already_normalized: Vec::new(),
                saved_assignments: Vec::new(),
                resolvable_expr_cache: HashMap::new(),
                resolvable_pending_cache: Vec::new(),
            }
        }

        fn in_outer_mode(&self) -> bool {
            self.fvar_subst.is_empty()
        }

        unsafe fn find_fvar_subst(&self, fid: *const LeanObject) -> Option<usize> {
            self.fvar_subst
                .iter()
                .position(|(key, _)| lean_name_eq(*key, fid))
        }

        unsafe fn get_mvar_assignment_raw(
            &mut self,
            mid: *mut LeanObject,
        ) -> Option<*mut LeanObject> {
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

        unsafe fn assign(&mut self, mid: *mut LeanObject, value: *mut LeanObject) {
            lean_inc(mid);
            lean_inc(value);
            self.mctx = lean_assign_mvar(self.mctx, mid, value);
            self.resolvable_expr_cache.clear();
            name_state_clear(&mut self.resolvable_pending_cache);
        }

        unsafe fn get_assignment(&mut self, mid: *const LeanObject) -> Option<*mut LeanObject> {
            let value = self.get_mvar_assignment_raw(mid as *mut LeanObject)?;
            if self.in_outer_mode() {
                if name_vec_contains(&self.already_normalized, mid) {
                    return Some(value);
                }
                name_vec_insert(&mut self.already_normalized, mid);
                let value_new = self.visit(value);
                if value_new != value {
                    lean_inc(value);
                    self.saved_assignments.push(value);
                    self.assign(mid, value_new);
                }
                lean_dec(value);
                Some(value_new)
            } else {
                let value_new = self.visit(value);
                lean_dec(value);
                Some(value_new)
            }
        }

        unsafe fn is_resolvable_pending(&mut self, pending: *const LeanObject) -> bool {
            if let Some(state) = name_state_get(&self.resolvable_pending_cache, pending) {
                return state == 1;
            }
            name_state_set(
                &mut self.resolvable_pending_cache,
                pending as *mut LeanObject,
                0,
            );
            let Some(a) = self.get_mvar_assignment_raw(pending as *mut LeanObject) else {
                name_state_set(
                    &mut self.resolvable_pending_cache,
                    pending as *mut LeanObject,
                    2,
                );
                return false;
            };
            let ok = self.is_resolvable_expr(a);
            name_state_set(
                &mut self.resolvable_pending_cache,
                pending as *mut LeanObject,
                if ok { 1 } else { 2 },
            );
            lean_dec(a);
            ok
        }

        unsafe fn is_resolvable_expr(&mut self, e: *const LeanObject) -> bool {
            if !has_expr_mvar(e) {
                return true;
            }
            let key = e as usize;
            if is_shared_object(e) {
                if let Some(&cached) = self.resolvable_expr_cache.get(&key) {
                    return cached;
                }
            }
            let r = self.is_resolvable_expr_core(e);
            if is_shared_object(e) {
                self.resolvable_expr_cache.insert(key, r);
            }
            r
        }

        unsafe fn is_resolvable_expr_core(&mut self, e: *const LeanObject) -> bool {
            match lean_obj_tag(e) {
                EXPR_MVAR_TAG => false,
                EXPR_APP_TAG => {
                    let f = app_head(e);
                    if lean_obj_tag(f) == EXPR_MVAR_TAG {
                        let d_opt = get_delayed_assignment(self.mctx, mvar_name(f));
                        if lean_is_scalar(d_opt) {
                            return false;
                        }
                        let d = lean_ctor_get(d_opt, 0);
                        lean_inc(d);
                        let fvars = lean_delayed_mvar_assignment_fvars(d);
                        if lean_array_size(fvars) > app_num_args(e) {
                            lean_dec(fvars);
                            lean_dec(d_opt);
                            return false;
                        }
                        let d = lean_ctor_get(d_opt, 0);
                        lean_inc(d);
                        let pending = lean_delayed_mvar_assignment_mvar_id_pending(d);
                        let ok_pending = self.is_resolvable_pending(pending);
                        lean_dec(pending);
                        if !ok_pending {
                            lean_dec(fvars);
                            lean_dec(d_opt);
                            return false;
                        }
                        let mut curr = e;
                        while lean_obj_tag(curr) == EXPR_APP_TAG {
                            if !self.is_resolvable_expr(lean_ctor_get(curr, 1)) {
                                lean_dec(fvars);
                                lean_dec(d_opt);
                                return false;
                            }
                            curr = lean_ctor_get(curr, 0);
                        }
                        lean_dec(fvars);
                        lean_dec(d_opt);
                        true
                    } else {
                        self.is_resolvable_expr(lean_ctor_get(e, 0))
                            && self.is_resolvable_expr(lean_ctor_get(e, 1))
                    }
                }
                EXPR_LAMBDA_TAG | EXPR_PI_TAG => {
                    self.is_resolvable_expr(lean_ctor_get(e, 1))
                        && self.is_resolvable_expr(lean_ctor_get(e, 2))
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

        unsafe fn lookup_fvar(&mut self, fid: *const LeanObject) -> Option<*mut LeanObject> {
            if let Some(pos) = self.find_fvar_subst(fid) {
                let entry = &self.fvar_subst[pos].1;
                self.result_scope = self.result_scope.max(entry.scope);
                let delta = self.depth - entry.depth;
                if delta == 0 {
                    lean_inc(entry.value);
                    Some(entry.value)
                } else {
                    Some(lean_expr_lift_loose_bvars(
                        entry.value,
                        lean_box(0),
                        lean_box(delta as usize),
                    ))
                }
            } else {
                None
            }
        }

        unsafe fn visit_delayed(
            &mut self,
            fvars: *mut LeanObject,
            mid_pending: *mut LeanObject,
            e: *mut LeanObject,
        ) -> *mut LeanObject {
            let mut args = Vec::new();
            let mut curr = e;
            while lean_obj_tag(curr) == EXPR_APP_TAG {
                args.push(self.visit(lean_ctor_get(curr, 1)));
                curr = lean_ctor_get(curr, 0);
            }
            let fvar_count = lean_array_size(fvars);
            let extra_count = args.len() - fvar_count;

            self.cache.push();
            let mut saved_entries: Vec<(
                *mut LeanObject,
                Option<(*mut LeanObject, FvarSubstEntry)>,
            )> = Vec::with_capacity(fvar_count);
            for i in 0..fvar_count {
                let fid = fvar_name(lean_array_get(fvars, i));
                let arg = args[args.len() - 1 - i];
                lean_inc(arg);
                let old = if let Some(pos) = self.find_fvar_subst(fid) {
                    Some(self.fvar_subst.remove(pos))
                } else {
                    None
                };
                lean_inc(fid);
                self.fvar_subst.push((
                    fid,
                    FvarSubstEntry {
                        depth: self.depth,
                        scope: self.cache.scope(),
                        value: arg,
                    },
                ));
                saved_entries.push((fid, old));
            }

            let pending_val = self
                .get_mvar_assignment_raw(mid_pending)
                .expect("delayed pending mvar must be assigned");
            let val_new = self.visit(pending_val);

            self.cache.pop();
            self.result_scope = self.result_scope.min(self.cache.scope());

            for (fid, old) in saved_entries {
                if let Some(pos) = self.find_fvar_subst(fid) {
                    let (key, current) = self.fvar_subst.remove(pos);
                    lean_dec(key);
                    lean_dec(current.value);
                }
                if let Some(v) = old {
                    self.fvar_subst.push(v);
                }
            }

            let result = apply_beta(val_new, extra_count, args.as_ptr(), false, true);
            lean_dec(val_new);
            lean_dec(pending_val);
            for arg in args {
                lean_dec(arg);
            }
            result
        }

        unsafe fn visit_nonmvar_app(&mut self, e: *mut LeanObject) -> *mut LeanObject {
            let old_a = lean_ctor_get(e, 1);
            let new_a = self.visit(old_a);
            let old_f = lean_ctor_get(e, 0);
            let new_f = if lean_obj_tag(old_f) == EXPR_APP_TAG {
                self.visit_nonmvar_app(old_f)
            } else {
                self.visit(old_f)
            };
            if new_f == old_f && new_a == old_a {
                lean_dec(new_f);
                lean_dec(new_a);
                lean_inc(e);
                e
            } else {
                lean_expr_mk_app(new_f, new_a)
            }
        }

        unsafe fn visit_app(&mut self, e: *mut LeanObject) -> *mut LeanObject {
            let f = app_head(e);
            if lean_obj_tag(f) != EXPR_MVAR_TAG {
                return self.visit_nonmvar_app(e);
            }
            let mid = mvar_name(f);
            let d_opt = get_delayed_assignment(self.mctx, mid);
            if lean_is_scalar(d_opt) {
                return self.visit_nonmvar_app(e);
            }
            let d = lean_ctor_get(d_opt, 0);
            lean_inc(d);
            let fvars = lean_delayed_mvar_assignment_fvars(d);
            let d = lean_ctor_get(d_opt, 0);
            lean_inc(d);
            let pending = lean_delayed_mvar_assignment_mvar_id_pending(d);
            let r = if lean_array_size(fvars) > app_num_args(e) {
                self.visit_nonmvar_app(e)
            } else if self.is_resolvable_pending(pending) {
                self.visit_delayed(fvars, pending, e)
            } else {
                let _ = self.get_assignment(pending);
                self.visit_nonmvar_app(e)
            };
            lean_dec(pending);
            lean_dec(fvars);
            lean_dec(d_opt);
            r
        }

        unsafe fn visit_fvar(&mut self, e: *mut LeanObject) -> *mut LeanObject {
            if let Some(r) = self.lookup_fvar(fvar_name(e)) {
                r
            } else {
                lean_inc(e);
                e
            }
        }

        unsafe fn visit(&mut self, e: *mut LeanObject) -> *mut LeanObject {
            if (!has_fvar(e) || self.in_outer_mode()) && !has_expr_mvar(e) {
                lean_inc(e);
                return e;
            }
            let shared = is_shared_object(e);
            let key = (e as usize, self.depth);
            if shared {
                if let Some(cached) = self.cache.lookup(key, &mut self.result_scope) {
                    return cached;
                }
            }
            let saved_result_scope = self.result_scope;
            self.result_scope = 0;
            let mut skip_cache = false;
            let r = match lean_obj_tag(e) {
                EXPR_FVAR_TAG => {
                    skip_cache = true;
                    self.visit_fvar(e)
                }
                EXPR_MVAR_TAG => {
                    skip_cache = true;
                    lean_inc(e);
                    e
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
                    let val = self.visit(lean_ctor_get(e, 2));
                    self.depth += 1;
                    let body = self.visit(lean_ctor_get(e, 3));
                    self.depth -= 1;
                    let name = lean_ctor_get(e, 0);
                    lean_inc(name);
                    lean_expr_mk_let(name, typ, val, body, expr_let_nondep(e))
                }
                _ => {
                    lean_inc(e);
                    e
                }
            };
            let r = if shared && !skip_cache {
                self.cache.insert(key, r, self.result_scope)
            } else {
                r
            };
            self.result_scope = self.result_scope.max(saved_result_scope);
            r
        }
    }

    impl Drop for InstantiateDelayed {
        fn drop(&mut self) {
            unsafe {
                for v in self.saved_assignments.drain(..) {
                    lean_dec(v);
                }
                for name in self.already_normalized.drain(..) {
                    lean_dec(name);
                }
                for (key, v) in self.fvar_subst.drain(..) {
                    lean_dec(key);
                    lean_dec(v.value);
                }
                name_state_clear(&mut self.resolvable_pending_cache);
            }
        }
    }

    /// `instantiateExprMVars (mctx : MetavarContext) (e : Expr) : MetavarContext × Expr`
    #[no_mangle]
    pub unsafe fn lean_instantiate_expr_mvars(
        mctx: *mut LeanObject,
        e: *mut LeanObject,
    ) -> *mut LeanObject {
        let mut pass1 = InstantiateDirect::new(mctx);
        let e1 = pass1.visit(e);
        let mctx1 = pass1.level_inst.mctx;
        pass1.level_inst.mctx = core::ptr::null_mut();
        let (mctx2, expr) = if pass1.has_updateable_delayed {
            let mut pass2 = InstantiateDelayed::new(mctx1);
            let e2 = pass2.visit(e1);
            lean_dec(e1);
            let mctx2 = pass2.mctx;
            pass2.mctx = core::ptr::null_mut();
            (mctx2, e2)
        } else {
            (mctx1, e1)
        };
        lean_dec(e);
        mk_pair(mctx2, expr)
    }
}
