// Port of src/library/instantiate_mvars.cpp to Rust.
//
// instantiate_mvars.cpp exports two LEAN_EXPORT functions:
//   lean_instantiate_level_mvars  — instantiates level metavariables
//   lean_instantiate_expr_mvars   — two-pass expr MVar instantiation
//
// The expression algorithm is deeply algorithmic (two traversal passes,
// scope_cache, name_hash_map, pointer-identity caching).  The level algorithm
// is compact enough to keep here directly and must not route through a C++
// compatibility symbol: in this Rust runtime those compatibility exports are
// aliases back to the Rust exports.

mod library_instantiate_mvars_impl {
    use super::*;
    use std::collections::HashMap;

    extern "C" {
        fn lean_cxx_instantiate_expr_mvars(
            mctx: *mut LeanObject,
            e: *mut LeanObject,
        ) -> *mut LeanObject;

        fn lean_get_lmvar_assignment(mctx: *mut LeanObject, mid: *mut LeanObject) -> *mut LeanObject;
        fn lean_assign_lmvar(
            mctx: *mut LeanObject,
            mid: *mut LeanObject,
            val: *mut LeanObject,
        ) -> *mut LeanObject;

        fn lean_level_mk_succ(l: *mut LeanObject) -> *mut LeanObject;
        fn lean_level_mk_max(l1: *mut LeanObject, l2: *mut LeanObject) -> *mut LeanObject;
        fn lean_level_mk_imax(l1: *mut LeanObject, l2: *mut LeanObject) -> *mut LeanObject;

        fn lean_get_mvar_assignment(mctx: *mut LeanObject, mid: *mut LeanObject) -> *mut LeanObject;
        fn lean_assign_mvar(
            mctx: *mut LeanObject,
            mid: *mut LeanObject,
            val: *mut LeanObject,
        ) -> *mut LeanObject;

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
    }

    const LEVEL_DATA_HAS_MVAR: u64 = 1 << 32;
    const EXPR_DATA_HAS_EXPR_MVAR: u64 = 1 << 41;
    const EXPR_DATA_HAS_LEVEL_MVAR: u64 = 1 << 42;

    unsafe fn has_level_mvar(l: *mut LeanObject) -> bool {
        if lean_is_scalar(l) {
            false
        } else {
            let num_objs = (*l).m_other as usize;
            let data = lean_ctor_get_uint64(l, num_objs * core::mem::size_of::<*mut LeanObject>());
            (data & LEVEL_DATA_HAS_MVAR) != 0
        }
    }

    unsafe fn expr_needs_instantiation(e: *mut LeanObject) -> bool {
        if lean_is_scalar(e) {
            false
        } else {
            let num_objs = (*e).m_other as usize;
            let data = lean_ctor_get_uint64(e, num_objs * core::mem::size_of::<*mut LeanObject>());
            (data & (EXPR_DATA_HAS_EXPR_MVAR | EXPR_DATA_HAS_LEVEL_MVAR)) != 0
        }
    }

    unsafe fn is_shared_object(o: *mut LeanObject) -> bool {
        !lean_is_scalar(o) && lean_is_st(o) && (*o).m_rc > 1
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

            match lean_obj_tag(l) {
                1 => {
                    let child = self.visit(lean_ctor_get(l, 0));
                    self.rebuild_unary(l, child, lean_level_mk_succ, shared)
                }
                2 => {
                    let lhs = self.visit(lean_ctor_get(l, 0));
                    let rhs = self.visit(lean_ctor_get(l, 1));
                    self.rebuild_binary(l, lhs, rhs, lean_level_mk_max, shared)
                }
                3 => {
                    let lhs = self.visit(lean_ctor_get(l, 0));
                    let rhs = self.visit(lean_ctor_get(l, 1));
                    self.rebuild_binary(l, lhs, rhs, lean_level_mk_imax, shared)
                }
                5 => {
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

    struct ExprMVarInstantiator {
        level_inst: LevelMVarInstantiator,
        cache: HashMap<*mut LeanObject, *mut LeanObject>,
        saved_assignments: Vec<*mut LeanObject>,
    }

    impl ExprMVarInstantiator {
        unsafe fn new(mctx: *mut LeanObject) -> Self {
            Self {
                level_inst: LevelMVarInstantiator::new(mctx),
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

        unsafe fn get_assignment(&mut self, mid: *mut LeanObject) -> Option<*mut LeanObject> {
            let mctx = self.level_inst.mctx;
            lean_inc_ref(mctx);
            lean_inc(mid);
            let opt = lean_get_mvar_assignment(mctx, mid);
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
            let mctx = self.level_inst.mctx;
            self.level_inst.mctx = lean_assign_mvar(mctx, mid, value);
        }

        unsafe fn map_level_list(&mut self, list: *mut LeanObject) -> *mut LeanObject {
            let mut curr = list;
            let mut levels = Vec::new();
            let mut changed = false;
            while !lean_is_scalar(curr) {
                let head = lean_ctor_get(curr, 0);
                let new_head = self.level_inst.visit(head);
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
                2 => {
                    let mid = lean_ctor_get(e, 0);
                    let Some(assignment) = self.get_assignment(mid) else {
                        lean_inc(e);
                        return e;
                    };
                    let assignment_new = if expr_needs_instantiation(assignment) {
                        self.visit(assignment)
                    } else {
                        lean_inc(assignment);
                        assignment
                    };
                    if assignment_new != assignment {
                        lean_inc(assignment);
                        self.saved_assignments.push(assignment);
                        self.assign(mid, assignment_new);
                    }
                    lean_dec(assignment);
                    assignment_new
                }
                3 => {
                    let old = lean_ctor_get(e, 0);
                    let level = self.level_inst.visit(old);
                    self.reuse_or(e, level != old, &[level], || lean_expr_mk_sort(level), shared)
                }
                4 => {
                    let old_levels = lean_ctor_get(e, 1);
                    let levels = self.map_level_list(old_levels);
                    self.reuse_or(e, levels != old_levels, &[levels], || {
                        let name = lean_ctor_get(e, 0);
                        lean_inc(name);
                        lean_expr_mk_const(name, levels)
                    }, shared)
                }
                5 => {
                    let old_fn = lean_ctor_get(e, 0);
                    let old_arg = lean_ctor_get(e, 1);
                    let new_fn = self.visit(old_fn);
                    let new_arg = self.visit(old_arg);
                    self.reuse_or(e, new_fn != old_fn || new_arg != old_arg, &[new_fn, new_arg], || {
                        lean_expr_mk_app(new_fn, new_arg)
                    }, shared)
                }
                6 => {
                    let old_domain = lean_ctor_get(e, 1);
                    let old_body = lean_ctor_get(e, 2);
                    let domain = self.visit(old_domain);
                    let body = self.visit(old_body);
                    self.reuse_or(e, domain != old_domain || body != old_body, &[domain, body], || {
                        let name = lean_ctor_get(e, 0);
                        lean_inc(name);
                        let bi = lean_ctor_get_uint8(e, 3 * core::mem::size_of::<*mut LeanObject>());
                        lean_expr_mk_lambda(name, domain, body, bi)
                    }, shared)
                }
                7 => {
                    let old_domain = lean_ctor_get(e, 1);
                    let old_body = lean_ctor_get(e, 2);
                    let domain = self.visit(old_domain);
                    let body = self.visit(old_body);
                    self.reuse_or(e, domain != old_domain || body != old_body, &[domain, body], || {
                        let name = lean_ctor_get(e, 0);
                        lean_inc(name);
                        let bi = lean_ctor_get_uint8(e, 3 * core::mem::size_of::<*mut LeanObject>());
                        lean_expr_mk_forall(name, domain, body, bi)
                    }, shared)
                }
                8 => {
                    let old_type = lean_ctor_get(e, 1);
                    let old_value = lean_ctor_get(e, 2);
                    let old_body = lean_ctor_get(e, 3);
                    let typ = self.visit(old_type);
                    let value = self.visit(old_value);
                    let body = self.visit(old_body);
                    self.reuse_or(
                        e,
                        typ != old_type || value != old_value || body != old_body,
                        &[typ, value, body],
                        || {
                            let name = lean_ctor_get(e, 0);
                            lean_inc(name);
                            let nondep = lean_ctor_get_uint8(e, 4 * core::mem::size_of::<*mut LeanObject>());
                            lean_expr_mk_let(name, typ, value, body, nondep)
                        },
                        shared,
                    )
                }
                10 => {
                    let old_expr = lean_ctor_get(e, 1);
                    let expr = self.visit(old_expr);
                    self.reuse_or(e, expr != old_expr, &[expr], || {
                        let mdata = lean_ctor_get(e, 0);
                        lean_inc(mdata);
                        lean_expr_mk_mdata(mdata, expr)
                    }, shared)
                }
                11 => {
                    let old_struct = lean_ctor_get(e, 2);
                    let structure = self.visit(old_struct);
                    self.reuse_or(e, structure != old_struct, &[structure], || {
                        let name = lean_ctor_get(e, 0);
                        let idx = lean_ctor_get(e, 1);
                        lean_inc(name);
                        lean_inc(idx);
                        lean_expr_mk_proj(name, idx, structure)
                    }, shared)
                }
                _ => {
                    lean_inc(e);
                    e
                }
            }
        }
    }

    impl Drop for ExprMVarInstantiator {
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

    /// `instantiateExprMVars (mctx : MetavarContext) (e : Expr) : MetavarContext × Expr`
    #[no_mangle]
    pub unsafe extern "C" fn lean_instantiate_expr_mvars(
        mctx: *mut LeanObject,
        e: *mut LeanObject,
    ) -> *mut LeanObject {
        let mut inst = ExprMVarInstantiator::new(mctx);
        let expr = inst.visit(e);
        let mctx = inst.level_inst.mctx;
        inst.level_inst.mctx = core::ptr::null_mut();
        lean_dec(e);
        mk_pair(mctx, expr)
    }
}
