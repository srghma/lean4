/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Port of src/library/instantiate_mvars.cpp level-MVar instantiation to Rust.
  lean_instantiate_level_mvars — fully implemented in Rust
  lean_instantiate_expr_mvars  — delegates to C++ lean_cxx_instantiate_expr_mvars
    (the expression case uses a two-pass algorithm for delayed MVars that is
    kept in C++ for correctness)
*/

#[cfg(feature = "export-runtime-ffi")]
mod library_instantiate_mvars_impl {
    use super::*;
    use std::collections::HashMap;

    extern "C" {
        // Expression mvar instantiation stays in C++ (two-pass delayed-MVar algorithm).
        fn lean_cxx_instantiate_expr_mvars(mctx: *mut LeanObject, e: *mut LeanObject) -> *mut LeanObject;

        fn lean_get_lmvar_assignment(mctx: *mut LeanObject, mid: *mut LeanObject) -> *mut LeanObject;
        fn lean_assign_lmvar(mctx: *mut LeanObject, mid: *mut LeanObject, val: *mut LeanObject) -> *mut LeanObject;

        fn lean_level_mk_succ(l: *mut LeanObject) -> *mut LeanObject;
        fn lean_level_mk_max(l1: *mut LeanObject, l2: *mut LeanObject) -> *mut LeanObject;
        fn lean_level_mk_imax(l1: *mut LeanObject, l2: *mut LeanObject) -> *mut LeanObject;
        fn lean_level_eq(l1: *mut LeanObject, l2: *mut LeanObject) -> u8;
    }

    // Level data bit 32 = hasMVar.
    const LEVEL_DATA_HAS_MVAR: u64 = 1 << 32;

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
                    self.rebuild_binary(l, lhs, rhs, lean_level_mk_max, shared)
                }
                3 => {
                    let lhs = self.visit(lean_ctor_get(l, 0));
                    let rhs = self.visit(lean_ctor_get(l, 1));
                    self.rebuild_binary(l, lhs, rhs, lean_level_mk_imax, shared)
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

    /// `instantiateExprMVars (mctx : MetavarContext) (e : Expr) : MetavarContext × Expr`
    /// Delegates to C++ for the two-pass delayed-MVar algorithm.
    #[no_mangle]
    pub unsafe extern "C" fn lean_instantiate_expr_mvars(
        mctx: *mut LeanObject,
        e: *mut LeanObject,
    ) -> *mut LeanObject {
        lean_cxx_instantiate_expr_mvars(mctx, e)
    }
}
