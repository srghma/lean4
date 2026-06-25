#[cfg(feature = "export-runtime-ffi")]
use crate::*;

/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Full Rust implementations of kernel/expr_eq_fn.cpp LEAN_EXPORT functions:
  lean_expr_eqv   — replaces lean_cxx_expr_eqv  (CompareBinderInfo=false)
  lean_expr_equal — replaces lean_cxx_expr_equal (CompareBinderInfo=true)

Algorithm: mirrors expr_eq_fn<CompareBinderInfo> in C++.
  - Pointer equality → true
  - Hash mismatch (bits [31:0] of Expr.Data) → false
  - Kind mismatch → false
  - Leaves (BVar/Lit/MVar/FVar/Sort): direct field comparison
  - Compound: cache pair (a,b) before recursing to handle DAG sharing
  - Counter-based heartbeat accumulation (add_heartbeats on drop)
  - Stack depth check against MAX_STACK_DEPTH threshold

MData KVMap comparison uses structural list equality (kvmap_eq), matching C++
list_ref<pair_ref<name,data_value>>::operator==, NOT pointer equality.
KVMap is list_ref<kvmap_entry> where kvmap_entry = pair_ref<name, data_value>.
  - list nil  = lean_is_scalar(ptr) (lean_box(0))
  - list cons = ctor(tag=1), field[0]=pair, field[1]=tail
  - pair      = ctor, field[0]=name, field[1]=data_value
  - data_value comparison uses lean_data_value_beq (consuming)
  - name comparison uses lean_name_eq (borrowing)

Expression kind tags:
  BVar=0  FVar=1  MVar=2  Sort=3  Const=4  App=5
  Lambda=6  Pi=7  Let=8  Lit=9  MData=10  Proj=11

Literal kind tags (for Lit.field[0]):
  natVal=0  strVal=1

Level kind tags:
  Zero=scalar  Succ=1  Max=2  IMax=3  Param=4  MVar=5
  (see kernel_level.rs)
*/

#[cfg(feature = "export-runtime-ffi")]
mod kernel_expr_eq_fn_impl {
    use super::runtime_alloc_impl::add_heartbeats;
    use super::runtime_object_name_impl::lean_name_eq;
    use super::runtime_object_panic_impl::lean_internal_panic;
    use super::*;
    use std::collections::HashSet;

    extern "C" {
        fn lean_level_eqv(l1: *mut LeanObject, l2: *mut LeanObject) -> u8;
        fn lean_nat_big_eq(a1: *mut LeanObject, a2: *mut LeanObject) -> bool;
        fn lean_string_eq_cold(s1: *mut LeanObject, s2: *mut LeanObject) -> bool;
        // Consumes both arguments (obj_arg semantics); call lean_inc before passing borrowed refs.
        fn lean_data_value_beq(a: *mut LeanObject, b: *mut LeanObject) -> u8;
    }

    const EXPR_BVAR: u8 = 0;
    const EXPR_FVAR: u8 = 1;
    const EXPR_MVAR: u8 = 2;
    const EXPR_SORT: u8 = 3;
    const EXPR_CONST: u8 = 4;
    const EXPR_APP: u8 = 5;
    const EXPR_LAMBDA: u8 = 6;
    const EXPR_PI: u8 = 7;
    const EXPR_LET: u8 = 8;
    const EXPR_LIT: u8 = 9;
    const EXPR_MDATA: u8 = 10;
    const EXPR_PROJ: u8 = 11;

    // Max recursion depth: get_available_stack_size() / 256 = 8*1024*1024 / 256 = 32768
    const MAX_STACK_DEPTH: usize = 8 * 1024 * 1024 / 256;

    // bits [31:0] of Expr.Data u64 = the expression hash.
    #[inline(always)]
    unsafe fn expr_hash(e: *mut LeanObject) -> u32 {
        let num_objs = (*e).other as usize;
        lean_ctor_get_uint64(e, num_objs * core::mem::size_of::<*mut LeanObject>()) as u32
    }

    // BinderInfo byte for Lambda/Pi (stored after the data u64).
    #[inline(always)]
    unsafe fn expr_binder_info_raw(e: *mut LeanObject) -> u8 {
        let num_objs = (*e).other as usize;
        lean_ctor_get_uint8(e, num_objs * 8 + 8)
    }

    // nondep byte for Let (4 obj fields).
    #[inline(always)]
    unsafe fn expr_let_nondep(e: *mut LeanObject) -> u8 {
        lean_ctor_get_uint8(e, 4 * 8 + 8)
    }

    // lean_string_size: reads m_size from lean_string_object (at byte offset 8).
    #[inline(always)]
    unsafe fn string_size(s: *mut LeanObject) -> usize {
        *((s as *const u8).add(8) as *const usize)
    }

    // Structural equality for KVMap = list_ref<pair_ref<name, data_value>>.
    // Mirrors C++ list_ref::operator== (ordered, element-wise comparison).
    // Borrowed references: does not consume m1 or m2.
    unsafe fn kvmap_eq(mut m1: *mut LeanObject, mut m2: *mut LeanObject) -> bool {
        loop {
            if m1 == m2 {
                return true;
            }
            let s1 = lean_is_scalar(m1);
            let s2 = lean_is_scalar(m2);
            if s1 && s2 {
                return true;
            } // both nil
            if s1 || s2 {
                return false;
            } // different lengths

            // cons cell: field[0]=pair, field[1]=tail
            let pair1 = lean_ctor_get(m1, 0);
            let pair2 = lean_ctor_get(m2, 0);
            if pair1 != pair2 {
                // pair: field[0]=name, field[1]=data_value
                let name1 = lean_ctor_get(pair1, 0);
                let name2 = lean_ctor_get(pair2, 0);
                if lean_name_eq(name1, name2) == 0 {
                    return false;
                }

                let dv1 = lean_ctor_get(pair1, 1);
                let dv2 = lean_ctor_get(pair2, 1);
                if dv1 != dv2 {
                    lean_inc(dv1);
                    lean_inc(dv2);
                    if lean_data_value_beq(dv1, dv2) == 0 {
                        return false;
                    }
                }
            }

            m1 = lean_ctor_get(m1, 1);
            m2 = lean_ctor_get(m2, 1);
        }
    }

    struct ExprEqFn {
        compare_binder_info: bool,
        cache: Option<HashSet<(usize, usize)>>,
        counter: u64,
    }

    impl Drop for ExprEqFn {
        fn drop(&mut self) {
            if self.counter > 0 {
                unsafe {
                    add_heartbeats(self.counter);
                }
            }
        }
    }

    impl ExprEqFn {
        fn new(compare_binder_info: bool) -> Self {
            Self {
                compare_binder_info,
                cache: None,
                counter: 0,
            }
        }

        // Returns true if (a, b) are already in the cache (proven equal or in progress).
        // Inserts (a, b) into the cache if not found, so future encounters return true.
        // Only caches shared objects (rc > 1).
        unsafe fn check_cache(&mut self, a: *mut LeanObject, b: *mut LeanObject) -> bool {
            if (*a).rc <= 1 || (*b).rc <= 1 {
                return false;
            }
            let key = (a as usize, b as usize);
            let cache = self.cache.get_or_insert_with(HashSet::new);
            if cache.contains(&key) {
                return true;
            }
            cache.insert(key);
            false
        }

        unsafe fn check_system(&self, depth: usize) {
            if depth > MAX_STACK_DEPTH {
                lean_internal_panic(b"expression equality test\0".as_ptr() as *const i8);
            }
        }

        // Compare two Nat objects (no ownership transfer).
        #[inline(always)]
        unsafe fn nat_eq(&self, a: *mut LeanObject, b: *mut LeanObject) -> bool {
            if a == b {
                return true;
            }
            if lean_is_scalar(a) || lean_is_scalar(b) {
                return false;
            }
            lean_nat_big_eq(a, b)
        }

        // Compare two String objects (no ownership transfer).
        #[inline(always)]
        unsafe fn str_eq(&self, s1: *mut LeanObject, s2: *mut LeanObject) -> bool {
            s1 == s2 || (string_size(s1) == string_size(s2) && lean_string_eq_cold(s1, s2))
        }

        // Compare two Literal objects (tag 0 = natVal, tag 1 = strVal).
        #[inline]
        unsafe fn lit_eq(&self, a: *mut LeanObject, b: *mut LeanObject) -> bool {
            if a == b {
                return true;
            }
            let tag_a = lean_obj_tag(a);
            let tag_b = lean_obj_tag(b);
            if tag_a != tag_b {
                return false;
            }
            match tag_a {
                0 => self.nat_eq(lean_ctor_get(a, 0), lean_ctor_get(b, 0)),
                1 => self.str_eq(lean_ctor_get(a, 0), lean_ctor_get(b, 0)),
                _ => false,
            }
        }

        // Compare two Level list objects (List Level, nil = lean_box(0), cons has tag 0).
        unsafe fn levels_eq(&self, mut ls1: *mut LeanObject, mut ls2: *mut LeanObject) -> bool {
            loop {
                if ls1 == ls2 {
                    return true;
                }
                let s1 = lean_is_scalar(ls1);
                let s2 = lean_is_scalar(ls2);
                if s1 && s2 {
                    return true;
                }
                if s1 || s2 {
                    return false;
                }
                if lean_level_eqv(lean_ctor_get(ls1, 0), lean_ctor_get(ls2, 0)) == 0 {
                    return false;
                }
                ls1 = lean_ctor_get(ls1, 1);
                ls2 = lean_ctor_get(ls2, 1);
            }
        }

        // Core comparison. `root=true` only for the top-level call.
        // `a` and `b` are borrowed.
        unsafe fn apply(
            &mut self,
            a: *mut LeanObject,
            b: *mut LeanObject,
            depth: usize,
            root: bool,
        ) -> bool {
            if a == b {
                return true;
            }
            if expr_hash(a) != expr_hash(b) {
                return false;
            }

            let tag = lean_obj_tag(a);
            if tag != lean_obj_tag(b) {
                return false;
            }

            // Leaf cases: compare directly without caching.
            match tag {
                EXPR_BVAR => {
                    return self.nat_eq(lean_ctor_get(a, 0), lean_ctor_get(b, 0));
                }
                EXPR_LIT => {
                    return self.lit_eq(lean_ctor_get(a, 0), lean_ctor_get(b, 0));
                }
                EXPR_MVAR | EXPR_FVAR => {
                    return lean_name_eq(lean_ctor_get(a, 0), lean_ctor_get(b, 0)) != 0;
                }
                EXPR_SORT => {
                    return lean_level_eqv(lean_ctor_get(a, 0), lean_ctor_get(b, 0)) != 0;
                }
                _ => {}
            }

            if root {
                // max_stack_depth already hardcoded; no action needed
            } else if self.check_cache(a, b) {
                return true;
            }

            self.counter += 1;
            let depth = depth + 1;

            match tag {
                EXPR_MDATA => {
                    // field[0] = KVMap (structural equality via kvmap_eq), field[1] = expr
                    self.apply(lean_ctor_get(a, 1), lean_ctor_get(b, 1), depth, false)
                        && kvmap_eq(lean_ctor_get(a, 0), lean_ctor_get(b, 0))
                }
                EXPR_PROJ => {
                    // field[0] = sname (Name), field[1] = idx (Nat), field[2] = expr
                    self.apply(lean_ctor_get(a, 2), lean_ctor_get(b, 2), depth, false)
                        && lean_name_eq(lean_ctor_get(a, 0), lean_ctor_get(b, 0)) != 0
                        && self.nat_eq(lean_ctor_get(a, 1), lean_ctor_get(b, 1))
                }
                EXPR_CONST => {
                    // field[0] = name, field[1] = List Level
                    lean_name_eq(lean_ctor_get(a, 0), lean_ctor_get(b, 0)) != 0
                        && self.levels_eq(lean_ctor_get(a, 1), lean_ctor_get(b, 1))
                }
                EXPR_APP => {
                    self.check_system(depth);
                    // Compare args first, then traverse the fn chain.
                    if !self.apply(lean_ctor_get(a, 1), lean_ctor_get(b, 1), depth, false) {
                        return false;
                    }
                    let mut curr_a = lean_ctor_get(a, 0);
                    let mut curr_b = lean_ctor_get(b, 0);
                    loop {
                        if lean_obj_tag(curr_a) != EXPR_APP {
                            break;
                        }
                        if lean_obj_tag(curr_b) != EXPR_APP {
                            return false;
                        }
                        if !self.apply(
                            lean_ctor_get(curr_a, 1),
                            lean_ctor_get(curr_b, 1),
                            depth,
                            false,
                        ) {
                            return false;
                        }
                        curr_a = lean_ctor_get(curr_a, 0);
                        curr_b = lean_ctor_get(curr_b, 0);
                    }
                    self.apply(curr_a, curr_b, depth, false)
                }
                EXPR_LAMBDA | EXPR_PI => {
                    // field[0]=name, field[1]=domain, field[2]=body; scalar: data u64, binder_info u8
                    self.check_system(depth);
                    if !self.apply(lean_ctor_get(a, 1), lean_ctor_get(b, 1), depth, false) {
                        return false;
                    }
                    if !self.apply(lean_ctor_get(a, 2), lean_ctor_get(b, 2), depth, false) {
                        return false;
                    }
                    if self.compare_binder_info {
                        if lean_name_eq(lean_ctor_get(a, 0), lean_ctor_get(b, 0)) == 0 {
                            return false;
                        }
                        if expr_binder_info_raw(a) != expr_binder_info_raw(b) {
                            return false;
                        }
                    }
                    true
                }
                EXPR_LET => {
                    // field[0]=name, field[1]=type, field[2]=value, field[3]=body; scalar: data u64, nondep u8
                    self.check_system(depth);
                    if !self.apply(lean_ctor_get(a, 1), lean_ctor_get(b, 1), depth, false) {
                        return false;
                    }
                    if !self.apply(lean_ctor_get(a, 2), lean_ctor_get(b, 2), depth, false) {
                        return false;
                    }
                    if !self.apply(lean_ctor_get(a, 3), lean_ctor_get(b, 3), depth, false) {
                        return false;
                    }
                    if expr_let_nondep(a) != expr_let_nondep(b) {
                        return false;
                    }
                    if self.compare_binder_info {
                        if lean_name_eq(lean_ctor_get(a, 0), lean_ctor_get(b, 0)) == 0 {
                            return false;
                        }
                    }
                    true
                }
                _ => false, // unreachable for valid exprs
            }
        }
    }

    // lean_expr_eqv (a b : @& Expr) : Bool  — structural equality, ignoring binder names/info
    #[no_mangle]
    pub unsafe extern "C" fn lean_expr_eqv(a: *mut LeanObject, b: *mut LeanObject) -> u8 {
        ExprEqFn::new(false).apply(a, b, 0, true) as u8
    }

    // lean_expr_equal (a b : @& Expr) : Bool  — structural equality including binder names/info
    #[no_mangle]
    pub unsafe extern "C" fn lean_expr_equal(a: *mut LeanObject, b: *mut LeanObject) -> u8 {
        ExprEqFn::new(true).apply(a, b, 0, true) as u8
    }
}
