use leanh::*;
use core::ffi::{c_char, c_int, c_long, c_uchar, c_uint, c_void, CStr};
use core::ptr;
use core::sync::atomic::{AtomicBool, AtomicI32, AtomicPtr, AtomicU32, Ordering};


/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Full Rust port of kernel/equiv_manager.cpp.
Provides an opaque C handle for the C++ equiv_manager class.

Algorithm: union-find over expression pointers.
  - to_node: expr raw pointer → node index
  - nodes: Vec of (parent: u32, rank: u8)
  - is_equiv_core: structural equality + union-find caching

Differences from C++:
  - No check_system() call inside is_equiv_core. The outer type_checker still
    checks the heartbeat at other call sites; equivalence checks may run slightly
    longer before detecting a timeout. This is not a correctness issue.
  - Owned expr refs are tracked in expr_refs for correct GC on drop.

Expression kind tags:
  BVar=0  FVar=1  MVar=2  Sort=3  Const=4  App=5
  Lambda=6  Pi=7  Let=8  Lit=9  MData=10  Proj=11

Literal tags: 0 = natVal, 1 = strVal
*/

pub(crate) mod kernel_equiv_manager_impl {
    use crate::kernel::level::kernel_level_impl::lean_level_eqv;
    use crate::runtime::runtime_object_string_impl::lean_string_eq_cold;
    use core::ffi::c_void;
    use std::collections::HashMap;
    use crate::runtime::runtime_object_nat_int_impl::lean_nat_big_eq;
    use crate::runtime::runtime_object_name_impl::lean_name_eq;

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

    struct EquivManager {
        nodes: Vec<(u32, u8)>,           // (parent, rank)
        to_node: HashMap<usize, u32>,    // raw expr ptr → node index
        expr_refs: Vec<*mut LeanObject>, // owned expr refs (must be dec'd on drop)
    }

    unsafe impl Send for EquivManager {}

    impl Drop for EquivManager {
        fn drop(&mut self) {
            unsafe {
                for &e in &self.expr_refs {
                    lean_dec(e);
                }
            }
        }
    }

    impl EquivManager {
        fn new() -> Self {
            Self {
                nodes: Vec::new(),
                to_node: HashMap::new(),
                expr_refs: Vec::new(),
            }
        }

        fn mk_node(&mut self) -> u32 {
            let r = self.nodes.len() as u32;
            self.nodes.push((r, 0));
            r
        }

        fn find(&self, mut n: u32) -> u32 {
            loop {
                let p = self.nodes[n as usize].0;
                if p == n {
                    return p;
                }
                n = p;
            }
        }

        fn merge(&mut self, r1: u32, r2: u32) {
            if r1 == r2 {
                return;
            }
            let rank1 = self.nodes[r1 as usize].1;
            let rank2 = self.nodes[r2 as usize].1;
            if rank1 < rank2 {
                self.nodes[r1 as usize].0 = r2;
            } else if rank1 > rank2 {
                self.nodes[r2 as usize].0 = r1;
            } else {
                self.nodes[r2 as usize].0 = r1;
                self.nodes[r1 as usize].1 += 1;
            }
        }

        unsafe fn to_node_ref(&mut self, e: *mut LeanObject) -> u32 {
            let key = e as usize;
            if let Some(&r) = self.to_node.get(&key) {
                return r;
            }
            let r = self.mk_node();
            lean_inc(e);
            self.expr_refs.push(e);
            self.to_node.insert(key, r);
            r
        }

        // Compare two Nat objects (borrowed).
        #[inline(always)]
        unsafe fn nat_eq(a: *mut LeanObject, b: *mut LeanObject) -> bool {
            if a == b {
                return true;
            }
            if lean_is_scalar(a) || lean_is_scalar(b) {
                return false;
            } // one scalar, one not
            lean_nat_big_eq(a, b)
        }

        // Compare two String objects (borrowed).
        #[inline(always)]
        unsafe fn str_eq(s1: *mut LeanObject, s2: *mut LeanObject) -> bool {
            if s1 == s2 {
                return true;
            }
            let size1 = *((s1 as *const u8).add(8) as *const usize);
            let size2 = *((s2 as *const u8).add(8) as *const usize);
            size1 == size2 && lean_string_eq_cold(s1, s2)
        }

        // Compare two Literal objects (tag 0 = natVal, tag 1 = strVal).
        #[inline]
        unsafe fn lit_eq(a: *mut LeanObject, b: *mut LeanObject) -> bool {
            if a == b {
                return true;
            }
            let ta = lean_obj_tag(a);
            if ta != lean_obj_tag(b) {
                return false;
            }
            match ta {
                0 => Self::nat_eq(lean_ctor_get(a, 0), lean_ctor_get(b, 0)),
                1 => Self::str_eq(lean_ctor_get(a, 0), lean_ctor_get(b, 0)),
                _ => false,
            }
        }

        // Compare two Level list objects (List Level, nil = lean_box(0)).
        unsafe fn levels_eq(mut ls1: *mut LeanObject, mut ls2: *mut LeanObject) -> bool {
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

        // Read the expression hash from the data u64 (bits 31:0).
        #[inline(always)]
        unsafe fn expr_hash(e: *mut LeanObject) -> u32 {
            let num_objs = (*e).other as usize;
            lean_ctor_get_uint64(e, num_objs * core::mem::size_of::<*mut LeanObject>()) as u32
        }

        unsafe fn is_equiv_core(
            &mut self,
            a: *mut LeanObject,
            b: *mut LeanObject,
            use_hash: bool,
        ) -> bool {
            if a == b {
                return true;
            }
            if use_hash && Self::expr_hash(a) != Self::expr_hash(b) {
                return false;
            }

            let tag_a = lean_obj_tag(a);
            let tag_b = lean_obj_tag(b);

            // BVar: compare indices directly without union-find (matches C++)
            if tag_a == EXPR_BVAR && tag_b == EXPR_BVAR {
                return Self::nat_eq(lean_ctor_get(a, 0), lean_ctor_get(b, 0));
            }

            let n1 = self.to_node_ref(a);
            let n2 = self.to_node_ref(b);
            let r1 = self.find(n1);
            let r2 = self.find(n2);
            if r1 == r2 {
                return true;
            }

            // Kind mismatch → not equivalent
            if tag_a != tag_b {
                return false;
            }

            // NOTE: check_system("expression equivalence test") is intentionally omitted.
            // The outer type_checker checks the heartbeat at other call sites.

            let result = match tag_a {
                EXPR_BVAR => unreachable!(), // handled above
                EXPR_CONST => {
                    lean_name_eq(lean_ctor_get(a, 0), lean_ctor_get(b, 0)) != 0
                        && Self::levels_eq(lean_ctor_get(a, 1), lean_ctor_get(b, 1))
                }
                EXPR_MVAR | EXPR_FVAR => {
                    lean_name_eq(lean_ctor_get(a, 0), lean_ctor_get(b, 0)) != 0
                }
                EXPR_APP => {
                    self.is_equiv_core(lean_ctor_get(a, 0), lean_ctor_get(b, 0), use_hash)
                        && self.is_equiv_core(lean_ctor_get(a, 1), lean_ctor_get(b, 1), use_hash)
                }
                EXPR_LAMBDA | EXPR_PI => {
                    self.is_equiv_core(lean_ctor_get(a, 1), lean_ctor_get(b, 1), use_hash)
                        && self.is_equiv_core(lean_ctor_get(a, 2), lean_ctor_get(b, 2), use_hash)
                }
                EXPR_SORT => lean_level_eqv(lean_ctor_get(a, 0), lean_ctor_get(b, 0)) != 0,
                EXPR_LIT => Self::lit_eq(lean_ctor_get(a, 0), lean_ctor_get(b, 0)),
                EXPR_MDATA => {
                    self.is_equiv_core(lean_ctor_get(a, 1), lean_ctor_get(b, 1), use_hash)
                }
                EXPR_PROJ => {
                    self.is_equiv_core(lean_ctor_get(a, 2), lean_ctor_get(b, 2), use_hash)
                        && Self::nat_eq(lean_ctor_get(a, 1), lean_ctor_get(b, 1))
                }
                EXPR_LET => {
                    self.is_equiv_core(lean_ctor_get(a, 1), lean_ctor_get(b, 1), use_hash)
                        && self.is_equiv_core(lean_ctor_get(a, 2), lean_ctor_get(b, 2), use_hash)
                        && self.is_equiv_core(lean_ctor_get(a, 3), lean_ctor_get(b, 3), use_hash)
                }
                _ => false,
            };

            if result {
                self.merge(r1, r2);
            }
            result
        }
    }

    /// Create a new EquivManager heap-allocated, returning an opaque pointer.
    #[inline]
    pub(crate) unsafe fn lean_equiv_manager_new() -> *mut c_void {
        Box::into_raw(Box::new(EquivManager::new())) as *mut c_void
    }

    /// Free an EquivManager created by lean_equiv_manager_new.
    #[inline]
    pub(crate) unsafe fn lean_equiv_manager_free(mgr: *mut c_void) {
        if !mgr.is_null() {
            drop(Box::from_raw(mgr as *mut EquivManager));
        }
    }

    /// Check if two expressions are equivalent, with optional hash pre-filter.
    /// Returns 1 if equivalent, 0 otherwise.
    #[inline]
    pub(crate) unsafe fn lean_equiv_manager_is_equiv(
        mgr: *mut c_void,
        a: *mut LeanObject,
        b: *mut LeanObject,
        use_hash: u8,
    ) -> u8 {
        let m = &mut *(mgr as *mut EquivManager);
        m.is_equiv_core(a, b, use_hash != 0) as u8
    }

    /// Record that e1 and e2 are equivalent (merges their union-find nodes).
    #[inline]
    pub(crate) unsafe fn lean_equiv_manager_add_equiv(
        mgr: *mut c_void,
        e1: *mut LeanObject,
        e2: *mut LeanObject,
    ) {
        let m = &mut *(mgr as *mut EquivManager);
        let n1 = m.to_node_ref(e1);
        let n2 = m.to_node_ref(e2);
        let r1 = m.find(n1);
        let r2 = m.find(n2);
        m.merge(r1, r2);
    }
}
