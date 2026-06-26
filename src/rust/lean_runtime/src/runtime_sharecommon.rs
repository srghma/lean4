/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

use crate::*;

pub(crate) mod runtime_sharecommon_impl {
    use super::*;
    use core::ffi::c_void;
    use std::collections::{HashMap, HashSet};
    use std::hash::{BuildHasherDefault, Hasher};

    const LEAN_PROMISE_TAG: u8 = 244;
    const LEAN_CLOSURE_TAG: u8 = 245;
    const LEAN_ARRAY_TAG: u8 = 246;
    const LEAN_SCALAR_ARRAY_TAG: u8 = 248;
    const LEAN_STRING_TAG: u8 = 249;
    const LEAN_MPZ_TAG: u8 = 250;
    const LEAN_THUNK_TAG: u8 = 251;
    const LEAN_TASK_TAG: u8 = 252;
    const LEAN_REF_TAG: u8 = 253;
    const LEAN_EXTERNAL_TAG: u8 = 254;
    const LEAN_RESERVED_TAG: u8 = 255;

    extern "C" {
        fn lean_object_data_byte_size(o: *mut LeanObject) -> usize;
        fn lean_mpz_hash(o: *mut LeanObject) -> u32;
        fn lean_mpz_eq(o1: *mut LeanObject, o2: *mut LeanObject) -> u8;
        fn lean_runtime_hash_str(len: usize, str: *const u8, init_value: u64) -> u64;
        fn lean_apply_2(
            f: *mut LeanObject,
            a1: *mut LeanObject,
            a2: *mut LeanObject,
        ) -> *mut LeanObject;
        fn lean_apply_3(
            f: *mut LeanObject,
            a1: *mut LeanObject,
            a2: *mut LeanObject,
            a3: *mut LeanObject,
        ) -> *mut LeanObject;
    }

    #[inline]
    fn hash_combine(mut h: u64, mut k: u64) -> u64 {
        let m: u64 = 0xc6a4a7935bd1e995;
        let r = 47;
        k = k.wrapping_mul(m);
        k ^= k >> r;
        k ^= m;
        h ^= k;
        h = h.wrapping_mul(m);
        h
    }

    #[inline]
    fn hash_str(len: usize, str: *const u8, init_value: u64) -> u64 {
        unsafe { lean_runtime_hash_str(len, str, init_value) }
    }

    #[derive(Default)]
    struct IdentityHasher(u64);

    impl Hasher for IdentityHasher {
        fn finish(&self) -> u64 {
            self.0
        }

        fn write(&mut self, bytes: &[u8]) {
            let mut h = 0u64;
            let mut shift = 0;
            for &byte in bytes.iter().take(8) {
                h |= (byte as u64) << shift;
                shift += 8;
            }
            self.0 = h;
        }

        fn write_usize(&mut self, i: usize) {
            self.0 = i as u64;
        }

        fn write_u64(&mut self, i: u64) {
            self.0 = i;
        }
    }

    type LeanHashBuilder = BuildHasherDefault<IdentityHasher>;
    type ShareCache = HashMap<usize, usize, LeanHashBuilder>;
    type ShareSet = HashSet<ShareConsNode, LeanHashBuilder>;

    #[inline]
    pub(crate) unsafe fn lean_sharecommon_eq(o1: *mut LeanObject, o2: *mut LeanObject) -> u8 {
        if o1 == o2 {
            return 1;
        }
        let sz1 = lean_object_data_byte_size(o1);
        let sz2 = lean_object_data_byte_size(o2);
        if sz1 != sz2 {
            return 0;
        }
        let tag = lean_ptr_tag(o1);
        if tag != lean_ptr_tag(o2) {
            return 0;
        }
        if (*o1).other != (*o2).other {
            return 0;
        }
        if tag == LEAN_MPZ_TAG {
            lean_mpz_eq(o1, o2)
        } else {
            let header_sz = core::mem::size_of::<LeanObject>();
            let body1 = (o1 as *const u8).add(header_sz);
            let body2 = (o2 as *const u8).add(header_sz);
            let len = sz1.saturating_sub(header_sz);
            if len == 0 {
                return 1;
            }
            let res = libc::memcmp(body1.cast(), body2.cast(), len);
            if res == 0 {
                1
            } else {
                0
            }
        }
    }

    #[inline]
    pub(crate) unsafe fn lean_sharecommon_hash(o: *mut LeanObject) -> u64 {
        let sz = lean_object_data_byte_size(o);
        let header_sz = core::mem::size_of::<LeanObject>();
        let tag = lean_ptr_tag(o);
        if tag == LEAN_MPZ_TAG {
            let h_mpz = lean_mpz_hash(o) as u64;
            hash_combine(tag as u64, h_mpz)
        } else {
            let init = hash_combine(tag as u64, (*o).other as u64);
            let body = (o as *const u8).add(header_sz);
            let len = sz.saturating_sub(header_sz);
            hash_str(len, body, init)
        }
    }

    #[derive(Clone, Copy)]
    struct ShareConsNode(*mut LeanObject);

    impl Eq for ShareConsNode {}
    impl PartialEq for ShareConsNode {
        fn eq(&self, other: &Self) -> bool {
            unsafe { lean_sharecommon_eq(self.0, other.0) != 0 }
        }
    }
    impl std::hash::Hash for ShareConsNode {
        fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
            let h = unsafe { lean_sharecommon_hash(self.0) };
            state.write_u64(h);
        }
    }

    // Helper for lean_state_sharecommon logic (non-quick stateful)
    struct ShareCommonState {
        map_find: *mut LeanObject,
        map_insert: *mut LeanObject,
        set_find: *mut LeanObject,
        set_insert: *mut LeanObject,
        map: *mut LeanObject,
        set: *mut LeanObject,
    }

    impl ShareCommonState {
        unsafe fn new(tc: *mut LeanObject, s: *mut LeanObject) -> Self {
            let map_find = lean_ctor_get(tc, 1);
            let map_insert = lean_ctor_get(tc, 2);
            let set_find = lean_ctor_get(tc, 3);
            let set_insert = lean_ctor_get(tc, 4);
            let map = lean_ctor_get(s, 0);
            lean_inc(map);
            let set = lean_ctor_get(s, 1);
            lean_inc(set);
            lean_dec(s);
            Self {
                map_find,
                map_insert,
                set_find,
                set_insert,
                map,
                set,
            }
        }

        unsafe fn pack(&mut self, a: *mut LeanObject) -> *mut LeanObject {
            let pair_state = lean_runtime_alloc_ctor(0, 2, 0);
            lean_runtime_ctor_set(pair_state, 0, self.map);
            lean_runtime_ctor_set(pair_state, 1, self.set);
            self.map = lean_box(0);
            self.set = lean_box(0);

            let r = lean_runtime_alloc_ctor(0, 2, 0);
            lean_runtime_ctor_set(r, 0, a);
            lean_runtime_ctor_set(r, 1, pair_state);
            r
        }

        unsafe fn map_find(&self, k: *mut LeanObject) -> *mut LeanObject {
            lean_inc(self.map_find);
            lean_inc(self.map);
            lean_inc(k);
            lean_apply_2(self.map_find, self.map, k)
        }

        unsafe fn map_insert(&mut self, k: *mut LeanObject, v: *mut LeanObject) {
            lean_inc(self.map_insert);
            self.map = lean_apply_3(self.map_insert, self.map, k, v);
        }

        unsafe fn set_find(&self, o: *mut LeanObject) -> *mut LeanObject {
            lean_inc(self.set_find);
            lean_inc(self.set);
            lean_inc(o);
            lean_apply_2(self.set_find, self.set, o)
        }

        unsafe fn set_insert(&mut self, o: *mut LeanObject) {
            lean_inc(self.set_insert);
            self.set = lean_apply_2(self.set_insert, self.set, o);
        }
    }

    struct ShareCommonFn {
        state: ShareCommonState,
        children: Vec<*mut LeanObject>,
        todo: Vec<*mut LeanObject>,
    }

    impl ShareCommonFn {
        unsafe fn push_child(&mut self, a: *mut LeanObject) -> bool {
            if lean_is_scalar(a) {
                self.children.push(a);
                return true;
            }
            let tag = lean_ptr_tag(a);
            if tag == LEAN_RESERVED_TAG {
                panic!("unreachable");
            }
            if tag == LEAN_THUNK_TAG
                || tag == LEAN_TASK_TAG
                || tag == LEAN_REF_TAG
                || tag == LEAN_EXTERNAL_TAG
                || tag == LEAN_CLOSURE_TAG
                || tag == LEAN_PROMISE_TAG
            {
                self.children.push(a);
                return true;
            }

            let o = self.state.map_find(a);
            if o != lean_box(0) {
                let r = lean_ctor_get(o, 0);
                self.children.push(r);
                lean_dec(o);
                return true;
            }

            self.todo.push(a);
            false
        }

        unsafe fn save(&mut self, a: *mut LeanObject, mut new_a: *mut LeanObject) {
            assert!(!self.todo.is_empty());
            assert_eq!(self.todo.last().copied(), Some(a));
            self.todo.pop();

            let opt_new_r = self.state.set_find(new_a);
            if opt_new_r != lean_box(0) {
                lean_dec(new_a);
                new_a = lean_ctor_get(opt_new_r, 0);
                lean_inc(new_a);
                lean_dec(opt_new_r);
                lean_inc(a);
                self.state.map_insert(a, new_a);
            } else {
                lean_inc(a);
                super::lean_inc_n(new_a, 3);
                self.state.set_insert(new_a);
                self.state.map_insert(a, new_a);
                self.state.map_insert(new_a, new_a);
            }
        }

        unsafe fn visit_array(&mut self, a: *mut LeanObject) {
            self.children.clear();
            let mut missing_children = false;
            let sz = lean_array_size(a);
            for i in 0..sz {
                if !self.push_child(lean_array_get_core(a, i)) {
                    missing_children = true;
                }
            }
            if missing_children {
                return;
            }
            let new_a = lean_alloc_array(sz, sz);
            let array_data_ptr = (new_a as *mut u8).add(24) as *mut *mut LeanObject;
            for i in 0..sz {
                let child = self.children[i];
                lean_inc(child);
                array_data_ptr.add(i).write(child);
            }
            self.save(a, new_a);
        }

        unsafe fn visit_sarray(&mut self, a: *mut LeanObject) {
            let sz = lean_sarray_size(a);
            let other = (*a).other;
            let new_a = lean_alloc_sarray(other as u32, sz, sz);
            let dest = lean_sarray_cptr(new_a).cast_mut();
            let src = lean_sarray_cptr(a);
            libc::memcpy(dest.cast(), src.cast(), (other as usize) * sz);
            self.save(a, new_a);
        }

        unsafe fn visit_string(&mut self, a: *mut LeanObject) {
            let sz = super::lean_string_size(a);
            let len = super::lean_string_len(a);
            let new_a = super::lean_alloc_string(sz, sz, len);
            let dest = lean_string_cstr(new_a).cast_mut();
            let src = lean_string_cstr(a);
            libc::memcpy(dest.cast(), src.cast(), sz);
            self.save(a, new_a);
        }

        unsafe fn visit_mpz(&mut self, a: *mut LeanObject) {
            // Wait, we need to allocate a new mpz. How? Let's check object.cpp:
            // object * alloc_mpz(mpz const & m)
            // But we don't have GMP/mpz functions in Rust. Wait, we can declare a C++ helper or FFI function:
            // extern "C" object * lean_alloc_mpz_from_mpz(object * o);
            // Wait, in object.cpp:
            // extern "C" LEAN_EXPORT object * lean_alloc_mpz_from_mpz(object * o) { return alloc_mpz(to_mpz(o)->m_value); }
            // Let's check if we can declare a function in object.cpp for this! Yes!
            // Wait, we can just define `lean_alloc_mpz_from_mpz` in object.cpp, or let's check:
            // "MPZ" constructor allocates a new MPZ by copying. Since we added lean_mpz_eq/hash, let's also add lean_alloc_mpz_from_mpz to object.cpp.
            // Let's do that!
            extern "C" {
                fn lean_alloc_mpz_from_mpz(o: *mut LeanObject) -> *mut LeanObject;
            }
            let new_a = lean_alloc_mpz_from_mpz(a);
            self.save(a, new_a);
        }

        unsafe fn visit_ctor(&mut self, a: *mut LeanObject) {
            self.children.clear();
            // How do we get the number of object fields?
            // In lean.h: static inline unsigned lean_ctor_num_objs(lean_object * o) { return lean_ptr_other(o); }
            // lean_ptr_other returns o->m_other. In our LeanObject, this is `other`.
            let num_objs = (*a).other as usize;
            let mut missing_child = false;
            for i in 0..num_objs {
                if !self.push_child(lean_ctor_get(a, i)) {
                    missing_child = true;
                }
            }
            if missing_child {
                return;
            }
            let tag = lean_ptr_tag(a) as u32;
            // object size: how to get it?
            // In object.h: unsigned lean_object_byte_size(lean_object * o);
            extern "C" {
                fn lean_object_byte_size(o: *mut LeanObject) -> usize;
            }
            let sz = lean_object_byte_size(a);
            let scalar_offset = core::mem::size_of::<LeanObject>()
                + num_objs * core::mem::size_of::<*mut LeanObject>();
            let scalar_sz = sz.saturating_sub(scalar_offset);
            let new_a = lean_runtime_alloc_ctor(tag, num_objs as u32, scalar_sz as u32);
            for i in 0..num_objs {
                let child = self.children[i];
                lean_inc(child);
                lean_runtime_ctor_set(new_a, i as u32, child);
            }
            if scalar_sz > 0 {
                let dest = (new_a as *mut u8).add(scalar_offset);
                let src = (a as *const u8).add(scalar_offset);
                libc::memcpy(dest.cast(), src.cast(), scalar_sz);
            }
            self.save(a, new_a);
        }
    }

    #[inline]
    pub(crate) unsafe fn lean_state_sharecommon(
        tc: *mut LeanObject,
        s: *mut LeanObject,
        a: *mut LeanObject,
    ) -> *mut LeanObject {
        let state = ShareCommonState::new(tc, s);
        let mut f = ShareCommonFn {
            state,
            children: Vec::new(),
            todo: Vec::new(),
        };

        if f.push_child(a) {
            let r = f.children[0];
            lean_inc(r);
            lean_dec(a);
            return f.state.pack(r);
        }

        while !f.todo.is_empty() {
            let curr = *f.todo.last().unwrap();
            match lean_ptr_tag(curr) {
                LEAN_CLOSURE_TAG => panic!("unreachable"),
                LEAN_ARRAY_TAG => f.visit_array(curr),
                LEAN_SCALAR_ARRAY_TAG => f.visit_sarray(curr),
                LEAN_STRING_TAG => f.visit_string(curr),
                LEAN_MPZ_TAG => f.visit_mpz(curr),
                LEAN_THUNK_TAG => panic!("unreachable"),
                LEAN_TASK_TAG => panic!("unreachable"),
                LEAN_PROMISE_TAG => panic!("unreachable"),
                LEAN_REF_TAG => panic!("unreachable"),
                LEAN_EXTERNAL_TAG => panic!("unreachable"),
                LEAN_RESERVED_TAG => panic!("unreachable"),
                _ => f.visit_ctor(curr),
            }
        }

        let o = f.state.map_find(a);
        assert_ne!(o, lean_box(0));
        let r = lean_ctor_get(o, 0);
        lean_inc(r);
        lean_dec(o);
        lean_dec(a);
        f.state.pack(r)
    }

    // Now, sharecommon_quick_fn state
    pub struct RustShareCommonQuick {
        cache: ShareCache,
        set: ShareSet,
        check_set: bool,
    }

    impl RustShareCommonQuick {
        fn new(check_set: bool) -> Self {
            Self {
                cache: ShareCache::default(),
                set: ShareSet::default(),
                check_set,
            }
        }

        fn set_check_set(&mut self, check_set: bool) {
            self.check_set = check_set;
        }

        unsafe fn check_cache(&mut self, a: *mut LeanObject) -> *mut LeanObject {
            if (*a).rc != 1 {
                if let Some(&cached) = self.cache.get(&(a as usize)) {
                    let res = cached as *mut LeanObject;
                    lean_inc(res);
                    return res;
                }
                if self.check_set {
                    if let Some(node) = self.set.get(&ShareConsNode(a)) {
                        let res = node.0;
                        lean_inc(res);
                        return res;
                    }
                }
            }
            std::ptr::null_mut()
        }

        unsafe fn save(&mut self, a: *mut LeanObject, new_a: *mut LeanObject) -> *mut LeanObject {
            let node = ShareConsNode(new_a);
            let result = if let Some(existing) = self.set.get(&node) {
                let res = existing.0;
                lean_dec(new_a);
                lean_inc(res);
                res
            } else {
                self.set.insert(node);
                new_a
            };
            if (*a).rc != 1 {
                self.cache.insert(a as usize, result as usize);
            }
            result
        }

        unsafe fn visit_terminal(&mut self, a: *mut LeanObject) -> *mut LeanObject {
            let node = ShareConsNode(a);
            let res = if let Some(existing) = self.set.get(&node) {
                existing.0
            } else {
                self.set.insert(node);
                a
            };
            lean_inc(res);
            res
        }

        unsafe fn visit_array(&mut self, a: *mut LeanObject) -> *mut LeanObject {
            let r = self.check_cache(a);
            if !r.is_null() {
                return r;
            }
            let sz = lean_array_size(a);
            let new_a = lean_alloc_array(sz, sz);
            let array_data_ptr = (new_a as *mut u8).add(24) as *mut *mut LeanObject;
            for i in 0..sz {
                let child = self.visit(lean_array_get_core(a, i));
                array_data_ptr.add(i).write(child);
            }
            self.save(a, new_a)
        }

        unsafe fn visit_ctor(&mut self, a: *mut LeanObject) -> *mut LeanObject {
            let r = self.check_cache(a);
            if !r.is_null() {
                return r;
            }
            let num_objs = (*a).other as usize;
            let tag = lean_ptr_tag(a) as u32;
            extern "C" {
                fn lean_object_byte_size(o: *mut LeanObject) -> usize;
            }
            let sz = lean_object_byte_size(a);
            let scalar_offset = core::mem::size_of::<LeanObject>()
                + num_objs * core::mem::size_of::<*mut LeanObject>();
            let scalar_sz = sz.saturating_sub(scalar_offset);
            let new_a = lean_runtime_alloc_ctor(tag, num_objs as u32, scalar_sz as u32);
            for i in 0..num_objs {
                lean_runtime_ctor_set(new_a, i as u32, self.visit(lean_ctor_get(a, i)));
            }
            if scalar_sz > 0 {
                let dest = (new_a as *mut u8).add(scalar_offset);
                let src = (a as *const u8).add(scalar_offset);
                libc::memcpy(dest.cast(), src.cast(), scalar_sz);
            }
            self.save(a, new_a)
        }

        unsafe fn visit(&mut self, a: *mut LeanObject) -> *mut LeanObject {
            if lean_is_scalar(a) {
                return a;
            }
            match lean_ptr_tag(a) {
                LEAN_CLOSURE_TAG | LEAN_THUNK_TAG | LEAN_TASK_TAG | LEAN_PROMISE_TAG
                | LEAN_REF_TAG | LEAN_EXTERNAL_TAG | LEAN_RESERVED_TAG => {
                    lean_inc(a);
                    a
                }
                LEAN_MPZ_TAG | LEAN_SCALAR_ARRAY_TAG | LEAN_STRING_TAG => self.visit_terminal(a),
                LEAN_ARRAY_TAG => self.visit_array(a),
                _ => self.visit_ctor(a),
            }
        }
    }

    #[inline]
    pub(crate) unsafe fn lean_sharecommon_quick(a: *mut LeanObject) -> *mut LeanObject {
        let mut quick = RustShareCommonQuick::new(false);
        quick.visit(a)
    }

    #[inline]
    pub(crate) unsafe fn lean_sharecommon_quick_with_check_set(
        a: *mut LeanObject,
        check_set: bool,
    ) -> *mut LeanObject {
        let mut quick = RustShareCommonQuick::new(check_set);
        quick.visit(a)
    }

    // FFI exports for sharecommon_persistent_fn
    pub struct RustShareCommonPersistent {
        quick: RustShareCommonQuick,
        saved: Vec<*mut LeanObject>,
    }

    #[inline]
    pub(crate) fn lean_sharecommon_persistent_create(check_set: bool) -> *mut c_void {
        let state = Box::new(RustShareCommonPersistent {
            quick: RustShareCommonQuick::new(check_set),
            saved: Vec::new(),
        });
        Box::into_raw(state).cast()
    }

    #[inline]
    pub(crate) unsafe fn lean_sharecommon_persistent_free(state: *mut c_void) {
        if !state.is_null() {
            let state = Box::from_raw(state.cast::<RustShareCommonPersistent>());
            for &obj in &state.saved {
                lean_dec(obj);
            }
        }
    }

    #[inline]
    pub(crate) unsafe fn lean_sharecommon_persistent_set_check_set(
        state: *mut c_void,
        check_set: bool,
    ) {
        let state = &mut *state.cast::<RustShareCommonPersistent>();
        state.quick.set_check_set(check_set);
    }

    #[inline]
    pub(crate) unsafe fn lean_sharecommon_persistent_run(
        state: *mut c_void,
        e: *mut LeanObject,
    ) -> *mut LeanObject {
        let state = &mut *state.cast::<RustShareCommonPersistent>();
        let r = state.quick.check_cache(e);
        if !r.is_null() {
            return r;
        }
        lean_inc(e);
        state.saved.push(e);
        let r = state.quick.visit(e);
        lean_inc(r);
        state.saved.push(r);
        r
    }
}
