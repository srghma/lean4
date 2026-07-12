/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

use crate::*;
use core::ffi::c_void;
use leanh::{
    LEAN_ARRAY_TAG, LEAN_CLOSURE_TAG, LEAN_EXTERNAL_TAG, LEAN_MPZ_TAG, LEAN_PROMISE_TAG,
    LEAN_REF_TAG, LEAN_RESERVED_TAG, LEAN_SCALAR_ARRAY_TAG, LEAN_STRING_TAG, LEAN_TASK_TAG,
    LEAN_THUNK_TAG,
};
use std::collections::{HashMap, HashSet};
use std::hash::{BuildHasherDefault, Hasher};

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
    unsafe { lean_hash_str(len, str, init_value) }
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

#[derive(Clone, Copy)]
struct ShareConsNode(*mut LeanObject);

impl Eq for ShareConsNode {}
impl PartialEq for ShareConsNode {
    fn eq(&self, other: &Self) -> bool {
        unsafe { lean_sharecommon_eq(self.0, other.0) }
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

unsafe fn sharecommon_state_new(tc: *mut LeanObject, s: *mut LeanObject) -> ShareCommonState {
    let map_find = lean_ctor_get(tc, 1);
    let map_insert = lean_ctor_get(tc, 2);
    let set_find = lean_ctor_get(tc, 3);
    let set_insert = lean_ctor_get(tc, 4);
    let map = lean_ctor_get(s, 0);
    lean_inc(map);
    let set = lean_ctor_get(s, 1);
    lean_inc(set);
    lean_dec(s);
    ShareCommonState {
        map_find,
        map_insert,
        set_find,
        set_insert,
        map,
        set,
    }
}

unsafe fn sharecommon_state_pack(
    state: &mut ShareCommonState,
    a: *mut LeanObject,
) -> *mut LeanObject {
    let pair_state = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(pair_state, 0, state.map);
    lean_ctor_set(pair_state, 1, state.set);
    state.map = lean_box(0);
    state.set = lean_box(0);

    let r = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(r, 0, a);
    lean_ctor_set(r, 1, pair_state);
    r
}

unsafe fn sharecommon_state_map_find(
    state: &ShareCommonState,
    k: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(state.map_find);
    lean_inc(state.map);
    lean_inc(k);
    lean_apply_2(state.map_find, state.map, k)
}

unsafe fn sharecommon_state_map_insert(
    state: &mut ShareCommonState,
    k: *mut LeanObject,
    v: *mut LeanObject,
) {
    lean_inc(state.map_insert);
    state.map = lean_apply_3(state.map_insert, state.map, k, v);
}

unsafe fn sharecommon_state_set_find(
    state: &ShareCommonState,
    o: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(state.set_find);
    lean_inc(state.set);
    lean_inc(o);
    lean_apply_2(state.set_find, state.set, o)
}

unsafe fn sharecommon_state_set_insert(state: &mut ShareCommonState, o: *mut LeanObject) {
    lean_inc(state.set_insert);
    state.set = lean_apply_2(state.set_insert, state.set, o);
}

struct ShareCommonFn {
    state: ShareCommonState,
    children: Vec<*mut LeanObject>,
    todo: Vec<*mut LeanObject>,
}

unsafe fn sharecommon_fn_push_child(this: &mut ShareCommonFn, a: *const LeanObject) -> bool {
    if lean_is_scalar(a) {
        this.children.push(a as *mut LeanObject);
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
        this.children.push(a as *mut LeanObject);
        return true;
    }

    let o = sharecommon_state_map_find(&this.state, a as *mut LeanObject);
    if o != lean_box(0) {
        let r = lean_ctor_get(o, 0);
        this.children.push(r);
        lean_dec(o);
        return true;
    }

    this.todo.push(a as *mut LeanObject);
    false
}

unsafe fn sharecommon_fn_save(
    this: &mut ShareCommonFn,
    a: *mut LeanObject,
    mut new_a: *mut LeanObject,
) {
    assert!(!this.todo.is_empty());
    assert_eq!(this.todo.last().copied(), Some(a));
    this.todo.pop();

    let opt_new_r = sharecommon_state_set_find(&this.state, new_a);
    if opt_new_r != lean_box(0) {
        lean_dec(new_a);
        new_a = lean_ctor_get(opt_new_r, 0);
        lean_inc(new_a);
        lean_dec(opt_new_r);
        lean_inc(a);
        sharecommon_state_map_insert(&mut this.state, a, new_a);
    } else {
        lean_inc(a);
        lean_inc_n(new_a, 3);
        sharecommon_state_set_insert(&mut this.state, new_a);
        sharecommon_state_map_insert(&mut this.state, a, new_a);
        sharecommon_state_map_insert(&mut this.state, new_a, new_a);
    }
}

unsafe fn sharecommon_fn_visit_array(this: &mut ShareCommonFn, a: *mut LeanObject) {
    this.children.clear();
    let mut missing_children = false;
    let sz = lean_array_size(a);
    for i in 0..sz {
        if !sharecommon_fn_push_child(this, lean_array_get(a, i)) {
            missing_children = true;
        }
    }
    if missing_children {
        return;
    }
    let new_a = lean_alloc_array(sz, sz);
    let array_data_ptr = (new_a as *mut u8).add(24) as *mut *mut LeanObject;
    for i in 0..sz {
        let child = this.children[i];
        lean_inc(child);
        array_data_ptr.add(i).write(child);
    }
    sharecommon_fn_save(this, a, new_a);
}

unsafe fn sharecommon_fn_visit_sarray(this: &mut ShareCommonFn, a: *mut LeanObject) {
    let sz = lean_sarray_size(a);
    let other = (*a).other;
    let new_a = lean_alloc_sarray(other as u32, sz, sz);
    let dest = lean_sarray_cptr(new_a).cast_mut();
    let src = lean_sarray_cptr(a);
    libc::memcpy(dest.cast(), src.cast(), (other as usize) * sz);
    sharecommon_fn_save(this, a, new_a);
}

unsafe fn sharecommon_fn_visit_string(this: &mut ShareCommonFn, a: *mut LeanObject) {
    let sz = lean_string_size(a);
    let len = lean_string_length(a);
    let new_a = lean_alloc_string(sz, sz, len);
    let dest = lean_string_cstr(new_a).cast_mut();
    let src = lean_string_cstr(a);
    libc::memcpy(dest.cast(), src.cast(), sz);
    sharecommon_fn_save(this, a, new_a);
}

unsafe fn sharecommon_fn_visit_mpz(this: &mut ShareCommonFn, a: *mut LeanObject) {
    let new_a = lean_alloc_mpz_from_mpz(a);
    sharecommon_fn_save(this, a, new_a);
}

unsafe fn sharecommon_fn_visit_ctor(this: &mut ShareCommonFn, a: *mut LeanObject) {
    this.children.clear();
    let num_objs = (*a).other as usize;
    let mut missing_child = false;
    for i in 0..num_objs {
        if !sharecommon_fn_push_child(this, lean_ctor_get(a, i)) {
            missing_child = true;
        }
    }
    if missing_child {
        return;
    }
    let tag = lean_ptr_tag(a) as u32;
    unsafe extern "C" {
        fn lean_object_byte_size(o: *mut LeanObject) -> usize;
    }
    let sz = lean_object_byte_size(a);
    let scalar_offset =
        core::mem::size_of::<LeanObject>() + num_objs * core::mem::size_of::<*mut LeanObject>();
    let scalar_sz = sz.saturating_sub(scalar_offset);
    let new_a = lean_alloc_ctor(tag, num_objs as u32, scalar_sz as u32);
    for i in 0..num_objs {
        let child = this.children[i];
        lean_inc(child);
        lean_ctor_set(new_a, i as u32, child);
    }
    if scalar_sz > 0 {
        let dest = (new_a as *mut u8).add(scalar_offset);
        let src = (a as *const u8).add(scalar_offset);
        libc::memcpy(dest.cast(), src.cast(), scalar_sz);
    }
    sharecommon_fn_save(this, a, new_a);
}

// Now, sharecommon_quick_fn state
pub struct RustShareCommonQuick {
    cache: ShareCache,
    set: ShareSet,
    check_set: bool,
}

fn sharecommon_quick_new(check_set: bool) -> RustShareCommonQuick {
    RustShareCommonQuick {
        cache: ShareCache::default(),
        set: ShareSet::default(),
        check_set,
    }
}

fn sharecommon_quick_set_check_set(this: &mut RustShareCommonQuick, check_set: bool) {
    this.check_set = check_set;
}

unsafe fn sharecommon_quick_check_cache(
    this: &mut RustShareCommonQuick,
    a: *mut LeanObject,
) -> *mut LeanObject {
    if (*a).rc != 1 {
        if let Some(&cached) = this.cache.get(&(a as usize)) {
            let res = cached as *mut LeanObject;
            lean_inc(res);
            return res;
        }
        if this.check_set {
            if let Some(node) = this.set.get(&ShareConsNode(a)) {
                let res = node.0;
                lean_inc(res);
                return res;
            }
        }
    }
    std::ptr::null_mut()
}

unsafe fn sharecommon_quick_save(
    this: &mut RustShareCommonQuick,
    a: *mut LeanObject,
    new_a: *mut LeanObject,
) -> *mut LeanObject {
    let node = ShareConsNode(new_a);
    let result = if let Some(existing) = this.set.get(&node) {
        let res = existing.0;
        lean_dec(new_a);
        lean_inc(res);
        res
    } else {
        this.set.insert(node);
        new_a
    };
    if (*a).rc != 1 {
        this.cache.insert(a as usize, result as usize);
    }
    result
}

unsafe fn sharecommon_quick_visit_terminal(
    this: &mut RustShareCommonQuick,
    a: *mut LeanObject,
) -> *mut LeanObject {
    let node = ShareConsNode(a);
    let res = if let Some(existing) = this.set.get(&node) {
        existing.0
    } else {
        this.set.insert(node);
        a
    };
    lean_inc(res);
    res
}

unsafe fn sharecommon_quick_visit_array(
    this: &mut RustShareCommonQuick,
    a: *mut LeanObject,
) -> *mut LeanObject {
    let r = sharecommon_quick_check_cache(this, a);
    if !r.is_null() {
        return r;
    }
    let sz = lean_array_size(a);
    let new_a = lean_alloc_array(sz, sz);
    let array_data_ptr = (new_a as *mut u8).add(24) as *mut *mut LeanObject;
    for i in 0..sz {
        let child = sharecommon_quick_visit(this, lean_array_get(a, i));
        array_data_ptr.add(i).write(child);
    }
    sharecommon_quick_save(this, a, new_a)
}

unsafe fn sharecommon_quick_visit_ctor(
    this: &mut RustShareCommonQuick,
    a: *mut LeanObject,
) -> *mut LeanObject {
    let r = sharecommon_quick_check_cache(this, a);
    if !r.is_null() {
        return r;
    }
    let num_objs = (*a).other as usize;
    let tag = lean_ptr_tag(a) as u32;
    unsafe extern "C" {
        fn lean_object_byte_size(o: *mut LeanObject) -> usize;
    }
    let sz = lean_object_byte_size(a);
    let scalar_offset =
        core::mem::size_of::<LeanObject>() + num_objs * core::mem::size_of::<*mut LeanObject>();
    let scalar_sz = sz.saturating_sub(scalar_offset);
    let new_a = lean_alloc_ctor(tag, num_objs as u32, scalar_sz as u32);
    for i in 0..num_objs {
        lean_ctor_set(
            new_a,
            i as u32,
            sharecommon_quick_visit(this, lean_ctor_get(a, i)),
        );
    }
    if scalar_sz > 0 {
        let dest = (new_a as *mut u8).add(scalar_offset);
        let src = (a as *const u8).add(scalar_offset);
        libc::memcpy(dest.cast(), src.cast(), scalar_sz);
    }
    sharecommon_quick_save(this, a, new_a)
}

unsafe fn sharecommon_quick_visit(
    this: &mut RustShareCommonQuick,
    a: *mut LeanObject,
) -> *mut LeanObject {
    if lean_is_scalar(a) {
        return a;
    }
    match lean_ptr_tag(a) {
        LEAN_CLOSURE_TAG | LEAN_THUNK_TAG | LEAN_TASK_TAG | LEAN_PROMISE_TAG | LEAN_REF_TAG
        | LEAN_EXTERNAL_TAG | LEAN_RESERVED_TAG => {
            lean_inc(a);
            a
        }
        LEAN_MPZ_TAG | LEAN_SCALAR_ARRAY_TAG | LEAN_STRING_TAG => {
            sharecommon_quick_visit_terminal(this, a)
        }
        LEAN_ARRAY_TAG => sharecommon_quick_visit_array(this, a),
        _ => sharecommon_quick_visit_ctor(this, a),
    }
}

pub unsafe fn lean_sharecommon_quick_with_check_set(
    a: *mut LeanObject,
    check_set: bool,
) -> *mut LeanObject {
    let mut quick = sharecommon_quick_new(check_set);
    sharecommon_quick_visit(&mut quick, a)
}

// FFI exports for sharecommon_persistent_fn
pub struct RustShareCommonPersistent {
    quick: RustShareCommonQuick,
    saved: Vec<*mut LeanObject>,
}

pub fn lean_sharecommon_persistent_create(check_set: bool) -> *mut c_void {
    let state = Box::new(RustShareCommonPersistent {
        quick: sharecommon_quick_new(check_set),
        saved: Vec::new(),
    });
    Box::into_raw(state).cast()
}

pub unsafe fn lean_sharecommon_persistent_free(state: *mut c_void) {
    if !state.is_null() {
        let state = Box::from_raw(state.cast::<RustShareCommonPersistent>());
        for &obj in &state.saved {
            lean_dec(obj);
        }
    }
}

pub unsafe fn lean_sharecommon_persistent_set_check_set(state: *mut c_void, check_set: bool) {
    let state = &mut *state.cast::<RustShareCommonPersistent>();
    sharecommon_quick_set_check_set(&mut state.quick, check_set);
}

pub unsafe fn lean_sharecommon_persistent_run(
    state: *mut c_void,
    e: *mut LeanObject,
) -> *mut LeanObject {
    let state = &mut *state.cast::<RustShareCommonPersistent>();
    let r = sharecommon_quick_check_cache(&mut state.quick, e);
    if !r.is_null() {
        return r;
    }
    lean_inc(e);
    state.saved.push(e);
    let r = sharecommon_quick_visit(&mut state.quick, e);
    lean_inc(r);
    state.saved.push(r);
    r
}
