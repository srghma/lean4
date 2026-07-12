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
