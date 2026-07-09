/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Port of src/library/util.cpp to Rust.

This file now owns the module init pair and the two value helpers that C++
still uses directly:
  - initialize_library_util / finalize_library_util
  - lean_mk_bool_true / lean_mk_bool_false
  - lean_short_version_string

The old C++ util.cpp implementation is removed.
*/

mod library_util_impl {
    use crate::*;
    use core::ffi::c_char;
    use core::ffi::{c_char, c_int, c_long, c_uchar, c_uint, c_void, CStr};
    use core::ptr;
    use core::sync::atomic::{AtomicBool, AtomicPtr, Ordering};

    include!(concat!(env!("OUT_DIR"), "/lean_version.rs"));

    static SHORT_VERSION_STRING: &[u8] = LEAN_VERSION_STRING_CSTR;

    unsafe fn finalize_library_util_impl() {
        let bool_false = BOOL_FALSE.swap(ptr::null_mut(), Ordering::AcqRel);
        if !bool_false.is_null() {
            lean_dec(bool_false);
        }

        let bool_true = BOOL_TRUE.swap(ptr::null_mut(), Ordering::AcqRel);
        if !bool_true.is_null() {
            lean_dec(bool_true);
        }

        let util_fresh = UTIL_FRESH.swap(ptr::null_mut(), Ordering::AcqRel);
        if !util_fresh.is_null() {
            lean_dec(util_fresh);
        }

        INITIALIZED.store(false, Ordering::Release);
    }

    pub unsafe fn lean_finalize_library_util() {
        if INITIALIZED.load(Ordering::Acquire) {
            finalize_library_util_impl();
        }
    }

    #[no_mangle]
    pub unsafe fn lean_mk_bool_true() -> *mut LeanObject {
        ensure_initialized();
        let result = BOOL_TRUE.load(Ordering::Acquire);
        lean_inc(result);
        result
    }

    #[no_mangle]
    pub unsafe fn lean_mk_bool_false() -> *mut LeanObject {
        ensure_initialized();
        let result = BOOL_FALSE.load(Ordering::Acquire);
        lean_inc(result);
        result
    }

    #[no_mangle]
    pub fn lean_short_version_string() -> *const c_char {
        SHORT_VERSION_STRING.as_ptr().cast::<c_char>()
    }
}
