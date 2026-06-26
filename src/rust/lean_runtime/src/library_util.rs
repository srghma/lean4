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
use crate::*;

pub(crate) mod library_util_impl {
    use super::*;
    use core::ffi::c_char;
    use core::ptr;
    use core::sync::atomic::{AtomicBool, AtomicPtr, Ordering};

    include!(concat!(env!("OUT_DIR"), "/lean_version.rs"));

    extern "C" {
        fn lean_expr_mk_const(name: *mut LeanObject, lvls: *mut LeanObject) -> *mut LeanObject;
    }

    static INITIALIZED: AtomicBool = AtomicBool::new(false);
    static BOOL_TRUE: AtomicPtr<LeanObject> = AtomicPtr::new(ptr::null_mut());
    static BOOL_FALSE: AtomicPtr<LeanObject> = AtomicPtr::new(ptr::null_mut());
    static UTIL_FRESH: AtomicPtr<LeanObject> = AtomicPtr::new(ptr::null_mut());

    static SHORT_VERSION_STRING: &[u8] = LEAN_VERSION_STRING_CSTR;

    unsafe fn initialize_library_util_impl() {
        let bool_false_name = *get_bool_false_name();
        let bool_true_name = *get_bool_true_name();

        let false_expr = lean_expr_mk_const(bool_false_name.obj, lean_box(0));
        let true_expr = lean_expr_mk_const(bool_true_name.obj, lean_box(0));

        lean_mark_persistent(false_expr);
        lean_mark_persistent(true_expr);

        BOOL_FALSE.store(false_expr, Ordering::Release);
        BOOL_TRUE.store(true_expr, Ordering::Release);

        let util_fresh = mk_name("_util_fresh");
        lean_mark_persistent(util_fresh.obj);
        UTIL_FRESH.store(util_fresh.obj, Ordering::Release);
        lean_register_name_generator_prefix(util_fresh.obj);
    }

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

    unsafe fn ensure_initialized() {
        if INITIALIZED
            .compare_exchange(false, true, Ordering::AcqRel, Ordering::Acquire)
            .is_ok()
        {
            initialize_library_util_impl();
        }
    }

    #[cfg_attr(
        feature = "export-runtime-ffi",
        export_name = "_ZN4lean23initialize_library_utilEv"
    )]
    pub unsafe extern "C" fn lean_initialize_library_util() {
        if INITIALIZED
            .compare_exchange(false, true, Ordering::AcqRel, Ordering::Acquire)
            .is_ok()
        {
            initialize_library_util_impl();
        }
    }

    #[cfg_attr(
        feature = "export-runtime-ffi",
        export_name = "_ZN4lean21finalize_library_utilEv"
    )]
    pub unsafe extern "C" fn lean_finalize_library_util() {
        if INITIALIZED.load(Ordering::Acquire) {
            finalize_library_util_impl();
        }
    }

    #[inline]
    pub(crate) unsafe fn lean_mk_bool_true() -> *mut LeanObject {
        ensure_initialized();
        let result = BOOL_TRUE.load(Ordering::Acquire);
        lean_inc(result);
        result
    }

    #[inline]
    pub(crate) unsafe fn lean_mk_bool_false() -> *mut LeanObject {
        ensure_initialized();
        let result = BOOL_FALSE.load(Ordering::Acquire);
        lean_inc(result);
        result
    }

    #[inline]
    pub(crate) fn lean_short_version_string() -> *const c_char {
        SHORT_VERSION_STRING.as_ptr().cast::<c_char>()
    }
}
