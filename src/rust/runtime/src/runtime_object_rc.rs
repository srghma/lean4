/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

// Port of the RC / deallocation / object graph traversal section of
// src/runtime/object.cpp.

pub(crate) mod runtime_object_rc_impl {
    use crate::*;
    use core::ffi::{CStr, c_char, c_int, c_long, c_uchar, c_uint, c_void};
    use core::ffi::c_void;
    use core::ptr;
    use core::sync::atomic::{AtomicI32, Ordering};
    use leanh::{
        LEAN_ARRAY_TAG, LEAN_CLOSURE_TAG, LEAN_EXTERNAL_TAG, LEAN_MAX_CTOR_TAG, LEAN_MPZ_TAG,
        LEAN_PROMISE_TAG, LEAN_REF_TAG, LEAN_SCALAR_ARRAY_TAG, LEAN_STRING_TAG, LEAN_TASK_TAG,
        LEAN_THUNK_TAG, LeanArrayObject, LeanClosureObject, LeanExternalClass, LeanExternalObject,
        LeanMpzObject, LeanObject, LeanPromiseObject, LeanRefObject, LeanScalarArray,
        LeanStringObject, LeanTaskObject, LeanThunkObject, MpzT,
    };
    #[cfg(all(lean_has_address_sanitizer, unix))]
    use libloading::os::unix::Library as UnixLibrary;
    use libmimalloc_sys as mi;

    const LEAN_MAX_SMALL_OBJECT_SIZE: usize = 4096;

    #[cfg(not(all(lean_has_address_sanitizer, unix)))]
    unsafe fn ignore_lsan_object(_: *mut c_void) {}

    unsafe extern "C" {
        fn lean_internal_panic(msg: *const i8) -> !;
        fn lean_task_get(task: *mut LeanObject) -> *mut LeanObject;
        fn lean_runtime_deactivate_task(task: *mut LeanTaskObject);
        fn lean_runtime_deactivate_promise(promise: *mut LeanPromiseObject);
    }

    pub unsafe fn lean_alloc_ctor_memory_export(sz: usize) -> *mut LeanObject {
        lean_alloc_ctor_memory(sz)
    }
}
