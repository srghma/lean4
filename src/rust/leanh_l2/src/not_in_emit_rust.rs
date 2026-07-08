use core::ffi::c_void;
use core::ptr;
use core::sync::atomic::{AtomicI32, Ordering};
use libmimalloc_sys as mi;
use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

use crate::datatypes::{
    LeanArrayObject, LeanClosureObject, LeanExternalObject, LeanMpzObject, LeanObject,
    LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, ObjInitFn, Size, LEAN_ARRAY_TAG, LEAN_CLOSURE_TAG,
    LEAN_EXTERNAL_TAG, LEAN_MAX_CTOR_TAG, LEAN_MPZ_TAG, LEAN_PROMISE_TAG, LEAN_REF_TAG,
    LEAN_SCALAR_ARRAY_TAG, LEAN_STRING_TAG, LEAN_TASK_TAG, LEAN_THUNK_TAG,
};

use crate::in_emit_rust::{lean_is_scalar, lean_unbox};
use crate::runtime_object_panic::lean_internal_panic_out_of_memory;
use crate::runtime_object_rc::{lean_alloc_object, lean_mark_persistent};
use crate::runtime_object_task::{lean_runtime_deactivate_promise, lean_runtime_deactivate_task};

// NOT IN EmitRust; here because it is used in `lean_alloc_ctor`, `lean_box_float`, `lean_box_float32`, `lean_box_uint32`, and 3 more EmitRust functions.
#[inline]
pub fn lean_align(v: usize, a: usize) -> usize {
    (v / a) * a + a * (!v.is_multiple_of(a)) as usize
}

// NOT IN EmitRust; here because it is used in `lean_alloc_closure`, `lean_alloc_ctor`, `lean_box_float`, `lean_box_float32`, and 6 more EmitRust functions.
#[inline]
pub unsafe fn lean_global_alloc(size: usize) -> *mut u8 {
    unsafe {
        let layout = Layout::from_size_align(size.max(1), core::mem::align_of::<usize>()).unwrap();
        let mem = alloc(layout);
        if mem.is_null() {
            handle_alloc_error(layout);
        }
        mem
    }
}

// NOT IN EmitRust; here because it is used in `lean_alloc_closure`, `lean_apply_m`, `lean_ctor_release`, `lean_dec`, and 5 more EmitRust functions.
#[inline]
pub unsafe fn lean_global_dealloc(mem: *mut u8, size: usize) {
    unsafe {
        let layout = Layout::from_size_align(size.max(1), core::mem::align_of::<usize>()).unwrap();
        dealloc(mem, layout);
    }
}

// NOT IN EmitRust; here because it is used in `lean_dec_ref_known`.
#[inline]
pub unsafe fn lean_is_ref(obj: *mut LeanObject) -> bool {
    unsafe { lean_ptr_tag(obj) == LEAN_REF_TAG }
}

// NOT IN EmitRust; here because it is used in `lean_mk_string`, `lean_mk_string_unchecked`.
#[inline]
pub unsafe fn lean_string_data(obj: *mut LeanObject) -> *mut u8 {
    unsafe {
        (*(obj as *mut LeanStringObject<0>))
            .m_data
            .as_mut_ptr()
            .cast::<u8>()
    }
}

// NOT IN EmitRust; here because it is used in `lean_obj_once`.
#[inline]
pub fn lock_once_cell(lock: &AtomicI32) {
    while lock
        .compare_exchange(0, 1, Ordering::Acquire, Ordering::Relaxed)
        .is_err()
    {
        std::thread::yield_now();
    }
}

// NOT IN EmitRust; here because it is used in `lean_obj_once`.
#[inline]
pub fn unlock_once_cell(lock: &AtomicI32) {
    lock.store(0, Ordering::Release);
}

// NOT IN EmitRust; here because it is used in `lean_float_once`, `lean_float32_once`, `lean_uint8_once`, `lean_uint16_once`, and 3 more EmitRust functions.
#[inline]
pub unsafe fn run_once<T: Copy>(loc: *mut T, tok: *mut LeanOnceCell, init: unsafe fn() -> T) -> T {
    unsafe {
        let tok = &*tok;
        lock_once_cell(&tok.lock);
        if tok.state.load(Ordering::Acquire) != 1 {
            *loc = init();
            tok.state.store(1, Ordering::Release);
        }
        let result = *loc;
        unlock_once_cell(&tok.lock);
        result
    }
}

#[inline(always)]
pub unsafe fn lean_has_rc(o: *mut LeanObject) -> bool {
    unsafe { (*o).rc != 0 }
}

// NOT IN EmitRust; here because it is used in `lean_obj_once`.
#[inline]
pub unsafe fn lean_obj_once_cold(
    loc: *mut *mut LeanObject,
    tok: *mut LeanOnceCell,
    init: ObjInitFn,
) -> *mut LeanObject {
    unsafe {
        let tok_ref = &*tok;
        lock_once_cell(&tok_ref.lock);
        if tok_ref.state.load(Ordering::Acquire) != 1 {
            *loc = init();
            lean_mark_persistent(*loc);
            tok_ref.state.store(1, Ordering::Release);
        }
        let result = *loc;
        unlock_once_cell(&tok_ref.lock);
        result
    }
}
