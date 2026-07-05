/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

use leanh::*;
use core::ffi::{c_char, c_int, c_long, c_uchar, c_uint, c_void, CStr};
use core::ptr;
use core::sync::atomic::{AtomicBool, AtomicI32, AtomicPtr, AtomicU32, Ordering};


pub(crate) mod runtime_io_ref_impl {
    use crate::runtime::runtime_object_panic_impl::lean_internal_panic;
    use core::sync::atomic::{AtomicPtr, Ordering};

    const LEAN_REF_TAG: u8 = 253; // duplicate in leanh at line 17 (🔁)

    #[repr(C)]
    struct LeanRefObject { // duplicate in leanh at line 20 (🔁)
        header: LeanObject,
        value: *mut LeanObject,
    }

    unsafe fn lean_set_st_header(o: *mut LeanObject, tag: u8, other: u8) {
        (*o).rc = 1;
        (*o).cs_size = 0;
        (*o).other = other;
        (*o).tag = tag;
    }

    unsafe fn lean_to_ref(o: *mut LeanObject) -> *mut LeanRefObject { // duplicate in leanh at line 32 (🔁)
        debug_assert!((*o).tag == LEAN_REF_TAG);
        o as *mut LeanRefObject
    }

    fn lean_is_mt(o: *mut LeanObject) -> bool { // duplicate in leanh at line 37 (🔁)
        unsafe { (*o).rc < 0 }
    }

    fn lean_is_persistent(o: *mut LeanObject) -> bool { // duplicate in leanh at line 41 (🔁)
        unsafe { (*o).rc == 0 }
    }

    fn ref_maybe_mt(o: *mut LeanObject) -> bool {
        lean_is_mt(o) || lean_is_persistent(o)
    }

    unsafe fn mt_ref_val_addr(o: *mut LeanObject) -> *mut AtomicPtr<LeanObject> {
        core::ptr::addr_of_mut!((*lean_to_ref(o)).value).cast::<AtomicPtr<LeanObject>>()
    }

    #[inline]
    pub(crate) unsafe fn lean_st_mk_ref(a: *mut LeanObject) -> *mut LeanObject { // [lean-audit] Lean imports from Rust ([extern]): Rust defined this function and function body is not empty (correct) (✅) | Lean: src/Init/System/ST.lean:186
        let o = crate::runtime::runtime_object_rc_impl::lean_alloc_small_object(core::mem::size_of::<
            LeanRefObject,
        >()) as *mut LeanRefObject;
        lean_set_st_header(o as *mut LeanObject, LEAN_REF_TAG, 0);
        (*o).value = a;
        o as *mut LeanObject
    }

    #[inline]
    pub(crate) unsafe fn lean_st_ref_get(ref_: *mut LeanObject) -> *mut LeanObject { // [lean-audit] Lean imports from Rust ([extern]): Rust defined this function and function body is not empty (correct) (✅) | Lean: src/Init/System/ST.lean:188
        if ref_maybe_mt(ref_) {
            let val_addr = mt_ref_val_addr(ref_);
            loop {
                let val = (*val_addr).swap(core::ptr::null_mut(), Ordering::AcqRel);
                if !val.is_null() {
                    lean_inc(val);
                    let tmp = (*val_addr).swap(val, Ordering::AcqRel);
                    if !tmp.is_null() {
                        lean_dec(tmp);
                    }
                    return val;
                }
                core::hint::spin_loop();
            }
        } else {
            let val = (*lean_to_ref(ref_)).value;
            debug_assert!(!val.is_null());
            lean_inc(val);
            val
        }
    }

    #[inline]
    pub(crate) unsafe fn lean_st_ref_take(ref_: *mut LeanObject) -> *mut LeanObject { // [lean-audit] Lean imports from Rust ([extern]): Rust defined this function and function body is not empty (correct) (✅) | Lean: src/Init/System/ST.lean:194
        if ref_maybe_mt(ref_) {
            let val_addr = mt_ref_val_addr(ref_);
            loop {
                let val = (*val_addr).swap(core::ptr::null_mut(), Ordering::AcqRel);
                if !val.is_null() {
                    return val;
                }
                core::hint::spin_loop();
            }
        } else {
            let val = (*lean_to_ref(ref_)).value;
            debug_assert!(!val.is_null());
            (*lean_to_ref(ref_)).value = core::ptr::null_mut();
            val
        }
    }

    #[inline]
    pub(crate) unsafe fn lean_st_ref_set( // [lean-audit] Lean imports from Rust ([extern]): Rust defined this function and function body is not empty (correct) (✅) | Lean: src/Init/System/ST.lean:190
        ref_: *mut LeanObject,
        a: *mut LeanObject,
    ) -> *mut LeanObject {
        if ref_maybe_mt(ref_) {
            lean_mark_mt(a);
            let val_addr = mt_ref_val_addr(ref_);
            let old_a = (*val_addr).swap(a, Ordering::AcqRel);
            if !old_a.is_null() {
                lean_dec(old_a);
            }
            lean_box(0)
        } else {
            let old_val = (*lean_to_ref(ref_)).value;
            if !old_val.is_null() {
                lean_dec(old_val);
            }
            (*lean_to_ref(ref_)).value = a;
            lean_box(0)
        }
    }

    #[inline]
    pub(crate) unsafe fn lean_st_ref_swap( // [lean-audit] Lean imports from Rust ([extern]): Rust defined this function and function body is not empty (correct) (✅) | Lean: src/Init/System/ST.lean:192
        ref_: *mut LeanObject,
        a: *mut LeanObject,
    ) -> *mut LeanObject {
        if ref_maybe_mt(ref_) {
            lean_mark_mt(a);
            let val_addr = mt_ref_val_addr(ref_);
            loop {
                let old_a = (*val_addr).swap(a, Ordering::AcqRel);
                if !old_a.is_null() {
                    return old_a;
                }
                core::hint::spin_loop();
            }
        } else {
            let old_a = (*lean_to_ref(ref_)).value;
            if old_a.is_null() {
                lean_internal_panic(c"null reference read".as_ptr());
            }
            (*lean_to_ref(ref_)).value = a;
            old_a
        }
    }

    #[inline]
    pub(crate) unsafe fn lean_st_ref_ptr_eq( // [lean-audit] Lean imports from Rust ([extern]): Rust defined this function and function body is not empty (correct) (✅) | Lean: src/Init/System/ST.lean:196
        ref1: *mut LeanObject,
        ref2: *mut LeanObject,
    ) -> u8 {
        (lean_to_ref(ref1) == lean_to_ref(ref2)) as u8
    }

    #[inline]
    pub(crate) fn lean_io_exit(code: u8) -> *mut LeanObject { // [lean-audit] Lean imports from Rust ([extern]): Rust defined this function and function body is not empty (correct) (✅) | Lean: src/Init/System/IO.lean:1579
        unsafe { libc::exit(code as i32) }
    }

    #[inline]
    pub(crate) fn lean_io_force_exit(code: u8) -> *mut LeanObject { // [lean-audit] Lean imports from Rust ([extern]): Rust defined this function and function body is not empty (correct) (✅) | Lean: src/Init/System/IO.lean:1588
        unsafe { libc::_exit(code as i32) }
    }

    #[inline]
    pub(crate) unsafe fn lean_runtime_mark_persistent(a: *mut LeanObject) -> *mut LeanObject { // [lean-audit] Lean imports from Rust ([extern]): Rust defined this function and function body is not empty (correct) (✅) | Lean: src/Init/System/IO.lean:1839
        lean_mark_persistent(a);
        a
    }

    #[inline]
    pub(crate) unsafe fn lean_runtime_mark_multi_threaded( // [lean-audit] Lean imports from Rust ([extern]): Rust defined this function and function body is not empty (correct) (✅) | Lean: src/Init/System/IO.lean:1826
        a: *mut LeanObject,
    ) -> *mut LeanObject {
        lean_mark_mt(a);
        a
    }

    #[inline]
    pub(crate) unsafe fn lean_runtime_forget(o: *mut LeanObject) -> *mut LeanObject { // [lean-audit] Lean imports from Rust ([extern]): Rust defined this function and function body is not empty (correct) (✅) | Lean: src/Init/System/IO.lean:1850
        let _ = o;
        lean_box(0)
    }
}
