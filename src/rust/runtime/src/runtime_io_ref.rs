/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

mod runtime_io_ref_impl {
    use crate::runtime_object_panic_impl::lean_internal_panic;
    use crate::*;
    use core::ffi::{CStr, c_char, c_int, c_long, c_uchar, c_uint, c_void};
    use leanh::LEAN_REF_TAG;
    use core::sync::atomic::{AtomicPtr, Ordering};

    unsafe extern "C" {
        fn lean_mark_mt(obj: *mut LeanObject);
        fn lean_mark_persistent(obj: *mut LeanObject); // duplicate in src/rust/leanh/src/in_emit_rust.rs at line 356 (🔁)
    }

    #[repr(C)]
    struct LeanRefObject { // duplicate in src/rust/leanh/src/datatypes.rs at line 97 (🔁)

        header: LeanObject,
        value: *mut LeanObject,
    }

    unsafe fn lean_set_st_header(o: *mut LeanObject, tag: u8, other: u8) {
        (*o).rc = 1;
        (*o).cs_size = 0;
        (*o).other = other;
        (*o).tag = tag;
    }

    unsafe fn lean_to_ref(o: *mut LeanObject) -> *mut LeanRefObject {
        debug_assert!((*o).tag == LEAN_REF_TAG);
        o as *mut LeanRefObject
    }

    fn lean_is_mt(o: *mut LeanObject) -> bool {
        unsafe { (*o).rc < 0 }
    }

    fn lean_is_persistent(o: *mut LeanObject) -> bool {
        unsafe { (*o).rc == 0 }
    }

    fn ref_maybe_mt(o: *mut LeanObject) -> bool {
        lean_is_mt(o) || lean_is_persistent(o)
    }

    unsafe fn mt_ref_val_addr(o: *mut LeanObject) -> *mut AtomicPtr<LeanObject> {
        core::ptr::addr_of_mut!((*lean_to_ref(o)).value).cast::<AtomicPtr<LeanObject>>()
    }

    pub unsafe fn lean_st_mk_ref(a: *mut LeanObject) -> *mut LeanObject {
        let o = crate::runtime_object_rc_impl::lean_alloc_small_object(core::mem::size_of::<
            LeanRefObject,
        >()) as *mut LeanRefObject;
        lean_set_st_header(o as *mut LeanObject, LEAN_REF_TAG, 0);
        (*o).value = a;
        o as *mut LeanObject
    }

    pub unsafe fn lean_st_ref_get(ref_: *mut LeanObject) -> *mut LeanObject {
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

    pub unsafe fn lean_st_ref_take(ref_: *mut LeanObject) -> *mut LeanObject {
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

    pub unsafe fn lean_st_ref_set(ref_: *mut LeanObject, a: *mut LeanObject) -> *mut LeanObject {
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

    pub unsafe fn lean_st_ref_swap(ref_: *mut LeanObject, a: *mut LeanObject) -> *mut LeanObject {
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

    pub unsafe fn lean_st_ref_ptr_eq(ref1: *mut LeanObject, ref2: *mut LeanObject) -> u8 {
        (lean_to_ref(ref1) == lean_to_ref(ref2)) as u8
    }

    pub fn lean_io_exit(code: u8) -> *mut LeanObject {
        unsafe { libc::exit(code as i32) }
    }

    pub fn lean_io_force_exit(code: u8) -> *mut LeanObject {
        unsafe { libc::_exit(code as i32) }
    }

    pub unsafe fn lean_runtime_mark_persistent(a: *mut LeanObject) -> *mut LeanObject {
        lean_mark_persistent(a);
        a
    }

    pub unsafe fn lean_runtime_mark_multi_threaded(a: *mut LeanObject) -> *mut LeanObject {
        lean_mark_mt(a);
        a
    }

    pub unsafe fn lean_runtime_forget(o: *mut LeanObject) -> *mut LeanObject {
        let _ = o;
        lean_box(0)
    }
}
