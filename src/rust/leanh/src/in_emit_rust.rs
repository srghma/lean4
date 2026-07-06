/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

use core::ffi::{c_char, c_int, c_void};
use core::ptr;
use core::sync::atomic::{AtomicI32, Ordering};

use crate::{
    F32InitFn, F64InitFn, LEAN_CLOSURE_TAG, LEAN_MAX_CTOR_TAG, LeanClosureObject, LeanObject,
    LeanOnceCell, ObjInitFn, U8InitFn, U16InitFn, U32InitFn, U64InitFn, UsizeInitFn,
    lean_alloc_ctor, lean_alloc_object, lean_alloc_string, lean_box, lean_ctor_num_objs,
    lean_ctor_obj_cptr, lean_ctor_scalar_cptr, lean_free_object, lean_is_ref, lean_is_scalar_bool,
    lean_is_st, lean_obj_once_cold, lean_ptr_tag, lean_string_data, lean_usize_to_nat, run_once,
};

use crate::not_in_emit_rust::{lean_closure_arg_cptr, lean_closure_num_fixed, lean_dec_ref_cold};

#[inline]
pub unsafe fn lean_box_uint32(value: u32) -> *mut LeanObject {
    unsafe { lean_box(value as usize) }
}

#[inline]
pub unsafe fn lean_box_usize(value: usize) -> *mut LeanObject {
    unsafe {
        let obj = lean_alloc_ctor(0, 0, core::mem::size_of::<usize>() as u32);
        ptr::copy_nonoverlapping(
            &value as *const usize as *const u8,
            lean_ctor_scalar_cptr(obj, 0),
            core::mem::size_of::<usize>(),
        );
        obj
    }
}

#[inline]
pub unsafe fn lean_closure_set(obj: *mut LeanObject, idx: u32, value: *mut LeanObject) {
    unsafe {
        debug_assert!((idx as usize) < lean_closure_num_fixed(obj));
        *lean_closure_arg_cptr(obj).add(idx as usize) = value;
    }
}

#[inline]
pub unsafe fn lean_cstr_to_nat(text: *const c_char) -> *mut LeanObject {
    unsafe {
        let s = std::ffi::CStr::from_ptr(text).to_str().unwrap();
        let value = s
            .parse::<usize>()
            .expect("big Nat is not supported in leanh.rs");
        lean_usize_to_nat(value)
    }
}

#[inline]
pub unsafe fn lean_ctor_get(obj: *mut LeanObject, idx: u32) -> *mut LeanObject {
    unsafe {
        debug_assert!((idx as usize) < lean_ctor_num_objs(obj));
        *lean_ctor_obj_cptr(obj).add(idx as usize)
    }
}

#[inline]
pub unsafe fn lean_ctor_get_float(obj: *mut LeanObject, offset: usize) -> f64 {
    unsafe { *((lean_ctor_obj_cptr(obj).cast::<u8>().add(offset)) as *const f64) }
}

#[inline]
pub unsafe fn lean_ctor_get_float32(obj: *mut LeanObject, offset: usize) -> f32 {
    unsafe { *((lean_ctor_obj_cptr(obj).cast::<u8>().add(offset)) as *const f32) }
}

#[inline]
pub unsafe fn lean_ctor_get_uint16(obj: *mut LeanObject, offset: usize) -> u16 {
    unsafe { *((lean_ctor_obj_cptr(obj).cast::<u8>().add(offset)) as *const u16) }
}

#[inline]
pub unsafe fn lean_ctor_get_uint32(obj: *mut LeanObject, offset: usize) -> u32 {
    unsafe { *((lean_ctor_obj_cptr(obj).cast::<u8>().add(offset)) as *const u32) }
}

#[inline]
pub unsafe fn lean_ctor_get_uint64(obj: *mut LeanObject, offset: usize) -> u64 {
    unsafe { *((lean_ctor_obj_cptr(obj).cast::<u8>().add(offset)) as *const u64) }
}

#[inline]
pub unsafe fn lean_ctor_get_uint8(obj: *mut LeanObject, offset: usize) -> u8 {
    unsafe { *((lean_ctor_obj_cptr(obj).cast::<u8>().add(offset)) as *const u8) }
}

#[inline]
pub unsafe fn lean_ctor_get_usize(obj: *mut LeanObject, idx: usize) -> usize {
    unsafe { *((lean_ctor_obj_cptr(obj).add(idx)) as *const usize) }
}

#[inline]
pub unsafe fn lean_ctor_set(obj: *mut LeanObject, idx: u32, value: *mut LeanObject) {
    unsafe {
        debug_assert!((idx as usize) < lean_ctor_num_objs(obj));
        *lean_ctor_obj_cptr(obj).add(idx as usize) = value;
    }
}

#[inline]
pub unsafe fn lean_ctor_set_float(obj: *mut LeanObject, offset: usize, value: f64) {
    unsafe { *((lean_ctor_obj_cptr(obj).cast::<u8>().add(offset)) as *mut f64) = value }
}

#[inline]
pub unsafe fn lean_box_float(value: f64) -> *mut LeanObject {
    unsafe {
        let obj = lean_alloc_ctor(0, 0, core::mem::size_of::<f64>() as u32);
        lean_ctor_set_float(obj, 0, value);
        obj
    }
}

#[inline]
pub unsafe fn lean_ctor_set_float32(obj: *mut LeanObject, offset: usize, value: f32) {
    unsafe { *((lean_ctor_obj_cptr(obj).cast::<u8>().add(offset)) as *mut f32) = value }
}

#[inline]
pub unsafe fn lean_box_float32(value: f32) -> *mut LeanObject {
    unsafe {
        let obj = lean_alloc_ctor(0, 0, core::mem::size_of::<f32>() as u32);
        lean_ctor_set_float32(obj, 0, value);
        obj
    }
}

#[inline]
pub unsafe fn lean_ctor_set_tag(obj: *mut LeanObject, new_tag: u8) {
    unsafe {
        debug_assert!(new_tag <= LEAN_MAX_CTOR_TAG);
        (*obj).tag = new_tag;
    }
}

#[inline]
pub unsafe fn lean_ctor_set_uint16(obj: *mut LeanObject, offset: usize, value: u16) {
    unsafe { *((lean_ctor_obj_cptr(obj).cast::<u8>().add(offset)) as *mut u16) = value }
}

#[inline]
pub unsafe fn lean_ctor_set_uint32(obj: *mut LeanObject, offset: usize, value: u32) {
    unsafe { *((lean_ctor_obj_cptr(obj).cast::<u8>().add(offset)) as *mut u32) = value }
}

#[inline]
pub unsafe fn lean_ctor_set_uint64(obj: *mut LeanObject, offset: usize, value: u64) {
    unsafe { *((lean_ctor_obj_cptr(obj).cast::<u8>().add(offset)) as *mut u64) = value }
}

#[inline]
pub unsafe fn lean_box_uint64(value: u64) -> *mut LeanObject {
    unsafe {
        let obj = lean_alloc_ctor(0, 0, core::mem::size_of::<u64>() as u32);
        lean_ctor_set_uint64(obj, 0, value);
        obj
    }
}

#[inline]
pub unsafe fn lean_ctor_set_uint8(obj: *mut LeanObject, offset: usize, value: u8) {
    unsafe { *((lean_ctor_obj_cptr(obj).cast::<u8>().add(offset)) as *mut u8) = value }
}

#[inline]
pub unsafe fn lean_ctor_set_usize(obj: *mut LeanObject, idx: usize, value: usize) {
    unsafe { *((lean_ctor_obj_cptr(obj).add(idx)) as *mut usize) = value }
}

// #[inline]
// pub unsafe fn lean_finalize_task_manager() {}

#[inline]
pub unsafe fn lean_float32_once(loc: *mut f32, tok: *mut LeanOnceCell, init: F32InitFn) -> f32 {
    unsafe {
        if (*tok).state.load(Ordering::Acquire) == 1 {
            *loc
        } else {
            run_once(loc, tok, init)
        }
    }
}

#[inline]
pub unsafe fn lean_float_once(loc: *mut f64, tok: *mut LeanOnceCell, init: F64InitFn) -> f64 {
    unsafe {
        if (*tok).state.load(Ordering::Acquire) == 1 {
            *loc
        } else {
            run_once(loc, tok, init)
        }
    }
}

#[inline]
pub unsafe fn lean_inc_ref_n(obj: *mut LeanObject, n: usize) {
    // 1. lean_is_st is unsafe because it dereferences obj inside
    if unsafe { lean_is_st(obj) } {
        // 2. Dereferencing obj to modify rc
        unsafe { (*obj).rc += n as i32 };
    }
    // 3. Dereferencing obj to check if rc != 0
    else if unsafe { (*obj).rc } != 0 {
        // 4. Using &raw mut to get field address (dereference to find offset)
        let rc = unsafe { &raw mut (*obj).rc }.cast::<AtomicI32>();
        unsafe { (*rc).fetch_sub(n as i32, Ordering::Relaxed) };
    }
}

#[inline]
#[allow(clippy::not_unsafe_ptr_arg_deref)]
pub fn lean_inc_ref(obj: *mut LeanObject) {
    unsafe { lean_inc_ref_n(obj, 1) };
}

#[inline]
pub unsafe fn lean_init_task_manager() {}

#[inline]
pub unsafe fn lean_initialize_runtime_module() {}

#[inline]
pub unsafe fn lean_initialize() {
    unsafe {
        lean_initialize_runtime_module();
    }
}

#[inline]
pub unsafe fn lean_io_mark_end_initialization() {}

#[inline]
pub unsafe fn lean_io_result_mk_ok(value: *mut LeanObject) -> *mut LeanObject {
    unsafe {
        let obj = lean_alloc_ctor(0, 1, 0);
        lean_ctor_set(obj, 0, value);
        obj
    }
}

#[inline]
pub unsafe fn lean_is_exclusive(obj: *mut LeanObject) -> bool {
    // if ::std::intrinsics::likely(lean_is_st(obj)) {
    unsafe { (*obj).rc == 1 }
    // } else {
    //     false
    // }
}

#[inline]
pub fn lean_is_scalar(obj: *mut LeanObject) -> u8 {
    ((obj as usize & 1) == 1) as u8
}

#[inline]
pub unsafe fn lean_alloc_closure(fun: *mut c_void, arity: u32, num_fixed: u32) -> *mut LeanObject {
    unsafe {
        debug_assert!(arity > 0);
        debug_assert!(num_fixed < arity);
        let byte_size = core::mem::size_of::<LeanClosureObject<0>>()
            .checked_add(
                core::mem::size_of::<*mut LeanObject>()
                    .checked_mul(num_fixed as usize)
                    .expect("closure allocation mul overflow"),
            )
            .expect("closure allocation add overflow");
        let obj = lean_alloc_object(byte_size) as *mut LeanClosureObject<0>;
        (*obj).m_header.rc = 1;
        (*obj).m_header.cs_size = 0;
        (*obj).m_header.other = 0;
        (*obj).m_header.tag = LEAN_CLOSURE_TAG;
        (*obj).m_fun = fun;
        (*obj).m_arity = arity as u16;
        (*obj).m_num_fixed = num_fixed as u16;
        obj as *mut LeanObject
    }
}

#[inline]
pub unsafe fn lean_dec_ref(obj: *mut LeanObject) {
    unsafe {
        if (*obj).rc > 1 {
            (*obj).rc -= 1;
        } else if (*obj).rc != 0 {
            lean_dec_ref_cold(obj);
        }
    }
}

#[inline]
pub unsafe fn lean_dec(obj: *mut LeanObject) {
    unsafe {
        if !lean_is_scalar_bool(obj) {
            lean_dec_ref(obj);
        }
    }
}

#[inline]
pub unsafe fn lean_ctor_release(obj: *mut LeanObject, idx: usize) {
    unsafe {
        debug_assert!(idx < lean_ctor_num_objs(obj));
        let slot = lean_ctor_obj_cptr(obj).add(idx);
        lean_dec(*slot);
        *slot = lean_box(0);
    }
}

#[inline]
pub unsafe fn lean_del_object(obj: *mut LeanObject) {
    unsafe {
        if !lean_is_scalar_bool(obj) {
            lean_free_object(obj);
        }
    }
}

#[inline]
pub unsafe fn lean_dec_ref_known(obj: *mut LeanObject, objs: u32) {
    unsafe {
        debug_assert!(lean_is_ref(obj));
        if lean_is_exclusive(obj) {
            for i in 0..objs {
                lean_dec(lean_ctor_get(obj, i));
            }
            lean_del_object(obj);
        } else {
            lean_dec_ref(obj);
        }
    }
}

#[inline]
pub fn lean_inc(obj: *mut LeanObject) {
    if !lean_is_scalar_bool(obj) {
        lean_inc_ref(obj);
    }
}

#[inline]
pub unsafe fn lean_inc_n(obj: *mut LeanObject, n: usize) {
    if !lean_is_scalar_bool(obj) {
        unsafe { lean_inc_ref_n(obj, n) };
    }
}

#[inline]
pub unsafe fn lean_mark_persistent(obj: *mut LeanObject) {
    unsafe {
        if !lean_is_scalar_bool(obj) {
            (*obj).rc = 0;
        }
    }
}

#[inline]
pub unsafe fn lean_mk_string_unchecked(
    s: *const c_char,
    byte_size: usize,
    len: usize,
) -> *mut LeanObject {
    unsafe {
        let obj = lean_alloc_string(byte_size + 1, byte_size + 1, len);
        ptr::copy_nonoverlapping(s.cast::<u8>(), lean_string_data(obj), byte_size);
        *lean_string_data(obj).add(byte_size) = 0;
        obj
    }
}

#[inline]
pub unsafe fn lean_mk_string(s: *const c_char) -> *mut LeanObject {
    unsafe {
        let len = libc::strlen(s);
        lean_mk_string_unchecked(s, len, len)
    }
}

#[inline]
pub unsafe fn lean_obj_once(
    loc: *mut *mut LeanObject,
    tok: *mut LeanOnceCell,
    init: ObjInitFn,
) -> *mut LeanObject {
    unsafe {
        if (*tok).state.load(Ordering::Acquire) == 1 {
            *loc
        } else {
            lean_obj_once_cold(loc, tok, init)
        }
    }
}

#[inline]
pub unsafe fn lean_run_main(
    main_fn: unsafe fn(c_int, *mut *mut c_char) -> *mut LeanObject,
    argc: c_int,
    argv: *mut *mut c_char,
) -> *mut LeanObject {
    unsafe { main_fn(argc, argv) }
}

#[inline]
pub unsafe fn lean_setup_args(_: c_int, argv: *mut *mut c_char) -> *mut *mut c_char {
    argv
}

#[inline]
pub unsafe fn lean_uint16_once(loc: *mut u16, tok: *mut LeanOnceCell, init: U16InitFn) -> u16 {
    unsafe {
        if (*tok).state.load(Ordering::Acquire) == 1 {
            *loc
        } else {
            run_once(loc, tok, init)
        }
    }
}

#[inline]
pub unsafe fn lean_uint32_once(loc: *mut u32, tok: *mut LeanOnceCell, init: U32InitFn) -> u32 {
    unsafe {
        if (*tok).state.load(Ordering::Acquire) == 1 {
            *loc
        } else {
            run_once(loc, tok, init)
        }
    }
}

#[inline]
pub unsafe fn lean_uint64_once(loc: *mut u64, tok: *mut LeanOnceCell, init: U64InitFn) -> u64 {
    unsafe {
        if (*tok).state.load(Ordering::Acquire) == 1 {
            *loc
        } else {
            run_once(loc, tok, init)
        }
    }
}

#[inline]
pub unsafe fn lean_uint8_once(loc: *mut u8, tok: *mut LeanOnceCell, init: U8InitFn) -> u8 {
    unsafe {
        if (*tok).state.load(Ordering::Acquire) == 1 {
            *loc
        } else {
            run_once(loc, tok, init)
        }
    }
}

#[inline]
pub unsafe fn lean_unbox(obj: *mut LeanObject) -> usize {
    (obj as usize) >> 1
}

#[inline]
pub unsafe fn lean_small_nat(obj: *mut LeanObject) -> usize {
    unsafe {
        if lean_is_scalar_bool(obj) {
            lean_unbox(obj)
        } else {
            panic!("big Nat is not supported in leanh.rs")
        }
    }
}

macro_rules! define_uint_family {
    ($ty:ty, $of_nat:ident, $of_nat_mk:ident, $to_nat:ident, $dec_eq:ident, $dec_lt:ident, $dec_le:ident) => {
        #[inline]
        pub unsafe fn $of_nat(obj: *mut LeanObject) -> $ty {
            unsafe { lean_small_nat(obj) as $ty }
        }

        #[inline]
        pub unsafe fn $of_nat_mk(obj: *mut LeanObject) -> $ty {
            unsafe {
                let result = $of_nat(obj);
                lean_dec(obj);
                result
            }
        }

        #[inline]
        pub unsafe fn $to_nat(value: $ty) -> *mut LeanObject {
            unsafe { lean_usize_to_nat(value as usize) }
        }

        #[inline]
        pub unsafe fn $dec_eq(a: $ty, b: $ty) -> u8 {
            (a == b) as u8
        }

        #[inline]
        pub unsafe fn $dec_lt(a: $ty, b: $ty) -> u8 {
            (a < b) as u8
        }

        #[inline]
        pub unsafe fn $dec_le(a: $ty, b: $ty) -> u8 {
            (a <= b) as u8
        }
    };
}

define_uint_family!(
    u8,
    lean_uint8_of_nat,
    lean_uint8_of_nat_mk,
    lean_uint8_to_nat,
    lean_uint8_dec_eq,
    lean_uint8_dec_lt,
    lean_uint8_dec_le
);

define_uint_family!(
    u16,
    lean_uint16_of_nat,
    lean_uint16_of_nat_mk,
    lean_uint16_to_nat,
    lean_uint16_dec_eq,
    lean_uint16_dec_lt,
    lean_uint16_dec_le
);

define_uint_family!(
    u32,
    lean_uint32_of_nat,
    lean_uint32_of_nat_mk,
    lean_uint32_to_nat,
    lean_uint32_dec_eq,
    lean_uint32_dec_lt,
    lean_uint32_dec_le
);

define_uint_family!(
    u64,
    lean_uint64_of_nat,
    lean_uint64_of_nat_mk,
    lean_uint64_to_nat,
    lean_uint64_dec_eq,
    lean_uint64_dec_lt,
    lean_uint64_dec_le
);

#[inline]
pub unsafe fn lean_obj_tag(obj: *mut LeanObject) -> u8 {
    unsafe {
        if lean_is_scalar_bool(obj) {
            lean_unbox(obj) as u8
        } else {
            lean_ptr_tag(obj)
        }
    }
}

#[inline]
pub unsafe fn lean_io_result_is_error(obj: *mut LeanObject) -> bool {
    unsafe { lean_obj_tag(obj) == 1 }
}

#[inline]
pub unsafe fn lean_io_result_is_ok(obj: *mut LeanObject) -> bool {
    unsafe { lean_obj_tag(obj) == 0 }
}

#[inline]
pub unsafe fn lean_io_result_get_value(obj: *mut LeanObject) -> *mut LeanObject {
    unsafe {
        debug_assert!(lean_io_result_is_ok(obj));
        lean_ctor_get(obj, 0)
    }
}

#[inline]
pub unsafe fn lean_io_result_show_error(r: *mut LeanObject) {
    unsafe {
        debug_assert!(lean_io_result_is_error(r));
        eprintln!("Lean IO error: {r:p}");
    }
}

#[inline]
pub unsafe fn lean_unbox_float(obj: *mut LeanObject) -> f64 {
    unsafe { lean_ctor_get_float(obj, 0) }
}

#[inline]
pub unsafe fn lean_unbox_float32(obj: *mut LeanObject) -> f32 {
    unsafe { lean_ctor_get_float32(obj, 0) }
}

#[inline]
pub unsafe fn lean_unbox_uint32(obj: *mut LeanObject) -> u32 {
    unsafe {
        let mut value = 0u32;
        ptr::copy_nonoverlapping(
            lean_ctor_scalar_cptr(obj, 0),
            &mut value as *mut u32 as *mut u8,
            core::mem::size_of::<u32>(),
        );
        value
    }
}

#[inline]
pub unsafe fn lean_unbox_uint64(obj: *mut LeanObject) -> u64 {
    unsafe { lean_ctor_get_uint64(obj, 0) }
}

#[inline]
pub unsafe fn lean_unbox_usize(obj: *mut LeanObject) -> usize {
    unsafe {
        let mut value = 0usize;
        ptr::copy_nonoverlapping(
            lean_ctor_scalar_cptr(obj, 0),
            &mut value as *mut usize as *mut u8,
            core::mem::size_of::<usize>(),
        );
        value
    }
}

#[inline]
pub unsafe fn lean_unsigned_to_nat(value: u32) -> *mut LeanObject {
    unsafe { lean_usize_to_nat(value as usize) }
}

#[inline]
pub unsafe fn lean_usize_once(loc: *mut usize, tok: *mut LeanOnceCell, init: UsizeInitFn) -> usize {
    unsafe {
        if (*tok).state.load(Ordering::Acquire) == 1 {
            *loc
        } else {
            run_once(loc, tok, init)
        }
    }
}
