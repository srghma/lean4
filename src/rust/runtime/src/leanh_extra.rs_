/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

use core::{
    ffi::c_void,
    ptr,
    sync::atomic::{AtomicPtr, Ordering},
};
use leanh::{
    LEAN_ARRAY_TAG, LEAN_CLOSURE_MAX_ARGS, LEAN_CLOSURE_TAG, LEAN_EXTERNAL_TAG, LEAN_MAX_CTOR_TAG,
    LEAN_MAX_SMALL_NAT, LEAN_MPZ_TAG, LEAN_PROMISE_TAG, LEAN_SCALAR_ARRAY_TAG, LEAN_STRING_TAG,
    LEAN_TASK_TAG, LEAN_THUNK_TAG, LeanArrayObject, LeanClosureObject, LeanCtorObject,
    LeanExternalClass, LeanExternalFinalizeProc, LeanExternalForeachProc, LeanExternalObject,
    LeanObject, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_object, lean_alloc_small_object, lean_alloc_string,
    lean_array_size, lean_box, lean_dec, lean_dec_ref, lean_inc, lean_inc_n, lean_is_exclusive,
    lean_is_ref, lean_is_scalar_bool, lean_is_st, lean_ptr_tag, lean_small_nat, lean_string_data,
    lean_unbox, lean_unsigned_to_nat, lean_usize_to_nat,
};

// Moved out of leanh: not hardcoded by EmitRust.

pub static EXTERNAL_CLASSES: std::sync::Mutex<Vec<usize>> = std::sync::Mutex::new(Vec::new());

#[inline]
pub unsafe fn lean_ptr_other(obj: *mut LeanObject) -> u8 {
    unsafe { (*obj).other }
}

#[inline]
pub unsafe fn lean_has_rc(obj: *mut LeanObject) -> bool {
    unsafe { (*obj).rc != 0 }
}

#[inline]
pub unsafe fn lean_is_mt(obj: *mut LeanObject) -> bool {
    unsafe { (*obj).rc < 0 }
}

#[inline]
pub unsafe fn lean_is_persistent(obj: *mut LeanObject) -> bool {
    unsafe { (*obj).rc == 0 }
}

#[inline]
pub unsafe fn lean_is_ctor(obj: *mut LeanObject) -> bool {
    unsafe { lean_ptr_tag(obj) <= LEAN_MAX_CTOR_TAG }
}

#[inline]
pub unsafe fn lean_is_closure(obj: *mut LeanObject) -> bool {
    unsafe { lean_ptr_tag(obj) == LEAN_CLOSURE_TAG }
}

#[inline]
pub unsafe fn lean_is_array(obj: *mut LeanObject) -> bool {
    unsafe { lean_ptr_tag(obj) == LEAN_ARRAY_TAG }
}

#[inline]
pub unsafe fn lean_is_sarray(obj: *mut LeanObject) -> bool {
    unsafe { lean_ptr_tag(obj) == LEAN_SCALAR_ARRAY_TAG }
}

#[inline]
pub unsafe fn lean_is_string(obj: *mut LeanObject) -> bool {
    unsafe { lean_ptr_tag(obj) == LEAN_STRING_TAG }
}

#[inline]
pub unsafe fn lean_is_mpz(obj: *mut LeanObject) -> bool {
    unsafe { lean_ptr_tag(obj) == LEAN_MPZ_TAG }
}

#[inline]
pub unsafe fn lean_is_thunk(obj: *mut LeanObject) -> bool {
    unsafe { lean_ptr_tag(obj) == LEAN_THUNK_TAG }
}

#[inline]
pub unsafe fn lean_is_task(obj: *mut LeanObject) -> bool {
    unsafe { lean_ptr_tag(obj) == LEAN_TASK_TAG }
}

#[inline]
pub unsafe fn lean_is_promise(obj: *mut LeanObject) -> bool {
    unsafe { lean_ptr_tag(obj) == LEAN_PROMISE_TAG }
}

#[inline]
pub unsafe fn lean_is_external(obj: *mut LeanObject) -> bool {
    unsafe { lean_ptr_tag(obj) == LEAN_EXTERNAL_TAG }
}

#[inline]
pub unsafe fn lean_array_capacity(obj: *mut LeanObject) -> usize {
    unsafe { (*(obj as *const LeanArrayObject<0>)).m_capacity }
}

#[inline]
pub unsafe fn lean_array_data(obj: *mut LeanObject) -> *mut *mut LeanObject {
    unsafe { (*(obj as *mut LeanArrayObject<0>)).m_data.as_mut_ptr() }
}

#[inline]
pub unsafe fn lean_array_get_core(obj: *mut LeanObject, idx: usize) -> *mut LeanObject {
    unsafe { *lean_array_data(obj).add(idx) }
}

#[inline]
pub unsafe fn lean_alloc_array(size: usize, capacity: usize) -> *mut LeanObject {
    unsafe {
        let byte_size = core::mem::size_of::<LeanArrayObject<0>>()
            + core::mem::size_of::<*mut LeanObject>() * capacity;
        let obj = lean_alloc_object(byte_size) as *mut LeanArrayObject<0>;
        (*obj).m_header.rc = 1;
        (*obj).m_header.cs_size = 0;
        (*obj).m_header.other = 0;
        (*obj).m_header.tag = LEAN_ARRAY_TAG;
        (*obj).m_size = size;
        (*obj).m_capacity = capacity;
        obj as *mut LeanObject
    }
}

#[inline]
pub unsafe fn lean_ensure_exclusive_array(obj: *mut LeanObject) -> *mut LeanObject {
    unsafe {
        if lean_is_exclusive(obj) {
            return obj;
        }
        let size = lean_array_size(obj);
        let capacity = lean_array_capacity(obj);
        let new_obj = lean_alloc_array(size, capacity);
        ptr::copy_nonoverlapping(lean_array_data(obj), lean_array_data(new_obj), size);
        for i in 0..size {
            lean_inc(lean_array_get_core(new_obj, i));
        }
        lean_dec_ref(obj);
        new_obj
    }
}

#[inline]
pub unsafe fn lean_array_get_size(obj: *mut LeanObject) -> *mut LeanObject {
    // used in src/rust/gen_init_ffi/src/ffi/Init/Prelude.rs:207 (🔌)
    unsafe { lean_box(lean_array_size(obj)) }
}

#[inline]
pub unsafe fn lean_array_fget(obj: *mut LeanObject, idx: *mut LeanObject) -> *mut LeanObject {
    // used in src/rust/gen_init_ffi/src/ffi/Init/Prelude.rs:220 (🔌)
    unsafe {
        let r = lean_array_get_core(obj, lean_unbox(idx));
        lean_inc(r);
        r
    }
}

#[inline]
pub unsafe fn lean_array_fget_borrowed(
    // used in src/rust/gen_init_ffi/src/ffi/Init/Prelude.rs:212 (🔌)
    obj: *mut LeanObject,
    idx: *mut LeanObject,
) -> *mut LeanObject {
    unsafe { lean_array_get_core(obj, lean_unbox(idx)) }
}

#[inline]
pub unsafe fn lean_array_uget(obj: *mut LeanObject, idx: usize) -> *mut LeanObject {
    // used in src/rust/gen_init_ffi/src/ffi/Init/Data/Array/Basic.rs:10 (🔌)
    unsafe {
        let r = lean_array_get_core(obj, idx);
        lean_inc(r);
        r
    }
}

#[inline]
pub unsafe fn lean_array_uget_borrowed(obj: *mut LeanObject, idx: usize) -> *mut LeanObject {
    // used in src/rust/gen_init_ffi/src/ffi/Init/Data/Array/Basic.rs:14 (🔌)
    unsafe { lean_array_get_core(obj, idx) }
}

#[inline]
pub unsafe fn lean_array_get(
    // used in src/rust/gen_init_ffi/src/ffi/Init/Prelude.rs:234 (🔌)
    def_val: *mut LeanObject,
    obj: *mut LeanObject,
    idx: *mut LeanObject,
) -> *mut LeanObject {
    unsafe {
        if lean_is_scalar_bool(idx) {
            let idx = lean_unbox(idx);
            if idx < lean_array_size(obj) {
                let r = lean_array_get_core(obj, idx);
                lean_inc(r);
                return r;
            }
        }
        lean_inc(def_val);
        def_val
    }
}

#[inline]
pub unsafe fn lean_array_get_borrowed(
    // used in src/rust/gen_init_ffi/src/ffi/Init/Prelude.rs:225 (🔌)
    def_val: *mut LeanObject,
    obj: *mut LeanObject,
    idx: *mut LeanObject,
) -> *mut LeanObject {
    unsafe {
        if lean_is_scalar_bool(idx) {
            let idx = lean_unbox(idx);
            if idx < lean_array_size(obj) {
                return lean_array_get_core(obj, idx);
            }
        }
        def_val
    }
}

#[inline]
pub unsafe fn lean_mk_empty_array_with_capacity(capacity: *mut LeanObject) -> *mut LeanObject {
    // used in src/rust/gen_init_ffi/src/ffi/Init/Prelude.rs:202 (🔌)
    unsafe {
        if !lean_is_scalar_bool(capacity) {
            panic!("big array capacity is not supported in leanh.rs");
        }
        lean_alloc_array(0, lean_unbox(capacity))
    }
}

#[inline]
pub unsafe fn lean_array_push(obj: *mut LeanObject, value: *mut LeanObject) -> *mut LeanObject {
    // used in src/rust/gen_init_ffi/src/ffi/Init/Prelude.rs:243 (🔌)
    unsafe {
        let size = lean_array_size(obj);
        let capacity = lean_array_capacity(obj);
        let target = if lean_is_exclusive(obj) && size < capacity {
            obj
        } else {
            let new_capacity = if capacity == 0 { 1 } else { capacity * 2 };
            let new_obj = lean_alloc_array(size, new_capacity);
            ptr::copy_nonoverlapping(lean_array_data(obj), lean_array_data(new_obj), size);
            lean_dec_ref(obj);
            new_obj
        };
        *lean_array_data(target).add(size) = value;
        (*(target as *mut LeanArrayObject<0>)).m_size = size + 1;
        target
    }
}

#[inline]
pub unsafe fn lean_array_uset(
    // used in src/rust/gen_init_ffi/src/ffi/Init/Data/Array/Basic.rs:18 (🔌)
    obj: *mut LeanObject,
    idx: usize,
    value: *mut LeanObject,
) -> *mut LeanObject {
    unsafe {
        let target = lean_ensure_exclusive_array(obj);
        let slot = lean_array_data(target).add(idx);
        lean_dec(*slot);
        *slot = value;
        target
    }
}

#[inline]
pub unsafe fn lean_array_fset(
    // used in src/rust/gen_init_ffi/src/ffi/Init/Data/Array/Set.rs:6 (🔌)
    obj: *mut LeanObject,
    idx: *mut LeanObject,
    value: *mut LeanObject,
) -> *mut LeanObject {
    unsafe { lean_array_uset(obj, lean_unbox(idx), value) }
}

#[inline]
pub unsafe fn lean_array_set(
    // used in src/rust/gen_init_ffi/src/ffi/Init/Data/Array/Set.rs:14 (🔌)
    obj: *mut LeanObject,
    idx: *mut LeanObject,
    value: *mut LeanObject,
) -> *mut LeanObject {
    unsafe {
        if lean_is_scalar_bool(idx) {
            let idx = lean_unbox(idx);
            if idx < lean_array_size(obj) {
                return lean_array_uset(obj, idx, value);
            }
        }
        panic!("lean_array_set_panic is not implemented in leanh.rs");
    }
}

#[inline]
pub unsafe fn lean_array_pop(obj: *mut LeanObject) -> *mut LeanObject {
    // used in src/rust/gen_init_ffi/src/ffi/Init/Data/Array/Basic.rs:26 (🔌)
    unsafe {
        let target = lean_ensure_exclusive_array(obj);
        let size = lean_array_size(target);
        if size == 0 {
            return target;
        }
        let new_size = size - 1;
        (*(target as *mut LeanArrayObject<0>)).m_size = new_size;
        lean_dec(*lean_array_data(target).add(new_size));
        target
    }
}

#[inline]
pub unsafe fn lean_array_uswap(obj: *mut LeanObject, i: usize, j: usize) -> *mut LeanObject {
    unsafe {
        let target = lean_ensure_exclusive_array(obj);
        let data = lean_array_data(target);
        let vi = *data.add(i);
        *data.add(i) = *data.add(j);
        *data.add(j) = vi;
        target
    }
}

#[inline]
pub unsafe fn lean_array_fswap(
    // used in src/rust/gen_init_ffi/src/ffi/Init/Data/Array/Basic.rs:34 (🔌)
    obj: *mut LeanObject,
    i: *mut LeanObject,
    j: *mut LeanObject,
) -> *mut LeanObject {
    unsafe { lean_array_uswap(obj, lean_unbox(i), lean_unbox(j)) }
}

#[inline]
pub unsafe fn lean_array_swap(
    // used in src/rust/gen_init_ffi/src/ffi/Init/Data/Array/Basic.rs:42 (🔌)
    obj: *mut LeanObject,
    i: *mut LeanObject,
    j: *mut LeanObject,
) -> *mut LeanObject {
    unsafe {
        if !lean_is_scalar_bool(i) || !lean_is_scalar_bool(j) {
            return obj;
        }
        let i = lean_unbox(i);
        let j = lean_unbox(j);
        let size = lean_array_size(obj);
        if i >= size || j >= size {
            return obj;
        }
        lean_array_uswap(obj, i, j)
    }
}

#[inline]
pub unsafe fn lean_mk_array(n: *mut LeanObject, value: *mut LeanObject) -> *mut LeanObject {
    // used in src/rust/gen_init_ffi/src/ffi/Init/Data/Array/Basic.rs:30 (🔌)
    unsafe {
        if !lean_is_scalar_bool(n) {
            panic!("big array size is not supported in leanh.rs");
        }
        let size = lean_unbox(n);
        let obj = lean_alloc_array(size, size);
        for i in 0..size {
            *lean_array_data(obj).add(i) = value;
        }
        if size == 0 {
            lean_dec(value);
        } else if size > 1 {
            lean_inc_n(value, size - 1);
        }
        obj
    }
}

#[inline]
pub unsafe fn lean_array_mk(_list: *mut LeanObject) -> *mut LeanObject {
    // used in src/rust/gen_init_ffi/src/ffi/Init/Prelude.rs:52 (🔌)
    panic!("lean_array_mk requires list traversal runtime");
}

#[inline]
pub unsafe fn lean_array_to_list(_array: *mut LeanObject) -> *mut LeanObject {
    // used in src/rust/gen_init_ffi/src/ffi/Init/Prelude.rs:47 (🔌)
    panic!("lean_array_to_list requires list construction runtime");
}

#[inline]
pub unsafe fn lean_mk_thunk(closure: *mut LeanObject) -> *mut LeanObject {
    // used in src/rust/gen_init_ffi/src/ffi/Init/Core.rs:6 (🔌)
    unsafe {
        let obj =
            lean_alloc_object(core::mem::size_of::<LeanThunkObject>()) as *mut LeanThunkObject;
        (*obj).m_header.rc = 1;
        (*obj).m_header.cs_size = 0;
        (*obj).m_header.other = 0;
        (*obj).m_header.tag = LEAN_THUNK_TAG;
        (*obj).m_value = AtomicPtr::new(core::ptr::null_mut());
        (*obj).m_closure = AtomicPtr::new(closure);
        obj as *mut LeanObject
    }
}

#[inline]
pub unsafe fn lean_thunk_pure(value: *mut LeanObject) -> *mut LeanObject {
    // used in src/rust/gen_init_ffi/src/ffi/Init/Core.rs:18 (🔌)
    unsafe {
        let obj =
            lean_alloc_object(core::mem::size_of::<LeanThunkObject>()) as *mut LeanThunkObject;
        (*obj).m_header.rc = 1;
        (*obj).m_header.cs_size = 0;
        (*obj).m_header.other = 0;
        (*obj).m_header.tag = LEAN_THUNK_TAG;
        (*obj).m_value = AtomicPtr::new(value);
        (*obj).m_closure = AtomicPtr::new(core::ptr::null_mut());
        obj as *mut LeanObject
    }
}

#[inline]
pub unsafe fn lean_thunk_get_own(thunk: *mut LeanObject) -> *mut LeanObject {
    // used in src/rust/gen_init_ffi/src/ffi/Init/Core.rs:22 (🔌)
    unsafe {
        let thunk = thunk as *mut LeanThunkObject;
        let value = (*thunk).m_value.load(Ordering::Acquire);
        if value.is_null() {
            panic!("lean_thunk_get_core is not implemented in leanh.rs");
        }
        lean_inc(value);
        value
    }
}

#[inline]
pub unsafe fn lean_sarray_size(obj: *mut LeanObject) -> usize {
    // used in src/rust/gen_init_ffi/src/ffi/common/lean_sarray_size.rs:7 (🔌)
    unsafe { (*(obj as *const LeanScalarArray<0>)).m_size }
}

#[inline]
pub unsafe fn lean_sarray_capacity(obj: *mut LeanObject) -> usize {
    unsafe { (*(obj as *const LeanScalarArray<0>)).m_capacity }
}

#[inline]
pub unsafe fn lean_sarray_data(obj: *mut LeanObject) -> *mut u8 {
    unsafe { (*(obj as *mut LeanScalarArray<0>)).m_data.as_mut_ptr() }
}

#[inline]
pub unsafe fn lean_alloc_sarray(elem_size: u32, size: usize, capacity: usize) -> *mut LeanObject {
    unsafe {
        let byte_size = core::mem::size_of::<LeanScalarArray<0>>() + elem_size as usize * capacity;
        let obj = lean_alloc_object(byte_size) as *mut LeanScalarArray<0>;
        (*obj).m_header.rc = 1;
        (*obj).m_header.cs_size = 0;
        (*obj).m_header.other = elem_size as u8;
        (*obj).m_header.tag = LEAN_SCALAR_ARRAY_TAG;
        (*obj).m_size = size;
        (*obj).m_capacity = capacity;
        obj as *mut LeanObject
    }
}

#[inline]
pub unsafe fn lean_mk_empty_byte_array(capacity: *mut LeanObject) -> *mut LeanObject {
    // used in src/rust/gen_init_ffi/src/ffi/Init/Prelude.rs:248 (🔌)
    unsafe {
        if !lean_is_scalar_bool(capacity) {
            panic!("big byte-array capacity is not supported in leanh.rs");
        }
        lean_alloc_sarray(1, 0, lean_unbox(capacity))
    }
}

#[inline]
pub unsafe fn lean_byte_array_size(obj: *mut LeanObject) -> *mut LeanObject {
    // used in src/rust/gen_init_ffi/src/ffi/Init/Prelude.rs:258 (🔌)
    unsafe { lean_box(lean_sarray_size(obj)) }
}

#[inline]
pub unsafe fn lean_byte_array_data(obj: *mut LeanObject) -> *mut LeanObject {
    // used in src/rust/gen_init_ffi/src/ffi/Init/Prelude.rs:62 (🔌)
    lean_inc(obj);
    obj
}

#[inline]
pub unsafe fn lean_byte_array_mk(obj: *mut LeanObject) -> *mut LeanObject {
    // used in src/rust/gen_init_ffi/src/ffi/Init/Prelude.rs:57 (🔌)
    lean_inc(obj);
    obj
}

#[inline]
pub unsafe fn lean_byte_array_push(obj: *mut LeanObject, value: u8) -> *mut LeanObject {
    // used in src/rust/gen_init_ffi/src/ffi/Init/Prelude.rs:253 (🔌)
    unsafe {
        let size = lean_sarray_size(obj);
        let capacity = lean_sarray_capacity(obj);
        let target = if lean_is_exclusive(obj) && size < capacity {
            obj
        } else {
            let new_capacity = if capacity == 0 { 1 } else { capacity * 2 };
            let new_obj = lean_alloc_sarray(1, size, new_capacity);
            ptr::copy_nonoverlapping(lean_sarray_data(obj), lean_sarray_data(new_obj), size);
            lean_dec_ref(obj);
            new_obj
        };
        *lean_sarray_data(target).add(size) = value;
        (*(target as *mut LeanScalarArray<0>)).m_size = size + 1;
        target
    }
}

#[inline]
pub unsafe fn lean_nat_add(a: *mut LeanObject, b: *mut LeanObject) -> *mut LeanObject {
    // used in src/rust/gen_init_ffi/src/ffi/Init/Prelude.rs:85 (🔌)
    unsafe { lean_usize_to_nat(lean_small_nat(a).wrapping_add(lean_small_nat(b))) }
}

#[inline]
pub unsafe fn lean_nat_sub(a: *mut LeanObject, b: *mut LeanObject) -> *mut LeanObject {
    // used in src/rust/gen_init_ffi/src/ffi/Init/Prelude.rs:120 (🔌)
    unsafe { lean_box(lean_small_nat(a).saturating_sub(lean_small_nat(b))) }
}

#[inline]
pub unsafe fn lean_nat_mul(a: *mut LeanObject, b: *mut LeanObject) -> *mut LeanObject {
    // used in src/rust/gen_init_ffi/src/ffi/Init/Prelude.rs:90 (🔌)
    unsafe { lean_usize_to_nat(lean_small_nat(a).wrapping_mul(lean_small_nat(b))) }
}

#[inline]
pub unsafe fn lean_nat_div(a: *mut LeanObject, b: *mut LeanObject) -> *mut LeanObject {
    // used in src/rust/gen_init_ffi/src/ffi/Init/Prelude.rs:125 (🔌)
    unsafe {
        let b = lean_small_nat(b);
        lean_box(lean_small_nat(a).checked_div(b).unwrap_or(0))
    }
}

#[inline]
pub unsafe fn lean_nat_mod(a: *mut LeanObject, b: *mut LeanObject) -> *mut LeanObject {
    // used in src/rust/gen_init_ffi/src/ffi/Init/Prelude.rs:130 (🔌)
    unsafe {
        let b = lean_small_nat(b);
        lean_box(if b == 0 {
            lean_small_nat(a)
        } else {
            lean_small_nat(a) % b
        })
    }
}

#[inline]
pub unsafe fn lean_nat_pow(a: *mut LeanObject, b: *mut LeanObject) -> *mut LeanObject {
    // used in src/rust/gen_init_ffi/src/ffi/Init/Prelude.rs:95 (🔌)
    unsafe { lean_usize_to_nat(lean_small_nat(a).wrapping_pow(lean_small_nat(b) as u32)) }
}

#[inline]
pub unsafe fn lean_nat_pred(a: *mut LeanObject) -> *mut LeanObject {
    // used in src/rust/gen_init_ffi/src/ffi/Init/Prelude.rs:110 (🔌)
    unsafe { lean_box(lean_small_nat(a).saturating_sub(1)) }
}

#[inline]
pub unsafe fn lean_nat_dec_eq(a: *mut LeanObject, b: *mut LeanObject) -> u8 {
    // used in src/rust/gen_init_ffi/src/ffi/Init/Prelude.rs:100 (🔌)
    unsafe { (lean_small_nat(a) == lean_small_nat(b)) as u8 }
}

#[inline]
pub unsafe fn lean_nat_dec_lt(a: *mut LeanObject, b: *mut LeanObject) -> u8 {
    // used in src/rust/gen_init_ffi/src/ffi/Init/Prelude.rs:115 (🔌)
    unsafe { (lean_small_nat(a) < lean_small_nat(b)) as u8 }
}

#[inline]
pub unsafe fn lean_nat_dec_le(a: *mut LeanObject, b: *mut LeanObject) -> u8 {
    // used in src/rust/gen_init_ffi/src/ffi/Init/Prelude.rs:105 (🔌)
    unsafe { (lean_small_nat(a) <= lean_small_nat(b)) as u8 }
}

#[inline]
pub unsafe fn lean_nat_shiftr(a: *mut LeanObject, b: *mut LeanObject) -> *mut LeanObject {
    // used in src/rust/gen_init_ffi/src/ffi/Init/Data/Nat/Bitwise/Basic.rs:22 (🔌)
    unsafe {
        if lean_is_scalar_bool(a) && lean_is_scalar_bool(b) {
            let a = lean_unbox(a);
            let b = lean_unbox(b);
            let result = if b < usize::BITS as usize { a >> b } else { 0 };
            lean_box(result)
        } else {
            panic!("big nat shiftr is not implemented in leanh.rs");
        }
    }
}

#[inline]
pub unsafe fn lean_nat_to_int(value: *mut LeanObject) -> *mut LeanObject {
    // used in src/rust/gen_init_ffi/src/ffi/Init/Data/Int/Basic.rs:7 (🔌)
    value
}

#[inline]
pub unsafe fn lean_usize_of_nat(obj: *mut LeanObject) -> usize {
    // used in src/rust/gen_init_ffi/src/ffi/common/lean_usize_of_nat.rs:8 (🔌)
    unsafe { lean_small_nat(obj) }
}

#[inline]
pub unsafe fn lean_usize_of_nat_mk(obj: *mut LeanObject) -> usize {
    // used in src/rust/gen_init_ffi/src/ffi/Init/Prelude.rs:39 (🔌)
    unsafe {
        let result = lean_usize_of_nat(obj);
        lean_dec(obj);
        result
    }
}

#[inline]
pub unsafe fn lean_usize_dec_eq(a: usize, b: usize) -> u8 {
    // used in src/rust/gen_init_ffi/src/ffi/Init/Prelude.rs:197 (🔌) // [lean-audit] Lean imports from Rust ([extern]): Rust defined this function and function body is not empty (correct) (✅) | Lean: src/Init/Prelude.lean:2806
    (a == b) as u8
}

#[inline]
pub unsafe fn lean_usize_dec_lt(a: usize, b: usize) -> u8 {
    // used in src/rust/gen_init_ffi/src/ffi/Init/Data/UInt/BasicAux.rs:93 (🔌) // [lean-audit] Lean imports from Rust ([extern]): Rust defined this function and function body is not empty (correct) (✅) | Lean: src/Init/Data/UInt/BasicAux.lean:422
    (a < b) as u8
}

#[inline]
pub unsafe fn lean_usize_dec_le(a: usize, b: usize) -> u8 {
    // used in src/rust/gen_init_ffi/src/ffi/Init/Data/UInt/BasicAux.rs:97 (🔌) // [lean-audit] Lean imports from Rust ([extern]): Rust defined this function and function body is not empty (correct) (✅) | Lean: src/Init/Data/UInt/BasicAux.lean:438
    (a <= b) as u8
}

#[inline]
pub unsafe fn lean_usize_add(a: usize, b: usize) -> usize {
    // used in src/rust/gen_init_ffi/src/ffi/Init/Data/UInt/BasicAux.rs:85 (🔌) // [lean-audit] Lean imports from Rust ([extern]): Rust defined this function and function body is not empty (correct) (✅) | Lean: src/Init/Data/UInt/BasicAux.lean:382
    a.wrapping_add(b)
}

#[inline]
pub unsafe fn lean_usize_sub(a: usize, b: usize) -> usize {
    // used in src/rust/gen_init_ffi/src/ffi/Init/Data/UInt/BasicAux.rs:89 (🔌) // [lean-audit] Lean imports from Rust ([extern]): Rust defined this function and function body is not empty (correct) (✅) | Lean: src/Init/Data/UInt/BasicAux.lean:390
    a.wrapping_sub(b)
}

#[inline]
pub unsafe fn lean_closure_max_args(_: *mut LeanObject) -> *mut LeanObject {
    // used in src/rust/gen_lean_ffi/src/ffi/Lean/Runtime.rs:4 (🔌)
    unsafe { lean_unsigned_to_nat(LEAN_CLOSURE_MAX_ARGS) }
}

#[inline]
pub unsafe fn lean_max_small_nat(_: *mut LeanObject) -> *mut LeanObject {
    // used in src/rust/gen_lean_ffi/src/ffi/Lean/Runtime.rs:8 (🔌)
    unsafe { lean_usize_to_nat(LEAN_MAX_SMALL_NAT) }
}

#[inline]
pub unsafe fn lean_libuv_version(_: *mut LeanObject) -> *mut LeanObject {
    // used in src/rust/gen_lean_ffi/src/ffi/Lean/Runtime.rs:12 (🔌)
    unsafe { lean_box(0) }
}

#[inline]
pub fn lean_uint64_mix_hash(a: u64, b: u64) -> u64 {
    // used in src/rust/gen_init_ffi/src/ffi/Init/Prelude.rs:284 (🔌)
    let mut h = a ^ b
        .wrapping_add(0x9e37_79b9_7f4a_7c15)
        .wrapping_add(a << 6)
        .wrapping_add(a >> 2);
    h ^= h >> 33;
    h = h.wrapping_mul(0xff51_afd7_ed55_8ccd);
    h ^= h >> 33;
    h
}

#[inline]
pub unsafe fn lean_string_utf8_byte_size(obj: *mut LeanObject) -> *mut LeanObject {
    // used in src/rust/gen_init_ffi/src/ffi/Init/Prelude.rs:271 (🔌)
    unsafe {
        lean_box(
            (*(obj as *const LeanStringObject<0>))
                .m_size
                .saturating_sub(1),
        )
    }
}

#[inline]
pub unsafe fn lean_string_to_utf8(obj: *mut LeanObject) -> *mut LeanObject {
    // used in src/rust/gen_init_ffi/src/ffi/common/lean_string_to_utf8.rs:9 (🔌)
    unsafe {
        let size = (*(obj as *const LeanStringObject<0>))
            .m_size
            .saturating_sub(1);
        let result = lean_alloc_sarray(1, size, size);
        ptr::copy_nonoverlapping(lean_string_data(obj), lean_sarray_data(result), size);
        result
    }
}

#[inline]
pub unsafe fn lean_string_from_utf8_unchecked(bytes: *mut LeanObject) -> *mut LeanObject {
    // used in src/rust/gen_init_ffi/src/ffi/Init/Prelude.rs:70 (🔌)
    unsafe {
        let size = lean_sarray_size(bytes);
        let result = lean_alloc_string(size + 1, size + 1, size);
        ptr::copy_nonoverlapping(lean_sarray_data(bytes), lean_string_data(result), size);
        *lean_string_data(result).add(size) = 0;
        lean_dec(bytes);
        result
    }
}

#[inline]
pub unsafe fn lean_string_mk(_list: *mut LeanObject) -> *mut LeanObject {
    // used in src/rust/gen_init_ffi/src/ffi/common/lean_string_mk.rs:9 (🔌)
    panic!("lean_string_mk requires list traversal runtime");
}

#[inline]
pub unsafe fn lean_string_dec_eq(a: *mut LeanObject, b: *mut LeanObject) -> u8 {
    // used in src/rust/gen_init_ffi/src/ffi/Init/Prelude.rs:266 (🔌)
    unsafe {
        let a_size = (*(a as *const LeanStringObject<0>)).m_size;
        let b_size = (*(b as *const LeanStringObject<0>)).m_size;
        if a_size != b_size {
            return 0;
        }
        (core::slice::from_raw_parts(lean_string_data(a), a_size)
            == core::slice::from_raw_parts(lean_string_data(b), b_size)) as u8
    }
}

#[inline]
pub unsafe fn lean_string_hash(obj: *mut LeanObject) -> u64 {
    // used in src/rust/gen_init_ffi/src/ffi/Init/Prelude.rs:289 (🔌)
    unsafe {
        let size = (*(obj as *const LeanStringObject<0>))
            .m_size
            .saturating_sub(1);
        let mut hash = 0xcbf2_9ce4_8422_2325u64;
        for byte in core::slice::from_raw_parts(lean_string_data(obj), size) {
            hash ^= *byte as u64;
            hash = hash.wrapping_mul(0x1000_0000_01b3);
        }
        hash
    }
}

#[inline]
pub unsafe fn lean_panic_fn_borrowed(
    // used in src/rust/gen_init_ffi/src/ffi/Init/Prelude.rs:276 (🔌)
    default_val: *mut LeanObject,
    msg: *mut LeanObject,
) -> *mut LeanObject {
    unsafe {
        lean_inc(default_val);
        lean_dec(msg);
        default_val
    }
}

#[inline]
pub unsafe fn lean_sorry(_: u8) -> *mut LeanObject {
    // used in src/rust/gen_init_ffi/src/ffi/Init/Prelude.rs:80 (🔌)
    panic!("executed 'sorry'")
}

#[inline]
pub unsafe fn lean_name_eq(a: *mut LeanObject, b: *mut LeanObject) -> u8 {
    // used in src/rust/gen_init_ffi/src/ffi/Init/Prelude.rs:294 (🔌)
    (a == b) as u8
}

#[inline]
pub unsafe fn lean_system_platform_nbits(_: *mut LeanObject) -> *mut LeanObject {
    // used in src/rust/gen_init_ffi/src/ffi/Init/Prelude.rs:135 (🔌)
    unsafe { lean_box(usize::BITS as usize) }
}

#[inline]
pub unsafe fn lean_to_ctor(obj: *mut LeanObject) -> *mut LeanCtorObject<0> {
    unsafe {
        debug_assert!(lean_is_ctor(obj));
        obj as *mut LeanCtorObject<0>
    }
}

#[inline]
pub unsafe fn lean_to_closure(obj: *mut LeanObject) -> *mut LeanClosureObject<0> {
    unsafe {
        debug_assert!(lean_is_closure(obj));
        obj as *mut LeanClosureObject<0>
    }
}

#[inline]
pub unsafe fn lean_to_array(obj: *mut LeanObject) -> *mut LeanArrayObject<0> {
    unsafe {
        debug_assert!(lean_is_array(obj));
        obj as *mut LeanArrayObject<0>
    }
}

#[inline]
pub unsafe fn lean_to_sarray(obj: *mut LeanObject) -> *mut LeanScalarArray<0> {
    unsafe {
        debug_assert!(lean_is_sarray(obj));
        obj as *mut LeanScalarArray<0>
    }
}

#[inline]
pub unsafe fn lean_to_string(obj: *mut LeanObject) -> *mut LeanStringObject<0> {
    unsafe {
        debug_assert!(lean_is_string(obj));
        obj as *mut LeanStringObject<0>
    }
}

#[inline]
pub unsafe fn lean_to_thunk(obj: *mut LeanObject) -> *mut LeanThunkObject {
    unsafe {
        debug_assert!(lean_is_thunk(obj));
        obj as *mut LeanThunkObject
    }
}

#[inline]
pub unsafe fn lean_to_task(obj: *mut LeanObject) -> *mut LeanTaskObject {
    unsafe {
        debug_assert!(lean_is_task(obj));
        obj as *mut LeanTaskObject
    }
}

#[inline]
pub unsafe fn lean_to_promise(obj: *mut LeanObject) -> *mut LeanPromiseObject {
    unsafe {
        debug_assert!(lean_is_promise(obj));
        obj as *mut LeanPromiseObject
    }
}

#[inline]
pub unsafe fn lean_to_ref(obj: *mut LeanObject) -> *mut LeanRefObject {
    unsafe { debug_assert!(lean_is_ref(obj)); }
    obj as *mut LeanRefObject
}

#[inline]
pub unsafe fn lean_to_external(obj: *mut LeanObject) -> *mut LeanExternalObject {
    unsafe { debug_assert!(lean_is_external(obj)); }
    obj as *mut LeanExternalObject
}

#[inline]
pub unsafe fn lean_is_exclusive_obj(obj: *mut LeanObject) -> u8 {
    // used in src/rust/gen_init_ffi/src/ffi/Init/Util.rs:25 (🔌)
    unsafe { lean_is_exclusive(obj) as u8 }
}

#[inline]
pub unsafe fn lean_is_shared(obj: *mut LeanObject) -> bool {
    unsafe { lean_is_st(obj) && (*obj).rc > 1 }
}

#[inline]
pub unsafe fn lean_name_eq_export(n1: *mut LeanObject, n2: *mut LeanObject) -> u8 {
    unsafe { lean_name_eq(n1, n2) }
}

pub unsafe fn lean_external_noop_finalize(_: *mut c_void) {}

pub unsafe fn lean_external_noop_foreach(_: *mut c_void, _: *mut LeanObject) {}

#[inline]
pub unsafe fn lean_register_external_class(
    finalize: Option<LeanExternalFinalizeProc>,
    foreach: Option<LeanExternalForeachProc>,
) -> *mut LeanExternalClass {
    let class = Box::into_raw(Box::new(LeanExternalClass {
        m_finalize: finalize.unwrap_or(lean_external_noop_finalize),
        m_foreach: foreach.unwrap_or(lean_external_noop_foreach),
    }));
    EXTERNAL_CLASSES.lock().unwrap().push(class as usize);
    class
}

#[inline]
pub unsafe fn lean_finalize_external_classes() {
    unsafe {
        let mut classes = EXTERNAL_CLASSES.lock().unwrap();
        for class in classes.drain(..) {
            drop(Box::from_raw(class as *mut LeanExternalClass));
        }
    }
}

#[inline]
pub unsafe fn lean_runtime_alloc_external(
    class: *mut LeanExternalClass,
    data: *mut c_void,
) -> *mut LeanObject {
    unsafe {
        let obj = lean_alloc_small_object(core::mem::size_of::<LeanExternalObject>())
            as *mut LeanExternalObject;
        (*obj).m_header.rc = 1;
        (*obj).m_header.other = 0;
        (*obj).m_header.tag = LEAN_EXTERNAL_TAG;
        (*obj).m_class = class;
        (*obj).m_data = data;
        obj as *mut LeanObject
    }
}

#[inline]
pub unsafe fn lean_runtime_get_external_data(obj: *mut LeanObject) -> *mut c_void {
    unsafe { (*(obj as *mut LeanExternalObject)).m_data }
}

#[inline]
pub unsafe fn lean_alloc_external(
    class: *mut LeanExternalClass,
    data: *mut c_void,
) -> *mut LeanObject {
    unsafe { lean_runtime_alloc_external(class, data) }
}

#[inline]
pub unsafe fn lean_get_external_class(obj: *mut LeanObject) -> *mut LeanExternalClass {
    unsafe { (*(obj as *mut LeanExternalObject)).m_class }
}

#[inline]
pub unsafe fn lean_set_external_data(obj: *mut LeanObject, data: *mut c_void) -> *mut LeanObject {
    unsafe {
        if lean_is_exclusive(obj) {
            (*(obj as *mut LeanExternalObject)).m_data = data;
            obj
        } else {
            let new_obj = lean_alloc_external(lean_get_external_class(obj), data);
            lean_dec_ref(obj);
            new_obj
        }
    }
}
