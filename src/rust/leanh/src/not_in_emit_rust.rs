use core::ptr;
use core::sync::atomic::{AtomicI32, Ordering};
use std::alloc::{Layout, alloc, dealloc, handle_alloc_error};

use crate::{
    LEAN_ARRAY_TAG, LEAN_CLOSURE_TAG, LEAN_EXTERNAL_TAG, LEAN_MAX_CTOR_TAG, LEAN_MPZ_TAG,
    LEAN_OBJECT_SIZE_DELTA, LEAN_PROMISE_TAG, LEAN_REF_TAG, LEAN_SCALAR_ARRAY_TAG, LEAN_STRING_TAG,
    LEAN_TASK_TAG, LEAN_THUNK_TAG, LeanArrayObject, LeanClosureObject, LeanExternalObject,
    LeanMpzObject, LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray,
    LeanStringObject, LeanTaskObject, LeanThunkObject, ObjInitFn, lean_is_scalar,
    lean_mark_persistent,
};

// NOT IN EmitRust; here because it is used in `lean_alloc_closure`, `lean_apply_m`, `lean_ctor_release`, `lean_dec`, and 4 more EmitRust functions.
#[inline]
pub unsafe fn get_next(obj: *mut LeanObject) -> *mut LeanObject {
    unsafe {
        #[cfg(target_pointer_width = "64")]
        {
            let mut header = 0usize;
            ptr::copy_nonoverlapping(obj as *const u8, &mut header as *mut usize as *mut u8, 8);
            header &= !(0xffff_usize << 48);
            header as *mut LeanObject
        }
    }
}

// NOT IN EmitRust; here because it is used in `lean_alloc_ctor`, `lean_box_float`, `lean_box_float32`, `lean_box_uint32`, and 3 more EmitRust functions.
#[inline]
pub fn lean_align(v: usize, a: usize) -> usize {
    (v / a) * a + a * (!v.is_multiple_of(a)) as usize
}

// NOT IN EmitRust; here because it is used in `lean_alloc_closure`, `lean_apply_m`, `lean_ctor_release`, `lean_dec`, and 5 more EmitRust functions.
#[inline]
pub unsafe fn lean_array_byte_size(obj: *mut LeanObject) -> usize {
    unsafe {
        core::mem::size_of::<LeanArrayObject<0>>()
            + core::mem::size_of::<*mut LeanObject>()
                * (*(obj as *const LeanArrayObject<0>)).m_capacity
    }
}

// NOT IN EmitRust; here because it is used in `lean_alloc_closure`, `lean_apply_m`, `lean_ctor_release`, `lean_dec`, and 4 more EmitRust functions.
#[inline]
pub unsafe fn lean_array_cptr(obj: *mut LeanObject) -> *mut *mut LeanObject {
    unsafe { (*(obj as *mut LeanArrayObject<0>)).m_data.as_mut_ptr() }
}

// NOT IN EmitRust; here because it is used in `lean_alloc_closure`, `lean_apply_m`, `lean_ctor_release`, `lean_dec`, and 4 more EmitRust functions.
#[inline]
pub unsafe fn lean_array_size(obj: *mut LeanObject) -> usize {
    unsafe { (*(obj as *const LeanArrayObject<0>)).m_size }
}

// NOT IN EmitRust; here because it is used in `lean_alloc_closure`, `lean_apply_m`, `lean_closure_set`, `lean_ctor_release`, and 5 more EmitRust functions.
#[inline]
pub unsafe fn lean_closure_arg_cptr(obj: *mut LeanObject) -> *mut *mut LeanObject {
    unsafe { (*(obj as *mut LeanClosureObject<0>)).m_objs.as_mut_ptr() }
}

// NOT IN EmitRust; here because it is used in `lean_alloc_closure`, `lean_apply_m`, `lean_closure_set`, `lean_ctor_release`, and 6 more EmitRust functions.
#[inline]
pub unsafe fn lean_closure_num_fixed(obj: *mut LeanObject) -> usize {
    unsafe { (*(obj as *const LeanClosureObject<0>)).m_num_fixed as usize }
}

// NOT IN EmitRust; here because it is used in `lean_alloc_closure`, `lean_apply_m`, `lean_ctor_release`, `lean_dec`, and 5 more EmitRust functions.
#[inline]
pub unsafe fn lean_closure_byte_size(obj: *mut LeanObject) -> usize {
    unsafe {
        core::mem::size_of::<LeanClosureObject<0>>()
            + core::mem::size_of::<*mut LeanObject>() * lean_closure_num_fixed(obj)
    }
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

// NOT IN EmitRust; here because it is used in `lean_alloc_ctor`, `lean_box_float`, `lean_box_float32`, `lean_box_uint32`, and 3 more EmitRust functions.
#[inline]
pub unsafe fn lean_alloc_small_object(size: usize) -> *mut LeanObject {
    unsafe {
        let size = lean_align(size, LEAN_OBJECT_SIZE_DELTA);
        let obj = lean_global_alloc(size) as *mut LeanObject;
        (*obj).cs_size = size as u16;
        obj
    }
}

// NOT IN EmitRust; here because it is used in `lean_alloc_ctor`, `lean_box_float`, `lean_box_float32`, `lean_box_uint32`, and 3 more EmitRust functions.
#[inline]
pub unsafe fn lean_alloc_ctor_memory(size: usize) -> *mut LeanObject {
    unsafe {
        let aligned = lean_align(size, LEAN_OBJECT_SIZE_DELTA);
        let obj = lean_alloc_small_object(aligned);
        if aligned > size {
            (obj as *mut u8).add(size).write_bytes(0, aligned - size);
        }
        obj
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

// NOT IN EmitRust; here because it is used in `lean_alloc_closure`, `lean_apply_m`, `lean_ctor_release`, `lean_dec`, and 5 more EmitRust functions.
#[inline]
pub unsafe fn lean_dealloc(obj: *mut LeanObject, size: usize) {
    unsafe {
        lean_global_dealloc(obj as *mut u8, size);
    }
}

// NOT IN EmitRust; here because it is used in `lean_alloc_closure`, `lean_apply_m`, `lean_ctor_release`, `lean_dec`, and 5 more EmitRust functions.
#[inline]
pub unsafe fn lean_free_small_object(obj: *mut LeanObject) {
    unsafe {
        lean_global_dealloc(obj as *mut u8, (*obj).cs_size as usize);
    }
}

// NOT IN EmitRust; here because it is used in `lean_dec_ref_known`, `lean_inc`, `lean_inc_n`, `lean_inc_ref`, and 2 more EmitRust functions.
#[inline]
pub unsafe fn lean_is_st(obj: *mut LeanObject) -> bool {
    unsafe { (*obj).rc > 0 }
}

// NOT IN EmitRust; here because it is used in `lean_alloc_closure`, `lean_apply_m`, `lean_ctor_release`, `lean_dec`, and 5 more EmitRust functions.
#[inline]
pub unsafe fn lean_mpz_clear(obj: *mut LeanObject) {
    unsafe {
        let mpz = &mut (*(obj as *mut LeanMpzObject)).m_value[0];
        if !mpz.mp_d.is_null() {
            libc::free(mpz.mp_d.cast());
            mpz.mp_alloc = 0;
            mpz.mp_size = 0;
            mpz.mp_d = ptr::null_mut();
        }
    }
}

// NOT IN EmitRust; here because it is used in `lean_alloc_closure`, `lean_apply_m`, `lean_box_float`, `lean_box_float32`, and 37 more EmitRust functions.
#[inline]
pub unsafe fn lean_ptr_tag(obj: *mut LeanObject) -> u8 {
    unsafe { (*obj).tag }
}

// NOT IN EmitRust; here because it is used in `lean_alloc_closure`, `lean_apply_m`, `lean_box_float`, `lean_box_float32`, and 28 more EmitRust functions.
#[inline]
pub unsafe fn lean_ctor_num_objs(obj: *mut LeanObject) -> usize {
    unsafe {
        debug_assert!(lean_ptr_tag(obj) <= LEAN_MAX_CTOR_TAG);
        (*obj).other as usize
    }
}

// NOT IN EmitRust; here because it is used in `lean_alloc_closure`, `lean_apply_m`, `lean_box_float`, `lean_box_float32`, and 32 more EmitRust functions.
#[inline]
pub unsafe fn lean_ctor_obj_cptr(obj: *mut LeanObject) -> *mut *mut LeanObject {
    unsafe {
        debug_assert!(lean_ptr_tag(obj) <= LEAN_MAX_CTOR_TAG);
        (obj as *mut u8).add(core::mem::size_of::<LeanObject>()) as *mut *mut LeanObject
    }
}

// NOT IN EmitRust; here because it is used in `lean_box_float`, `lean_box_float32`, `lean_box_uint32`, `lean_box_uint64`, and 18 more EmitRust functions.
#[inline]
pub unsafe fn lean_ctor_scalar_cptr(obj: *mut LeanObject, offset: usize) -> *mut u8 {
    unsafe { lean_ctor_obj_cptr(obj).cast::<u8>().add(offset) }
}

// NOT IN EmitRust; here because it is used in `lean_dec_ref_known`.
#[inline]
pub unsafe fn lean_is_ref(obj: *mut LeanObject) -> bool {
    unsafe { lean_ptr_tag(obj) == LEAN_REF_TAG }
}

// NOT IN EmitRust; here because it is used in `lean_alloc_closure`, `lean_apply_m`, `lean_ctor_release`, `lean_dec`, and 5 more EmitRust functions.
#[inline]
pub unsafe fn lean_sarray_byte_size(obj: *mut LeanObject) -> usize {
    unsafe {
        core::mem::size_of::<LeanScalarArray<0>>()
            + (*obj).other as usize * (*(obj as *const LeanScalarArray<0>)).m_capacity
    }
}

// NOT IN EmitRust; here because it is used in `lean_alloc_closure`, `lean_apply_m`, `lean_ctor_release`, `lean_dec`, and 5 more EmitRust functions.
#[inline]
pub unsafe fn lean_string_byte_size(obj: *mut LeanObject) -> usize {
    unsafe {
        core::mem::size_of::<LeanStringObject<0>>()
            + (*(obj as *const LeanStringObject<0>)).m_capacity
    }
}

// NOT IN EmitRust; here because it is used in `lean_dec_ref_known`, `lean_del_object`.
#[inline]
pub unsafe fn lean_free_object(obj: *mut LeanObject) {
    unsafe {
        match lean_ptr_tag(obj) {
            LEAN_ARRAY_TAG => lean_dealloc(obj, lean_array_byte_size(obj)),
            LEAN_SCALAR_ARRAY_TAG => lean_dealloc(obj, lean_sarray_byte_size(obj)),
            LEAN_STRING_TAG => lean_dealloc(obj, lean_string_byte_size(obj)),
            LEAN_CLOSURE_TAG => lean_dealloc(obj, lean_closure_byte_size(obj)),
            LEAN_MPZ_TAG => {
                lean_mpz_clear(obj);
                lean_free_small_object(obj);
            }
            _ => lean_free_small_object(obj),
        }
    }
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

// NOT IN EmitRust; here because it is used in `lean_alloc_closure`, `lean_apply_m`, `lean_ctor_release`, `lean_dec`, and 4 more EmitRust functions.
#[inline]
pub unsafe fn pop_back(todo: &mut *mut LeanObject) -> *mut LeanObject {
    unsafe {
        let result = *todo;
        *todo = get_next(result);
        result
    }
}

// NOT IN EmitRust; here because it is used in `lean_alloc_closure`, `lean_apply_m`, `lean_ctor_release`, `lean_dec`, and 4 more EmitRust functions.
#[inline]
pub unsafe fn set_next(obj: *mut LeanObject, next: *mut LeanObject) {
    unsafe {
        #[cfg(target_pointer_width = "64")]
        {
            let mut hi = 0u16;
            ptr::copy_nonoverlapping((obj as *const u8).add(6), &mut hi as *mut u16 as *mut u8, 2);
            let header = ((hi as usize) << 48) | (next as usize);
            ptr::copy_nonoverlapping(&header as *const usize as *const u8, obj as *mut u8, 8);
        }
    }
}

// NOT IN EmitRust; here because it is used in `lean_alloc_closure`, `lean_apply_m`, `lean_ctor_release`, `lean_dec`, and 4 more EmitRust functions.
#[inline]
pub unsafe fn push_back(todo: &mut *mut LeanObject, obj: *mut LeanObject) {
    unsafe {
        set_next(obj, *todo);
        *todo = obj;
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

#[inline]
pub unsafe fn lean_alloc_ctor(tag: u32, num_objs: u32, scalar_size: u32) -> *mut LeanObject {
    unsafe {
        debug_assert!(tag <= LEAN_MAX_CTOR_TAG as u32);
        debug_assert!(num_objs < 256);
        debug_assert!(scalar_size < 1024);
        let byte_size = core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * num_objs as usize
            + scalar_size as usize;
        let obj = lean_alloc_ctor_memory(byte_size);
        (*obj).rc = 1;
        (*obj).other = num_objs as u8;
        (*obj).tag = tag as u8;
        obj
    }
}

#[inline]
pub unsafe fn lean_box(n: usize) -> *mut LeanObject {
    ((n << 1) | 1) as *mut LeanObject
}

// NOT IN EmitRust; here because it is used in `lean_cstr_to_nat`, `lean_unsigned_to_nat`.
#[inline]
pub unsafe fn lean_usize_to_nat(value: usize) -> *mut LeanObject {
    unsafe {
        if value <= (usize::MAX >> 1) {
            lean_box(value)
        } else {
            panic!("big Nat is not supported in leanh.rs")
        }
    }
}

// Private implementation helpers for the hardcoded EmitRust surface.
// NOT IN EmitRust; here because it is used in `lean_alloc_closure`, `lean_apply_m`, `lean_ctor_release`, `lean_dec`, and 14 more EmitRust functions.
#[inline]
pub fn lean_is_scalar_bool(obj: *mut LeanObject) -> bool {
    // same as
    // (obj as Size) & 1 == 1
    lean_is_scalar(obj) != 0 // same as `== 1`
}

// NOT IN EmitRust; here because it is used in `lean_alloc_closure`, `lean_apply_m`, `lean_ctor_release`, `lean_dec`, and 4 more EmitRust functions.
#[inline]
pub unsafe fn dec_for_del(obj: *mut LeanObject, todo: &mut *mut LeanObject) {
    unsafe {
        if lean_is_scalar_bool(obj) {
            return;
        }
        if (*obj).rc > 1 {
            (*obj).rc -= 1;
        } else if (*obj).rc == 1 {
            push_back(todo, obj);
        } else if (*obj).rc != 0 {
            let rc = core::ptr::addr_of_mut!((*obj).rc).cast::<AtomicI32>();
            if (*rc).fetch_add(1, Ordering::AcqRel) == -1 {
                push_back(todo, obj);
            }
        }
    }
}

// NOT IN EmitRust; here because it is used in `lean_alloc_closure`, `lean_apply_m`, `lean_ctor_release`, `lean_dec`, and 4 more EmitRust functions.
#[inline]
pub unsafe fn lean_del_core_other(obj: *mut LeanObject, tag: u8, todo: &mut *mut LeanObject) {
    unsafe {
        match tag {
            LEAN_CLOSURE_TAG => {
                let args = lean_closure_arg_cptr(obj);
                for i in 0..lean_closure_num_fixed(obj) {
                    dec_for_del(*args.add(i), todo);
                }
                lean_dealloc(obj, lean_closure_byte_size(obj));
            }
            LEAN_ARRAY_TAG => {
                let data = lean_array_cptr(obj);
                for i in 0..lean_array_size(obj) {
                    dec_for_del(*data.add(i), todo);
                }
                lean_dealloc(obj, lean_array_byte_size(obj));
            }
            LEAN_SCALAR_ARRAY_TAG => lean_dealloc(obj, lean_sarray_byte_size(obj)),
            LEAN_STRING_TAG => lean_dealloc(obj, lean_string_byte_size(obj)),
            LEAN_THUNK_TAG => {
                let thunk = obj as *mut LeanThunkObject;
                let closure = (*thunk).m_closure.load(Ordering::Acquire);
                if !closure.is_null() {
                    dec_for_del(closure, todo);
                }
                let value = (*thunk).m_value.load(Ordering::Acquire);
                if !value.is_null() {
                    dec_for_del(value, todo);
                }
                lean_free_small_object(obj);
            }
            LEAN_REF_TAG => {
                let r = obj as *mut LeanRefObject;
                if !(*r).m_value.is_null() {
                    dec_for_del((*r).m_value, todo);
                }
                lean_free_small_object(obj);
            }
            LEAN_PROMISE_TAG => {
                let promise = obj as *mut LeanPromiseObject;
                if !(*promise).m_result.is_null() {
                    dec_for_del((*promise).m_result as *mut LeanObject, todo);
                }
                lean_free_small_object(obj);
            }
            LEAN_TASK_TAG => {
                let task = obj as *mut LeanTaskObject;
                let value = (*task).m_value.load(Ordering::Acquire);
                if !value.is_null() {
                    dec_for_del(value, todo);
                }
                lean_free_small_object(obj);
            }
            LEAN_EXTERNAL_TAG => {
                let external = obj as *mut LeanExternalObject;
                ((*(*external).m_class).m_finalize)((*external).m_data);
                lean_free_small_object(obj);
            }
            LEAN_MPZ_TAG => {
                lean_mpz_clear(obj);
                lean_free_small_object(obj);
            }
            _ => panic!("lean_del_core: unknown object tag {tag}"),
        }
    }
}

// NOT IN EmitRust; here because it is used in `lean_alloc_closure`, `lean_apply_m`, `lean_ctor_release`, `lean_dec`, and 4 more EmitRust functions.
#[inline]
pub unsafe fn lean_del_core(obj: *mut LeanObject, todo: &mut *mut LeanObject) {
    unsafe {
        let tag = lean_ptr_tag(obj);
        if tag <= LEAN_MAX_CTOR_TAG {
            let fields = lean_ctor_obj_cptr(obj);
            for i in 0..lean_ctor_num_objs(obj) {
                dec_for_del(*fields.add(i), todo);
            }
            lean_free_small_object(obj);
        } else {
            lean_del_core_other(obj, tag, todo);
        }
    }
}

// NOT IN EmitRust; here because it is used in `lean_alloc_closure`, `lean_mk_string`, `lean_mk_string_unchecked`.
#[inline]
pub unsafe fn lean_alloc_object(size: usize) -> *mut LeanObject {
    unsafe {
        let obj = lean_global_alloc(size) as *mut LeanObject;
        (*obj).cs_size = 0;
        obj
    }
}

// NOT IN EmitRust; here because it is used in `lean_mk_string`, `lean_mk_string_unchecked`.
#[inline]
pub unsafe fn lean_alloc_string(byte_size: usize, capacity: usize, len: usize) -> *mut LeanObject {
    unsafe {
        let obj = lean_alloc_object(core::mem::size_of::<LeanStringObject<0>>() + capacity)
            as *mut LeanStringObject<0>;
        (*obj).m_header.rc = 1;
        (*obj).m_header.cs_size = 0;
        (*obj).m_header.other = 0;
        (*obj).m_header.tag = LEAN_STRING_TAG;
        (*obj).m_size = byte_size;
        (*obj).m_capacity = capacity;
        (*obj).m_length = len;
        obj as *mut LeanObject
    }
}

// NOT IN EmitRust; here because it is used in `lean_apply_m`, `lean_ctor_release`, `lean_dec`, `lean_dec_ref`, and 1 more EmitRust functions.
#[inline]
pub unsafe fn lean_dec_ref_cold(mut obj: *mut LeanObject) {
    unsafe {
        if lean_is_scalar_bool(obj) {
            return;
        }
        if (*obj).rc == 1 || {
            let rc = core::ptr::addr_of_mut!((*obj).rc).cast::<AtomicI32>();
            (*rc).fetch_add(1, Ordering::AcqRel) == -1
        } {
            let mut todo = ptr::null_mut();
            loop {
                lean_del_core(obj, &mut todo);
                if todo.is_null() {
                    return;
                }
                obj = pop_back(&mut todo);
            }
        }
    }
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
