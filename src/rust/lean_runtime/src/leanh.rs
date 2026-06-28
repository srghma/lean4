/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

#![allow(dead_code, non_upper_case_globals, non_snake_case)]

use core::ffi::{c_char, c_void};
use core::ptr;
use core::sync::atomic::{AtomicI32, AtomicPtr, Ordering};
use std::alloc::{Layout, alloc, dealloc, handle_alloc_error};
use std::cell::Cell;

// This module is the Rust equivalent of upstream `lean.h` for ABI layouts and
// helpers hardcoded by EmitRust. Do not import runtime modules here; runtime
// modules may depend on `leanh`, but `leanh` must stay the top-level ABI layer.

type Size = usize;

pub const LEAN_CLOSURE_MAX_ARGS: u32 = 16;
pub const LEAN_MAX_SMALL_NAT: usize = usize::MAX >> 1;

#[repr(C)]
pub struct LeanObject {
    pub rc: i32,
    pub cs_size: u16,
    pub other: u8,
    pub tag: u8,
}

#[repr(C)]
pub struct LeanCtorObject<const N: usize> {
    pub m_header: LeanObject,
    pub m_objs: [*mut LeanObject; N],
}

unsafe impl<const N: usize> Sync for LeanCtorObject<N> {}

pub type LeanExternalFinalizeProc = unsafe fn(*mut c_void);
pub type LeanExternalForeachProc = unsafe fn(*mut c_void, *mut LeanObject);
pub type ObjInitFn = unsafe fn() -> *mut LeanObject;
pub type U8InitFn = unsafe fn() -> u8;
pub type U16InitFn = unsafe fn() -> u16;
pub type U32InitFn = unsafe fn() -> u32;
pub type U64InitFn = unsafe fn() -> u64;
pub type UsizeInitFn = unsafe fn() -> usize;
pub type F32InitFn = unsafe fn() -> f32;
pub type F64InitFn = unsafe fn() -> f64;

#[repr(C)]
pub struct LeanExternalClass {
    pub m_finalize: LeanExternalFinalizeProc,
    pub m_foreach: LeanExternalForeachProc,
}

#[repr(C)]
pub struct LeanArrayObject<const N: usize> {
    pub m_header: LeanObject,
    pub m_size: Size,
    pub m_capacity: Size,
    pub m_data: [*mut LeanObject; N],
}

unsafe impl<const N: usize> Sync for LeanArrayObject<N> {}

#[repr(C)]
pub struct LeanStringObject<const N: usize> {
    pub m_header: LeanObject,
    pub m_size: Size,
    pub m_capacity: Size,
    pub m_length: Size,
    pub m_data: [u8; N],
}

unsafe impl<const N: usize> Sync for LeanStringObject<N> {}

#[repr(C)]
pub struct LeanClosureObject<const N: usize> {
    pub m_header: LeanObject,
    pub m_fun: *const c_void,
    pub m_arity: u16,
    pub m_num_fixed: u16,
    pub m_objs: [*mut LeanObject; N],
}

unsafe impl<const N: usize> Sync for LeanClosureObject<N> {}

#[repr(C)]
pub struct LeanScalarArray<const N: usize> {
    pub m_header: LeanObject,
    pub m_size: Size,
    pub m_capacity: Size,
    pub m_data: [u8; N],
}

unsafe impl<const N: usize> Sync for LeanScalarArray<N> {}

#[repr(C)]
pub struct LeanPromiseObject {
    pub m_header: LeanObject,
    pub m_result: *mut LeanTaskObject,
}

#[repr(C)]
pub struct LeanThunkObject {
    pub m_header: LeanObject,
    pub m_value: AtomicPtr<LeanObject>,
    pub m_closure: AtomicPtr<LeanObject>,
}

#[repr(C)]
pub struct LeanRefObject {
    pub m_header: LeanObject,
    pub m_value: *mut LeanObject,
}

#[repr(C)]
pub struct LeanOnceCell {
    pub state: AtomicI32,
    pub lock: AtomicI32,
}

#[repr(C)]
struct LeanTaskImp {
    m_closure: *mut LeanObject,
    m_head_dep: *mut LeanTaskObject,
    m_next_dep: *mut LeanTaskObject,
    m_prio: u32,
    m_canceled: bool,
    m_keep_alive: bool,
    m_deleted: bool,
}

#[repr(C)]
pub struct LeanTaskObject {
    pub m_header: LeanObject,
    pub m_value: AtomicPtr<LeanObject>,
    pub m_imp: *mut c_void,
}

#[repr(C)]
pub struct LeanExternalObject {
    pub m_header: LeanObject,
    pub m_class: *mut LeanExternalClass,
    pub m_data: *mut c_void,
}

#[repr(C)]
struct LeanMpzStruct {
    mp_alloc: i32,
    mp_size: i32,
    mp_d: *mut u64,
}

type MpzT = [LeanMpzStruct; 1];

#[repr(C)]
struct LeanMpzObject {
    m_header: LeanObject,
    m_value: MpzT,
}

const LEAN_MAX_CTOR_TAG: u8 = 243;
const LEAN_PROMISE_TAG: u8 = 244;
const LEAN_CLOSURE_TAG: u8 = 245;
const LEAN_ARRAY_TAG: u8 = 246;
const LEAN_STRUCT_ARRAY_TAG: u8 = 247;
const LEAN_SCALAR_ARRAY_TAG: u8 = 248;
const LEAN_STRING_TAG: u8 = 249;
const LEAN_MPZ_TAG: u8 = 250;
const LEAN_THUNK_TAG: u8 = 251;
const LEAN_TASK_TAG: u8 = 252;
const LEAN_REF_TAG: u8 = 253;
const LEAN_EXTERNAL_TAG: u8 = 254;
const LEAN_RESERVED_TAG: u8 = 255;
const LEAN_OBJECT_SIZE_DELTA: usize = 8;

thread_local! {
    static G_TO_FREE: Cell<*mut LeanObject> = const { Cell::new(ptr::null_mut()) };
}

#[inline]
pub unsafe fn lean_is_scalar(obj: *mut LeanObject) -> u8 {
    ((obj as usize & 1) == 1) as u8
}

#[inline]
unsafe fn lean_is_scalar_bool(obj: *mut LeanObject) -> bool {
    lean_is_scalar(obj) != 0
}

#[inline]
pub unsafe fn lean_box(n: usize) -> *mut LeanObject {
    ((n << 1) | 1) as *mut LeanObject
}

#[inline]
pub unsafe fn lean_unbox(obj: *mut LeanObject) -> usize {
    (obj as usize) >> 1
}

#[inline]
unsafe fn lean_ptr_tag(obj: *mut LeanObject) -> u8 {
    (*obj).tag
}

#[cfg(false)]
#[inline]
pub unsafe fn lean_ptr_other(obj: *mut LeanObject) -> u8 {
    (*obj).other
}

#[inline]
unsafe fn lean_has_rc(obj: *mut LeanObject) -> bool {
    (*obj).rc != 0
}

#[inline]
unsafe fn lean_is_st(obj: *mut LeanObject) -> bool {
    (*obj).rc > 0
}

#[cfg(false)]
#[inline]
pub unsafe fn lean_is_mt(obj: *mut LeanObject) -> bool {
    (*obj).rc < 0
}

#[cfg(false)]
#[inline]
pub unsafe fn lean_is_persistent(obj: *mut LeanObject) -> bool {
    (*obj).rc == 0
}

#[inline]
pub unsafe fn lean_inc_ref_n(obj: *mut LeanObject, n: usize) {
    if lean_is_st(obj) {
        (*obj).rc += n as i32;
    } else if (*obj).rc != 0 {
        let rc = (&raw mut (*obj).rc).cast::<AtomicI32>();
        (*rc).fetch_sub(n as i32, Ordering::Relaxed);
    }
}

#[inline]
pub unsafe fn lean_inc_ref(obj: *mut LeanObject) {
    lean_inc_ref_n(obj, 1);
}

#[inline]
pub unsafe fn lean_dec_ref(obj: *mut LeanObject) {
    if (*obj).rc > 1 {
        (*obj).rc -= 1;
    } else if (*obj).rc != 0 {
        lean_dec_ref_cold(obj);
    }
}

#[inline]
pub unsafe fn lean_dec_ref_known(obj: *mut LeanObject, objs: u32) {
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

#[inline]
pub unsafe fn lean_del_object(obj: *mut LeanObject) {
    if !lean_is_scalar_bool(obj) {
        lean_free_object(obj);
    }
}

#[inline]
pub unsafe fn lean_inc(obj: *mut LeanObject) {
    if !lean_is_scalar_bool(obj) {
        lean_inc_ref(obj);
    }
}

#[inline]
pub unsafe fn lean_inc_n(obj: *mut LeanObject, n: usize) {
    if !lean_is_scalar_bool(obj) {
        lean_inc_ref_n(obj, n);
    }
}

#[inline]
pub unsafe fn lean_dec(obj: *mut LeanObject) {
    if !lean_is_scalar_bool(obj) {
        lean_dec_ref(obj);
    }
}

#[cfg(false)]
#[inline]
pub unsafe fn lean_is_ctor(obj: *mut LeanObject) -> bool {
    lean_ptr_tag(obj) <= LEAN_MAX_CTOR_TAG
}

#[cfg(false)]
#[inline]
pub unsafe fn lean_is_closure(obj: *mut LeanObject) -> bool {
    lean_ptr_tag(obj) == LEAN_CLOSURE_TAG
}

#[cfg(false)]
#[inline]
pub unsafe fn lean_is_array(obj: *mut LeanObject) -> bool {
    lean_ptr_tag(obj) == LEAN_ARRAY_TAG
}

#[cfg(false)]
#[inline]
pub unsafe fn lean_is_sarray(obj: *mut LeanObject) -> bool {
    lean_ptr_tag(obj) == LEAN_SCALAR_ARRAY_TAG
}

#[cfg(false)]
#[inline]
pub unsafe fn lean_is_string(obj: *mut LeanObject) -> bool {
    lean_ptr_tag(obj) == LEAN_STRING_TAG
}

#[cfg(false)]
#[inline]
pub unsafe fn lean_is_mpz(obj: *mut LeanObject) -> bool {
    lean_ptr_tag(obj) == LEAN_MPZ_TAG
}

#[cfg(false)]
#[inline]
pub unsafe fn lean_is_thunk(obj: *mut LeanObject) -> bool {
    lean_ptr_tag(obj) == LEAN_THUNK_TAG
}

#[cfg(false)]
#[inline]
pub unsafe fn lean_is_task(obj: *mut LeanObject) -> bool {
    lean_ptr_tag(obj) == LEAN_TASK_TAG
}

#[cfg(false)]
#[inline]
pub unsafe fn lean_is_promise(obj: *mut LeanObject) -> bool {
    lean_ptr_tag(obj) == LEAN_PROMISE_TAG
}

#[cfg(false)]
#[inline]
pub unsafe fn lean_is_external(obj: *mut LeanObject) -> bool {
    lean_ptr_tag(obj) == LEAN_EXTERNAL_TAG
}

#[inline]
unsafe fn lean_is_ref(obj: *mut LeanObject) -> bool {
    lean_ptr_tag(obj) == LEAN_REF_TAG
}

#[inline]
pub unsafe fn lean_obj_tag(obj: *mut LeanObject) -> u8 {
    if lean_is_scalar_bool(obj) {
        lean_unbox(obj) as u8
    } else {
        lean_ptr_tag(obj)
    }
}

#[inline]
unsafe fn lean_ctor_num_objs(obj: *mut LeanObject) -> usize {
    debug_assert!(lean_ptr_tag(obj) <= LEAN_MAX_CTOR_TAG);
    (*obj).other as usize
}

#[inline]
unsafe fn lean_ctor_obj_cptr(obj: *mut LeanObject) -> *mut *mut LeanObject {
    debug_assert!(lean_ptr_tag(obj) <= LEAN_MAX_CTOR_TAG);
    (obj as *mut u8).add(core::mem::size_of::<LeanObject>()) as *mut *mut LeanObject
}

#[inline]
pub unsafe fn lean_ctor_get(obj: *mut LeanObject, idx: u32) -> *mut LeanObject {
    debug_assert!((idx as usize) < lean_ctor_num_objs(obj));
    *lean_ctor_obj_cptr(obj).add(idx as usize)
}

#[inline]
pub unsafe fn lean_ctor_set(obj: *mut LeanObject, idx: u32, value: *mut LeanObject) {
    debug_assert!((idx as usize) < lean_ctor_num_objs(obj));
    *lean_ctor_obj_cptr(obj).add(idx as usize) = value;
}

#[inline]
pub unsafe fn lean_ctor_set_tag(obj: *mut LeanObject, new_tag: u8) {
    debug_assert!(new_tag <= LEAN_MAX_CTOR_TAG);
    (*obj).tag = new_tag;
}

#[inline]
pub unsafe fn lean_ctor_release(obj: *mut LeanObject, idx: usize) {
    debug_assert!(idx < lean_ctor_num_objs(obj));
    let slot = lean_ctor_obj_cptr(obj).add(idx);
    lean_dec(*slot);
    *slot = lean_box(0);
}

#[inline]
unsafe fn lean_ctor_scalar_cptr(obj: *mut LeanObject, offset: usize) -> *mut u8 {
    lean_ctor_obj_cptr(obj).cast::<u8>().add(offset)
}

#[inline]
pub unsafe fn lean_ctor_get_usize(obj: *mut LeanObject, idx: usize) -> usize {
    debug_assert!(idx >= lean_ctor_num_objs(obj));
    let mut value = 0usize;
    ptr::copy_nonoverlapping(
        lean_ctor_obj_cptr(obj).cast::<u8>().add(idx * core::mem::size_of::<usize>()),
        &mut value as *mut usize as *mut u8,
        core::mem::size_of::<usize>(),
    );
    value
}

#[inline]
pub unsafe fn lean_ctor_set_usize(obj: *mut LeanObject, idx: usize, value: usize) {
    debug_assert!(idx >= lean_ctor_num_objs(obj));
    ptr::copy_nonoverlapping(
        &value as *const usize as *const u8,
        lean_ctor_obj_cptr(obj).cast::<u8>().add(idx * core::mem::size_of::<usize>()),
        core::mem::size_of::<usize>(),
    );
}

#[inline]
pub unsafe fn lean_ctor_get_uint8(obj: *mut LeanObject, offset: usize) -> u8 {
    debug_assert!(offset >= lean_ctor_num_objs(obj) * core::mem::size_of::<*mut LeanObject>());
    *lean_ctor_scalar_cptr(obj, offset)
}

#[inline]
pub unsafe fn lean_ctor_set_uint8(obj: *mut LeanObject, offset: usize, value: u8) {
    debug_assert!(offset >= lean_ctor_num_objs(obj) * core::mem::size_of::<*mut LeanObject>());
    *lean_ctor_scalar_cptr(obj, offset) = value;
}

#[inline]
pub unsafe fn lean_ctor_get_uint16(obj: *mut LeanObject, offset: usize) -> u16 {
    debug_assert!(offset >= lean_ctor_num_objs(obj) * core::mem::size_of::<*mut LeanObject>());
    let mut value = 0u16;
    ptr::copy_nonoverlapping(
        lean_ctor_scalar_cptr(obj, offset),
        &mut value as *mut u16 as *mut u8,
        core::mem::size_of::<u16>(),
    );
    value
}

#[inline]
pub unsafe fn lean_ctor_set_uint16(obj: *mut LeanObject, offset: usize, value: u16) {
    debug_assert!(offset >= lean_ctor_num_objs(obj) * core::mem::size_of::<*mut LeanObject>());
    ptr::copy_nonoverlapping(
        &value as *const u16 as *const u8,
        lean_ctor_scalar_cptr(obj, offset),
        core::mem::size_of::<u16>(),
    );
}

#[inline]
pub unsafe fn lean_ctor_get_uint32(obj: *mut LeanObject, offset: usize) -> u32 {
    debug_assert!(offset >= lean_ctor_num_objs(obj) * core::mem::size_of::<*mut LeanObject>());
    let mut value = 0u32;
    ptr::copy_nonoverlapping(
        lean_ctor_scalar_cptr(obj, offset),
        &mut value as *mut u32 as *mut u8,
        core::mem::size_of::<u32>(),
    );
    value
}

#[inline]
pub unsafe fn lean_ctor_set_uint32(obj: *mut LeanObject, offset: usize, value: u32) {
    debug_assert!(offset >= lean_ctor_num_objs(obj) * core::mem::size_of::<*mut LeanObject>());
    ptr::copy_nonoverlapping(
        &value as *const u32 as *const u8,
        lean_ctor_scalar_cptr(obj, offset),
        core::mem::size_of::<u32>(),
    );
}

#[inline]
pub unsafe fn lean_ctor_get_uint64(obj: *mut LeanObject, offset: usize) -> u64 {
    debug_assert!(offset >= lean_ctor_num_objs(obj) * core::mem::size_of::<*mut LeanObject>());
    let mut value = 0u64;
    ptr::copy_nonoverlapping(
        lean_ctor_scalar_cptr(obj, offset),
        &mut value as *mut u64 as *mut u8,
        core::mem::size_of::<u64>(),
    );
    value
}

#[inline]
pub unsafe fn lean_ctor_set_uint64(obj: *mut LeanObject, offset: usize, value: u64) {
    debug_assert!(offset >= lean_ctor_num_objs(obj) * core::mem::size_of::<*mut LeanObject>());
    ptr::copy_nonoverlapping(
        &value as *const u64 as *const u8,
        lean_ctor_scalar_cptr(obj, offset),
        core::mem::size_of::<u64>(),
    );
}

#[inline]
pub unsafe fn lean_ctor_get_float(obj: *mut LeanObject, offset: usize) -> f64 {
    debug_assert!(offset >= lean_ctor_num_objs(obj) * core::mem::size_of::<*mut LeanObject>());
    let mut value = 0.0f64;
    ptr::copy_nonoverlapping(
        lean_ctor_scalar_cptr(obj, offset),
        &mut value as *mut f64 as *mut u8,
        core::mem::size_of::<f64>(),
    );
    value
}

#[inline]
pub unsafe fn lean_ctor_set_float(obj: *mut LeanObject, offset: usize, value: f64) {
    debug_assert!(offset >= lean_ctor_num_objs(obj) * core::mem::size_of::<*mut LeanObject>());
    ptr::copy_nonoverlapping(
        &value as *const f64 as *const u8,
        lean_ctor_scalar_cptr(obj, offset),
        core::mem::size_of::<f64>(),
    );
}

#[inline]
pub unsafe fn lean_ctor_get_float32(obj: *mut LeanObject, offset: usize) -> f32 {
    debug_assert!(offset >= lean_ctor_num_objs(obj) * core::mem::size_of::<*mut LeanObject>());
    let mut value = 0.0f32;
    ptr::copy_nonoverlapping(
        lean_ctor_scalar_cptr(obj, offset),
        &mut value as *mut f32 as *mut u8,
        core::mem::size_of::<f32>(),
    );
    value
}

#[inline]
pub unsafe fn lean_ctor_set_float32(obj: *mut LeanObject, offset: usize, value: f32) {
    debug_assert!(offset >= lean_ctor_num_objs(obj) * core::mem::size_of::<*mut LeanObject>());
    ptr::copy_nonoverlapping(
        &value as *const f32 as *const u8,
        lean_ctor_scalar_cptr(obj, offset),
        core::mem::size_of::<f32>(),
    );
}

#[inline]
fn lean_align(v: usize, a: usize) -> usize {
    (v / a) * a + a * (!v.is_multiple_of(a)) as usize
}

#[inline]
unsafe fn lean_global_alloc(size: usize) -> *mut u8 {
    let layout = Layout::from_size_align(size.max(1), core::mem::align_of::<usize>()).unwrap();
    let mem = alloc(layout);
    if mem.is_null() {
        handle_alloc_error(layout);
    }
    mem
}

#[inline]
unsafe fn lean_global_dealloc(mem: *mut u8, size: usize) {
    let layout = Layout::from_size_align(size.max(1), core::mem::align_of::<usize>()).unwrap();
    dealloc(mem, layout);
}

#[inline]
unsafe fn lean_dealloc(obj: *mut LeanObject, size: usize) {
    lean_global_dealloc(obj as *mut u8, size);
}

#[inline]
unsafe fn lean_alloc_small_object(size: usize) -> *mut LeanObject {
    let size = lean_align(size, LEAN_OBJECT_SIZE_DELTA);
    let obj = lean_global_alloc(size) as *mut LeanObject;
    (*obj).cs_size = size as u16;
    obj
}

#[inline]
unsafe fn lean_alloc_ctor_memory(size: usize) -> *mut LeanObject {
    let aligned = lean_align(size, LEAN_OBJECT_SIZE_DELTA);
    let obj = lean_alloc_small_object(aligned);
    if aligned > size {
        (obj as *mut u8).add(size).write_bytes(0, aligned - size);
    }
    obj
}

#[inline]
unsafe fn lean_free_small_object(obj: *mut LeanObject) {
    lean_global_dealloc(obj as *mut u8, (*obj).cs_size as usize);
}

#[inline]
unsafe fn lean_mpz_clear(obj: *mut LeanObject) {
    let mpz = &mut (*(obj as *mut LeanMpzObject)).m_value[0];
    if !mpz.mp_d.is_null() {
        libc::free(mpz.mp_d.cast());
        mpz.mp_alloc = 0;
        mpz.mp_size = 0;
        mpz.mp_d = ptr::null_mut();
    }
}

#[inline]
unsafe fn lean_array_cptr(obj: *mut LeanObject) -> *mut *mut LeanObject {
    (*(obj as *mut LeanArrayObject<0>)).m_data.as_mut_ptr()
}

#[inline]
pub unsafe fn lean_array_size(obj: *mut LeanObject) -> usize {
    (*(obj as *const LeanArrayObject<0>)).m_size
}

#[inline]
unsafe fn lean_array_byte_size(obj: *mut LeanObject) -> usize {
    core::mem::size_of::<LeanArrayObject<0>>()
        + core::mem::size_of::<*mut LeanObject>() * (*(obj as *const LeanArrayObject<0>)).m_capacity
}

#[inline]
unsafe fn lean_sarray_byte_size(obj: *mut LeanObject) -> usize {
    core::mem::size_of::<LeanScalarArray<0>>()
        + (*obj).other as usize * (*(obj as *const LeanScalarArray<0>)).m_capacity
}

#[inline]
unsafe fn lean_string_byte_size(obj: *mut LeanObject) -> usize {
    core::mem::size_of::<LeanStringObject<0>>() + (*(obj as *const LeanStringObject<0>)).m_capacity
}

#[inline]
unsafe fn lean_closure_arg_cptr(obj: *mut LeanObject) -> *mut *mut LeanObject {
    (*(obj as *mut LeanClosureObject<0>)).m_objs.as_mut_ptr()
}

#[inline]
unsafe fn lean_closure_num_fixed(obj: *mut LeanObject) -> usize {
    (*(obj as *const LeanClosureObject<0>)).m_num_fixed as usize
}

#[inline]
unsafe fn lean_closure_byte_size(obj: *mut LeanObject) -> usize {
    core::mem::size_of::<LeanClosureObject<0>>()
        + core::mem::size_of::<*mut LeanObject>() * lean_closure_num_fixed(obj)
}

#[inline]
pub unsafe fn lean_alloc_ctor(tag: u32, num_objs: u32, scalar_size: u32) -> *mut LeanObject {
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

#[inline]
pub unsafe fn lean_alloc_closure(fun: *mut c_void, arity: u32, num_fixed: u32) -> *mut LeanObject {
    debug_assert!(arity > 0);
    debug_assert!(num_fixed < arity);
    let byte_size = core::mem::size_of::<LeanClosureObject<0>>()
        + core::mem::size_of::<*mut LeanObject>() * num_fixed as usize;
    let obj = lean_alloc_object(byte_size) as *mut LeanClosureObject<0>;
    (*obj).m_header.rc = 1;
    (*obj).m_header.other = 0;
    (*obj).m_header.tag = LEAN_CLOSURE_TAG;
    (*obj).m_fun = fun;
    (*obj).m_arity = arity as u16;
    (*obj).m_num_fixed = num_fixed as u16;
    obj as *mut LeanObject
}

#[inline]
pub unsafe fn lean_closure_set(obj: *mut LeanObject, idx: u32, value: *mut LeanObject) {
    debug_assert!((idx as usize) < lean_closure_num_fixed(obj));
    *lean_closure_arg_cptr(obj).add(idx as usize) = value;
}

#[inline]
unsafe fn get_next(obj: *mut LeanObject) -> *mut LeanObject {
    #[cfg(target_pointer_width = "64")]
    {
        let mut header = 0usize;
        ptr::copy_nonoverlapping(obj as *const u8, &mut header as *mut usize as *mut u8, 8);
        header &= !(0xffff_usize << 48);
        header as *mut LeanObject
    }
    #[cfg(target_pointer_width = "32")]
    {
        *(obj as *mut *mut LeanObject)
    }
}

#[inline]
unsafe fn set_next(obj: *mut LeanObject, next: *mut LeanObject) {
    #[cfg(target_pointer_width = "64")]
    {
        let mut hi = 0u16;
        ptr::copy_nonoverlapping((obj as *const u8).add(6), &mut hi as *mut u16 as *mut u8, 2);
        let header = ((hi as usize) << 48) | (next as usize);
        ptr::copy_nonoverlapping(&header as *const usize as *const u8, obj as *mut u8, 8);
    }
    #[cfg(target_pointer_width = "32")]
    {
        *(obj as *mut *mut LeanObject) = next;
    }
}

#[inline]
unsafe fn push_back(todo: &mut *mut LeanObject, obj: *mut LeanObject) {
    set_next(obj, *todo);
    *todo = obj;
}

#[inline]
unsafe fn pop_back(todo: &mut *mut LeanObject) -> *mut LeanObject {
    let result = *todo;
    *todo = get_next(result);
    result
}

#[inline]
unsafe fn dec_for_del(obj: *mut LeanObject, todo: &mut *mut LeanObject) {
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

#[inline]
unsafe fn lean_del_core_other(obj: *mut LeanObject, tag: u8, todo: &mut *mut LeanObject) {
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

#[inline]
unsafe fn lean_del_core(obj: *mut LeanObject, todo: &mut *mut LeanObject) {
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

#[inline]
unsafe fn lean_alloc_object(size: usize) -> *mut LeanObject {
    #[cfg(lean_lazy_rc)]
    G_TO_FREE.with(|cell| {
        let mut todo = cell.replace(ptr::null_mut());
        if !todo.is_null() {
            let obj = pop_back(&mut todo);
            lean_del_core(obj, &mut todo);
            cell.set(todo);
        }
    });

    let obj = lean_global_alloc(size) as *mut LeanObject;
    (*obj).cs_size = 0;
    obj
}

#[inline]
pub unsafe fn lean_free_object(obj: *mut LeanObject) {
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

#[inline]
pub unsafe fn lean_dec_ref_cold(mut obj: *mut LeanObject) {
    if lean_is_scalar_bool(obj) {
        return;
    }
    if (*obj).rc == 1 || {
        let rc = core::ptr::addr_of_mut!((*obj).rc).cast::<AtomicI32>();
        (*rc).fetch_add(1, Ordering::AcqRel) == -1
    } {
        #[cfg(lean_lazy_rc)]
        G_TO_FREE.with(|cell| {
            let mut todo = cell.get();
            push_back(&mut todo, obj);
            cell.set(todo);
        });

        #[cfg(not(lean_lazy_rc))]
        {
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

#[inline]
pub unsafe fn lean_apply_1(f: *mut LeanObject, a1: *mut LeanObject) -> *mut LeanObject {
    let fun: unsafe fn(*mut LeanObject) -> *mut LeanObject =
        core::mem::transmute((*(f as *mut LeanClosureObject<0>)).m_fun);
    let r = fun(a1);
    lean_dec_ref(f);
    r
}

#[inline]
pub unsafe fn lean_apply_2(
    f: *mut LeanObject,
    a1: *mut LeanObject,
    a2: *mut LeanObject,
) -> *mut LeanObject {
    let fun: unsafe fn(*mut LeanObject, *mut LeanObject) -> *mut LeanObject =
        core::mem::transmute((*(f as *mut LeanClosureObject<0>)).m_fun);
    let r = fun(a1, a2);
    lean_dec_ref(f);
    r
}

#[inline]
pub unsafe fn lean_apply_3(
    f: *mut LeanObject,
    a1: *mut LeanObject,
    a2: *mut LeanObject,
    a3: *mut LeanObject,
) -> *mut LeanObject {
    let fun: unsafe fn(*mut LeanObject, *mut LeanObject, *mut LeanObject) -> *mut LeanObject =
        core::mem::transmute((*(f as *mut LeanClosureObject<0>)).m_fun);
    let r = fun(a1, a2, a3);
    lean_dec_ref(f);
    r
}

#[inline]
pub unsafe fn lean_apply_4(
    f: *mut LeanObject,
    a1: *mut LeanObject,
    a2: *mut LeanObject,
    a3: *mut LeanObject,
    a4: *mut LeanObject,
) -> *mut LeanObject {
    let fun: unsafe fn(
        *mut LeanObject,
        *mut LeanObject,
        *mut LeanObject,
        *mut LeanObject,
    ) -> *mut LeanObject = core::mem::transmute((*(f as *mut LeanClosureObject<0>)).m_fun);
    let r = fun(a1, a2, a3, a4);
    lean_dec_ref(f);
    r
}

macro_rules! define_lean_apply {
    ($name:ident, $($arg:ident),+) => {
        #[inline]
        pub unsafe fn $name(f: *mut LeanObject, $($arg: *mut LeanObject),+) -> *mut LeanObject {
            let fun: unsafe fn($(lean_apply_arg_ty!($arg)),+) -> *mut LeanObject =
                core::mem::transmute((*(f as *mut LeanClosureObject<0>)).m_fun);
            let r = fun($($arg),+);
            lean_dec_ref(f);
            r
        }
    };
}

macro_rules! lean_apply_arg_ty {
    ($arg:ident) => {
        *mut LeanObject
    };
}

define_lean_apply!(lean_apply_5, a1, a2, a3, a4, a5);
define_lean_apply!(lean_apply_6, a1, a2, a3, a4, a5, a6);
define_lean_apply!(lean_apply_7, a1, a2, a3, a4, a5, a6, a7);
define_lean_apply!(lean_apply_8, a1, a2, a3, a4, a5, a6, a7, a8);
define_lean_apply!(lean_apply_9, a1, a2, a3, a4, a5, a6, a7, a8, a9);
define_lean_apply!(lean_apply_10, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10);
define_lean_apply!(lean_apply_11, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11);
define_lean_apply!(
    lean_apply_12,
    a1,
    a2,
    a3,
    a4,
    a5,
    a6,
    a7,
    a8,
    a9,
    a10,
    a11,
    a12
);
define_lean_apply!(
    lean_apply_13,
    a1,
    a2,
    a3,
    a4,
    a5,
    a6,
    a7,
    a8,
    a9,
    a10,
    a11,
    a12,
    a13
);
define_lean_apply!(
    lean_apply_14,
    a1,
    a2,
    a3,
    a4,
    a5,
    a6,
    a7,
    a8,
    a9,
    a10,
    a11,
    a12,
    a13,
    a14
);
define_lean_apply!(
    lean_apply_15,
    a1,
    a2,
    a3,
    a4,
    a5,
    a6,
    a7,
    a8,
    a9,
    a10,
    a11,
    a12,
    a13,
    a14,
    a15
);
define_lean_apply!(
    lean_apply_16,
    a1,
    a2,
    a3,
    a4,
    a5,
    a6,
    a7,
    a8,
    a9,
    a10,
    a11,
    a12,
    a13,
    a14,
    a15,
    a16
);

#[inline]
pub unsafe fn lean_apply_m(
    f: *mut LeanObject,
    _n: u32,
    args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let fun: unsafe fn(*mut *mut LeanObject) -> *mut LeanObject =
        core::mem::transmute((*(f as *mut LeanClosureObject<0>)).m_fun);
    let r = fun(args);
    lean_dec_ref(f);
    r
}

#[inline]
unsafe fn lean_array_capacity(obj: *mut LeanObject) -> usize {
    (*(obj as *const LeanArrayObject<0>)).m_capacity
}

#[inline]
unsafe fn lean_array_data(obj: *mut LeanObject) -> *mut *mut LeanObject {
    (*(obj as *mut LeanArrayObject<0>)).m_data.as_mut_ptr()
}

#[inline]
unsafe fn lean_array_get_core(obj: *mut LeanObject, idx: usize) -> *mut LeanObject {
    *lean_array_data(obj).add(idx)
}

#[inline]
unsafe fn lean_alloc_array(size: usize, capacity: usize) -> *mut LeanObject {
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

#[inline]
pub unsafe fn lean_array_get_size(obj: *mut LeanObject) -> *mut LeanObject {
    lean_box(lean_array_size(obj))
}

#[inline]
pub unsafe fn lean_array_fget(obj: *mut LeanObject, idx: *mut LeanObject) -> *mut LeanObject {
    let r = lean_array_get_core(obj, lean_unbox(idx));
    lean_inc(r);
    r
}

#[inline]
pub unsafe fn lean_array_fget_borrowed(
    obj: *mut LeanObject,
    idx: *mut LeanObject,
) -> *mut LeanObject {
    lean_array_get_core(obj, lean_unbox(idx))
}

#[inline]
pub unsafe fn lean_array_get(
    def_val: *mut LeanObject,
    obj: *mut LeanObject,
    idx: *mut LeanObject,
) -> *mut LeanObject {
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

#[inline]
pub unsafe fn lean_array_get_borrowed(
    def_val: *mut LeanObject,
    obj: *mut LeanObject,
    idx: *mut LeanObject,
) -> *mut LeanObject {
    if lean_is_scalar_bool(idx) {
        let idx = lean_unbox(idx);
        if idx < lean_array_size(obj) {
            return lean_array_get_core(obj, idx);
        }
    }
    def_val
}

#[inline]
pub unsafe fn lean_mk_empty_array_with_capacity(capacity: *mut LeanObject) -> *mut LeanObject {
    if !lean_is_scalar_bool(capacity) {
        panic!("big array capacity is not supported in leanh.rs");
    }
    lean_alloc_array(0, lean_unbox(capacity))
}

#[inline]
pub unsafe fn lean_array_push(obj: *mut LeanObject, value: *mut LeanObject) -> *mut LeanObject {
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

#[inline]
pub unsafe fn lean_array_mk(_list: *mut LeanObject) -> *mut LeanObject {
    panic!("lean_array_mk requires list traversal runtime");
}

#[inline]
pub unsafe fn lean_array_to_list(_array: *mut LeanObject) -> *mut LeanObject {
    panic!("lean_array_to_list requires list construction runtime");
}

#[inline]
unsafe fn lean_sarray_size(obj: *mut LeanObject) -> usize {
    (*(obj as *const LeanScalarArray<0>)).m_size
}

#[inline]
unsafe fn lean_sarray_capacity(obj: *mut LeanObject) -> usize {
    (*(obj as *const LeanScalarArray<0>)).m_capacity
}

#[inline]
unsafe fn lean_sarray_data(obj: *mut LeanObject) -> *mut u8 {
    (*(obj as *mut LeanScalarArray<0>)).m_data.as_mut_ptr()
}

#[inline]
unsafe fn lean_alloc_sarray(elem_size: u32, size: usize, capacity: usize) -> *mut LeanObject {
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

#[inline]
pub unsafe fn lean_mk_empty_byte_array(capacity: *mut LeanObject) -> *mut LeanObject {
    if !lean_is_scalar_bool(capacity) {
        panic!("big byte-array capacity is not supported in leanh.rs");
    }
    lean_alloc_sarray(1, 0, lean_unbox(capacity))
}

#[inline]
pub unsafe fn lean_byte_array_size(obj: *mut LeanObject) -> *mut LeanObject {
    lean_box(lean_sarray_size(obj))
}

#[inline]
pub unsafe fn lean_byte_array_data(obj: *mut LeanObject) -> *mut LeanObject {
    lean_inc(obj);
    obj
}

#[inline]
pub unsafe fn lean_byte_array_mk(obj: *mut LeanObject) -> *mut LeanObject {
    lean_inc(obj);
    obj
}

#[inline]
pub unsafe fn lean_byte_array_push(obj: *mut LeanObject, value: u8) -> *mut LeanObject {
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

#[inline]
pub unsafe fn lean_box_uint32(value: u32) -> *mut LeanObject {
    let obj = lean_alloc_ctor(0, 0, core::mem::size_of::<u32>() as u32);
    ptr::copy_nonoverlapping(
        &value as *const u32 as *const u8,
        lean_ctor_scalar_cptr(obj),
        core::mem::size_of::<u32>(),
    );
    obj
}

#[inline]
pub unsafe fn lean_unbox_uint32(obj: *mut LeanObject) -> u32 {
    let mut value = 0u32;
    ptr::copy_nonoverlapping(
        lean_ctor_scalar_cptr(obj),
        &mut value as *mut u32 as *mut u8,
        core::mem::size_of::<u32>(),
    );
    value
}

#[inline]
pub unsafe fn lean_box_uint64(value: u64) -> *mut LeanObject {
    let obj = lean_alloc_ctor(0, 0, core::mem::size_of::<u64>() as u32);
    lean_ctor_set_uint64(obj, 0, value);
    obj
}

#[inline]
pub unsafe fn lean_unbox_uint64(obj: *mut LeanObject) -> u64 {
    lean_ctor_get_uint64(obj, 0)
}

#[inline]
pub unsafe fn lean_box_usize(value: usize) -> *mut LeanObject {
    let obj = lean_alloc_ctor(0, 0, core::mem::size_of::<usize>() as u32);
    ptr::copy_nonoverlapping(
        &value as *const usize as *const u8,
        lean_ctor_scalar_cptr(obj),
        core::mem::size_of::<usize>(),
    );
    obj
}

#[inline]
pub unsafe fn lean_unbox_usize(obj: *mut LeanObject) -> usize {
    let mut value = 0usize;
    ptr::copy_nonoverlapping(
        lean_ctor_scalar_cptr(obj),
        &mut value as *mut usize as *mut u8,
        core::mem::size_of::<usize>(),
    );
    value
}

#[inline]
pub unsafe fn lean_box_float(value: f64) -> *mut LeanObject {
    let obj = lean_alloc_ctor(0, 0, core::mem::size_of::<f64>() as u32);
    lean_ctor_set_float(obj, 0, value);
    obj
}

#[inline]
pub unsafe fn lean_unbox_float(obj: *mut LeanObject) -> f64 {
    lean_ctor_get_float(obj, 0)
}

#[inline]
pub unsafe fn lean_box_float32(value: f32) -> *mut LeanObject {
    let obj = lean_alloc_ctor(0, 0, core::mem::size_of::<f32>() as u32);
    lean_ctor_set_float32(obj, 0, value);
    obj
}

#[inline]
pub unsafe fn lean_unbox_float32(obj: *mut LeanObject) -> f32 {
    lean_ctor_get_float32(obj, 0)
}

#[inline]
unsafe fn lean_small_nat(obj: *mut LeanObject) -> usize {
    if lean_is_scalar_bool(obj) {
        lean_unbox(obj)
    } else {
        panic!("big Nat is not supported in leanh.rs")
    }
}

#[inline]
unsafe fn lean_usize_to_nat_impl(value: usize) -> *mut LeanObject {
    if value <= (usize::MAX >> 1) {
        lean_box(value)
    } else {
        panic!("big Nat is not supported in leanh.rs")
    }
}

#[inline]
pub unsafe fn lean_unsigned_to_nat(value: u32) -> *mut LeanObject {
    lean_usize_to_nat(value as usize)
}

#[inline]
pub unsafe fn lean_cstr_to_nat(text: *const c_char) -> *mut LeanObject {
    let s = std::ffi::CStr::from_ptr(text).to_str().unwrap();
    let value = s
        .parse::<usize>()
        .expect("big Nat is not supported in leanh.rs");
    lean_usize_to_nat(value)
}

#[inline]
pub unsafe fn lean_nat_add(a: *mut LeanObject, b: *mut LeanObject) -> *mut LeanObject {
    lean_usize_to_nat(lean_small_nat(a).wrapping_add(lean_small_nat(b)))
}

#[inline]
pub unsafe fn lean_nat_sub(a: *mut LeanObject, b: *mut LeanObject) -> *mut LeanObject {
    lean_box(lean_small_nat(a).saturating_sub(lean_small_nat(b)))
}

#[inline]
pub unsafe fn lean_nat_mul(a: *mut LeanObject, b: *mut LeanObject) -> *mut LeanObject {
    lean_usize_to_nat(lean_small_nat(a).wrapping_mul(lean_small_nat(b)))
}

#[inline]
pub unsafe fn lean_nat_div(a: *mut LeanObject, b: *mut LeanObject) -> *mut LeanObject {
    let b = lean_small_nat(b);
    lean_box(lean_small_nat(a).checked_div(b).unwrap_or(0))
}

#[inline]
pub unsafe fn lean_nat_mod(a: *mut LeanObject, b: *mut LeanObject) -> *mut LeanObject {
    let b = lean_small_nat(b);
    lean_box(if b == 0 {
        lean_small_nat(a)
    } else {
        lean_small_nat(a) % b
    })
}

#[inline]
pub unsafe fn lean_nat_pow(a: *mut LeanObject, b: *mut LeanObject) -> *mut LeanObject {
    lean_usize_to_nat(lean_small_nat(a).wrapping_pow(lean_small_nat(b) as u32))
}

#[inline]
pub unsafe fn lean_nat_pred(a: *mut LeanObject) -> *mut LeanObject {
    lean_box(lean_small_nat(a).saturating_sub(1))
}

#[inline]
pub unsafe fn lean_nat_dec_eq(a: *mut LeanObject, b: *mut LeanObject) -> u8 {
    (lean_small_nat(a) == lean_small_nat(b)) as u8
}

#[inline]
pub unsafe fn lean_nat_dec_lt(a: *mut LeanObject, b: *mut LeanObject) -> u8 {
    (lean_small_nat(a) < lean_small_nat(b)) as u8
}

#[inline]
pub unsafe fn lean_nat_dec_le(a: *mut LeanObject, b: *mut LeanObject) -> u8 {
    (lean_small_nat(a) <= lean_small_nat(b)) as u8
}

macro_rules! define_uint_family {
    ($ty:ty, $of_nat:ident, $of_nat_mk:ident, $to_nat:ident, $dec_eq:ident, $dec_lt:ident, $dec_le:ident) => {
        #[inline]
        pub unsafe fn $of_nat(obj: *mut LeanObject) -> $ty {
            lean_small_nat(obj) as $ty
        }

        #[inline]
        pub unsafe fn $of_nat_mk(obj: *mut LeanObject) -> $ty {
            let result = $of_nat(obj);
            lean_dec(obj);
            result
        }

        #[inline]
        pub unsafe fn $to_nat(value: $ty) -> *mut LeanObject {
            lean_usize_to_nat(value as usize)
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
pub unsafe fn lean_usize_of_nat(obj: *mut LeanObject) -> usize {
    lean_small_nat(obj)
}

#[inline]
pub unsafe fn lean_usize_of_nat_mk(obj: *mut LeanObject) -> usize {
    let result = lean_usize_of_nat(obj);
    lean_dec(obj);
    result
}

#[inline]
pub unsafe fn lean_usize_dec_eq(a: usize, b: usize) -> u8 {
    (a == b) as u8
}

#[inline]
pub unsafe fn lean_usize_dec_lt(a: usize, b: usize) -> u8 {
    (a < b) as u8
}

#[inline]
pub unsafe fn lean_usize_dec_le(a: usize, b: usize) -> u8 {
    (a <= b) as u8
}

#[inline]
pub unsafe fn lean_usize_to_nat(value: usize) -> *mut LeanObject {
    lean_usize_to_nat_impl(value)
}

#[inline]
pub unsafe fn lean_closure_max_args(_: *mut LeanObject) -> *mut LeanObject {
    lean_unsigned_to_nat(LEAN_CLOSURE_MAX_ARGS)
}

#[inline]
pub unsafe fn lean_max_small_nat(_: *mut LeanObject) -> *mut LeanObject {
    lean_usize_to_nat(LEAN_MAX_SMALL_NAT)
}

#[inline]
pub unsafe fn lean_libuv_version(_: *mut LeanObject) -> *mut LeanObject {
    lean_box(0)
}

#[inline]
pub fn lean_uint64_mix_hash(a: u64, b: u64) -> u64 {
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
unsafe fn lean_string_data(obj: *mut LeanObject) -> *mut u8 {
    (*(obj as *mut LeanStringObject<0>))
        .m_data
        .as_mut_ptr()
        .cast::<u8>()
}

#[inline]
unsafe fn lean_alloc_string(byte_size: usize, capacity: usize, len: usize) -> *mut LeanObject {
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

#[inline]
pub unsafe fn lean_mk_string_unchecked(
    s: *const c_char,
    byte_size: usize,
    len: usize,
) -> *mut LeanObject {
    let obj = lean_alloc_string(byte_size + 1, byte_size + 1, len);
    ptr::copy_nonoverlapping(s.cast::<u8>(), lean_string_data(obj), byte_size);
    *lean_string_data(obj).add(byte_size) = 0;
    obj
}

#[inline]
pub unsafe fn lean_string_utf8_byte_size(obj: *mut LeanObject) -> *mut LeanObject {
    lean_box(
        (*(obj as *const LeanStringObject<0>))
            .m_size
            .saturating_sub(1),
    )
}

#[inline]
pub unsafe fn lean_string_to_utf8(obj: *mut LeanObject) -> *mut LeanObject {
    let size = (*(obj as *const LeanStringObject<0>))
        .m_size
        .saturating_sub(1);
    let result = lean_alloc_sarray(1, size, size);
    ptr::copy_nonoverlapping(lean_string_data(obj), lean_sarray_data(result), size);
    result
}

#[inline]
pub unsafe fn lean_string_from_utf8_unchecked(bytes: *mut LeanObject) -> *mut LeanObject {
    let size = lean_sarray_size(bytes);
    let result = lean_alloc_string(size + 1, size + 1, size);
    ptr::copy_nonoverlapping(lean_sarray_data(bytes), lean_string_data(result), size);
    *lean_string_data(result).add(size) = 0;
    lean_dec(bytes);
    result
}

#[inline]
pub unsafe fn lean_string_mk(_list: *mut LeanObject) -> *mut LeanObject {
    panic!("lean_string_mk requires list traversal runtime");
}

#[inline]
pub unsafe fn lean_string_dec_eq(a: *mut LeanObject, b: *mut LeanObject) -> u8 {
    let a_size = (*(a as *const LeanStringObject<0>)).m_size;
    let b_size = (*(b as *const LeanStringObject<0>)).m_size;
    if a_size != b_size {
        return 0;
    }
    (core::slice::from_raw_parts(lean_string_data(a), a_size)
        == core::slice::from_raw_parts(lean_string_data(b), b_size)) as u8
}

#[inline]
pub unsafe fn lean_string_hash(obj: *mut LeanObject) -> u64 {
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

#[inline]
pub unsafe fn lean_io_result_mk_ok(value: *mut LeanObject) -> *mut LeanObject {
    let obj = lean_alloc_ctor(0, 1, 0);
    lean_ctor_set(obj, 0, value);
    obj
}

#[inline]
pub unsafe fn lean_io_result_is_error(obj: *mut LeanObject) -> bool {
    lean_obj_tag(obj) == 1
}

#[inline]
pub unsafe fn lean_panic_fn_borrowed(
    default_val: *mut LeanObject,
    msg: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(default_val);
    lean_dec(msg);
    default_val
}

#[inline]
pub unsafe fn lean_sorry(_: u8) -> *mut LeanObject {
    panic!("executed 'sorry'")
}

#[inline]
pub unsafe fn lean_name_eq(a: *mut LeanObject, b: *mut LeanObject) -> u8 {
    (a == b) as u8
}

#[inline]
pub unsafe fn lean_system_platform_nbits(_: *mut LeanObject) -> *mut LeanObject {
    lean_box(usize::BITS as usize)
}

#[cfg(false)]
#[inline]
pub unsafe fn lean_to_ctor(obj: *mut LeanObject) -> *mut LeanCtorObject<0> {
    debug_assert!(lean_is_ctor(obj));
    obj as *mut LeanCtorObject<0>
}

#[cfg(false)]
#[inline]
pub unsafe fn lean_to_closure(obj: *mut LeanObject) -> *mut LeanClosureObject<0> {
    debug_assert!(lean_is_closure(obj));
    obj as *mut LeanClosureObject<0>
}

#[cfg(false)]
#[inline]
pub unsafe fn lean_to_array(obj: *mut LeanObject) -> *mut LeanArrayObject<0> {
    debug_assert!(lean_is_array(obj));
    obj as *mut LeanArrayObject<0>
}

#[cfg(false)]
#[inline]
pub unsafe fn lean_to_sarray(obj: *mut LeanObject) -> *mut LeanScalarArray<0> {
    debug_assert!(lean_is_sarray(obj));
    obj as *mut LeanScalarArray<0>
}

#[cfg(false)]
#[inline]
pub unsafe fn lean_to_string(obj: *mut LeanObject) -> *mut LeanStringObject<0> {
    debug_assert!(lean_is_string(obj));
    obj as *mut LeanStringObject<0>
}

#[cfg(false)]
#[inline]
pub unsafe fn lean_to_thunk(obj: *mut LeanObject) -> *mut LeanThunkObject {
    debug_assert!(lean_is_thunk(obj));
    obj as *mut LeanThunkObject
}

#[cfg(false)]
#[inline]
pub unsafe fn lean_to_task(obj: *mut LeanObject) -> *mut LeanTaskObject {
    debug_assert!(lean_is_task(obj));
    obj as *mut LeanTaskObject
}

#[cfg(false)]
#[inline]
pub unsafe fn lean_to_promise(obj: *mut LeanObject) -> *mut LeanPromiseObject {
    debug_assert!(lean_is_promise(obj));
    obj as *mut LeanPromiseObject
}

#[cfg(false)]
#[inline]
pub unsafe fn lean_to_ref(obj: *mut LeanObject) -> *mut LeanRefObject {
    debug_assert!(lean_is_ref(obj));
    obj as *mut LeanRefObject
}

#[cfg(false)]
#[inline]
pub unsafe fn lean_to_external(obj: *mut LeanObject) -> *mut LeanExternalObject {
    debug_assert!(lean_is_external(obj));
    obj as *mut LeanExternalObject
}

#[inline]
pub unsafe fn lean_is_exclusive(obj: *mut LeanObject) -> bool {
    lean_is_st(obj) && (*obj).rc == 1
}

#[inline]
pub unsafe fn lean_mark_persistent(obj: *mut LeanObject) {
    if !lean_is_scalar_bool(obj) {
        (*obj).rc = 0;
    }
}

#[cfg(false)]
#[inline]
pub unsafe fn lean_is_exclusive_obj(obj: *mut LeanObject) -> u8 {
    lean_is_exclusive(obj) as u8
}

#[cfg(false)]
#[inline]
pub unsafe fn lean_is_shared(obj: *mut LeanObject) -> bool {
    lean_is_st(obj) && (*obj).rc > 1
}

#[cfg(false)]
#[inline]
pub unsafe fn lean_name_eq_export(n1: *mut LeanObject, n2: *mut LeanObject) -> u8 {
    crate::lean_name_eq(n1, n2)
}

#[cfg(false)]
static EXTERNAL_CLASSES: std::sync::Mutex<Vec<usize>> = std::sync::Mutex::new(Vec::new());

#[cfg(false)]
unsafe fn lean_external_noop_finalize(_: *mut c_void) {}

#[cfg(false)]
unsafe fn lean_external_noop_foreach(_: *mut c_void, _: *mut LeanObject) {}

#[cfg(false)]
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

#[cfg(false)]
#[inline]
pub unsafe fn lean_finalize_external_classes() {
    let mut classes = EXTERNAL_CLASSES.lock().unwrap();
    for class in classes.drain(..) {
        drop(Box::from_raw(class as *mut LeanExternalClass));
    }
}

#[cfg(false)]
#[inline]
pub unsafe fn lean_runtime_alloc_external(
    class: *mut LeanExternalClass,
    data: *mut c_void,
) -> *mut LeanObject {
    let obj = crate::lean_alloc_small_object(core::mem::size_of::<LeanExternalObject>())
        as *mut LeanExternalObject;
    (*obj).m_header.rc = 1;
    (*obj).m_header.other = 0;
    (*obj).m_header.tag = LEAN_EXTERNAL_TAG;
    (*obj).m_class = class;
    (*obj).m_data = data;
    obj as *mut LeanObject
}

#[cfg(false)]
#[inline]
pub unsafe fn lean_runtime_get_external_data(obj: *mut LeanObject) -> *mut c_void {
    (*(obj as *mut LeanExternalObject)).m_data
}

#[cfg(false)]
#[inline]
pub unsafe fn lean_alloc_external(
    class: *mut LeanExternalClass,
    data: *mut c_void,
) -> *mut LeanObject {
    lean_runtime_alloc_external(class, data)
}

#[cfg(false)]
#[inline]
pub unsafe fn lean_get_external_class(obj: *mut LeanObject) -> *mut LeanExternalClass {
    (*(obj as *mut LeanExternalObject)).m_class
}

#[cfg(false)]
#[inline]
pub unsafe fn lean_set_external_data(obj: *mut LeanObject, data: *mut c_void) -> *mut LeanObject {
    if lean_is_exclusive(obj) {
        (*(obj as *mut LeanExternalObject)).m_data = data;
        obj
    } else {
        let new_obj = lean_alloc_external(lean_get_external_class(obj), data);
        lean_dec_ref(obj);
        new_obj
    }
}

#[inline]
fn lock_once_cell(lock: &AtomicI32) {
    while lock
        .compare_exchange(0, 1, Ordering::Acquire, Ordering::Relaxed)
        .is_err()
    {
        std::thread::yield_now();
    }
}

#[inline]
fn unlock_once_cell(lock: &AtomicI32) {
    lock.store(0, Ordering::Release);
}

#[inline]
unsafe fn run_once<T: Copy>(loc: *mut T, tok: *mut LeanOnceCell, init: unsafe fn() -> T) -> T {
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

#[inline]
unsafe fn lean_obj_once_cold(
    loc: *mut *mut LeanObject,
    tok: *mut LeanOnceCell,
    init: ObjInitFn,
) -> *mut LeanObject {
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

#[inline]
pub unsafe fn lean_obj_once(
    loc: *mut *mut LeanObject,
    tok: *mut LeanOnceCell,
    init: ObjInitFn,
) -> *mut LeanObject {
    if (*tok).state.load(Ordering::Acquire) == 1 {
        *loc
    } else {
        lean_obj_once_cold(loc, tok, init)
    }
}

#[inline]
pub unsafe fn lean_uint8_once(loc: *mut u8, tok: *mut LeanOnceCell, init: U8InitFn) -> u8 {
    if (*tok).state.load(Ordering::Acquire) == 1 {
        *loc
    } else {
        run_once(loc, tok, init)
    }
}

#[inline]
pub unsafe fn lean_uint16_once(loc: *mut u16, tok: *mut LeanOnceCell, init: U16InitFn) -> u16 {
    if (*tok).state.load(Ordering::Acquire) == 1 {
        *loc
    } else {
        run_once(loc, tok, init)
    }
}

#[inline]
pub unsafe fn lean_uint32_once(loc: *mut u32, tok: *mut LeanOnceCell, init: U32InitFn) -> u32 {
    if (*tok).state.load(Ordering::Acquire) == 1 {
        *loc
    } else {
        run_once(loc, tok, init)
    }
}

#[inline]
pub unsafe fn lean_uint64_once(loc: *mut u64, tok: *mut LeanOnceCell, init: U64InitFn) -> u64 {
    if (*tok).state.load(Ordering::Acquire) == 1 {
        *loc
    } else {
        run_once(loc, tok, init)
    }
}

#[inline]
pub unsafe fn lean_usize_once(loc: *mut usize, tok: *mut LeanOnceCell, init: UsizeInitFn) -> usize {
    if (*tok).state.load(Ordering::Acquire) == 1 {
        *loc
    } else {
        run_once(loc, tok, init)
    }
}

#[cfg(false)]
#[inline]
pub unsafe fn lean_float32_once(loc: *mut f32, tok: *mut LeanOnceCell, init: F32InitFn) -> f32 {
    if (*tok).state.load(Ordering::Acquire) == 1 {
        *loc
    } else {
        crate::lean_float32_once_cold(loc, tok, init)
    }
}

#[cfg(false)]
#[inline]
pub unsafe fn lean_float_once(loc: *mut f64, tok: *mut LeanOnceCell, init: F64InitFn) -> f64 {
    if (*tok).state.load(Ordering::Acquire) == 1 {
        *loc
    } else {
        crate::lean_float_once_cold(loc, tok, init)
    }
}
