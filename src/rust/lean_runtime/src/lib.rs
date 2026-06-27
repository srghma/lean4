/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

#![cfg_attr(not(feature = "std"), no_std)]
#![allow(
    dead_code,
    non_upper_case_globals,
    non_snake_case,
)]

use core::ffi::{c_char, c_int, c_long, c_uchar, c_uint, c_void, CStr};
#[cfg(not(feature = "std"))]
use core::panic::PanicInfo;
use core::ptr;
use core::sync::atomic::{AtomicBool, AtomicI32, AtomicPtr, AtomicU32, Ordering};

type Size = usize;

const LEAN_REF_TAG: u8 = 253;
const LEAN_SINGLE_THREADED_RC: i32 = 1;
const LEAN_MAX_CTOR_TAG: u8 = 243;
const LEAN_PROMISE_TAG: u8 = 244;
const LEAN_CLOSURE_TAG: u8 = 245;
const LEAN_ARRAY_TAG: u8 = 246;
const LEAN_SCALAR_ARRAY_TAG: u8 = 248;
const LEAN_STRING_TAG: u8 = 249;
const LEAN_MPZ_TAG: u8 = 250;
const LEAN_THUNK_TAG: u8 = 251;
const LEAN_TASK_TAG: u8 = 252;
const LEAN_EXTERNAL_TAG: u8 = 254;
const LEAN_MAX_CTOR_FIELDS: usize = 256;
const LEAN_MAX_CTOR_SCALARS_SIZE: usize = 1024;
const LEAN_OBJECT_SIZE_DELTA: usize = 8;

extern "C" {
    fn lean_name_mk_string(prefix: *mut LeanObject, s: *mut LeanObject) -> *mut LeanObject;
    fn lean_mk_io_user_error(msg: *mut LeanObject) -> *mut LeanObject;
    fn lean_mk_io_error_invalid_argument(errnum: u32, details: *mut LeanObject) -> *mut LeanObject;
    fn lean_mk_io_error_invalid_argument_file(
        name: *mut LeanObject,
        errnum: u32,
        details: *mut LeanObject,
    ) -> *mut LeanObject;
    fn lean_io_eprintln(msg: *mut LeanObject) -> *mut LeanObject;
    #[link_name = "_ZN4lean20lean_promise_resolveEP11lean_objectS1_"]
    fn lean_promise_resolve(value: *mut LeanObject, promise: *mut LeanObject);
    fn lean_io_error_to_string(err: *mut LeanObject) -> *mut LeanObject;
    fn lean_options_get_empty(_: *mut LeanObject) -> *mut LeanObject;
    fn lean_options_get_bool(
        opts: *mut LeanObject,
        name: *mut LeanObject,
        default_value: bool,
    ) -> bool;
    fn lean_options_update_bool(
        opts: *mut LeanObject,
        name: *mut LeanObject,
        value: bool,
    ) -> *mut LeanObject;
    fn lean_get_init_fn_name_for(env: *mut LeanObject, name: *mut LeanObject) -> *mut LeanObject;
    fn lean_get_profiler(opts: *mut LeanObject) -> u8;
    fn lean_get_profiler_threshold(opts: *mut LeanObject) -> f64;
    // initialize_annotation / finalize_annotation removed (annotation.cpp deleted; no state)
    #[link_name = "_ZN4lean23initialize_library_utilEv"]
    fn initialize_library_util();
    #[link_name = "_ZN4lean21finalize_library_utilEv"]
    fn finalize_library_util();
    fn initialize_Init(builtin: u8) -> *mut LeanObject;
    fn initialize_Std(builtin: u8) -> *mut LeanObject;
    fn initialize_Lean(builtin: u8) -> *mut LeanObject;}

#[inline]
pub unsafe fn lean_io_error_to_string_rust(err: *mut LeanObject) -> *mut LeanObject {
    lean_io_error_to_string(err)
}

/// cbindgen:field-names=[m_rc, m_cs_sz, m_other, m_tag]
#[repr(C)]
pub struct LeanObject {
    pub rc: i32,
    pub cs_size: u16,
    pub other: u8,
    pub tag: u8,
}

#[repr(C)]
pub struct LeanCtorObject {
    header: LeanObject,
    data: [*mut LeanObject; 0],
}

type LeanExternalFinalizeProc = unsafe fn(*mut c_void);
type LeanExternalForeachProc = unsafe fn(*mut c_void, *mut LeanObject);

/// cbindgen:field-names=[m_finalize, m_foreach]
#[repr(C)]
pub struct LeanExternalClass {
    pub(crate) finalize: LeanExternalFinalizeProc,
    pub(crate) foreach: LeanExternalForeachProc,
}

#[repr(C)]
struct LeanListCell {
    rc: AtomicU32,
    head: c_uint,
    tail: *mut LeanListCell,
}

/// cbindgen:field-names=[m_header, m_size, m_capacity, m_data]
#[repr(C)]
pub struct LeanArrayObject {
    pub(crate) header: LeanObject,
    pub(crate) size: Size,
    pub(crate) capacity: Size,
    pub(crate) data: [*mut LeanObject; 0],
}

/// cbindgen:field-names=[m_header, m_size, m_capacity, m_length, m_data]
#[repr(C)]
pub struct LeanStringObject {
    pub(crate) header: LeanObject,
    pub(crate) size: Size,
    pub(crate) capacity: Size,
    pub(crate) len: Size,
    pub(crate) data: [c_char; 0],
}

/// cbindgen:field-names=[m_header, m_fun, m_arity, m_num_fixed, m_objs]
#[repr(C)]
pub struct LeanClosureObject {
    pub(crate) header: LeanObject,
    pub(crate) fun: *mut c_void,
    pub(crate) arity: u16,
    pub(crate) num_fixed: u16,
    pub(crate) data: [*mut LeanObject; 0],
}

/// cbindgen:field-names=[m_header, m_size, m_capacity, m_data]
#[repr(C)]
pub struct LeanScalarArray {
    pub(crate) header: LeanObject,
    pub(crate) size: Size,
    pub(crate) capacity: Size,
    pub(crate) data: [u8; 0],
}

/// cbindgen:field-names=[m_header, m_result]
#[repr(C)]
pub struct LeanPromiseObject {
    pub(crate) header: LeanObject,
    pub(crate) result: *mut LeanObject,
}

/// cbindgen:field-names=[m_header, m_value, m_closure]
#[repr(C)]
pub struct LeanThunkObject {
    pub m_header: LeanObject,
    pub m_value: AtomicPtr<LeanObject>,
    pub m_closure: AtomicPtr<LeanObject>,
}

/// cbindgen:field-names=[m_header, m_value]
#[repr(C)]
pub struct LeanRefObject {
    pub m_header: LeanObject,
    pub m_value: *mut LeanObject,
}

/// cbindgen:field-names=[state, lock]
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
    header: LeanObject,
    value: AtomicPtr<LeanObject>,
    imp: *mut c_void,
}

#[repr(C)]
pub struct UvHandle {
    pub data: *mut c_void,
    pub loop_: *mut c_void,
    pub rest: [u8; 80],
}

#[repr(C)]
#[derive(Copy, Clone)]
pub struct LeanName {
    obj: *mut LeanObject,
}

#[repr(C)]
#[derive(Copy, Clone)]
pub struct LeanOptions {
    obj: *mut LeanObject,
}

#[repr(C)]
pub struct LeanNameGenerator {
    prefix: LeanName,
    next_idx: c_uint,
}

#[repr(C)]
pub struct LeanOptionalName {
    some: bool,
    value: LeanName,
}

static mut VERBOSE_OPT: LeanName = LeanName {
    obj: ptr::null_mut(),
};
static mut MAX_MEMORY_OPT: LeanName = LeanName {
    obj: ptr::null_mut(),
};
static mut TIMEOUT_OPT: LeanName = LeanName {
    obj: ptr::null_mut(),
};
static mut CONSTRUCTIONS_FRESH: LeanName = LeanName {
    obj: ptr::null_mut(),
};
static INTERNAL_UNIQUE_NAME_ID: std::sync::atomic::AtomicU32 = std::sync::atomic::AtomicU32::new(0);

struct NameGeneratorState {
    tmp_prefix: *mut LeanObject,
    prefixes: Vec<*mut LeanObject>,
}

unsafe impl Send for NameGeneratorState {}

static NAME_GENERATOR_STATE: std::sync::Mutex<Option<NameGeneratorState>> =
    std::sync::Mutex::new(None);

#[inline]
pub unsafe fn lean_unbox(obj: *mut LeanObject) -> Size {
    (obj as Size) >> 1
}

#[inline]
pub(crate) unsafe fn lean_is_scalar(obj: *mut LeanObject) -> bool {
    (obj as Size) & 1 == 1
}

#[inline]
pub(crate) unsafe fn lean_ptr_tag(obj: *mut LeanObject) -> u8 {
    if lean_is_scalar(obj) {
        lean_unbox(obj) as u8
    } else {
        (*obj).tag
    }
}

#[inline]
pub(crate) unsafe fn lean_obj_tag(obj: *mut LeanObject) -> u8 {
    lean_ptr_tag(obj)
}

#[inline]
pub(crate) unsafe fn lean_ptr_other(obj: *mut LeanObject) -> u8 {
    (*obj).other
}

#[inline]
pub(crate) fn lean_is_big_object_tag(tag: u8) -> bool {
    tag == LEAN_ARRAY_TAG || tag == LEAN_SCALAR_ARRAY_TAG || tag == LEAN_STRING_TAG
}

#[inline]
pub(crate) fn lean_usize_mul_would_overflow(a: Size, b: Size) -> bool {
    a.checked_mul(b).is_none()
}

#[inline]
pub(crate) fn lean_usize_add_would_overflow(a: Size, b: Size) -> bool {
    a.checked_add(b).is_none()
}

#[inline]
pub(crate) unsafe fn lean_usize_mul_checked(a: Size, b: Size) -> Size {
    match a.checked_mul(b) {
        Some(value) => value,
        None => runtime_object_panic_impl::lean_internal_panic_overflow(),
    }
}

#[inline]
pub(crate) unsafe fn lean_usize_add_checked(a: Size, b: Size) -> Size {
    match a.checked_add(b) {
        Some(value) => value,
        None => runtime_object_panic_impl::lean_internal_panic_overflow(),
    }
}

#[inline]
pub(crate) fn lean_align(v: Size, a: Size) -> Size {
    (v / a) * a + a * ((v % a) != 0) as Size
}

#[inline]
pub(crate) fn lean_get_slot_idx(sz: u32) -> u32 {
    debug_assert!(sz > 0);
    debug_assert_eq!(lean_align(sz as Size, LEAN_OBJECT_SIZE_DELTA), sz as Size);
    sz / LEAN_OBJECT_SIZE_DELTA as u32 - 1
}



#[inline]
pub(crate) unsafe fn lean_inc_ref_n(obj: *mut LeanObject, n: usize) {
    if runtime_object_rc_impl::UAF_DETECT && (*obj).rc == runtime_object_rc_impl::LEAN_UAF_POISON_RC
    {
        runtime_object_rc_impl::quar_report_uaf(obj, "inc");
    }
    if (*obj).rc > 0 {
        (*obj).rc += n as i32;
    } else if (*obj).rc != 0 {
        let rc = (&raw mut (*obj).rc).cast::<AtomicI32>();
        (*rc).fetch_sub(n as i32, Ordering::Relaxed);
    }
}

#[inline]
pub(crate) unsafe fn lean_inc_ref(obj: *mut LeanObject) {
    lean_inc_ref_n(obj, 1);
}

#[inline]
pub(crate) unsafe fn lean_dec_ref(obj: *mut LeanObject) {
    if runtime_object_rc_impl::UAF_DETECT && (*obj).rc == runtime_object_rc_impl::LEAN_UAF_POISON_RC
    {
        runtime_object_rc_impl::quar_report_uaf(obj, "dec");
    }
    if (*obj).rc > 1 {
        (*obj).rc -= 1;
    } else if (*obj).rc != 0 {
        lean_dec_ref_cold(obj);
    }
}

#[inline]
pub unsafe fn lean_inc(obj: *mut LeanObject) {
    if !lean_is_scalar(obj) {
        lean_inc_ref(obj);
    }
}

#[inline]
pub(crate) unsafe fn lean_inc_n(obj: *mut LeanObject, n: usize) {
    if !lean_is_scalar(obj) {
        lean_inc_ref_n(obj, n);
    }
}

#[inline]
pub unsafe fn lean_dec(obj: *mut LeanObject) {
    if !lean_is_scalar(obj) {
        lean_dec_ref(obj);
    }
}

#[inline]
pub(crate) unsafe fn lean_del_object(obj: *mut LeanObject) {
    if !lean_is_scalar(obj) {
        runtime_object_rc_impl::lean_free_object(obj);
    }
}

#[inline]
pub(crate) unsafe fn lean_is_mt(obj: *mut LeanObject) -> bool {
    (*obj).rc < 0
}

#[inline]
pub(crate) unsafe fn lean_is_st(obj: *mut LeanObject) -> bool {
    (*obj).rc > 0
}

#[inline]
pub(crate) unsafe fn lean_is_persistent(obj: *mut LeanObject) -> bool {
    (*obj).rc == 0
}

#[inline]
pub(crate) unsafe fn lean_has_rc(obj: *mut LeanObject) -> bool {
    (*obj).rc != 0
}

#[inline]
pub(crate) unsafe fn lean_get_rc_mt_addr(obj: *mut LeanObject) -> *mut AtomicI32 {
    (&raw mut (*obj).rc).cast::<AtomicI32>()
}

#[inline]
pub(crate) unsafe fn lean_is_ctor(obj: *mut LeanObject) -> bool {
    lean_ptr_tag(obj) <= LEAN_MAX_CTOR_TAG
}

#[inline]
pub(crate) unsafe fn lean_is_closure(obj: *mut LeanObject) -> bool {
    lean_ptr_tag(obj) == LEAN_CLOSURE_TAG
}

#[inline]
pub(crate) unsafe fn lean_is_array(obj: *mut LeanObject) -> bool {
    lean_ptr_tag(obj) == LEAN_ARRAY_TAG
}

#[inline]
pub(crate) unsafe fn lean_is_sarray(obj: *mut LeanObject) -> bool {
    lean_ptr_tag(obj) == LEAN_SCALAR_ARRAY_TAG
}

#[inline]
pub(crate) unsafe fn lean_is_string(obj: *mut LeanObject) -> bool {
    lean_ptr_tag(obj) == LEAN_STRING_TAG
}

#[inline]
pub(crate) unsafe fn lean_is_mpz(obj: *mut LeanObject) -> bool {
    lean_ptr_tag(obj) == LEAN_MPZ_TAG
}

#[inline]
pub(crate) unsafe fn lean_is_thunk(obj: *mut LeanObject) -> bool {
    lean_ptr_tag(obj) == LEAN_THUNK_TAG
}

#[inline]
pub(crate) unsafe fn lean_is_task(obj: *mut LeanObject) -> bool {
    lean_ptr_tag(obj) == LEAN_TASK_TAG
}

#[inline]
pub(crate) unsafe fn lean_is_promise(obj: *mut LeanObject) -> bool {
    lean_ptr_tag(obj) == LEAN_PROMISE_TAG
}

#[inline]
pub(crate) unsafe fn lean_is_external(obj: *mut LeanObject) -> bool {
    lean_ptr_tag(obj) == LEAN_EXTERNAL_TAG
}

#[inline]
pub(crate) unsafe fn lean_is_ref(obj: *mut LeanObject) -> bool {
    lean_ptr_tag(obj) == LEAN_REF_TAG
}

#[inline]
pub(crate) unsafe fn lean_to_ctor(obj: *mut LeanObject) -> *mut LeanCtorObject {
    debug_assert!(lean_is_ctor(obj));
    obj as *mut LeanCtorObject
}

#[inline]
pub(crate) unsafe fn lean_to_closure(obj: *mut LeanObject) -> *mut LeanClosureObject {
    debug_assert!(lean_is_closure(obj));
    obj as *mut LeanClosureObject
}

#[inline]
pub(crate) unsafe fn lean_to_array(obj: *mut LeanObject) -> *mut LeanArrayObject {
    debug_assert!(lean_is_array(obj));
    obj as *mut LeanArrayObject
}

#[inline]
pub(crate) unsafe fn lean_to_sarray(obj: *mut LeanObject) -> *mut LeanScalarArray {
    debug_assert!(lean_is_sarray(obj));
    obj as *mut LeanScalarArray
}

#[inline]
pub(crate) unsafe fn lean_to_string(obj: *mut LeanObject) -> *mut LeanStringObject {
    debug_assert!(lean_is_string(obj));
    obj as *mut LeanStringObject
}

#[inline]
pub(crate) unsafe fn lean_to_thunk(obj: *mut LeanObject) -> *mut LeanThunkObject {
    debug_assert!(lean_is_thunk(obj));
    obj as *mut LeanThunkObject
}

#[inline]
pub(crate) unsafe fn lean_to_task(obj: *mut LeanObject) -> *mut LeanTaskObject {
    debug_assert!(lean_is_task(obj));
    obj as *mut LeanTaskObject
}

#[inline]
pub(crate) unsafe fn lean_to_promise(obj: *mut LeanObject) -> *mut LeanPromiseObject {
    debug_assert!(lean_is_promise(obj));
    obj as *mut LeanPromiseObject
}

#[inline]
pub(crate) unsafe fn lean_to_ref(obj: *mut LeanObject) -> *mut LeanRefObject {
    debug_assert!(lean_is_ref(obj));
    obj as *mut LeanRefObject
}

#[inline]
pub(crate) unsafe fn lean_to_external(obj: *mut LeanObject) -> *mut LeanExternalObject {
    debug_assert!(lean_is_external(obj));
    obj as *mut LeanExternalObject
}

#[inline]
pub(crate) unsafe fn lean_is_exclusive(obj: *mut LeanObject) -> bool {
    lean_is_st(obj) && (*obj).rc == 1
}

#[inline]
pub(crate) unsafe fn lean_is_exclusive_obj(obj: *mut LeanObject) -> u8 {
    lean_is_exclusive(obj) as u8
}

#[inline]
pub(crate) unsafe fn lean_is_shared(obj: *mut LeanObject) -> bool {
    lean_is_st(obj) && (*obj).rc > 1
}

#[inline]
pub(crate) unsafe fn lean_set_st_header(obj: *mut LeanObject, tag: u32, other: u32) {
    (*obj).rc = 1;
    (*obj).tag = tag as u8;
    (*obj).other = other as u8;
}

#[inline]
pub(crate) unsafe fn lean_set_non_heap_header(
    obj: *mut LeanObject,
    sz: Size,
    tag: u32,
    other: u32,
) {
    debug_assert!(sz > 0);
    debug_assert!(sz < (1usize << 16));
    debug_assert!(sz == 1 || !lean_is_big_object_tag(tag as u8));
    (*obj).rc = 0;
    (*obj).tag = tag as u8;
    (*obj).other = other as u8;
    (*obj).cs_size = sz as u16;
}

#[inline]
pub(crate) unsafe fn lean_set_non_heap_header_for_big(
    obj: *mut LeanObject,
    tag: u32,
    other: u32,
) {
    lean_set_non_heap_header(obj, 1, tag, other);
}

#[inline]
pub(crate) unsafe fn lean_ctor_get(obj: *mut LeanObject, idx: usize) -> *mut LeanObject {
    (obj.add(1) as *mut *mut LeanObject).add(idx).read()
}

#[inline]
pub(crate) unsafe fn lean_ctor_num_objs(obj: *mut LeanObject) -> u32 {
    (*obj).other as u32
}

#[inline]
pub(crate) unsafe fn lean_ctor_obj_cptr(obj: *mut LeanObject) -> *mut *mut LeanObject {
    obj.add(1) as *mut *mut LeanObject
}

#[inline]
pub(crate) unsafe fn lean_ctor_scalar_cptr(obj: *mut LeanObject) -> *mut u8 {
    lean_ctor_obj_cptr(obj).add(lean_ctor_num_objs(obj) as usize).cast::<u8>()
}

#[inline]
pub(crate) unsafe fn lean_ctor_get_usize(obj: *mut LeanObject, idx: usize) -> Size {
    debug_assert!(idx >= lean_ctor_num_objs(obj) as usize);
    *((lean_ctor_obj_cptr(obj) as *const Size).add(idx))
}

#[inline]
pub(crate) unsafe fn lean_ctor_get_uint8(obj: *mut LeanObject, offset: usize) -> u8 {
    (obj.add(1) as *mut u8).add(offset).read()
}

#[inline]
pub(crate) unsafe fn lean_ctor_get_uint16(obj: *mut LeanObject, offset: usize) -> u16 {
    (obj.add(1) as *mut u8).add(offset).cast::<u16>().read()
}

#[inline]
pub(crate) unsafe fn lean_ctor_get_uint32(obj: *mut LeanObject, offset: usize) -> u32 {
    (obj.add(1) as *mut u8).add(offset).cast::<u32>().read()
}

#[inline]
pub(crate) unsafe fn lean_ctor_get_uint64(obj: *mut LeanObject, offset: usize) -> u64 {
    (obj.add(1) as *mut u8).add(offset).cast::<u64>().read()
}

#[inline]
pub(crate) unsafe fn lean_ctor_get_float(obj: *mut LeanObject, offset: usize) -> f64 {
    (obj.add(1) as *mut u8).add(offset).cast::<f64>().read()
}

#[inline]
pub(crate) unsafe fn lean_ctor_get_float32(obj: *mut LeanObject, offset: usize) -> f32 {
    (obj.add(1) as *mut u8).add(offset).cast::<f32>().read()
}

#[inline]
pub(crate) unsafe fn lean_ctor_set_usize(obj: *mut LeanObject, idx: usize, value: Size) {
    debug_assert!(idx >= lean_ctor_num_objs(obj) as usize);
    *((lean_ctor_obj_cptr(obj) as *mut Size).add(idx)) = value;
}

#[inline]
pub(crate) unsafe fn lean_ctor_set_uint8(obj: *mut LeanObject, offset: usize, value: u8) {
    (obj.add(1) as *mut u8).add(offset).write(value);
}

#[inline]
pub(crate) unsafe fn lean_ctor_set_uint16(obj: *mut LeanObject, offset: usize, value: u16) {
    (obj.add(1) as *mut u8)
        .add(offset)
        .cast::<u16>()
        .write(value);
}

#[inline]
pub(crate) unsafe fn lean_ctor_set_uint32(obj: *mut LeanObject, offset: usize, value: u32) {
    (obj.add(1) as *mut u8)
        .add(offset)
        .cast::<u32>()
        .write(value);
}

#[inline]
pub(crate) unsafe fn lean_ctor_set_uint64(obj: *mut LeanObject, offset: usize, value: u64) {
    (obj.add(1) as *mut u8)
        .add(offset)
        .cast::<u64>()
        .write(value);
}

#[inline]
pub(crate) unsafe fn lean_ctor_set_float(obj: *mut LeanObject, offset: usize, value: f64) {
    (obj.add(1) as *mut u8)
        .add(offset)
        .cast::<f64>()
        .write(value);
}

#[inline]
pub(crate) unsafe fn lean_ctor_set_float32(obj: *mut LeanObject, offset: usize, value: f32) {
    (obj.add(1) as *mut u8)
        .add(offset)
        .cast::<f32>()
        .write(value);
}

#[inline]
pub(crate) unsafe fn lean_runtime_alloc_ctor(
    tag: c_uint,
    num_objs: c_uint,
    scalar_size: c_uint,
) -> *mut LeanObject {
    const LEAN_MAX_CTOR_TAG: c_uint = 243;
    const LEAN_MAX_CTOR_FIELDS: c_uint = 256;
    const LEAN_MAX_CTOR_SCALARS_SIZE: c_uint = 1024;

    debug_assert!(tag <= LEAN_MAX_CTOR_TAG);
    debug_assert!(num_objs < LEAN_MAX_CTOR_FIELDS);
    debug_assert!(scalar_size < LEAN_MAX_CTOR_SCALARS_SIZE);

    let byte_size = core::mem::size_of::<LeanCtorObject>()
        .checked_add(
            core::mem::size_of::<*mut LeanObject>()
                .checked_mul(num_objs as Size)
                .expect("constructor allocation overflow"),
        )
        .and_then(|size| size.checked_add(scalar_size as Size))
        .expect("constructor allocation overflow");
    let obj = runtime_object_rc_impl::lean_alloc_ctor_memory(byte_size) as *mut LeanCtorObject;
    (*obj).header.rc = 1;
    (*obj).header.other = num_objs as u8;
    (*obj).header.tag = tag as u8;
    obj as *mut LeanObject
}

#[inline]
pub(crate) unsafe fn lean_alloc_ctor(
    tag: c_uint,
    num_objs: c_uint,
    scalar_size: c_uint,
) -> *mut LeanObject {
    lean_runtime_alloc_ctor(tag, num_objs, scalar_size)
}

#[inline]
pub(crate) unsafe fn lean_runtime_ctor_set(
    obj: *mut LeanObject,
    index: c_uint,
    value: *mut LeanObject,
) {
    debug_assert!(index < (*obj).other as c_uint);
    let fields = (obj as *mut LeanCtorObject)
        .cast::<u8>()
        .add(core::mem::size_of::<LeanCtorObject>()) as *mut *mut LeanObject;
    fields.add(index as Size).write(value);
}

#[inline]
pub(crate) unsafe fn lean_ctor_set(
    obj: *mut LeanObject,
    index: c_uint,
    value: *mut LeanObject,
) {
    lean_runtime_ctor_set(obj, index, value);
}

#[inline]
pub(crate) unsafe fn lean_ctor_set_tag(obj: *mut LeanObject, new_tag: u8) {
    (*obj).tag = new_tag;
}

#[inline]
pub(crate) unsafe fn lean_ctor_release(obj: *mut LeanObject, index: c_uint) {
    let value = lean_ctor_get(obj, index as usize);
    lean_dec(value);
    lean_ctor_set(obj, index, lean_box(0));
}

#[inline]
pub(crate) unsafe fn lean_dec_ref_known(obj: *mut LeanObject, objs: c_uint) {
    debug_assert!(lean_ptr_tag(obj) == LEAN_REF_TAG);
    if (*obj).rc == LEAN_SINGLE_THREADED_RC {
        for i in 0..objs {
            lean_dec(lean_ctor_get(obj, i as usize));
        }
        if !lean_is_scalar(obj) {
            runtime_object_rc_impl::lean_free_object(obj);
        }
    } else {
        lean_dec_ref(obj);
    }
}

#[inline]
pub(crate) unsafe fn lean_box_uint64(v: u64) -> *mut LeanObject {
    let r = lean_runtime_alloc_ctor(0, 0, core::mem::size_of::<u64>() as c_uint);
    lean_ctor_set_uint64(r, 0, v);
    r
}

#[inline]
pub(crate) unsafe fn lean_unbox_uint64(o: *mut LeanObject) -> u64 {
    lean_ctor_get_uint64(o, 0)
}

#[inline]
pub(crate) unsafe fn lean_box_usize(v: usize) -> *mut LeanObject {
    let r = lean_runtime_alloc_ctor(0, 0, core::mem::size_of::<usize>() as c_uint);
    lean_ctor_set_usize(r, 0, v);
    r
}

#[inline]
pub(crate) unsafe fn lean_unbox_usize(o: *mut LeanObject) -> usize {
    lean_ctor_get_usize(o, 0)
}

#[inline]
pub(crate) fn lean_bool_to_uint8(a: u8) -> u8 {
    a
}

#[inline]
pub(crate) fn lean_bool_to_uint16(a: u8) -> u16 {
    a as u16
}

#[inline]
pub(crate) fn lean_bool_to_uint32(a: u8) -> u32 {
    a as u32
}

#[inline]
pub(crate) fn lean_bool_to_uint64(a: u8) -> u64 {
    a as u64
}

#[inline]
pub(crate) fn lean_bool_to_usize(a: u8) -> usize {
    a as usize
}

#[inline]
pub(crate) fn lean_bool_to_int8(a: u8) -> u8 {
    a as i8 as u8
}

#[inline]
pub(crate) fn lean_bool_to_int16(a: u8) -> u16 {
    a as i16 as u16
}

#[inline]
pub(crate) fn lean_bool_to_int32(a: u8) -> u32 {
    a as i32 as u32
}

#[inline]
pub(crate) fn lean_bool_to_int64(a: u8) -> u64 {
    a as i64 as u64
}

#[inline]
pub(crate) fn lean_bool_to_isize(a: u8) -> usize {
    a as usize
}

#[inline]
pub(crate) fn lean_ptr_addr(a: *mut LeanObject) -> usize {
    a as usize
}

#[inline]
pub(crate) unsafe fn lean_hashmap_mk_idx(sz: *mut LeanObject, hash: u64) -> usize {
    hash as usize & (unsafe { lean_unbox(sz) } - 1)
}

#[inline]
pub(crate) unsafe fn lean_hashset_mk_idx(sz: *mut LeanObject, hash: u64) -> usize {
    hash as usize & (unsafe { lean_unbox(sz) } - 1)
}

#[inline]
pub(crate) unsafe fn lean_expr_data(expr: *mut LeanObject) -> u64 {
    lean_ctor_get_uint64(expr, lean_ctor_num_objs(expr) as usize * core::mem::size_of::<*mut LeanObject>())
}

#[inline]
pub(crate) unsafe fn lean_get_max_ctor_fields(_: *mut LeanObject) -> *mut LeanObject {
    unsafe { lean_box(LEAN_MAX_CTOR_FIELDS) }
}

#[inline]
pub(crate) unsafe fn lean_get_max_ctor_scalars_size(_: *mut LeanObject) -> *mut LeanObject {
    unsafe { lean_box(LEAN_MAX_CTOR_SCALARS_SIZE) }
}

#[inline]
pub(crate) unsafe fn lean_get_usize_size(_: *mut LeanObject) -> *mut LeanObject {
    unsafe { lean_box(core::mem::size_of::<usize>()) }
}

#[inline]
pub(crate) unsafe fn lean_get_max_ctor_tag(_: *mut LeanObject) -> *mut LeanObject {
    unsafe { lean_box(LEAN_MAX_CTOR_TAG as usize) }
}

#[inline]
pub(crate) fn lean_strict_or(b1: u8, b2: u8) -> u8 {
    (b1 != 0 || b2 != 0) as u8
}

#[inline]
pub(crate) fn lean_strict_and(b1: u8, b2: u8) -> u8 {
    (b1 != 0 && b2 != 0) as u8
}

#[inline]
pub(crate) unsafe fn lean_nat_pred(n: *mut LeanObject) -> *mut LeanObject {
    // Mirrors origin-master-src/include/lean/static runtime layout: lean_nat_pred(n) = lean_nat_sub(n, lean_box(1)).
    if lean_is_scalar(n) {
        let v = lean_unbox(n);
        unsafe { lean_box(if v == 0 { 0 } else { v - 1 }) }
    } else {
        runtime_object_nat_int_impl::lean_nat_big_sub(n, unsafe { lean_box(1) })
    }
}

#[inline]
pub(crate) unsafe fn lean_runtime_hold(_: *mut LeanObject) -> *mut LeanObject {
    unsafe { lean_box(0) }
}

#[inline]
pub(crate) unsafe fn lean_version_get_major(_: *mut LeanObject) -> *mut LeanObject {
    unsafe { lean_box(env!("LEAN_RUST_VERSION_MAJOR").parse::<usize>().unwrap()) }
}

#[inline]
pub(crate) unsafe fn lean_version_get_minor(_: *mut LeanObject) -> *mut LeanObject {
    unsafe { lean_box(env!("LEAN_RUST_VERSION_MINOR").parse::<usize>().unwrap()) }
}

#[inline]
pub(crate) unsafe fn lean_version_get_patch(_: *mut LeanObject) -> *mut LeanObject {
    unsafe { lean_box(env!("LEAN_RUST_VERSION_PATCH").parse::<usize>().unwrap()) }
}

#[inline]
pub(crate) fn lean_version_get_is_release(_: *mut LeanObject) -> u8 {
    env!("LEAN_RUST_VERSION_IS_RELEASE").parse::<u8>().unwrap()
}

#[inline]
pub(crate) unsafe fn lean_version_get_special_desc(_: *mut LeanObject) -> *mut LeanObject {
    unsafe { lean_mk_string(concat!(env!("LEAN_RUST_VERSION_SPECIAL_DESC"), "\0").as_ptr() as *const core::ffi::c_char) }
}

#[inline]
pub(crate) unsafe fn lean_system_platform_target(_: *mut LeanObject) -> *mut LeanObject {
    unsafe { lean_mk_string(concat!(env!("LEAN_RUST_PLATFORM_TARGET"), "\0").as_ptr() as *const core::ffi::c_char) }
}

#[inline]
pub(crate) fn lean_internal_is_stage0(_: *mut LeanObject) -> u8 {
    env!("LEAN_RUST_IS_STAGE0").parse::<u8>().unwrap()
}

#[inline]
pub(crate) unsafe fn lean_manual_get_root(_: *mut LeanObject) -> *mut LeanObject {
    unsafe { lean_mk_string(concat!(env!("LEAN_RUST_MANUAL_ROOT"), "\0").as_ptr() as *const core::ffi::c_char) }
}

#[inline]
pub(crate) unsafe fn lean_array_get(
    def_val: *mut LeanObject,
    a: *mut LeanObject,
    i: *mut LeanObject,
) -> *mut LeanObject {
    // Mirrors lean_array_get from origin-master-src/include/lean/static runtime layout
    if lean_is_scalar(i) {
        let idx = lean_unbox(i);
        if idx < lean_array_size(a) {
            let r = lean_array_get_core(a, idx);
            lean_inc(r);
            return r;
        }
    }
    // If i is not a scalar it must be out of bounds (i > LEAN_MAX_SMALL_NAT)
    lean_inc(def_val);
    runtime_object_array_impl::lean_array_get_panic(def_val)
}

#[inline]
pub(crate) unsafe fn lean_array_get_borrowed(
    def_val: *mut LeanObject,
    a: *mut LeanObject,
    i: *mut LeanObject,
) -> *mut LeanObject {
    // Mirrors lean_array_get_borrowed from origin-master-src/include/lean/static runtime layout
    if lean_is_scalar(i) {
        let idx = lean_unbox(i);
        if idx < lean_array_size(a) {
            return lean_array_get_core(a, idx);
        }
    }
    lean_inc(def_val);
    runtime_object_array_impl::lean_array_get_panic(def_val)
}

#[inline]
pub(crate) unsafe fn lean_array_size(obj: *mut LeanObject) -> usize {
    let array = obj as *const LeanArrayObject;
    (*array).size
}

#[inline]
pub(crate) unsafe fn lean_alloc_array(size: usize, capacity: usize) -> *mut LeanObject {
    let byte_size = core::mem::size_of::<LeanArrayObject>()
        .checked_add(
            core::mem::size_of::<*mut LeanObject>()
                .checked_mul(capacity)
                .expect("array allocation overflow"),
        )
        .expect("array allocation overflow");
    let obj = lean_alloc_object(byte_size) as *mut LeanArrayObject;
    (*obj).header.rc = 1;
    (*obj).header.cs_size = 0;
    (*obj).header.other = 0;
    (*obj).header.tag = 246;
    (*obj).size = size;
    (*obj).capacity = capacity;
    obj as *mut LeanObject
}

#[inline]
pub(crate) unsafe fn lean_array_sz(a: *mut LeanObject) -> *mut LeanObject {
    let r = lean_box(lean_array_size(a));
    lean_dec(a);
    r
}

#[inline]
pub(crate) unsafe fn lean_array_get_size(a: *mut LeanObject) -> *mut LeanObject {
    lean_box(lean_array_size(a))
}

#[inline]
pub(crate) unsafe fn lean_mk_empty_array() -> *mut LeanObject {
    lean_alloc_array(0, 0)
}

#[inline]
pub(crate) unsafe fn lean_mk_empty_array_with_capacity(capacity: *mut LeanObject) -> *mut LeanObject {
    if !lean_is_scalar(capacity) {
        runtime_object_panic_impl::lean_internal_panic_out_of_memory();
    }
    lean_alloc_array(0, lean_unbox(capacity))
}

#[inline]
pub(crate) unsafe fn lean_array_uget(a: *mut LeanObject, i: usize) -> *mut LeanObject {
    let r = lean_array_get_core(a, i);
    lean_inc(r);
    r
}

#[inline]
pub(crate) unsafe fn lean_array_uget_borrowed(a: *mut LeanObject, i: usize) -> *mut LeanObject {
    lean_array_get_core(a, i)
}

#[inline]
pub(crate) unsafe fn lean_array_fget(a: *mut LeanObject, i: *mut LeanObject) -> *mut LeanObject {
    lean_array_uget(a, lean_unbox(i))
}

#[inline]
pub(crate) unsafe fn lean_array_fget_borrowed(a: *mut LeanObject, i: *mut LeanObject) -> *mut LeanObject {
    lean_array_get_core(a, lean_unbox(i))
}

#[inline]
pub(crate) unsafe fn lean_ensure_exclusive_array(a: *mut LeanObject) -> *mut LeanObject {
    if lean_is_exclusive(a) {
        a
    } else {
        runtime_object_array_impl::lean_copy_expand_array_nonlinear(a, false)
    }
}

#[inline]
pub(crate) unsafe fn lean_array_uset(a: *mut LeanObject, i: usize, v: *mut LeanObject) -> *mut LeanObject {
    let r = lean_ensure_exclusive_array(a);
    let it = lean_array_cptr(r).add(i);
    lean_dec(*it);
    *it = v;
    r
}

#[inline]
pub(crate) unsafe fn lean_array_fset(a: *mut LeanObject, i: *mut LeanObject, v: *mut LeanObject) -> *mut LeanObject {
    lean_array_uset(a, lean_unbox(i), v)
}

#[inline]
pub(crate) unsafe fn lean_array_set(a: *mut LeanObject, i: *mut LeanObject, v: *mut LeanObject) -> *mut LeanObject {
    if lean_is_scalar(i) {
        let idx = lean_unbox(i);
        if idx < lean_array_size(a) {
            return lean_array_uset(a, idx, v);
        }
    }
    runtime_object_array_impl::lean_array_set_panic(a, v)
}

#[inline]
pub(crate) unsafe fn lean_array_pop(a: *mut LeanObject) -> *mut LeanObject {
    let r = lean_ensure_exclusive_array(a);
    let mut sz = (*lean_to_array(r)).size;
    if sz == 0 {
        return r;
    }
    sz -= 1;
    let last = lean_array_cptr(r).add(sz);
    (*lean_to_array(r)).size = sz;
    lean_dec(*last);
    r
}

#[inline]
pub(crate) unsafe fn lean_array_uswap(a: *mut LeanObject, i: usize, j: usize) -> *mut LeanObject {
    let r = lean_ensure_exclusive_array(a);
    let it = lean_array_cptr(r);
    let v1 = *it.add(i);
    *it.add(i) = *it.add(j);
    *it.add(j) = v1;
    r
}

#[inline]
pub(crate) unsafe fn lean_array_fswap(a: *mut LeanObject, i: *mut LeanObject, j: *mut LeanObject) -> *mut LeanObject {
    lean_array_uswap(a, lean_unbox(i), lean_unbox(j))
}

#[inline]
pub(crate) unsafe fn lean_array_swap(a: *mut LeanObject, i: *mut LeanObject, j: *mut LeanObject) -> *mut LeanObject {
    if !lean_is_scalar(i) || !lean_is_scalar(j) {
        return a;
    }
    let ui = lean_unbox(i);
    let uj = lean_unbox(j);
    let sz = (*lean_to_array(a)).size;
    if ui >= sz || uj >= sz {
        return a;
    }
    lean_array_uswap(a, ui, uj)
}

#[inline]
pub(crate) unsafe fn lean_array_capacity(obj: *mut LeanObject) -> usize {
    let array = obj as *const LeanArrayObject;
    (*array).capacity
}

#[inline]
pub(crate) unsafe fn lean_array_byte_size(obj: *mut LeanObject) -> usize {
    core::mem::size_of::<LeanArrayObject>() + core::mem::size_of::<*mut LeanObject>() * lean_array_capacity(obj)
}

#[inline]
pub(crate) unsafe fn lean_array_data_byte_size(obj: *mut LeanObject) -> usize {
    core::mem::size_of::<LeanArrayObject>() + core::mem::size_of::<*mut LeanObject>() * lean_array_size(obj)
}

#[inline]
pub(crate) unsafe fn lean_array_cptr(obj: *mut LeanObject) -> *mut *mut LeanObject {
    (*(obj as *mut LeanArrayObject)).data.as_mut_ptr()
}

#[inline]
pub(crate) unsafe fn lean_array_set_size(obj: *mut LeanObject, sz: usize) {
    debug_assert!(lean_is_array(obj));
    debug_assert!(lean_is_exclusive(obj));
    debug_assert!(sz <= lean_array_capacity(obj));
    (*(obj as *mut LeanArrayObject)).size = sz;
}

#[inline]
pub(crate) unsafe fn lean_array_get_core(obj: *mut LeanObject, i: usize) -> *mut LeanObject {
    debug_assert!(i < lean_array_size(obj));
    lean_array_cptr(obj).add(i).read()
}

#[inline]
pub(crate) unsafe fn lean_array_set_core(obj: *mut LeanObject, i: usize, v: *mut LeanObject) {
    debug_assert!(!lean_has_rc(obj) || lean_is_exclusive(obj));
    debug_assert!(i < lean_array_size(obj));
    lean_array_cptr(obj).add(i).write(v);
}

#[inline]
pub(crate) unsafe fn lean_closure_fun(obj: *mut LeanObject) -> *mut core::ffi::c_void {
    (*lean_to_closure(obj)).fun
}

#[inline]
pub(crate) unsafe fn lean_closure_arity(obj: *mut LeanObject) -> u32 {
    (*lean_to_closure(obj)).arity as u32
}

#[inline]
pub(crate) unsafe fn lean_closure_num_fixed(obj: *mut LeanObject) -> u32 {
    (*lean_to_closure(obj)).num_fixed as u32
}

#[inline]
pub(crate) unsafe fn lean_closure_arg_cptr(obj: *mut LeanObject) -> *mut *mut LeanObject {
    (*lean_to_closure(obj)).data.as_mut_ptr()
}

#[inline]
pub(crate) unsafe fn lean_closure_get(obj: *mut LeanObject, i: u32) -> *mut LeanObject {
    debug_assert!(i < lean_closure_num_fixed(obj));
    *lean_closure_arg_cptr(obj).add(i as usize)
}

#[inline]
pub(crate) unsafe fn lean_closure_set(obj: *mut LeanObject, i: u32, a: *mut LeanObject) {
    debug_assert!(i < lean_closure_num_fixed(obj));
    *lean_closure_arg_cptr(obj).add(i as usize) = a;
}

#[inline]
pub(crate) unsafe fn lean_closure_byte_size(obj: *mut LeanObject) -> usize {
    core::mem::size_of::<LeanClosureObject>()
        + core::mem::size_of::<*mut LeanObject>() * lean_closure_num_fixed(obj) as usize
}

#[inline]
pub(crate) unsafe fn lean_closure_data_byte_size(obj: *mut LeanObject) -> usize {
    lean_closure_byte_size(obj)
}

#[inline]
pub(crate) unsafe fn lean_mk_empty_byte_array(capacity: *mut LeanObject) -> *mut LeanObject {
    if !lean_is_scalar(capacity) {
        runtime_object_panic_impl::lean_internal_panic_out_of_memory();
    }
    lean_alloc_sarray(1, 0, lean_unbox(capacity))
}

#[inline]
pub(crate) unsafe fn lean_byte_array_size(a: *mut LeanObject) -> *mut LeanObject {
    lean_box(lean_sarray_size(a))
}

#[inline]
pub(crate) unsafe fn lean_byte_array_uget(a: *mut LeanObject, i: usize) -> u8 {
    debug_assert!(i < lean_sarray_size(a));
    *lean_sarray_cptr(a).add(i)
}

#[inline]
pub(crate) unsafe fn lean_byte_array_get(a: *mut LeanObject, i: *mut LeanObject) -> u8 {
    if lean_is_scalar(i) {
        let idx = lean_unbox(i);
        if idx < lean_sarray_size(a) {
            return lean_byte_array_uget(a, idx);
        }
    }
    0
}

#[inline]
pub(crate) unsafe fn lean_byte_array_fget(a: *mut LeanObject, i: *mut LeanObject) -> u8 {
    lean_byte_array_uget(a, lean_unbox(i))
}

#[inline]
pub(crate) unsafe fn lean_byte_array_uset(a: *mut LeanObject, i: usize, v: u8) -> *mut LeanObject {
    let r = if lean_is_exclusive(a) {
        a
    } else {
        runtime_object_array_impl::lean_copy_byte_array(a)
    };
    *(lean_sarray_cptr(r) as *mut u8).add(i) = v;
    r
}

#[inline]
pub(crate) unsafe fn lean_byte_array_set(a: *mut LeanObject, i: *mut LeanObject, b: u8) -> *mut LeanObject {
    if !lean_is_scalar(i) {
        a
    } else {
        let idx = lean_unbox(i);
        if idx >= lean_sarray_size(a) {
            a
        } else {
            lean_byte_array_uset(a, idx, b)
        }
    }
}

#[inline]
pub(crate) unsafe fn lean_byte_array_fset(a: *mut LeanObject, i: *mut LeanObject, b: u8) -> *mut LeanObject {
    lean_byte_array_uset(a, lean_unbox(i), b)
}

#[inline]
pub(crate) unsafe fn lean_mk_empty_float_array(capacity: *mut LeanObject) -> *mut LeanObject {
    if !lean_is_scalar(capacity) {
        runtime_object_panic_impl::lean_internal_panic_out_of_memory();
    }
    lean_alloc_sarray(core::mem::size_of::<f64>() as c_uint, 0, lean_unbox(capacity))
}

#[inline]
pub(crate) unsafe fn lean_float_array_size(a: *mut LeanObject) -> *mut LeanObject {
    lean_box(lean_sarray_size(a))
}

#[inline]
pub(crate) unsafe fn lean_float_array_cptr(a: *mut LeanObject) -> *mut f64 {
    lean_sarray_cptr(a) as *mut f64
}

#[inline]
pub(crate) unsafe fn lean_float_array_uget(a: *mut LeanObject, i: usize) -> f64 {
    debug_assert!(i < lean_sarray_size(a));
    *lean_float_array_cptr(a).add(i)
}

#[inline]
pub(crate) unsafe fn lean_float_array_fget(a: *mut LeanObject, i: *mut LeanObject) -> f64 {
    lean_float_array_uget(a, lean_unbox(i))
}

#[inline]
pub(crate) unsafe fn lean_float_array_get(a: *mut LeanObject, i: *mut LeanObject) -> f64 {
    if lean_is_scalar(i) {
        let idx = lean_unbox(i);
        if idx < lean_sarray_size(a) {
            return lean_float_array_uget(a, idx);
        }
    }
    0.0
}

#[inline]
pub(crate) unsafe fn lean_float_array_uset(a: *mut LeanObject, i: usize, d: f64) -> *mut LeanObject {
    let r = if lean_is_exclusive(a) {
        a
    } else {
        runtime_object_array_impl::lean_copy_float_array(a)
    };
    *lean_float_array_cptr(r).add(i) = d;
    r
}

#[inline]
pub(crate) unsafe fn lean_float_array_set(a: *mut LeanObject, i: *mut LeanObject, d: f64) -> *mut LeanObject {
    if !lean_is_scalar(i) {
        a
    } else {
        let idx = lean_unbox(i);
        if idx >= lean_sarray_size(a) {
            a
        } else {
            lean_float_array_uset(a, idx, d)
        }
    }
}

#[inline]
pub(crate) unsafe fn lean_float_array_fset(a: *mut LeanObject, i: *mut LeanObject, d: f64) -> *mut LeanObject {
    lean_float_array_uset(a, lean_unbox(i), d)
}

pub(crate) unsafe fn lean_alloc_string(
    size: usize,
    capacity: usize,
    len: usize,
) -> *mut LeanObject {
    const LEAN_STRING_TAG: u8 = 249;
    let byte_size = core::mem::size_of::<LeanStringObject>()
        .checked_add(capacity)
        .expect("string allocation overflow");
    let obj = lean_alloc_object(byte_size) as *mut LeanStringObject;
    (*obj).header.rc = 1;
    (*obj).header.cs_size = 0;
    (*obj).header.other = 0;
    (*obj).header.tag = LEAN_STRING_TAG;
    (*obj).size = size;
    (*obj).capacity = capacity;
    (*obj).len = len;
    obj as *mut LeanObject
}

#[inline]
pub(crate) unsafe fn lean_sarray_set_size(obj: *mut LeanObject, size: Size) {
    let sarray = obj as *mut LeanScalarArray;
    (*sarray).size = size;
}

#[inline]
pub(crate) unsafe fn lean_sarray_size(obj: *mut LeanObject) -> Size {
    let sarray = obj as *const LeanScalarArray;
    (*sarray).size
}

#[inline]
pub(crate) unsafe fn lean_sarray_capacity(obj: *mut LeanObject) -> Size {
    let sarray = obj as *const LeanScalarArray;
    (*sarray).capacity
}

#[inline]
pub(crate) unsafe fn lean_alloc_sarray_would_overflow(elem_size: c_uint, capacity: Size) -> bool {
    if lean_usize_mul_would_overflow(elem_size as usize, capacity) {
        return true;
    }
    if lean_usize_add_would_overflow(core::mem::size_of::<LeanScalarArray>(), (elem_size as usize) * capacity) {
        return true;
    }
    false
}

#[inline]
pub(crate) unsafe fn lean_alloc_sarray(elem_size: c_uint, size: Size, capacity: Size) -> *mut LeanObject {
    let byte_size = core::mem::size_of::<LeanScalarArray>()
        .checked_add(
            (elem_size as usize)
                .checked_mul(capacity)
                .expect("sarray allocation overflow"),
        )
        .expect("sarray allocation overflow");
    let obj = lean_alloc_object(byte_size) as *mut LeanScalarArray;
    (*obj).header.rc = 1;
    (*obj).header.cs_size = 0;
    (*obj).header.other = elem_size as u8;
    (*obj).header.tag = 248;
    (*obj).size = size;
    (*obj).capacity = capacity;
    obj as *mut LeanObject
}

#[inline]
pub(crate) unsafe fn lean_sarray_byte_size(obj: *mut LeanObject) -> usize {
    core::mem::size_of::<LeanScalarArray>() + lean_sarray_elem_size(obj) as usize * lean_sarray_capacity(obj)
}

#[inline]
pub(crate) unsafe fn lean_sarray_data_byte_size(obj: *mut LeanObject) -> usize {
    core::mem::size_of::<LeanScalarArray>() + lean_sarray_elem_size(obj) as usize * lean_sarray_size(obj)
}

#[inline]
pub(crate) unsafe fn lean_sarray_elem_size(obj: *mut LeanObject) -> u8 {
    (*obj).other
}

#[inline]
pub unsafe fn lean_io_result_is_ok(obj: *mut LeanObject) -> bool {
    lean_ptr_tag(obj) == 0
}

#[inline]
pub(crate) unsafe fn lean_io_result_is_error(obj: *mut LeanObject) -> bool {
    lean_ptr_tag(obj) == 1
}


#[inline]
pub(crate) unsafe fn lean_string_utf8_get_fast(s: *mut LeanObject, i: *mut LeanObject) -> u32 {
    let str = lean_string_cstr(s);
    let idx = lean_unbox(i);
    let c = *str.add(idx) as u8;
    if c & 0x80 == 0 {
        c as u32
    } else {
        runtime_object_string_impl::lean_string_utf8_get_fast_cold(str, idx, lean_string_size(s), c)
    }
}

#[inline]
pub(crate) unsafe fn lean_string_get_byte_fast(s: *mut LeanObject, i: *mut LeanObject) -> u8 {
    let str = lean_string_cstr(s);
    let idx = lean_unbox(i);
    *str.add(idx) as u8
}

#[inline]
pub(crate) unsafe fn lean_string_utf8_next_fast(s: *mut LeanObject, i: *mut LeanObject) -> *mut LeanObject {
    let str = lean_string_cstr(s);
    let idx = lean_unbox(i);
    let c = *str.add(idx) as u8;
    if c & 0x80 == 0 {
        lean_box(idx + 1)
    } else {
        runtime_object_string_impl::lean_string_utf8_next_fast_cold(idx, c)
    }
}

#[inline]
pub(crate) unsafe fn lean_string_utf8_at_end(s: *mut LeanObject, i: *mut LeanObject) -> bool {
    !lean_is_scalar(i) || lean_unbox(i) >= lean_string_size(s) - 1
}

#[inline]
pub(crate) unsafe fn lean_string_capacity(obj: *mut LeanObject) -> usize {
    (*(obj as *const LeanStringObject)).capacity
}

#[inline]
pub(crate) unsafe fn lean_string_byte_size(obj: *mut LeanObject) -> usize {
    core::mem::size_of::<LeanStringObject>() + lean_string_capacity(obj)
}

#[inline]
pub(crate) unsafe fn lean_string_size(obj: *mut LeanObject) -> usize {
    (*(obj as *const LeanStringObject)).size
}

#[inline]
pub(crate) unsafe fn lean_string_len(obj: *mut LeanObject) -> usize {
    (*(obj as *const LeanStringObject)).len
}

#[inline]
pub(crate) unsafe fn lean_string_data_byte_size(obj: *mut LeanObject) -> usize {
    core::mem::size_of::<LeanStringObject>() + lean_string_size(obj)
}

#[inline]
pub(crate) unsafe fn lean_string_length(s: *mut LeanObject) -> *mut LeanObject {
    lean_box(lean_string_len(s))
}

#[inline]
pub(crate) unsafe fn lean_string_utf8_byte_size(s: *mut LeanObject) -> *mut LeanObject {
    lean_box(lean_string_size(s) - 1)
}

#[inline]
pub(crate) unsafe fn lean_string_eq(s1: *mut LeanObject, s2: *mut LeanObject) -> bool {
    let len1 = lean_string_size(s1);
    let len2 = lean_string_size(s2);
    len1 == len2 && runtime_object_string_impl::lean_string_eq_cold(s1, s2)
}

#[inline]
pub(crate) unsafe fn lean_string_ne(s1: *mut LeanObject, s2: *mut LeanObject) -> bool {
    !lean_string_eq(s1, s2)
}

#[inline]
pub(crate) unsafe fn lean_string_dec_eq(s1: *mut LeanObject, s2: *mut LeanObject) -> u8 {
    lean_string_eq(s1, s2) as u8
}

#[inline]
pub(crate) unsafe fn lean_string_dec_lt(s1: *mut LeanObject, s2: *mut LeanObject) -> u8 {
    runtime_object_string_impl::lean_string_lt(s1, s2) as u8
}

#[inline]
pub(crate) unsafe fn lean_sarray_eq(a1: *mut LeanObject, a2: *mut LeanObject) -> bool {
    debug_assert!(lean_sarray_elem_size(a1) == lean_sarray_elem_size(a2));
    a1 == a2 || (lean_sarray_size(a1) == lean_sarray_size(a2) && runtime_object_string_impl::lean_sarray_eq_cold(a1, a2))
}

#[inline]
pub(crate) unsafe fn lean_sarray_dec_eq(a1: *mut LeanObject, a2: *mut LeanObject) -> u8 {
    lean_sarray_eq(a1, a2) as u8
}

#[inline]
pub unsafe fn lean_io_result_get_value(obj: *mut LeanObject) -> *mut LeanObject {
    debug_assert!(lean_io_result_is_ok(obj));
    lean_ctor_get(obj, 0)
}

#[inline]
pub unsafe fn lean_io_result_get_error(obj: *mut LeanObject) -> *mut LeanObject {
    debug_assert!(lean_io_result_is_error(obj));
    lean_ctor_get(obj, 0)
}

#[inline]
pub(crate) unsafe fn lean_io_result_take_value(obj: *mut LeanObject) -> *mut LeanObject {
    debug_assert!(lean_io_result_is_ok(obj));
    let v = lean_ctor_get(obj, 0);
    lean_inc(v);
    lean_dec(obj);
    v
}

#[inline]
pub(crate) unsafe fn lean_io_result_show_error(r: *mut LeanObject) {
    let err = lean_io_result_get_error(r);
    lean_inc(err);
    let msg = lean_io_error_to_string(err);
    let text = CStr::from_ptr(lean_string_cstr(msg));
    eprintln!("uncaught exception: {}", text.to_string_lossy());
    lean_dec(msg);
    lean_dec(err);
}

pub unsafe fn mk_embedded_nul_error(str: *mut LeanObject) -> *mut LeanObject {
    lean_inc(str);
    let details = lean_mk_string(c"string contains NUL bytes".as_ptr());
    lean_io_result_mk_error(lean_mk_io_error_invalid_argument_file(
        str,
        libc::EINVAL as u32,
        details,
    ))
}

#[inline]
pub(crate) unsafe fn lean_io_prim_handle_is_tty(h: *mut LeanObject) -> u8 {
    let fp = lean_runtime_get_external_data(h).cast::<libc::FILE>();
    #[cfg(target_os = "windows")]
    {
        use windows_sys::Win32::System::Console::GetConsoleMode;

        let fd = libc::_fileno(fp);
        let handle = libc::_get_osfhandle(fd) as isize;
        let mut mode = 0u32;
        GetConsoleMode(handle, &mut mode) as u8
    }
    #[cfg(not(target_os = "windows"))]
    {
        libc::isatty(libc::fileno(fp)) as u8
    }
}

#[inline]
pub(crate) unsafe fn lean_io_prim_handle_is_eof(h: *mut LeanObject) -> u8 {
    let fp = lean_runtime_get_external_data(h).cast::<libc::FILE>();
    (libc::feof(fp) != 0) as u8
}

unsafe fn lean_runtime_errno() -> c_int {
    #[cfg(target_os = "windows")]
    {
        *libc::_errno()
    }
    #[cfg(not(target_os = "windows"))]
    {
        *libc::__errno_location()
    }
}

#[inline]
pub(crate) unsafe fn lean_io_prim_handle_flush(h: *mut LeanObject) -> *mut LeanObject {
    let fp = lean_runtime_get_external_data(h).cast::<libc::FILE>();
    if libc::fflush(fp) == 0 {
        lean_io_result_mk_ok(lean_box(0))
    } else {
        lean_io_result_mk_error(lean_decode_io_error(
            lean_runtime_errno(),
            core::ptr::null_mut(),
        ))
    }
}

#[inline]
pub(crate) unsafe fn lean_io_prim_handle_rewind(h: *mut LeanObject) -> *mut LeanObject {
    let fp = lean_runtime_get_external_data(h).cast::<libc::FILE>();
    if libc::fseek(fp, 0, libc::SEEK_SET) == 0 {
        lean_io_result_mk_ok(lean_box(0))
    } else {
        lean_io_result_mk_error(lean_decode_io_error(
            lean_runtime_errno(),
            core::ptr::null_mut(),
        ))
    }
}

#[inline]
pub(crate) unsafe fn lean_io_prim_handle_truncate(h: *mut LeanObject) -> *mut LeanObject {
    let fp = lean_runtime_get_external_data(h).cast::<libc::FILE>();
    #[cfg(target_os = "windows")]
    {
        if libc::_chsize_s(libc::_fileno(fp), libc::_ftelli64(fp)) == 0 {
            lean_io_result_mk_ok(lean_box(0))
        } else {
            lean_io_result_mk_error(lean_decode_io_error(
                lean_runtime_errno(),
                core::ptr::null_mut(),
            ))
        }
    }
    #[cfg(not(target_os = "windows"))]
    {
        if libc::ftruncate(libc::fileno(fp), libc::ftello(fp)) == 0 {
            lean_io_result_mk_ok(lean_box(0))
        } else {
            lean_io_result_mk_error(lean_decode_io_error(
                lean_runtime_errno(),
                core::ptr::null_mut(),
            ))
        }
    }
}

#[inline]
pub(crate) unsafe fn lean_io_prim_handle_read(
    h: *mut LeanObject,
    nbytes: Size,
) -> *mut LeanObject {
    let fp = lean_runtime_get_external_data(h).cast::<libc::FILE>();
    if lean_alloc_sarray_would_overflow(1, nbytes) {
        return lean_io_result_mk_error(lean_decode_io_error(libc::ENOMEM, core::ptr::null_mut()));
    }

    let res = lean_alloc_sarray(1, 0, nbytes);
    if nbytes == 0 {
        return lean_io_result_mk_ok(res);
    }

    let n = libc::fread(
        lean_sarray_cptr(res) as *mut core::ffi::c_void,
        1,
        nbytes,
        fp,
    );
    if n > 0 {
        lean_sarray_set_size(res, n);
        lean_io_result_mk_ok(res)
    } else if libc::feof(fp) != 0 {
        libc::clearerr(fp);
        lean_sarray_set_size(res, n);
        lean_io_result_mk_ok(res)
    } else {
        lean_dec(res);
        lean_io_result_mk_error(lean_decode_io_error(
            lean_runtime_errno(),
            core::ptr::null_mut(),
        ))
    }
}

#[inline]
pub(crate) unsafe fn lean_io_prim_handle_write(
    h: *mut LeanObject,
    buf: *mut LeanObject,
) -> *mut LeanObject {
    let fp = lean_runtime_get_external_data(h).cast::<libc::FILE>();
    let n = lean_sarray_size(buf);
    let m = libc::fwrite(lean_sarray_cptr(buf).cast(), 1, n, fp);
    if m == n {
        lean_io_result_mk_ok(lean_box(0))
    } else {
        lean_io_result_mk_error(lean_decode_io_error(
            lean_runtime_errno(),
            core::ptr::null_mut(),
        ))
    }
}

#[inline]
pub(crate) unsafe fn lean_io_prim_handle_get_line(h: *mut LeanObject) -> *mut LeanObject {
    let fp = lean_runtime_get_external_data(h).cast::<libc::FILE>();
    let mut result = Vec::<u8>::new();
    #[cfg(windows)]
    unsafe {
        extern "C" {
            fn _lock_file(fp: *mut libc::FILE);
            fn _unlock_file(fp: *mut libc::FILE);
            fn _fgetc_nolock(fp: *mut libc::FILE) -> libc::c_int;
        }
        _lock_file(fp);
        loop {
            let c = _fgetc_nolock(fp);
            if c == libc::EOF {
                break;
            }
            result.push(c as u8);
            if c == b'\n' as i32 {
                break;
            }
        }
        _unlock_file(fp);
    }
    #[cfg(not(windows))]
    unsafe {
        extern "C" {
            fn flockfile(fp: *mut libc::FILE);
            fn funlockfile(fp: *mut libc::FILE);
            fn getc_unlocked(fp: *mut libc::FILE) -> libc::c_int;
        }
        flockfile(fp);
        loop {
            let c = getc_unlocked(fp);
            if c == libc::EOF {
                break;
            }
            result.push(c as u8);
            if c == b'\n' as i32 {
                break;
            }
        }
        funlockfile(fp);
    }

    if libc::ferror(fp) != 0 {
        lean_io_result_mk_error(lean_decode_io_error(
            lean_runtime_errno(),
            core::ptr::null_mut(),
        ))
    } else {
        if libc::feof(fp) != 0 {
            libc::clearerr(fp);
        }
        let s = lean_mk_string_from_bytes(result.as_ptr() as *const c_char, result.len());
        lean_io_result_mk_ok(s)
    }
}

#[inline]
pub(crate) unsafe fn lean_io_prim_handle_put_str(
    h: *mut LeanObject,
    s: *mut LeanObject,
) -> *mut LeanObject {
    let fp = lean_runtime_get_external_data(h).cast::<libc::FILE>();
    let n = lean_string_size(s) - 1;
    let m = libc::fwrite(lean_string_cstr(s).cast::<core::ffi::c_void>(), 1, n, fp);
    if m == n {
        lean_io_result_mk_ok(lean_box(0))
    } else {
        lean_io_result_mk_error(lean_decode_io_error(
            lean_runtime_errno(),
            core::ptr::null_mut(),
        ))
    }
}

#[inline]
pub(crate) unsafe fn lean_io_prim_handle_mk(
    filename: *mut LeanObject,
    mode: u8,
) -> *mut LeanObject {
    let fname = lean_string_cstr(filename);
    if libc::strlen(fname) != lean_string_size(filename) - 1 {
        return mk_embedded_nul_error(filename);
    }

    let mut flags: libc::c_int = 0;
    #[cfg(target_os = "windows")]
    {
        const O_BINARY: libc::c_int = 0x8000;
        const O_NOINHERIT: libc::c_int = 0x0080;
        flags |= O_BINARY | O_NOINHERIT;
    }
    #[cfg(not(target_os = "windows"))]
    {
        flags |= libc::O_CLOEXEC;
    }

    flags |= match mode {
        0 => libc::O_RDONLY,
        1 => libc::O_WRONLY | libc::O_CREAT | libc::O_TRUNC,
        2 => libc::O_WRONLY | libc::O_CREAT | libc::O_TRUNC | libc::O_EXCL,
        3 => libc::O_RDWR,
        4 => libc::O_WRONLY | libc::O_CREAT | libc::O_APPEND,
        _ => libc::O_RDONLY,
    };

    let fd = libc::open(fname, flags, 0o666);
    if fd == -1 {
        return lean_io_result_mk_error(lean_decode_io_error(lean_runtime_errno(), filename));
    }

    let fp_mode: *const libc::c_char = match mode {
        0 => c"r".as_ptr(),
        1 | 2 => c"w".as_ptr(),
        3 => c"r+".as_ptr(),
        4 => c"a".as_ptr(),
        _ => c"r".as_ptr(),
    };

    let fp = libc::fdopen(fd, fp_mode);
    if fp.is_null() {
        lean_io_result_mk_error(lean_decode_io_error(lean_runtime_errno(), filename))
    } else {
        lean_io_result_mk_ok(runtime_io_stream_impl::io_wrap_handle(fp))
    }
}

#[inline]
pub(crate) unsafe fn lean_windows_get_next_transition(
    timezone_str: *mut LeanObject,
    tm_obj: u64,
    default_time: u8,
) -> *mut LeanObject {
    #[cfg(target_os = "windows")]
    {
        type UErrorCode = c_int;
        type UDate = f64;
        type UChar = u16;
        type UBool = i8;

        const UCAL_GREGORIAN: c_int = 2;
        const UCAL_TZ_TRANSITION_NEXT: c_int = 1;
        const UCAL_DST_OFFSET: c_int = 16;
        const UCAL_ZONE_OFFSET: c_int = 15;
        const UCAL_STANDARD: c_int = 0;
        const UCAL_DST: c_int = 2;
        const UCAL_SHORT_STANDARD: c_int = 1;
        const UCAL_SHORT_DST: c_int = 3;

        extern "C" {
            fn u_strFromUTF8(
                dest: *mut UChar,
                dest_capacity: c_int,
                p_dest_length: *mut c_int,
                src: *const c_char,
                src_length: c_int,
                p_error_code: *mut UErrorCode,
            ) -> *mut UChar;
            fn u_strToUTF8(
                dest: *mut c_char,
                dest_capacity: c_int,
                p_dest_length: *mut c_int,
                src: *const UChar,
                src_length: c_int,
                p_error_code: *mut UErrorCode,
            ) -> *mut c_char;
            fn ucal_open(
                zone_id: *const UChar,
                len: c_int,
                locale: *const c_char,
                typ: c_int,
                ec: *mut UErrorCode,
            ) -> *mut c_void;
            fn ucal_close(cal: *mut c_void);
            fn ucal_setMillis(cal: *mut c_void, date: UDate, ec: *mut UErrorCode);
            fn ucal_getTimeZoneTransitionDate(
                cal: *const c_void,
                direction: c_int,
                transition_time: *mut UDate,
                ec: *mut UErrorCode,
            ) -> UBool;
            fn ucal_get(cal: *const c_void, field: c_int, ec: *mut UErrorCode) -> c_int;
            fn ucal_getTimeZoneDisplayName(
                cal: *const c_void,
                typ: c_int,
                locale: *const c_char,
                result: *mut UChar,
                result_length: c_int,
                ec: *mut UErrorCode,
            ) -> c_int;
        }

        #[inline]
        unsafe fn icu_failed(status: UErrorCode) -> bool {
            status < 0
        }

        let mut status: UErrorCode = 0;
        let dst_name_id = lean_string_cstr(timezone_str);
        let mut tz_id = [0u16; 256];
        u_strFromUTF8(
            tz_id.as_mut_ptr(),
            tz_id.len() as c_int,
            ptr::null_mut(),
            dst_name_id,
            (lean_string_size(timezone_str) - 1) as c_int,
            &mut status,
        );
        if icu_failed(status) {
            return lean_io_result_mk_error(lean_mk_io_error_invalid_argument(
                libc::EINVAL as u32,
                lean_mk_string(c"failed to read identifier".as_ptr()),
            ));
        }

        let cal = ucal_open(tz_id.as_ptr(), -1, ptr::null(), UCAL_GREGORIAN, &mut status);
        if cal.is_null() || icu_failed(status) {
            if !cal.is_null() {
                ucal_close(cal);
            }
            return lean_io_result_mk_error(lean_mk_io_error_invalid_argument(
                libc::EINVAL as u32,
                lean_mk_string(c"failed to open calendar".as_ptr()),
            ));
        }

        let mut tm: i64 = 0;
        if default_time == 0 {
            let timestamp_secs = tm_obj as i64;
            ucal_setMillis(cal, (timestamp_secs * 1000) as UDate, &mut status);
            if icu_failed(status) {
                ucal_close(cal);
                return lean_io_result_mk_error(lean_mk_io_error_invalid_argument(
                    libc::EINVAL as u32,
                    lean_mk_string(c"failed to set calendar time".as_ptr()),
                ));
            }

            let mut next_transition: UDate = 0.0;
            if ucal_getTimeZoneTransitionDate(
                cal,
                UCAL_TZ_TRANSITION_NEXT,
                &mut next_transition,
                &mut status,
            ) == 0
            {
                ucal_close(cal);
                return lean_io_result_mk_ok(lean_box(0));
            }
            if icu_failed(status) {
                ucal_close(cal);
                return lean_io_result_mk_error(lean_mk_io_error_invalid_argument(
                    libc::EINVAL as u32,
                    lean_mk_string(c"failed to get next transition".as_ptr()),
                ));
            }
            tm = (next_transition / 1000.0) as i64;
        }

        let dst_offset = ucal_get(cal, UCAL_DST_OFFSET, &mut status);
        if icu_failed(status) {
            ucal_close(cal);
            return lean_io_result_mk_error(lean_mk_io_error_invalid_argument(
                libc::EINVAL as u32,
                lean_mk_string(c"failed to get dst_offset".as_ptr()),
            ));
        }
        let is_dst = dst_offset != 0;

        let mut tz_id_name = [0u16; 32];
        let tz_id_len = ucal_getTimeZoneDisplayName(
            cal,
            if is_dst { UCAL_DST } else { UCAL_STANDARD },
            c"en_US".as_ptr(),
            tz_id_name.as_mut_ptr(),
            tz_id_name.len() as c_int,
            &mut status,
        );
        if icu_failed(status) {
            ucal_close(cal);
            return lean_io_result_mk_error(lean_mk_io_error_invalid_argument(
                libc::EINVAL as u32,
                lean_mk_string(c"failed to timezone identifier".as_ptr()),
            ));
        }
        let mut dst_name = [0u8; 256];
        let mut dst_name_len: c_int = 0;
        u_strToUTF8(
            dst_name.as_mut_ptr().cast(),
            dst_name.len() as c_int,
            &mut dst_name_len,
            tz_id_name.as_ptr(),
            tz_id_len,
            &mut status,
        );
        if icu_failed(status) {
            ucal_close(cal);
            return lean_io_result_mk_error(lean_mk_io_error_invalid_argument(
                libc::EINVAL as u32,
                lean_mk_string(c"failed to convert DST name to UTF-8".as_ptr()),
            ));
        }

        let mut display_name = [0u16; 32];
        let display_name_len = ucal_getTimeZoneDisplayName(
            cal,
            if is_dst {
                UCAL_SHORT_DST
            } else {
                UCAL_SHORT_STANDARD
            },
            c"en_US".as_ptr(),
            display_name.as_mut_ptr(),
            display_name.len() as c_int,
            &mut status,
        );
        if icu_failed(status) {
            ucal_close(cal);
            return lean_io_result_mk_error(lean_mk_io_error_invalid_argument(
                libc::EINVAL as u32,
                lean_mk_string(c"failed to read abbreaviation".as_ptr()),
            ));
        }
        let mut display_name_str = [0u8; 256];
        let mut display_name_str_len: c_int = 0;
        u_strToUTF8(
            display_name_str.as_mut_ptr().cast(),
            display_name_str.len() as c_int,
            &mut display_name_str_len,
            display_name.as_ptr(),
            display_name_len,
            &mut status,
        );
        if icu_failed(status) {
            ucal_close(cal);
            return lean_io_result_mk_error(lean_mk_io_error_invalid_argument(
                libc::EINVAL as u32,
                lean_mk_string(c"failed to get abbreviation to cstr".as_ptr()),
            ));
        }

        let zone_offset = ucal_get(cal, UCAL_ZONE_OFFSET, &mut status) + dst_offset;
        if icu_failed(status) {
            ucal_close(cal);
            return lean_io_result_mk_error(lean_mk_io_error_invalid_argument(
                libc::EINVAL as u32,
                lean_mk_string(c"failed to get zone_offset".as_ptr()),
            ));
        }
        ucal_close(cal);

        let offset_seconds = zone_offset / 1000;
        let lean_tz = lean_alloc_ctor(0, 3, 1);
        lean_ctor_set(lean_tz, 0, lean_int64_to_int_rust(offset_seconds as i64));
        lean_ctor_set(
            lean_tz,
            1,
            lean_mk_string_from_bytes_unchecked(dst_name.as_ptr().cast(), dst_name_len as usize),
        );
        lean_ctor_set(
            lean_tz,
            2,
            lean_mk_string_from_bytes_unchecked(
                display_name_str.as_ptr().cast(),
                display_name_str_len as usize,
            ),
        );
        lean_ctor_set_uint8(
            lean_tz,
            core::mem::size_of::<*mut c_void>() * 3,
            is_dst as u8,
        );

        let lean_pair = lean_alloc_ctor(0, 2, 0);
        lean_ctor_set(lean_pair, 0, lean_box_uint64(tm as u64));
        lean_ctor_set(lean_pair, 1, lean_tz);
        lean_io_result_mk_ok(mk_option_some(lean_pair))
    }
    #[cfg(not(target_os = "windows"))]
    {
        let _ = (timezone_str, tm_obj, default_time);
        lean_io_result_mk_error(lean_mk_io_error_invalid_argument(
            libc::EINVAL as u32,
            lean_mk_string(c"failed to get timezone, its windows only.".as_ptr()),
        ))
    }
}

#[inline]
pub(crate) unsafe fn lean_get_windows_local_timezone_id_at(tm_obj: u64) -> *mut LeanObject {
    #[cfg(target_os = "windows")]
    {
        type UErrorCode = c_int;
        type UChar = u16;
        type UDate = f64;

        const UCAL_GREGORIAN: c_int = 2;

        extern "C" {
            fn ucal_open(
                zone_id: *const UChar,
                len: c_int,
                locale: *const c_char,
                typ: c_int,
                ec: *mut UErrorCode,
            ) -> *mut c_void;
            fn ucal_close(cal: *mut c_void);
            fn ucal_setMillis(cal: *mut c_void, date: UDate, ec: *mut UErrorCode);
            fn ucal_getTimeZoneID(
                cal: *const c_void,
                result: *mut UChar,
                result_length: c_int,
                ec: *mut UErrorCode,
            ) -> c_int;
            fn u_strToUTF8(
                dest: *mut c_char,
                dest_capacity: c_int,
                p_dest_length: *mut c_int,
                src: *const UChar,
                src_length: c_int,
                p_error_code: *mut UErrorCode,
            ) -> *mut c_char;
        }

        #[inline]
        unsafe fn icu_failed(status: UErrorCode) -> bool {
            status < 0
        }

        let mut status: UErrorCode = 0;
        let cal = ucal_open(ptr::null(), -1, ptr::null(), UCAL_GREGORIAN, &mut status);
        if cal.is_null() || icu_failed(status) {
            if !cal.is_null() {
                ucal_close(cal);
            }
            return lean_io_result_mk_error(lean_mk_io_error_invalid_argument(
                libc::EINVAL as u32,
                lean_mk_string(c"failed to open calendar".as_ptr()),
            ));
        }

        ucal_setMillis(cal, (tm_obj as i64 * 1000) as UDate, &mut status);
        if icu_failed(status) {
            ucal_close(cal);
            return lean_io_result_mk_error(lean_mk_io_error_invalid_argument(
                libc::EINVAL as u32,
                lean_mk_string(c"failed to set calendar time".as_ptr()),
            ));
        }

        let mut tz_id = [0u16; 256];
        let tz_id_len =
            ucal_getTimeZoneID(cal, tz_id.as_mut_ptr(), tz_id.len() as c_int, &mut status);
        ucal_close(cal);
        if icu_failed(status) {
            return lean_io_result_mk_error(lean_mk_io_error_invalid_argument(
                libc::EINVAL as u32,
                lean_mk_string(c"failed to get timezone ID".as_ptr()),
            ));
        }

        let mut tz_id_str = [0u8; 256];
        let mut tz_id_str_len: c_int = 0;
        u_strToUTF8(
            tz_id_str.as_mut_ptr().cast(),
            tz_id_str.len() as c_int,
            &mut tz_id_str_len,
            tz_id.as_ptr(),
            tz_id_len,
            &mut status,
        );
        if icu_failed(status) {
            return lean_io_result_mk_error(lean_mk_io_error_invalid_argument(
                libc::EINVAL as u32,
                lean_mk_string(c"failed to convert timezone ID to UTF-8".as_ptr()),
            ));
        }

        lean_io_result_mk_ok(lean_mk_ascii_string_unchecked(
            core::str::from_utf8_unchecked(core::slice::from_raw_parts(
                tz_id_str.as_ptr(),
                tz_id_str_len as usize,
            )),
        ))
    }
    #[cfg(not(target_os = "windows"))]
    {
        let _ = tm_obj;
        lean_io_result_mk_error(lean_mk_io_error_invalid_argument(
            libc::EINVAL as u32,
            lean_mk_string(c"timezone retrieval is Windows-only".as_ptr()),
        ))
    }
}

#[inline]
pub(crate) unsafe fn lean_sarray_cptr(obj: *mut LeanObject) -> *const u8 {
    (obj as *const u8).add(24)
}

#[inline]
pub unsafe fn lean_string_cstr(obj: *mut LeanObject) -> *const c_char {
    (obj as *const u8).add(32) as *const c_char
}

#[inline]
pub unsafe fn lean_box(value: Size) -> *mut LeanObject {
    ((value << 1) | 1) as *mut LeanObject
}

fn env_flag(value: &str) -> u8 {
    if value.as_bytes() == b"1" {
        1
    } else {
        0
    }
}

unsafe fn mk_name(text: &str) -> LeanName {
    let c_text = std::ffi::CString::new(text).expect("option names never contain NUL");
    let raw_text = lean_mk_string(c_text.as_ptr());
    let raw_name = lean_name_mk_string(lean_box(0), raw_text);
    LeanName { obj: raw_name }
}

unsafe fn mk_name_path(components: &[&str]) -> LeanName {
    let mut name = mk_name(components[0]);
    for component in &components[1..] {
        let c_text = std::ffi::CString::new(*component).expect("option names never contain NUL");
        let raw_text = lean_mk_string(c_text.as_ptr());
        let raw_name = lean_name_mk_string(name.obj, raw_text);
        name = LeanName { obj: raw_name };
    }
    name
}

pub mod library_constants;
pub(crate) use library_constants::*;
pub mod library_util;
pub mod library_dynlib;
pub(crate) use library_dynlib::*;
pub mod runtime_apply;
pub mod runtime_debug;
pub(crate) use runtime_debug::*;
pub mod runtime_dns;
pub mod runtime_event_loop;
pub(crate) use runtime_event_loop::*;
pub mod runtime_libuv;
pub(crate) use runtime_libuv::*;
pub mod runtime_mpn;
pub mod runtime_mutex;
pub(crate) use runtime_mutex::*;
pub mod runtime_net_addr;
pub(crate) use runtime_net_addr::*;
pub mod runtime_signal;
pub mod runtime_process;
pub mod runtime_stack_overflow;
pub(crate) use runtime_stack_overflow::*;
pub mod runtime_stack_info;
pub(crate) use runtime_stack_info::*;
pub mod runtime_exception;
pub(crate) use runtime_exception::*;
pub mod runtime_interrupt;
pub(crate) use runtime_interrupt::*;
pub mod runtime_system;
pub mod runtime_tcp;
pub mod runtime_timer;
pub mod runtime_udp;
pub mod runtime_alloc;
pub mod runtime_memory;
pub mod runtime_object_panic;
pub mod runtime_object_size;
pub mod runtime_object_array;
pub mod runtime_object_rc;
pub mod runtime_object_task;
pub(crate) use runtime_object_task::*;
pub mod library_formatter;
pub mod runtime_io_ref;
pub mod runtime_io_fs;
pub mod runtime_io_error;
pub mod runtime_io_handle;
pub mod runtime_io_task;
pub mod runtime_io_stream;
pub mod runtime_sharecommon;
pub mod runtime_thread;
pub(crate) use runtime_thread::*;
pub mod runtime_once;
pub mod runtime_float;
pub(crate) use runtime_float::*;
pub mod runtime_mpz;
pub mod runtime_object_nat_int;
pub mod runtime_object_string;
pub mod runtime_object_name;
pub mod kernel_abstract;
pub mod library_expr_lt;
pub mod library_time_task;
pub mod library_print;
pub mod runtime_compact;
pub(crate) use runtime_compact::*;
pub mod runtime_compact_writer;
pub mod kernel_replace_fn;
pub mod kernel_expr_eq_fn;
pub mod kernel_for_each_fn;
pub mod kernel_level;
pub mod kernel_expr;
pub mod kernel_equiv_manager;
pub mod kernel_instantiate;
pub mod kernel_local_ctx;
pub mod kernel_declaration;
pub mod kernel_environment;
pub mod kernel_quot;
pub mod kernel_type_checker;
pub(crate) use kernel_type_checker::*;
pub mod library_instantiate_mvars;
pub mod library_module;
pub mod library_elab_environment;
pub mod library_ir_interpreter;
pub mod library_llvm;
pub mod kernel_num;
pub mod kernel_trace;

pub mod generated_abi {
    pub use crate::*;

    #[repr(C)]
    pub struct LeanCtorObject<const N: usize> {
        pub m_header: LeanObject,
        pub m_objs: [*mut LeanObject; N],
    }

    #[repr(C)]
    pub struct LeanStringObject<const N: usize> {
        pub m_header: LeanObject,
        pub m_size: usize,
        pub m_capacity: usize,
        pub m_length: usize,
        pub m_data: [core::ffi::c_char; N],
    }

    #[repr(C)]
    pub struct LeanClosureObject<const N: usize> {
        pub m_header: LeanObject,
        pub m_fun: *const core::ffi::c_void,
        pub m_arity: u16,
        pub m_num_fixed: u16,
        pub m_objs: [*mut LeanObject; N],
    }

    #[repr(C)]
    pub struct LeanArrayObject<const N: usize> {
        pub m_header: LeanObject,
        pub m_size: usize,
        pub m_capacity: usize,
        pub m_data: [*mut LeanObject; N],
    }

    #[repr(C)]
    pub struct LeanScalarArrayObject<const N: usize> {
        pub m_header: LeanObject,
        pub m_size: usize,
        pub m_capacity: usize,
        pub m_data: [u8; N],
    }
}

pub(crate) use library_ir_interpreter::library_ir_interpreter_impl::finalize_ir_interpreter;
pub(crate) use kernel_level::kernel_level_impl::finalize_level;
pub(crate) use library_time_task::library_time_task_impl::finalize_time_task;
pub(crate) use runtime_io_stream::runtime_io_stream_impl::initialize_io;
pub(crate) use kernel_level::kernel_level_impl::initialize_level;
pub(crate) use runtime_object_rc::runtime_object_rc_impl::lean_alloc_object;
pub(crate) use runtime_object_array::runtime_object_array_impl::lean_array_push;
pub(crate) use runtime_object_rc::runtime_object_rc_impl::lean_dec_ref_cold;
pub(crate) use runtime_io_error::runtime_io_error_impl::lean_decode_io_error;
pub(crate) use runtime_io_error::runtime_io_error_impl::lean_decode_uv_error;
pub(crate) use runtime_object_task::runtime_object_task_impl::lean_io_promise_new;
pub(crate) use runtime_object_task::runtime_object_task_impl::lean_io_promise_resolve;
pub(crate) use runtime_object_rc::runtime_object_rc_impl::lean_mark_mt;
pub(crate) use runtime_object_rc::runtime_object_rc_impl::lean_mark_persistent;
pub use runtime_object_string::runtime_object_string_impl::lean_mk_string;
pub(crate) use runtime_object_string::runtime_object_string_impl::lean_mk_string_from_bytes;
pub(crate) use runtime_apply::{lean_alloc_closure, lean_apply_1, lean_apply_2};
pub(crate) use runtime_object_task::lean_task_get;
pub(crate) use runtime_alloc::{lean_get_num_heartbeats, lean_set_heartbeats};

pub(crate) use runtime_object_panic::runtime_object_panic_impl;
pub(crate) use runtime_io_stream::runtime_io_stream_impl;
pub(crate) use runtime_object_string::runtime_object_string_impl;
pub(crate) use runtime_object_name::runtime_object_name_impl;
pub(crate) use runtime_alloc::runtime_alloc_impl;
pub(crate) use runtime_object_array::runtime_object_array_impl;
pub(crate) use runtime_object_size::runtime_object_size_impl;
pub(crate) use runtime_apply::runtime_apply_impl;
pub(crate) use runtime_object_rc::runtime_object_rc_impl;
pub(crate) use runtime_object_nat_int::runtime_object_nat_int_impl;




pub unsafe fn lean_name_eq_export(n1: *mut LeanObject, n2: *mut LeanObject) -> u8 {
    runtime_object_name_impl::lean_name_eq(n1, n2)
}

/// cbindgen:field-names=[m_header, m_class, m_data]
#[repr(C)]
pub struct LeanExternalObject {
    pub(crate) header: LeanObject,
    pub(crate) class: *mut LeanExternalClass,
    pub(crate) data: *mut c_void,
}

static EXTERNAL_CLASSES: std::sync::Mutex<Vec<usize>> = std::sync::Mutex::new(Vec::new());

unsafe fn lean_external_noop_finalize(_: *mut c_void) {}

unsafe fn lean_external_noop_foreach(_: *mut c_void, _: *mut LeanObject) {}

#[inline]
pub(crate) unsafe fn lean_register_external_class(
    finalize: Option<LeanExternalFinalizeProc>,
    foreach: Option<LeanExternalForeachProc>,
) -> *mut LeanExternalClass {
    let class = Box::into_raw(Box::new(LeanExternalClass {
        finalize: finalize.unwrap_or(lean_external_noop_finalize),
        foreach: foreach.unwrap_or(lean_external_noop_foreach),
    }));
    EXTERNAL_CLASSES.lock().unwrap().push(class as usize);
    class
}

#[inline]
pub(crate) unsafe fn lean_finalize_external_classes() {
    let mut classes = EXTERNAL_CLASSES.lock().unwrap();
    for class in classes.drain(..) {
        drop(Box::from_raw(class as *mut LeanExternalClass));
    }
}

#[inline]
pub(crate) unsafe fn lean_runtime_alloc_external(
    class: *mut LeanExternalClass,
    data: *mut c_void,
) -> *mut LeanObject {
    const LEAN_EXTERNAL_TAG: u8 = 254;
    let obj = runtime_object_rc_impl::lean_alloc_small_object(core::mem::size_of::<
        LeanExternalObject,
    >()) as *mut LeanExternalObject;
    (*obj).header.rc = 1;
    (*obj).header.other = 0;
    (*obj).header.tag = LEAN_EXTERNAL_TAG;
    (*obj).class = class;
    (*obj).data = data;
    obj as *mut LeanObject
}

#[inline]
pub(crate) unsafe fn lean_runtime_get_external_data(obj: *mut LeanObject) -> *mut c_void {
    (*(obj as *mut LeanExternalObject)).data
}

#[inline]
pub(crate) unsafe fn lean_alloc_external(
    class: *mut LeanExternalClass,
    data: *mut c_void,
) -> *mut LeanObject {
    lean_runtime_alloc_external(class, data)
}

#[inline]
pub(crate) unsafe fn lean_get_external_class(obj: *mut LeanObject) -> *mut LeanExternalClass {
    (*(obj as *mut LeanExternalObject)).class
}

#[inline]
pub(crate) unsafe fn lean_get_external_data(obj: *mut LeanObject) -> *mut c_void {
    lean_runtime_get_external_data(obj)
}

#[inline]
pub(crate) unsafe fn lean_set_external_data(
    obj: *mut LeanObject,
    data: *mut c_void,
) -> *mut LeanObject {
    if (*obj).rc == 1 {
        (*(obj as *mut LeanExternalObject)).data = data;
        obj
    } else {
        let new_obj = lean_alloc_external(lean_get_external_class(obj), data);
        lean_dec_ref(obj);
        new_obj
    }
}

#[inline]
pub(crate) fn lean_internal_get_hardware_concurrency(_: *mut LeanObject) -> u32 {
    std::thread::available_parallelism()
        .map(|count| count.get() as u32)
        .unwrap_or(1)
}

#[inline]
pub(crate) fn lean_io_mk_world() -> *mut LeanObject {
    unsafe { lean_box(0) }
}

#[inline]
pub(crate) unsafe fn lean_void_mk(obj: *mut LeanObject) -> *mut LeanObject {
    lean_dec(obj);
    lean_box(0)
}

#[inline]
pub(crate) unsafe fn lean_unsigned_to_nat(value: c_uint) -> *mut LeanObject {
    lean_usize_to_nat(value as usize)
}

#[inline]
pub(crate) unsafe fn lean_nat_succ(value: *mut LeanObject) -> *mut LeanObject {
    if lean_is_scalar(value) {
        lean_usize_to_nat(lean_unbox(value).wrapping_add(1))
    } else {
        runtime_object_nat_int_impl::lean_nat_big_succ(value)
    }
}

#[inline]
pub(crate) unsafe fn lean_int_to_int(value: c_int) -> *mut LeanObject {
    // Original: lean_box((unsigned)(n)) unconditionally on 64-bit (all i32 are small ints).
    // On 32-bit only values in LEAN_MIN_SMALL_INT..=LEAN_MAX_SMALL_INT are small.
    // Must cast through u32 to match C `(unsigned)(n)`.
    #[cfg(target_pointer_width = "64")]
    {
        lean_box(value as u32 as usize)
    }
    #[cfg(not(target_pointer_width = "64"))]
    {
        const LEAN_MAX_SMALL_INT: i32 = i32::MAX >> 1;
        const LEAN_MIN_SMALL_INT: i32 = i32::MIN >> 1;
        if value >= LEAN_MIN_SMALL_INT && value <= LEAN_MAX_SMALL_INT {
            lean_box(value as u32 as usize)
        } else {
            runtime_object_nat_int_impl::lean_big_int_to_int(value)
        }
    }
}

#[inline]
pub(crate) unsafe fn lean_int64_to_int(value: i64) -> *mut LeanObject {
    // Original: lean_box((unsigned)(int)n) when LEAN_MIN_SMALL_INT <= n <= LEAN_MAX_SMALL_INT
    // On 64-bit: LEAN_MAX_SMALL_INT = INT_MAX, LEAN_MIN_SMALL_INT = INT_MIN (full i32 range)
    // On 32-bit: LEAN_MAX_SMALL_INT = INT_MAX>>1, LEAN_MIN_SMALL_INT = INT_MIN>>1
    #[cfg(target_pointer_width = "64")]
    {
        const LEAN_MAX_SMALL_INT: i64 = i32::MAX as i64;
        const LEAN_MIN_SMALL_INT: i64 = i32::MIN as i64;
        if value >= LEAN_MIN_SMALL_INT && value <= LEAN_MAX_SMALL_INT {
            // Match C: lean_box((unsigned)(int)n) — truncate to i32 then reinterpret as u32
            lean_box(value as i32 as u32 as usize)
        } else {
            runtime_object_nat_int_impl::lean_big_int64_to_int(value)
        }
    }
    #[cfg(not(target_pointer_width = "64"))]
    {
        const LEAN_MAX_SMALL_INT: i64 = (i32::MAX >> 1) as i64;
        const LEAN_MIN_SMALL_INT: i64 = (i32::MIN >> 1) as i64;
        if value >= LEAN_MIN_SMALL_INT && value <= LEAN_MAX_SMALL_INT {
            lean_box(value as i32 as u32 as usize)
        } else {
            runtime_object_nat_int_impl::lean_big_int64_to_int(value)
        }
    }
}

#[inline]
pub(crate) unsafe fn lean_scalar_to_int64(value: *mut LeanObject) -> i64 {
    debug_assert!(lean_is_scalar(value));
    #[cfg(target_pointer_width = "64")]
    {
        lean_unbox(value) as u32 as i32 as i64
    }
    #[cfg(not(target_pointer_width = "64"))]
    {
        ((value as usize) as i32) as i64 >> 1
    }
}

#[inline]
pub(crate) unsafe fn lean_scalar_to_int(value: *mut LeanObject) -> c_int {
    debug_assert!(lean_is_scalar(value));
    #[cfg(target_pointer_width = "64")]
    {
        lean_unbox(value) as u32 as i32
    }
    #[cfg(not(target_pointer_width = "64"))]
    {
        ((value as usize) as i32) >> 1
    }
}

#[inline]
pub(crate) unsafe fn lean_nat_to_int(value: *mut LeanObject) -> *mut LeanObject {
    // Original: if lean_is_scalar(a) { v = lean_unbox(a); if v <= LEAN_MAX_SMALL_INT return a; }
    // LEAN_MAX_SMALL_INT = INT_MAX on 64-bit, INT_MAX>>1 on 32-bit
    if lean_is_scalar(value) {
        let unboxed = lean_unbox(value);
        #[cfg(target_pointer_width = "64")]
        let max_small = i32::MAX as usize; // INT_MAX = 2147483647
        #[cfg(not(target_pointer_width = "64"))]
        let max_small = (i32::MAX >> 1) as usize; // INT_MAX>>1 = 1073741823
        if unboxed <= max_small {
            value
        } else {
            runtime_object_nat_int_impl::lean_big_size_t_to_int(unboxed)
        }
    } else {
        value
    }
}

#[inline]
pub(crate) unsafe fn lean_int_neg(value: *mut LeanObject) -> *mut LeanObject {
    if lean_is_scalar(value) {
        lean_int64_to_int(-lean_scalar_to_int64(value))
    } else {
        runtime_object_nat_int_impl::lean_int_big_neg(value)
    }
}

#[inline]
pub(crate) unsafe fn lean_int_neg_succ_of_nat(value: *mut LeanObject) -> *mut LeanObject {
    let succ = lean_nat_succ(value);
    lean_dec(value);
    let int_value = lean_nat_to_int(succ);
    let result = lean_int_neg(int_value);
    lean_dec(int_value);
    result
}

/// Int → Nat (absolute value).
/// Takes a *borrowed* Int, returns a *new owned* Nat.
/// Original C++:
///   if (lean_int_lt(i, lean_box(0))) return lean_int_to_nat(lean_int_neg(i));
///   else { lean_inc(i); return lean_int_to_nat(i); }
pub(crate) unsafe fn lean_nat_abs(i: *mut LeanObject) -> *mut LeanObject {
    // Check sign: negative if scalar < 0, or big MPZ with negative sign
    let is_negative = if lean_is_scalar(i) {
        lean_scalar_to_int(i) < 0
    } else {
        runtime_object_nat_int_impl::lean_int_big_lt(i, lean_box(0))
    };

    if is_negative {
        // lean_int_neg borrows i (b_lean_obj_arg) and returns a new owned negated Int.
        // lean_int_to_nat consumes (lean_obj_arg) that owned Int and returns an owned Nat.
        let negated = lean_int_neg(i);
        // lean_int_to_nat: scalar → pass through; big → clone mpz and lean_dec input
        if lean_is_scalar(negated) {
            negated // scalar identity: Nat and Int share scalar representation for small values
        } else {
            runtime_object_nat_int_impl::lean_big_int_to_nat(negated)
        }
    } else {
        // i is borrowed; inc to get an owned copy for lean_int_to_nat to consume
        lean_inc(i);
        // lean_int_to_nat: scalar → pass through; big → clone mpz and lean_dec input
        if lean_is_scalar(i) {
            i // scalar identity
        } else {
            runtime_object_nat_int_impl::lean_big_int_to_nat(i)
        }
    }
}

#[inline]
pub(crate) unsafe fn lean_int_add(a: *mut LeanObject, b: *mut LeanObject) -> *mut LeanObject {
    if lean_is_scalar(a) && lean_is_scalar(b) {
        lean_int64_to_int(lean_scalar_to_int64(a).wrapping_add(lean_scalar_to_int64(b)))
    } else {
        runtime_object_nat_int_impl::lean_int_big_add(a, b)
    }
}

#[inline]
pub(crate) unsafe fn lean_int_sub(a: *mut LeanObject, b: *mut LeanObject) -> *mut LeanObject {
    if lean_is_scalar(a) && lean_is_scalar(b) {
        lean_int64_to_int(lean_scalar_to_int64(a).wrapping_sub(lean_scalar_to_int64(b)))
    } else {
        runtime_object_nat_int_impl::lean_int_big_sub(a, b)
    }
}

#[inline]
pub(crate) unsafe fn lean_int_mul(a: *mut LeanObject, b: *mut LeanObject) -> *mut LeanObject {
    if lean_is_scalar(a) && lean_is_scalar(b) {
        lean_int64_to_int(lean_scalar_to_int64(a).wrapping_mul(lean_scalar_to_int64(b)))
    } else {
        runtime_object_nat_int_impl::lean_int_big_mul(a, b)
    }
}

#[inline]
pub(crate) unsafe fn lean_int_div(a: *mut LeanObject, b: *mut LeanObject) -> *mut LeanObject {
    if lean_is_scalar(a) && lean_is_scalar(b) {
        let v1 = lean_scalar_to_int64(a);
        let v2 = lean_scalar_to_int64(b);
        if v2 == 0 {
            lean_box(0)
        } else {
            lean_int64_to_int(v1 / v2)
        }
    } else {
        runtime_object_nat_int_impl::lean_int_big_div(a, b)
    }
}

#[inline]
pub(crate) unsafe fn lean_int_div_exact(a: *mut LeanObject, b: *mut LeanObject) -> *mut LeanObject {
    if lean_is_scalar(a) && lean_is_scalar(b) {
        let v1 = lean_scalar_to_int64(a);
        let v2 = lean_scalar_to_int64(b);
        if v2 == 0 {
            lean_box(0)
        } else {
            lean_int64_to_int(v1 / v2)
        }
    } else {
        runtime_object_nat_int_impl::lean_int_big_div_exact(a, b)
    }
}

#[inline]
pub(crate) unsafe fn lean_int_mod(a: *mut LeanObject, b: *mut LeanObject) -> *mut LeanObject {
    if lean_is_scalar(a) && lean_is_scalar(b) {
        let v1 = lean_scalar_to_int64(a);
        let v2 = lean_scalar_to_int64(b);
        if v2 == 0 {
            a
        } else {
            lean_int64_to_int(v1 % v2)
        }
    } else {
        runtime_object_nat_int_impl::lean_int_big_mod(a, b)
    }
}

#[inline]
pub(crate) unsafe fn lean_int_ediv(a: *mut LeanObject, b: *mut LeanObject) -> *mut LeanObject {
    if lean_is_scalar(a) && lean_is_scalar(b) {
        let n = lean_scalar_to_int64(a);
        let d = lean_scalar_to_int64(b);
        if d == 0 {
            lean_box(0)
        } else {
            let mut q = n / d;
            let r = n % d;
            if r < 0 {
                q = if d > 0 { q - 1 } else { q + 1 };
            }
            lean_int64_to_int(q)
        }
    } else {
        runtime_object_nat_int_impl::lean_int_big_ediv(a, b)
    }
}

#[inline]
pub(crate) unsafe fn lean_int_emod(a: *mut LeanObject, b: *mut LeanObject) -> *mut LeanObject {
    if lean_is_scalar(a) && lean_is_scalar(b) {
        let n = lean_scalar_to_int64(a);
        let d = lean_scalar_to_int64(b);
        if d == 0 {
            a
        } else {
            let mut r = n % d;
            if r < 0 {
                r = if d > 0 { r + d } else { r - d };
            }
            lean_int64_to_int(r)
        }
    } else {
        runtime_object_nat_int_impl::lean_int_big_emod(a, b)
    }
}

#[inline]
pub(crate) unsafe fn lean_int_eq(a: *mut LeanObject, b: *mut LeanObject) -> bool {
    if lean_is_scalar(a) && lean_is_scalar(b) {
        a == b
    } else {
        runtime_object_nat_int_impl::lean_int_big_eq(a, b)
    }
}

#[inline]
pub(crate) unsafe fn lean_int_ne(a: *mut LeanObject, b: *mut LeanObject) -> bool {
    !lean_int_eq(a, b)
}

#[inline]
pub(crate) unsafe fn lean_int_le(a: *mut LeanObject, b: *mut LeanObject) -> bool {
    if lean_is_scalar(a) && lean_is_scalar(b) {
        lean_scalar_to_int(a) <= lean_scalar_to_int(b)
    } else {
        runtime_object_nat_int_impl::lean_int_big_le(a, b)
    }
}

#[inline]
pub(crate) unsafe fn lean_int_lt(a: *mut LeanObject, b: *mut LeanObject) -> bool {
    if lean_is_scalar(a) && lean_is_scalar(b) {
        lean_scalar_to_int(a) < lean_scalar_to_int(b)
    } else {
        runtime_object_nat_int_impl::lean_int_big_lt(a, b)
    }
}

#[inline]
pub(crate) unsafe fn lean_int_dec_eq(a: *mut LeanObject, b: *mut LeanObject) -> u8 {
    lean_int_eq(a, b) as u8
}

#[inline]
pub(crate) unsafe fn lean_int_dec_le(a: *mut LeanObject, b: *mut LeanObject) -> u8 {
    lean_int_le(a, b) as u8
}

#[inline]
pub(crate) unsafe fn lean_int_dec_lt(a: *mut LeanObject, b: *mut LeanObject) -> u8 {
    lean_int_lt(a, b) as u8
}

#[inline]
pub(crate) unsafe fn lean_int_dec_nonneg(a: *mut LeanObject) -> u8 {
    if lean_is_scalar(a) {
        (lean_scalar_to_int(a) >= 0) as u8
    } else {
        runtime_object_nat_int_impl::lean_int_big_nonneg(a) as u8
    }
}


macro_rules! define_unsigned_numeric_family {
    (
        $ty:ty,
        $width:expr,
        $of_nat_fn:ident,
        $to_nat_fn:ident,
        $of_big_fn:path,
        $to_u8_fn:ident,
        $to_u16_fn:ident,
        $to_u32_fn:ident,
        $to_u64_fn:ident,
        $to_usize_fn:ident,
        $add_fn:ident,
        $sub_fn:ident,
        $mul_fn:ident,
        $div_fn:ident,
        $mod_fn:ident,
        $land_fn:ident,
        $lor_fn:ident,
        $xor_fn:ident,
        $shift_left_fn:ident,
        $shift_right_fn:ident,
        $complement_fn:ident,
        $neg_fn:ident,
        $log2_fn:ident,
        $dec_eq_fn:ident,
        $dec_lt_fn:ident,
        $dec_le_fn:ident
    ) => {
        pub unsafe fn $of_nat_fn(value: *mut LeanObject) -> $ty {
            if lean_is_scalar(value) {
                lean_unbox(value) as $ty
            } else {
                $of_big_fn(value)
            }
        }

        pub unsafe fn $to_nat_fn(value: $ty) -> *mut LeanObject {
            lean_usize_to_nat(value as usize)
        }

        pub unsafe fn $add_fn(a1: $ty, a2: $ty) -> $ty {
            a1.wrapping_add(a2)
        }

        pub unsafe fn $sub_fn(a1: $ty, a2: $ty) -> $ty {
            a1.wrapping_sub(a2)
        }

        pub unsafe fn $mul_fn(a1: $ty, a2: $ty) -> $ty {
            a1.wrapping_mul(a2)
        }

        pub unsafe fn $div_fn(a1: $ty, a2: $ty) -> $ty {
            if a2 == 0 {
                0
            } else {
                a1 / a2
            }
        }

        pub unsafe fn $mod_fn(a1: $ty, a2: $ty) -> $ty {
            if a2 == 0 {
                a1
            } else {
                a1 % a2
            }
        }

        pub unsafe fn $land_fn(a: $ty, b: $ty) -> $ty {
            a & b
        }

        pub unsafe fn $lor_fn(a: $ty, b: $ty) -> $ty {
            a | b
        }

        pub unsafe fn $xor_fn(a: $ty, b: $ty) -> $ty {
            a ^ b
        }

        pub unsafe fn $shift_left_fn(a: $ty, b: $ty) -> $ty {
            let width = $width;
            a.wrapping_shl((b as u32) % width)
        }

        pub unsafe fn $shift_right_fn(a: $ty, b: $ty) -> $ty {
            let width = $width;
            a.wrapping_shr((b as u32) % width)
        }

        pub unsafe fn $complement_fn(a: $ty) -> $ty {
            !a
        }

        pub unsafe fn $neg_fn(a: $ty) -> $ty {
            (0 as $ty).wrapping_sub(a)
        }

        pub unsafe fn $log2_fn(mut a: $ty) -> $ty {
            let mut res: $ty = 0;
            while a >= 2 {
                res = res.wrapping_add(1);
                a /= 2;
            }
            res
        }

        pub unsafe fn $dec_eq_fn(a1: $ty, a2: $ty) -> u8 {
            (a1 == a2) as u8
        }

        pub unsafe fn $dec_lt_fn(a1: $ty, a2: $ty) -> u8 {
            (a1 < a2) as u8
        }

        pub unsafe fn $dec_le_fn(a1: $ty, a2: $ty) -> u8 {
            (a1 <= a2) as u8
        }

        pub unsafe fn $to_u8_fn(a: $ty) -> u8 {
            a as u8
        }

        pub unsafe fn $to_u16_fn(a: $ty) -> u16 {
            a as u16
        }

        pub unsafe fn $to_u32_fn(a: $ty) -> u32 {
            a as u32
        }

        pub unsafe fn $to_u64_fn(a: $ty) -> u64 {
            a as u64
        }

        pub unsafe fn $to_usize_fn(a: $ty) -> usize {
            a as usize
        }
    };
}

macro_rules! define_usize_numeric_family {
    (
        $of_nat_fn:ident,
        $to_nat_fn:ident,
        $of_big_fn:path,
        $to_u8_fn:ident,
        $to_u16_fn:ident,
        $to_u32_fn:ident,
        $to_u64_fn:ident,
        $add_fn:ident,
        $sub_fn:ident,
        $mul_fn:ident,
        $div_fn:ident,
        $mod_fn:ident,
        $land_fn:ident,
        $lor_fn:ident,
        $xor_fn:ident,
        $shift_left_fn:ident,
        $shift_right_fn:ident,
        $complement_fn:ident,
        $neg_fn:ident,
        $log2_fn:ident,
        $dec_eq_fn:ident,
        $dec_lt_fn:ident,
        $dec_le_fn:ident
    ) => {
        pub unsafe fn $of_nat_fn(value: *mut LeanObject) -> usize {
            if lean_is_scalar(value) {
                lean_unbox(value)
            } else {
                $of_big_fn(value)
            }
        }

        pub unsafe fn $to_nat_fn(value: usize) -> *mut LeanObject {
            lean_usize_to_nat_impl(value)
        }

        pub unsafe fn $add_fn(a1: usize, a2: usize) -> usize {
            a1.wrapping_add(a2)
        }

        pub unsafe fn $sub_fn(a1: usize, a2: usize) -> usize {
            a1.wrapping_sub(a2)
        }

        pub unsafe fn $mul_fn(a1: usize, a2: usize) -> usize {
            a1.wrapping_mul(a2)
        }

        pub unsafe fn $div_fn(a1: usize, a2: usize) -> usize {
            if a2 == 0 {
                0
            } else {
                a1 / a2
            }
        }

        pub unsafe fn $mod_fn(a1: usize, a2: usize) -> usize {
            if a2 == 0 {
                a1
            } else {
                a1 % a2
            }
        }

        pub unsafe fn $land_fn(a: usize, b: usize) -> usize {
            a & b
        }

        pub unsafe fn $lor_fn(a: usize, b: usize) -> usize {
            a | b
        }

        pub unsafe fn $xor_fn(a: usize, b: usize) -> usize {
            a ^ b
        }

        pub unsafe fn $shift_left_fn(a: usize, b: usize) -> usize {
            let width = usize::BITS;
            a.wrapping_shl((b as u32) % width)
        }

        pub unsafe fn $shift_right_fn(a: usize, b: usize) -> usize {
            let width = usize::BITS;
            a.wrapping_shr((b as u32) % width)
        }

        pub unsafe fn $complement_fn(a: usize) -> usize {
            !a
        }

        pub unsafe fn $neg_fn(a: usize) -> usize {
            0usize.wrapping_sub(a)
        }

        pub unsafe fn $log2_fn(mut a: usize) -> usize {
            let mut res: usize = 0;
            while a >= 2 {
                res = res.wrapping_add(1);
                a /= 2;
            }
            res
        }

        pub unsafe fn $dec_eq_fn(a1: usize, a2: usize) -> u8 {
            (a1 == a2) as u8
        }

        pub unsafe fn $dec_lt_fn(a1: usize, a2: usize) -> u8 {
            (a1 < a2) as u8
        }

        pub unsafe fn $dec_le_fn(a1: usize, a2: usize) -> u8 {
            (a1 <= a2) as u8
        }

        pub unsafe fn $to_u8_fn(a: usize) -> u8 {
            a as u8
        }

        pub unsafe fn $to_u16_fn(a: usize) -> u16 {
            a as u16
        }

        pub unsafe fn $to_u32_fn(a: usize) -> u32 {
            a as u32
        }

        pub unsafe fn $to_u64_fn(a: usize) -> u64 {
            a as u64
        }
    };
}

define_unsigned_numeric_family!(
    u8,
    8u32,
    lean_uint8_of_nat,
    lean_uint8_to_nat,
    runtime_object_nat_int_impl::lean_uint8_of_big_nat,
    lean_uint8_to_uint8,
    lean_uint8_to_uint16,
    lean_uint8_to_uint32,
    lean_uint8_to_uint64,
    lean_uint8_to_usize,
    lean_uint8_add,
    lean_uint8_sub,
    lean_uint8_mul,
    lean_uint8_div,
    lean_uint8_mod,
    lean_uint8_land,
    lean_uint8_lor,
    lean_uint8_xor,
    lean_uint8_shift_left,
    lean_uint8_shift_right,
    lean_uint8_complement,
    lean_uint8_neg,
    lean_uint8_log2,
    lean_uint8_dec_eq,
    lean_uint8_dec_lt,
    lean_uint8_dec_le
);

#[inline]
pub(crate) unsafe fn lean_uint8_of_nat_mk(value: *mut LeanObject) -> u8 {
    let result = lean_uint8_of_nat(value);
    lean_dec(value);
    result
}

define_unsigned_numeric_family!(
    u16,
    16u32,
    lean_uint16_of_nat,
    lean_uint16_to_nat,
    runtime_object_nat_int_impl::lean_uint16_of_big_nat,
    lean_uint16_to_uint8,
    lean_uint16_to_uint16,
    lean_uint16_to_uint32,
    lean_uint16_to_uint64,
    lean_uint16_to_usize,
    lean_uint16_add,
    lean_uint16_sub,
    lean_uint16_mul,
    lean_uint16_div,
    lean_uint16_mod,
    lean_uint16_land,
    lean_uint16_lor,
    lean_uint16_xor,
    lean_uint16_shift_left,
    lean_uint16_shift_right,
    lean_uint16_complement,
    lean_uint16_neg,
    lean_uint16_log2,
    lean_uint16_dec_eq,
    lean_uint16_dec_lt,
    lean_uint16_dec_le
);

#[inline]
pub(crate) unsafe fn lean_uint16_of_nat_mk(value: *mut LeanObject) -> u16 {
    let result = lean_uint16_of_nat(value);
    lean_dec(value);
    result
}

define_unsigned_numeric_family!(
    u32,
    32u32,
    lean_uint32_of_nat,
    lean_uint32_to_nat,
    runtime_object_nat_int_impl::lean_uint32_of_big_nat,
    lean_uint32_to_uint8,
    lean_uint32_to_uint16,
    lean_uint32_to_uint32,
    lean_uint32_to_uint64,
    lean_uint32_to_usize,
    lean_uint32_add,
    lean_uint32_sub,
    lean_uint32_mul,
    lean_uint32_div,
    lean_uint32_mod,
    lean_uint32_land,
    lean_uint32_lor,
    lean_uint32_xor,
    lean_uint32_shift_left,
    lean_uint32_shift_right,
    lean_uint32_complement,
    lean_uint32_neg,
    lean_uint32_log2,
    lean_uint32_dec_eq,
    lean_uint32_dec_lt,
    lean_uint32_dec_le
);

#[inline]
pub(crate) unsafe fn lean_uint32_of_nat_mk(value: *mut LeanObject) -> u32 {
    let result = lean_uint32_of_nat(value);
    lean_dec(value);
    result
}

define_unsigned_numeric_family!(
    u64,
    64u32,
    lean_uint64_of_nat,
    lean_uint64_to_nat,
    runtime_object_nat_int_impl::lean_uint64_of_big_nat,
    lean_uint64_to_uint8,
    lean_uint64_to_uint16,
    lean_uint64_to_uint32,
    lean_uint64_to_uint64,
    lean_uint64_to_usize,
    lean_uint64_add,
    lean_uint64_sub,
    lean_uint64_mul,
    lean_uint64_div,
    lean_uint64_mod,
    lean_uint64_land,
    lean_uint64_lor,
    lean_uint64_xor,
    lean_uint64_shift_left,
    lean_uint64_shift_right,
    lean_uint64_complement,
    lean_uint64_neg,
    lean_uint64_log2,
    lean_uint64_dec_eq,
    lean_uint64_dec_lt,
    lean_uint64_dec_le
);

#[inline]
pub(crate) unsafe fn lean_uint64_of_nat_mk(value: *mut LeanObject) -> u64 {
    let result = lean_uint64_of_nat(value);
    lean_dec(value);
    result
}

define_usize_numeric_family!(
    lean_usize_of_nat,
    lean_usize_to_nat,
    runtime_object_nat_int_impl::lean_usize_of_big_nat,
    lean_usize_to_uint8,
    lean_usize_to_uint16,
    lean_usize_to_uint32,
    lean_usize_to_uint64,
    lean_usize_add,
    lean_usize_sub,
    lean_usize_mul,
    lean_usize_div,
    lean_usize_mod,
    lean_usize_land,
    lean_usize_lor,
    lean_usize_xor,
    lean_usize_shift_left,
    lean_usize_shift_right,
    lean_usize_complement,
    lean_usize_neg,
    lean_usize_log2,
    lean_usize_dec_eq,
    lean_usize_dec_lt,
    lean_usize_dec_le
);

#[inline]
pub(crate) unsafe fn lean_usize_to_nat_impl(value: usize) -> *mut LeanObject {
    if value <= usize::MAX >> 1 {
        lean_box(value)
    } else {
        runtime_object_nat_int_impl::lean_big_usize_to_nat(value)
    }
}

#[inline]
pub(crate) unsafe fn lean_usize_of_nat_mk(value: *mut LeanObject) -> usize {
    let result = lean_usize_of_nat(value);
    lean_dec(value);
    result
}

macro_rules! define_signed_numeric_family {
    (
        $storage:ty,
        $signed:ty,
        $width:expr,
        $of_int_fn:ident,
        $of_nat_fn:ident,
        $to_int_fn:ident,
        $of_big_fn:path,
        $add_fn:ident,
        $sub_fn:ident,
        $mul_fn:ident,
        $div_fn:ident,
        $mod_fn:ident,
        $land_fn:ident,
        $lor_fn:ident,
        $xor_fn:ident,
        $shift_left_fn:ident,
        $shift_right_fn:ident,
        $complement_fn:ident,
        $neg_fn:ident,
        $abs_fn:ident,
        $dec_eq_fn:ident,
        $dec_lt_fn:ident,
        $dec_le_fn:ident,
        $to_int8_fn:ident,
        $to_int16_fn:ident,
        $to_int32_fn:ident,
        $to_int64_fn:ident,
        $to_isize_fn:ident
    ) => {
        pub unsafe fn $of_int_fn(value: *mut LeanObject) -> $storage {
            if lean_is_scalar(value) {
                lean_scalar_to_int64(value) as $storage
            } else {
                $of_big_fn(value) as $storage
            }
        }

        pub unsafe fn $of_nat_fn(value: *mut LeanObject) -> $storage {
            if lean_is_scalar(value) {
                lean_unbox(value) as $storage
            } else {
                $of_big_fn(value) as $storage
            }
        }

        pub unsafe fn $to_int_fn(value: $storage) -> *mut LeanObject {
            lean_int64_to_int((value as $signed) as i64)
        }

        pub unsafe fn $add_fn(a1: $storage, a2: $storage) -> $storage {
            a1.wrapping_add(a2)
        }

        pub unsafe fn $sub_fn(a1: $storage, a2: $storage) -> $storage {
            a1.wrapping_sub(a2)
        }

        pub unsafe fn $mul_fn(a1: $storage, a2: $storage) -> $storage {
            a1.wrapping_mul(a2)
        }

        pub unsafe fn $div_fn(a1: $storage, a2: $storage) -> $storage {
            let lhs = a1 as $signed;
            let rhs = a2 as $signed;
            if rhs == 0 {
                0 as $storage
            } else if lhs == <$signed>::MIN && rhs == -1 {
                lhs as $storage
            } else {
                (lhs / rhs) as $storage
            }
        }

        pub unsafe fn $mod_fn(a1: $storage, a2: $storage) -> $storage {
            let lhs = a1 as $signed;
            let rhs = a2 as $signed;
            if rhs == 0 {
                lhs as $storage
            } else if lhs == <$signed>::MIN && rhs == -1 {
                0 as $storage
            } else {
                (lhs % rhs) as $storage
            }
        }

        pub unsafe fn $land_fn(a1: $storage, a2: $storage) -> $storage {
            (a1 as $signed & a2 as $signed) as $storage
        }

        pub unsafe fn $lor_fn(a1: $storage, a2: $storage) -> $storage {
            (a1 as $signed | a2 as $signed) as $storage
        }

        pub unsafe fn $xor_fn(a1: $storage, a2: $storage) -> $storage {
            (a1 as $signed ^ a2 as $signed) as $storage
        }

        pub unsafe fn $shift_right_fn(a1: $storage, a2: $storage) -> $storage {
            let width = $width as $signed;
            let rhs = (((a2 as $signed) % width) + width) % width;
            ((a1 as $signed) >> rhs) as $storage
        }

        pub unsafe fn $shift_left_fn(a1: $storage, a2: $storage) -> $storage {
            let width = $width as $signed;
            let rhs = (((a2 as $signed) % width) + width) % width;
            a1.wrapping_shl(rhs as u32)
        }

        pub unsafe fn $complement_fn(a: $storage) -> $storage {
            !(a as $signed) as $storage
        }

        pub unsafe fn $neg_fn(a: $storage) -> $storage {
            (0 as $storage).wrapping_sub(a)
        }

        pub unsafe fn $abs_fn(a: $storage) -> $storage {
            let signed = a as $signed;
            if signed < 0 {
                (0 as $storage).wrapping_sub(a)
            } else {
                a
            }
        }

        pub unsafe fn $dec_eq_fn(a1: $storage, a2: $storage) -> u8 {
            ((a1 as $signed) == (a2 as $signed)) as u8
        }

        pub unsafe fn $dec_lt_fn(a1: $storage, a2: $storage) -> u8 {
            ((a1 as $signed) < (a2 as $signed)) as u8
        }

        pub unsafe fn $dec_le_fn(a1: $storage, a2: $storage) -> u8 {
            ((a1 as $signed) <= (a2 as $signed)) as u8
        }

        pub unsafe fn $to_int8_fn(a: $storage) -> u8 {
            (a as $signed as i8) as u8
        }

        pub unsafe fn $to_int16_fn(a: $storage) -> u16 {
            (a as $signed as i16) as u16
        }

        pub unsafe fn $to_int32_fn(a: $storage) -> u32 {
            (a as $signed as i32) as u32
        }

        pub unsafe fn $to_int64_fn(a: $storage) -> u64 {
            (a as $signed as i64) as u64
        }

        pub unsafe fn $to_isize_fn(a: $storage) -> usize {
            (a as $signed as isize) as usize
        }

    };
}

define_signed_numeric_family!(
    u8,
    i8,
    8i8,
    lean_int8_of_int,
    lean_int8_of_nat,
    lean_int8_to_int,
    runtime_object_nat_int_impl::lean_int8_of_big_int,
    lean_int8_add,
    lean_int8_sub,
    lean_int8_mul,
    lean_int8_div,
    lean_int8_mod,
    lean_int8_land,
    lean_int8_lor,
    lean_int8_xor,
    lean_int8_shift_left,
    lean_int8_shift_right,
    lean_int8_complement,
    lean_int8_neg,
    lean_int8_abs,
    lean_int8_dec_eq,
    lean_int8_dec_lt,
    lean_int8_dec_le,
    lean_int8_to_int8,
    lean_int8_to_int16,
    lean_int8_to_int32,
    lean_int8_to_int64,
    lean_int8_to_isize
);

define_signed_numeric_family!(
    u16,
    i16,
    16i16,
    lean_int16_of_int,
    lean_int16_of_nat,
    lean_int16_to_int,
    runtime_object_nat_int_impl::lean_int16_of_big_int,
    lean_int16_add,
    lean_int16_sub,
    lean_int16_mul,
    lean_int16_div,
    lean_int16_mod,
    lean_int16_land,
    lean_int16_lor,
    lean_int16_xor,
    lean_int16_shift_left,
    lean_int16_shift_right,
    lean_int16_complement,
    lean_int16_neg,
    lean_int16_abs,
    lean_int16_dec_eq,
    lean_int16_dec_lt,
    lean_int16_dec_le,
    lean_int16_to_int8,
    lean_int16_to_int16,
    lean_int16_to_int32,
    lean_int16_to_int64,
    lean_int16_to_isize
);

define_signed_numeric_family!(
    u32,
    i32,
    32i32,
    lean_int32_of_int,
    lean_int32_of_nat,
    lean_int32_to_int,
    runtime_object_nat_int_impl::lean_int32_of_big_int,
    lean_int32_add,
    lean_int32_sub,
    lean_int32_mul,
    lean_int32_div,
    lean_int32_mod,
    lean_int32_land,
    lean_int32_lor,
    lean_int32_xor,
    lean_int32_shift_left,
    lean_int32_shift_right,
    lean_int32_complement,
    lean_int32_neg,
    lean_int32_abs,
    lean_int32_dec_eq,
    lean_int32_dec_lt,
    lean_int32_dec_le,
    lean_int32_to_int8,
    lean_int32_to_int16,
    lean_int32_to_int32,
    lean_int32_to_int64,
    lean_int32_to_isize
);

define_signed_numeric_family!(
    u64,
    i64,
    64i64,
    lean_int64_of_int,
    lean_int64_of_nat,
    lean_int64_to_int_sint,
    runtime_object_nat_int_impl::lean_int64_of_big_int,
    lean_int64_add,
    lean_int64_sub,
    lean_int64_mul,
    lean_int64_div,
    lean_int64_mod,
    lean_int64_land,
    lean_int64_lor,
    lean_int64_xor,
    lean_int64_shift_left,
    lean_int64_shift_right,
    lean_int64_complement,
    lean_int64_neg,
    lean_int64_abs,
    lean_int64_dec_eq,
    lean_int64_dec_lt,
    lean_int64_dec_le,
    lean_int64_to_int8,
    lean_int64_to_int16,
    lean_int64_to_int32,
    lean_int64_to_int64,
    lean_int64_to_isize
);

macro_rules! define_isize_numeric_family {
    (
        $of_int_fn:ident,
        $of_nat_fn:ident,
        $to_int_fn:ident,
        $of_big_fn:path,
        $add_fn:ident,
        $sub_fn:ident,
        $mul_fn:ident,
        $div_fn:ident,
        $mod_fn:ident,
        $land_fn:ident,
        $lor_fn:ident,
        $xor_fn:ident,
        $shift_right_fn:ident,
        $shift_left_fn:ident,
        $complement_fn:ident,
        $neg_fn:ident,
        $abs_fn:ident,
        $dec_eq_fn:ident,
        $dec_lt_fn:ident,
        $dec_le_fn:ident,
        $to_int8_fn:ident,
        $to_int16_fn:ident,
        $to_int32_fn:ident,
        $to_int64_fn:ident
    ) => {
        pub unsafe fn $of_int_fn(value: *mut LeanObject) -> usize {
            if lean_is_scalar(value) {
                lean_scalar_to_int64(value) as isize as usize
            } else {
                $of_big_fn(value) as usize
            }
        }

        pub unsafe fn $of_nat_fn(value: *mut LeanObject) -> usize {
            if lean_is_scalar(value) {
                lean_unbox(value)
            } else {
                $of_big_fn(value) as usize
            }
        }

        pub unsafe fn $to_int_fn(value: usize) -> *mut LeanObject {
            lean_int64_to_int((value as isize) as i64)
        }

        pub unsafe fn $add_fn(a1: usize, a2: usize) -> usize {
            a1.wrapping_add(a2)
        }

        pub unsafe fn $sub_fn(a1: usize, a2: usize) -> usize {
            a1.wrapping_sub(a2)
        }

        pub unsafe fn $mul_fn(a1: usize, a2: usize) -> usize {
            a1.wrapping_mul(a2)
        }

        pub unsafe fn $div_fn(a1: usize, a2: usize) -> usize {
            let lhs = a1 as isize;
            let rhs = a2 as isize;
            if rhs == 0 {
                0
            } else if lhs == isize::MIN && rhs == -1 {
                lhs as usize
            } else {
                (lhs / rhs) as usize
            }
        }

        pub unsafe fn $mod_fn(a1: usize, a2: usize) -> usize {
            let lhs = a1 as isize;
            let rhs = a2 as isize;
            if rhs == 0 {
                lhs as usize
            } else if lhs == isize::MIN && rhs == -1 {
                0
            } else {
                (lhs % rhs) as usize
            }
        }

        pub unsafe fn $land_fn(a1: usize, a2: usize) -> usize {
            (a1 as isize & a2 as isize) as usize
        }

        pub unsafe fn $lor_fn(a1: usize, a2: usize) -> usize {
            (a1 as isize | a2 as isize) as usize
        }

        pub unsafe fn $xor_fn(a1: usize, a2: usize) -> usize {
            (a1 as isize ^ a2 as isize) as usize
        }

        pub unsafe fn $shift_right_fn(a1: usize, a2: usize) -> usize {
            let width = usize::BITS as isize;
            let rhs = (((a2 as isize) % width) + width) % width;
            ((a1 as isize) >> rhs) as usize
        }

        pub unsafe fn $shift_left_fn(a1: usize, a2: usize) -> usize {
            let width = usize::BITS as isize;
            let rhs = (((a2 as isize) % width) + width) % width;
            a1.wrapping_shl(rhs as u32)
        }

        pub unsafe fn $complement_fn(a: usize) -> usize {
            !(a as isize) as usize
        }

        pub unsafe fn $neg_fn(a: usize) -> usize {
            0usize.wrapping_sub(a)
        }

        pub unsafe fn $abs_fn(a: usize) -> usize {
            let signed = a as isize;
            if signed < 0 {
                (0usize).wrapping_sub(a)
            } else {
                a
            }
        }

        pub unsafe fn $dec_eq_fn(a1: usize, a2: usize) -> u8 {
            ((a1 as isize) == (a2 as isize)) as u8
        }

        pub unsafe fn $dec_lt_fn(a1: usize, a2: usize) -> u8 {
            ((a1 as isize) < (a2 as isize)) as u8
        }

        pub unsafe fn $dec_le_fn(a1: usize, a2: usize) -> u8 {
            ((a1 as isize) <= (a2 as isize)) as u8
        }

        pub unsafe fn $to_int8_fn(a: usize) -> u8 {
            (a as isize as i8) as u8
        }

        pub unsafe fn $to_int16_fn(a: usize) -> u16 {
            (a as isize as i16) as u16
        }

        pub unsafe fn $to_int32_fn(a: usize) -> u32 {
            (a as isize as i32) as u32
        }

        pub unsafe fn $to_int64_fn(a: usize) -> u64 {
            (a as isize as i64) as u64
        }
    };
}

macro_rules! define_float_casts {
    (
        $to_u8_fn:ident,
        $to_u16_fn:ident,
        $to_u32_fn:ident,
        $to_u64_fn:ident,
        $to_usize_fn:ident,
        $to_i8_fn:ident,
        $to_i16_fn:ident,
        $to_i32_fn:ident,
        $to_i64_fn:ident,
        $to_isize_fn:ident,
        $to_f32_fn:ident,
        $to_f64_fn:ident
    ) => {
        pub unsafe fn $to_u8_fn(a: f64) -> u8 {
            if 0.0 <= a {
                if a < u8::MAX as f64 {
                    a as u8
                } else {
                    u8::MAX
                }
            } else {
                0
            }
        }

        pub unsafe fn $to_u16_fn(a: f64) -> u16 {
            if 0.0 <= a {
                if a < u16::MAX as f64 {
                    a as u16
                } else {
                    u16::MAX
                }
            } else {
                0
            }
        }

        pub unsafe fn $to_u32_fn(a: f64) -> u32 {
            if 0.0 <= a {
                if a < u32::MAX as f64 {
                    a as u32
                } else {
                    u32::MAX
                }
            } else {
                0
            }
        }

        pub unsafe fn $to_u64_fn(a: f64) -> u64 {
            if 0.0 <= a {
                if a < u64::MAX as f64 {
                    a as u64
                } else {
                    u64::MAX
                }
            } else {
                0
            }
        }

        pub unsafe fn $to_usize_fn(a: f64) -> usize {
            if 0.0 <= a {
                if a < usize::MAX as f64 {
                    a as usize
                } else {
                    usize::MAX
                }
            } else {
                0
            }
        }

        pub unsafe fn $to_i8_fn(a: f64) -> u8 {
            if a.is_nan() {
                0
            } else if -129.0 < a {
                if a < 128.0 {
                    (a as i8) as u8
                } else {
                    i8::MAX as u8
                }
            } else {
                i8::MIN as u8
            }
        }

        pub unsafe fn $to_i16_fn(a: f64) -> u16 {
            if a.is_nan() {
                0
            } else if -32769.0 < a {
                if a < 32768.0 {
                    (a as i16) as u16
                } else {
                    i16::MAX as u16
                }
            } else {
                i16::MIN as u16
            }
        }

        pub unsafe fn $to_i32_fn(a: f64) -> u32 {
            if a.is_nan() {
                0
            } else if -2147483649.0 < a {
                if a < 2147483648.0 {
                    (a as i32) as u32
                } else {
                    i32::MAX as u32
                }
            } else {
                i32::MIN as u32
            }
        }

        pub unsafe fn $to_i64_fn(a: f64) -> u64 {
            if a.is_nan() {
                0
            } else if -9223372036854775809.0 < a {
                if a < 9223372036854775808.0 {
                    (a as i64) as u64
                } else {
                    i64::MAX as u64
                }
            } else {
                i64::MIN as u64
            }
        }

        pub unsafe fn $to_isize_fn(a: f64) -> usize {
            if a.is_nan() {
                0
            } else if usize::BITS == 64 {
                if -9223372036854775809.0 < a {
                    if a < 9223372036854775808.0 {
                        (a as isize) as usize
                    } else {
                        isize::MAX as usize
                    }
                } else {
                    isize::MIN as usize
                }
            } else if -2147483649.0 < a {
                if a < 2147483648.0 {
                    (a as i32) as usize
                } else {
                    i32::MAX as usize
                }
            } else {
                i32::MIN as usize
            }
        }

        pub unsafe fn $to_f64_fn(a: f32) -> f64 {
            a as f64
        }

        pub unsafe fn $to_f32_fn(a: f64) -> f32 {
            a as f32
        }
    };
}

macro_rules! define_integer_float_casts {
    (
        $to_f64_u8:ident,
        $to_f64_u16:ident,
        $to_f64_u32:ident,
        $to_f64_u64:ident,
        $to_f64_usize:ident,
        $to_f64_i8:ident,
        $to_f64_i16:ident,
        $to_f64_i32:ident,
        $to_f64_i64:ident,
        $to_f64_isize:ident,
        $to_f32_u8:ident,
        $to_f32_u16:ident,
        $to_f32_u32:ident,
        $to_f32_u64:ident,
        $to_f32_usize:ident,
        $to_f32_i8:ident,
        $to_f32_i16:ident,
        $to_f32_i32:ident,
        $to_f32_i64:ident,
        $to_f32_isize:ident
    ) => {
        pub unsafe fn $to_f64_u8(a: u8) -> f64 { a as f64 }
        pub unsafe fn $to_f64_u16(a: u16) -> f64 { a as f64 }
        pub unsafe fn $to_f64_u32(a: u32) -> f64 { a as f64 }
        pub unsafe fn $to_f64_u64(a: u64) -> f64 { a as f64 }
        pub unsafe fn $to_f64_usize(a: usize) -> f64 { a as f64 }
        pub unsafe fn $to_f64_i8(a: u8) -> f64 { (a as i8) as f64 }
        pub unsafe fn $to_f64_i16(a: u16) -> f64 { (a as i16) as f64 }
        pub unsafe fn $to_f64_i32(a: u32) -> f64 { (a as i32) as f64 }
        pub unsafe fn $to_f64_i64(a: u64) -> f64 { (a as i64) as f64 }
        pub unsafe fn $to_f64_isize(a: usize) -> f64 { (a as isize) as f64 }
        pub unsafe fn $to_f32_u8(a: u8) -> f32 { a as f32 }
        pub unsafe fn $to_f32_u16(a: u16) -> f32 { a as f32 }
        pub unsafe fn $to_f32_u32(a: u32) -> f32 { a as f32 }
        pub unsafe fn $to_f32_u64(a: u64) -> f32 { a as f32 }
        pub unsafe fn $to_f32_usize(a: usize) -> f32 { a as f32 }
        pub unsafe fn $to_f32_i8(a: u8) -> f32 { (a as i8) as f32 }
        pub unsafe fn $to_f32_i16(a: u16) -> f32 { (a as i16) as f32 }
        pub unsafe fn $to_f32_i32(a: u32) -> f32 { (a as i32) as f32 }
        pub unsafe fn $to_f32_i64(a: u64) -> f32 { (a as i64) as f32 }
        pub unsafe fn $to_f32_isize(a: usize) -> f32 { (a as isize) as f32 }
    };
}

macro_rules! define_float32_to_integer_casts {
    (
        $to_u8_fn:ident,
        $to_u16_fn:ident,
        $to_u32_fn:ident,
        $to_u64_fn:ident,
        $to_usize_fn:ident,
        $to_i8_fn:ident,
        $to_i16_fn:ident,
        $to_i32_fn:ident,
        $to_i64_fn:ident,
        $to_isize_fn:ident
    ) => {
        pub unsafe fn $to_u8_fn(a: f32) -> u8 {
            if 0.0 <= a {
                if a < u8::MAX as f32 {
                    a as u8
                } else {
                    u8::MAX
                }
            } else {
                0
            }
        }

        pub unsafe fn $to_u16_fn(a: f32) -> u16 {
            if 0.0 <= a {
                if a < u16::MAX as f32 {
                    a as u16
                } else {
                    u16::MAX
                }
            } else {
                0
            }
        }

        pub unsafe fn $to_u32_fn(a: f32) -> u32 {
            if 0.0 <= a {
                if a < u32::MAX as f32 {
                    a as u32
                } else {
                    u32::MAX
                }
            } else {
                0
            }
        }

        pub unsafe fn $to_u64_fn(a: f32) -> u64 {
            if 0.0 <= a {
                if a < u64::MAX as f32 {
                    a as u64
                } else {
                    u64::MAX
                }
            } else {
                0
            }
        }

        pub unsafe fn $to_usize_fn(a: f32) -> usize {
            if 0.0 <= a {
                if usize::BITS == 64 {
                    if a < u64::MAX as f32 {
                        a as usize
                    } else {
                        usize::MAX
                    }
                } else if a < u32::MAX as f32 {
                    a as usize
                } else {
                    usize::MAX
                }
            } else {
                0
            }
        }

        pub unsafe fn $to_i8_fn(a: f32) -> u8 {
            if a.is_nan() {
                0
            } else if a <= (i8::MIN as f32) {
                i8::MIN as u8
            } else if a < (i8::MAX as f32 + 1.0) {
                (a as i8) as u8
            } else {
                i8::MAX as u8
            }
        }

        pub unsafe fn $to_i16_fn(a: f32) -> u16 {
            if a.is_nan() {
                0
            } else if -32769.0 < a {
                if a < 32768.0 {
                    (a as i16) as u16
                } else {
                    i16::MAX as u16
                }
            } else {
                i16::MIN as u16
            }
        }

        pub unsafe fn $to_i32_fn(a: f32) -> u32 {
            if a.is_nan() {
                0
            } else if -2147483649.0 < a {
                if a < 2147483648.0 {
                    (a as i32) as u32
                } else {
                    i32::MAX as u32
                }
            } else {
                i32::MIN as u32
            }
        }

        pub unsafe fn $to_i64_fn(a: f32) -> u64 {
            if a.is_nan() {
                0
            } else if -9223372036854775809.0 < a {
                if a < 9223372036854775808.0 {
                    (a as i64) as u64
                } else {
                    i64::MAX as u64
                }
            } else {
                i64::MIN as u64
            }
        }

        pub unsafe fn $to_isize_fn(a: f32) -> usize {
            if a.is_nan() {
                0
            } else if usize::BITS == 64 {
                if -9223372036854775809.0 < a {
                    if a < 9223372036854775808.0 {
                        (a as isize) as usize
                    } else {
                        isize::MAX as usize
                    }
                } else {
                    isize::MIN as usize
                }
            } else if -2147483649.0 < a {
                if a < 2147483648.0 {
                    (a as i32) as usize
                } else {
                    i32::MAX as usize
                }
            } else {
                i32::MIN as usize
            }
        }
    };
}

define_isize_numeric_family!(
    lean_isize_of_int,
    lean_isize_of_nat,
    lean_isize_to_int,
    runtime_object_nat_int_impl::lean_isize_of_big_int,
    lean_isize_add,
    lean_isize_sub,
    lean_isize_mul,
    lean_isize_div,
    lean_isize_mod,
    lean_isize_land,
    lean_isize_lor,
    lean_isize_xor,
    lean_isize_shift_right,
    lean_isize_shift_left,
    lean_isize_complement,
    lean_isize_neg,
    lean_isize_abs,
    lean_isize_dec_eq,
    lean_isize_dec_lt,
    lean_isize_dec_le,
    lean_isize_to_int8,
    lean_isize_to_int16,
    lean_isize_to_int32,
    lean_isize_to_int64
);

define_integer_float_casts!(
    lean_uint8_to_float,
    lean_uint16_to_float,
    lean_uint32_to_float,
    lean_uint64_to_float,
    lean_usize_to_float,
    lean_int8_to_float,
    lean_int16_to_float,
    lean_int32_to_float,
    lean_int64_to_float,
    lean_isize_to_float,
    lean_uint8_to_float32,
    lean_uint16_to_float32,
    lean_uint32_to_float32,
    lean_uint64_to_float32,
    lean_usize_to_float32,
    lean_int8_to_float32,
    lean_int16_to_float32,
    lean_int32_to_float32,
    lean_int64_to_float32,
    lean_isize_to_float32
);

define_float_casts!(
    lean_float_to_uint8,
    lean_float_to_uint16,
    lean_float_to_uint32,
    lean_float_to_uint64,
    lean_float_to_usize,
    lean_float_to_int8,
    lean_float_to_int16,
    lean_float_to_int32,
    lean_float_to_int64,
    lean_float_to_isize,
    lean_float_to_float32,
    lean_float32_to_float
);

define_float32_to_integer_casts!(
    lean_float32_to_uint8,
    lean_float32_to_uint16,
    lean_float32_to_uint32,
    lean_float32_to_uint64,
    lean_float32_to_usize,
    lean_float32_to_int8,
    lean_float32_to_int16,
    lean_float32_to_int32,
    lean_float32_to_int64,
    lean_float32_to_isize
);

#[inline]
pub(crate) unsafe fn lean_option_get_or_block(opt: *mut LeanObject) -> *mut LeanObject {
    if !lean_is_scalar(opt) {
        let value = lean_ctor_get(opt, 0);
        lean_inc(value);
        lean_dec(opt);
        value
    } else {
        runtime_object_panic_impl::lean_panic(
            c"PANIC: Promise.result!: promise has been dropped without ever being resolved"
                .as_ptr(),
            true,
        );
        loop {
            std::thread::sleep(std::time::Duration::MAX);
        }
    }
}

#[inline]
pub(crate) unsafe fn lean_runtime_get_lean_num_threads() -> c_uint {
    #[cfg(not(target_os = "emscripten"))]
    {
        let name = b"LEAN_NUM_THREADS\0";
        let value = libc::getenv(name.as_ptr().cast());
        if !value.is_null() {
            return libc::atoi(value) as c_uint;
        }
    }
    std::thread::available_parallelism()
        .map(|count| count.get() as c_uint)
        .unwrap_or(1)
}

#[inline]
pub(crate) unsafe fn lean_io_allocprof(
    msg: *mut LeanObject,
    fn_obj: *mut LeanObject,
) -> *mut LeanObject {
    let label = CStr::from_ptr(lean_string_cstr(msg)).to_string_lossy();
    let result = lean_apply_1(fn_obj, lean_box(0));
    let output = std::ffi::CString::new(format!(
        "{label}\nAllocation profiling data is not available, compile lean using `-D RUNTIME_STATS=ON`\n"
    ))
    .expect("allocation profiler output has no NUL");
    let print_result = lean_io_eprintln(lean_mk_string(output.as_ptr()));
    lean_dec(print_result);
    result
}

fn utf8_size(byte: c_uchar) -> Size {
    if byte & 0x80 == 0 {
        1
    } else if byte & 0xE0 == 0xC0 {
        2
    } else if byte & 0xF0 == 0xE0 {
        3
    } else if byte & 0xF8 == 0xF0 {
        4
    } else if byte & 0xFC == 0xF8 {
        5
    } else if byte & 0xFE == 0xFC {
        6
    } else {
        1
    }
}

fn is_safe_ascii_byte(byte: u8) -> bool {
    matches!(
        byte,
        b'0'..=b'9'
            | b'a'..=b'z'
            | b'A'..=b'Z'
            | b'_'
            | b' '
            | b'\t'
            | b'\r'
            | b'\n'
            | b'('
            | b')'
            | b'{'
            | b'}'
            | b':'
            | b'.'
            | b','
            | b'"'
            | b'\''
            | b'`'
            | b'!'
            | b'#'
            | b'='
            | b'<'
            | b'>'
            | b'@'
            | b'^'
            | b'|'
            | b'&'
            | b'~'
            | b'+'
            | b'-'
            | b'*'
            | b'/'
            | b'\\'
            | b'$'
            | b'%'
            | b'?'
            | b';'
            | b'['
            | b']'
    )
}

#[inline]
pub(crate) fn lean_util_is_safe_ascii_char(byte: c_char) -> bool {
    is_safe_ascii_byte(byte as u8)
}

#[inline]
pub(crate) unsafe fn lean_util_is_safe_ascii(mut text: *const c_char) -> bool {
    if text.is_null() {
        return true;
    }
    while *text != 0 {
        if !is_safe_ascii_byte(*text as u8) {
            return false;
        }
        text = text.add(1);
    }
    true
}

#[inline]
pub(crate) unsafe fn lean_util_is_safe_ascii_n(text: *const c_char, size: Size) -> bool {
    for offset in 0..size {
        if !is_safe_ascii_byte(*text.add(offset) as u8) {
            return false;
        }
    }
    true
}

#[inline]
pub(crate) fn lean_util_log2(mut value: c_uint) -> c_uint {
    let mut result = 0;
    if value & 0xFFFF0000 != 0 {
        value >>= 16;
        result |= 16;
    }
    if value & 0xFF00 != 0 {
        value >>= 8;
        result |= 8;
    }
    if value & 0xF0 != 0 {
        value >>= 4;
        result |= 4;
    }
    if value & 0xC != 0 {
        value >>= 2;
        result |= 2;
    }
    if value & 0x2 != 0 {
        result |= 1;
    }
    result
}

#[inline]
pub(crate) fn lean_util_lbool_name(value: i32) -> *const c_char {
    match value {
        -1 => c"l_false".as_ptr(),
        1 => c"l_true".as_ptr(),
        _ => c"l_undef".as_ptr(),
    }
}

#[inline]
pub(crate) fn lean_util_mk_list_range(from: c_uint, to: c_uint) -> *mut c_void {
    let mut list: *mut LeanListCell = ptr::null_mut();
    let mut i = to;
    while i > from {
        i -= 1;
        let tail = list;
        if !tail.is_null() {
            unsafe {
                (*tail).rc.fetch_add(1, Ordering::Relaxed);
            }
        }
        list = Box::into_raw(Box::new(LeanListCell {
            rc: AtomicU32::new(0),
            head: i,
            tail,
        }));
    }
    list.cast()
}

unsafe fn name_is_anonymous(obj: *mut LeanObject) -> bool {
    lean_is_scalar(obj)
}

unsafe fn name_prefix(obj: *mut LeanObject) -> *mut LeanObject {
    debug_assert!(!lean_is_scalar(obj));
    lean_ctor_get(obj, 0)
}

unsafe fn name_contains_registered_prefix(state: &NameGeneratorState, n: *mut LeanObject) -> bool {
    state
        .prefixes
        .iter()
        .copied()
        .any(|p| runtime_object_name_impl::lean_name_eq(p, n) != 0)
}

unsafe fn name_uses_registered_prefix(state: &NameGeneratorState, n: *mut LeanObject) -> bool {
    if name_is_anonymous(n) {
        return false;
    }
    if name_contains_registered_prefix(state, n) {
        return true;
    }
    name_uses_registered_prefix(state, name_prefix(n))
}

unsafe fn consume_io_result(label: &str, result: *mut LeanObject) {
    if lean_io_result_is_ok(result) {
        lean_dec(result);
    } else {
        let err = lean_io_result_get_error(result);
        lean_inc(err);
        lean_dec(result);
        let msg = lean_io_error_to_string(err);
        let text = core::ffi::CStr::from_ptr(lean_string_cstr(msg));

        let prefix = b"IO Error in lean_initialize: ";
        libc::write(2, prefix.as_ptr().cast(), prefix.len());
        libc::write(2, label.as_ptr().cast(), label.len());
        libc::write(2, b": ".as_ptr().cast(), 2);
        let bytes = text.to_bytes();
        libc::write(2, bytes.as_ptr().cast(), bytes.len());
        libc::write(2, b"\n".as_ptr().cast(), 1);
        std::process::exit(1);
    }
}

unsafe fn initialize_runtime_module_body() {
    initialize_debug();
    // initialize_object was a no-op (object.cpp deleted)
    initialize_io();
    initialize_mutex();
    initialize_stack_overflow();
    #[cfg(all(feature = "std", not(target_family = "wasm")))]
    initialize_libuv();
}

unsafe fn finalize_runtime_module_body() {
    finalize_stack_overflow();
    lean_finalize_external_classes(); // was finalize_object() in object.cpp
    finalize_debug();
}

unsafe fn initialize_util_module_body() {
    initialize_runtime_module_body();
    initialize_name();
    initialize_name_generator();
    initialize_options();
}

unsafe fn finalize_util_module_body() {
    finalize_options();
    finalize_name_generator();
    finalize_runtime_module_body();
}

unsafe fn initialize_kernel_module_body() {
    initialize_level();
    initialize_type_checker();
}

unsafe fn finalize_kernel_module_body() {
    finalize_type_checker();
    finalize_level();
}



unsafe fn initialize_library_core_module_body() {
    initialize_constants();
}

unsafe fn finalize_library_core_module_body() {
    finalize_constants();
}

unsafe fn initialize_library_module_body() {
    initialize_library_util();
    initialize_dynlib();
}

unsafe fn finalize_library_module_body() {
    finalize_ir_interpreter();
    finalize_time_task();
    finalize_library_util();
}

unsafe fn initialize_constructions_module_body() {
    initialize_constructions_util();
}

unsafe fn finalize_constructions_module_body() {
    finalize_constructions_util();
}

#[inline]
pub(crate) fn lean_initialize_runtime_module() {
    unsafe { initialize_runtime_module_body() }
}

#[inline]
pub(crate) fn initialize_runtime_module() {
    unsafe { initialize_runtime_module_body() }
}

#[inline]
pub(crate) fn finalize_runtime_module() {
    unsafe { finalize_runtime_module_body() }
}

#[inline]
pub(crate) fn initialize_util_module() {
    unsafe { initialize_util_module_body() }
}

#[inline]
pub(crate) fn finalize_util_module() {
    unsafe { finalize_util_module_body() }
}

#[inline]
pub(crate) fn initialize_kernel_module() {
    unsafe { initialize_kernel_module_body() }
}

#[inline]
pub(crate) fn finalize_kernel_module() {
    unsafe { finalize_kernel_module_body() }
}

#[inline]
pub(crate) fn initialize_library_core_module() {
    unsafe { initialize_library_core_module_body() }
}

#[inline]
pub(crate) fn finalize_library_core_module() {
    unsafe { finalize_library_core_module_body() }
}

#[inline]
pub(crate) fn initialize_library_module() {
    unsafe { initialize_library_module_body() }
}

#[inline]
pub(crate) fn finalize_library_module() {
    unsafe { finalize_library_module_body() }
}

#[inline]
pub(crate) fn initialize_constructions_module() {
    unsafe { initialize_constructions_module_body() }
}

#[inline]
pub(crate) fn finalize_constructions_module() {
    unsafe { finalize_constructions_module_body() }
}

#[inline]
pub(crate) fn lean_initialize_runtime_for_plugin(_: u8) -> *mut LeanObject {
    unsafe {
        initialize_runtime_module_body();
        lean_io_result_mk_ok(lean_box(0))
    }
}

#[inline]
pub(crate) fn run_thread_finalizers() {
    unsafe { run_thread_finalizers_internal() }
}

#[inline]
pub(crate) fn run_post_thread_finalizers() {
    unsafe { run_post_thread_finalizers_internal() }
}

#[inline]
pub(crate) fn delete_thread_finalizer_manager() {
    unsafe { delete_thread_finalizer_manager_internal() }
}

#[inline]
pub fn lean_initialize() {
    unsafe {
        save_stack_info(true);
        initialize_util_module();
        let builtin = 1u8;
        consume_io_result("initialize_Init", initialize_Init(builtin));
        consume_io_result("initialize_Std", initialize_Std(builtin));
        consume_io_result("initialize_Lean", initialize_Lean(builtin));
        initialize_kernel_module();
        initialize_library_core_module();
        initialize_library_module();
        initialize_constructions_module();
    }
}

pub fn initialize_options() {
    unsafe {
        VERBOSE_OPT = mk_name("verbose");
        MAX_MEMORY_OPT = mk_name("max_memory");
        TIMEOUT_OPT = mk_name("timeout");
        lean_mark_persistent(VERBOSE_OPT.obj);
        lean_mark_persistent(MAX_MEMORY_OPT.obj);
        lean_mark_persistent(TIMEOUT_OPT.obj);
    }
}

pub fn finalize_options() {
    unsafe {
        if !VERBOSE_OPT.obj.is_null() {
            lean_dec(VERBOSE_OPT.obj);
            VERBOSE_OPT.obj = ptr::null_mut();
        }
        if !MAX_MEMORY_OPT.obj.is_null() {
            lean_dec(MAX_MEMORY_OPT.obj);
            MAX_MEMORY_OPT.obj = ptr::null_mut();
        }
        if !TIMEOUT_OPT.obj.is_null() {
            lean_dec(TIMEOUT_OPT.obj);
            TIMEOUT_OPT.obj = ptr::null_mut();
        }
    }
}

pub unsafe fn mk_constructions_name_generator(
    result: *mut LeanNameGenerator,
) -> *mut LeanNameGenerator {
    lean_inc(CONSTRUCTIONS_FRESH.obj);
    result.write(LeanNameGenerator {
        prefix: CONSTRUCTIONS_FRESH,
        next_idx: 0,
    });
    result
}

pub fn initialize_constructions_util() {
    unsafe {
        CONSTRUCTIONS_FRESH = mk_name("_cnstr_fresh");
        lean_mark_persistent(CONSTRUCTIONS_FRESH.obj);
        lean_register_name_generator_prefix(CONSTRUCTIONS_FRESH.obj);
    }
}

pub fn finalize_constructions_util() {
    unsafe {
        if !CONSTRUCTIONS_FRESH.obj.is_null() {
            lean_dec(CONSTRUCTIONS_FRESH.obj);
            CONSTRUCTIONS_FRESH.obj = ptr::null_mut();
        }
    }
}

pub unsafe fn get_init_fn_name_for(
    result: *mut LeanOptionalName,
    env: *const LeanName,
    name: *const LeanName,
) -> *mut LeanOptionalName {
    let env = (*env).obj;
    let name = (*name).obj;
    lean_inc(env);
    lean_inc(name);
    let value = lean_get_init_fn_name_for(env, name);
    if lean_is_scalar(value) {
        result.write(LeanOptionalName {
            some: false,
            value: LeanName { obj: lean_box(0) },
        });
    } else {
        let name = lean_ctor_get(value, 0);
        lean_inc(name);
        lean_dec(value);
        result.write(LeanOptionalName {
            some: true,
            value: LeanName { obj: name },
        });
    }
    result
}

#[inline]
pub(crate) fn lean_name_generator_tmp_prefix() -> *mut LeanObject {
    let guard = NAME_GENERATOR_STATE.lock().unwrap();
    guard.as_ref().map_or(ptr::null_mut(), |state| {
        unsafe {
            lean_inc(state.tmp_prefix);
        }
        state.tmp_prefix
    })
}

#[inline]
pub(crate) unsafe fn lean_register_name_generator_prefix(n: *mut LeanObject) {
    let mut guard = NAME_GENERATOR_STATE.lock().unwrap();
    let state = guard
        .as_mut()
        .expect("name generator registry is not initialized");
    assert!(!name_contains_registered_prefix(state, n));
    lean_inc(n);
    state.prefixes.push(n);
}

#[inline]
pub(crate) unsafe fn lean_uses_name_generator_prefix(n: *mut LeanObject) -> bool {
    let guard = NAME_GENERATOR_STATE.lock().unwrap();
    let Some(state) = guard.as_ref() else {
        return false;
    };
    name_uses_registered_prefix(state, n)
}

pub fn initialize_name_generator() {
    unsafe {
        let c_str = std::ffi::CString::new("_uniq").expect("static string has no NULs");
        let string = lean_mk_string(c_str.as_ptr());
        let tmp = lean_name_mk_string(lean_box(0), string);
        lean_mark_persistent(tmp);
        let mut guard = NAME_GENERATOR_STATE.lock().unwrap();
        let state = NameGeneratorState {
            tmp_prefix: tmp,
            prefixes: vec![tmp],
        };
        *guard = Some(state);
    }
}

pub fn initialize_name() {
    INTERNAL_UNIQUE_NAME_ID.store(0, Ordering::Relaxed);
}


#[inline]
pub(crate) fn lean_name_next_internal_unique_id() -> c_uint {
    INTERNAL_UNIQUE_NAME_ID.fetch_add(1, Ordering::Relaxed)
}

pub fn finalize_name_generator() {
    let mut guard = NAME_GENERATOR_STATE.lock().unwrap();
    if let Some(state) = guard.take() {
        for prefix in state.prefixes {
            unsafe { lean_dec(prefix) };
        }
    }
}

pub fn get_verbose_opt_name() -> *const LeanName {
    core::ptr::addr_of!(VERBOSE_OPT)
}

pub fn get_max_memory_opt_name() -> *const LeanName {
    core::ptr::addr_of!(MAX_MEMORY_OPT)
}

pub fn get_timeout_opt_name() -> *const LeanName {
    core::ptr::addr_of!(TIMEOUT_OPT)
}

pub unsafe fn get_verbose(opts: *const LeanOptions) -> bool {
    let opts = (*opts).obj;
    let name = (*get_verbose_opt_name()).obj;
    lean_inc(opts);
    lean_inc(name);
    lean_options_get_bool(opts, name, true)
}

pub unsafe fn options_ctor_c1(this: *mut LeanOptions) {
    (*this).obj = lean_options_get_empty(lean_box(0));
}

pub unsafe fn options_ctor_c2(this: *mut LeanOptions) {
    options_ctor_c1(this);
}

pub unsafe fn options_get_bool(
    this: *const LeanOptions,
    name: *const LeanName,
    default_value: bool,
) -> bool {
    let opts = (*this).obj;
    let name = (*name).obj;
    lean_inc(opts);
    lean_inc(name);
    lean_options_get_bool(opts, name, default_value)
}

pub unsafe fn options_update(
    this: *const LeanOptions,
    name: *const LeanName,
    value: bool,
) -> LeanOptions {
    let opts = (*this).obj;
    let name = (*name).obj;
    lean_inc(opts);
    lean_inc(name);
    LeanOptions {
        obj: lean_options_update_bool(opts, name, value),
    }
}

pub unsafe fn get_profiler(opts: *const LeanOptions) -> bool {
    let opts = (*opts).obj;
    lean_inc(opts);
    lean_get_profiler(opts) != 0
}

pub unsafe fn get_profiling_threshold(opts: *const LeanOptions) -> f64 {
    let opts = (*opts).obj;
    lean_inc(opts);
    lean_get_profiler_threshold(opts)
}



#[inline]
pub(crate) fn lean_internal_get_default_verbose(_: *mut LeanObject) -> u8 {
    true as u8
}

#[inline]
pub(crate) unsafe fn lean_internal_get_default_options(_: *mut LeanObject) -> *mut LeanObject {
    let mut opts = lean_options_get_empty(lean_box(0));
    if env_flag(env!("LEAN_RUST_IS_STAGE0")) != 0 {
        let updates = [
            (["debug", "proofAsSorry"].as_slice(), false),
            (["debug", "terminalTacticsAsSorry"].as_slice(), false),
            (["interpreter", "prefer_native"].as_slice(), false),
            (["internal", "parseQuotWithCurrentStage"].as_slice(), true),
            (["quotPrecheck"].as_slice(), true),
            (["pp", "rawOnError"].as_slice(), true),
        ];
        for (components, value) in updates {
            let name = mk_name_path(components);
            opts = lean_options_update_bool(opts, name.obj, value);
        }
    }
    opts
}

#[inline]
pub fn lean_finalize() {
    run_thread_finalizers();
    run_post_thread_finalizers();
    delete_thread_finalizer_manager();
}

#[inline]
pub(crate) unsafe fn lean_system_platform_nbits(_: *mut LeanObject) -> *mut LeanObject {
    lean_box(core::mem::size_of::<*const u8>() * 8)
}

#[inline]
pub(crate) fn lean_system_platform_windows(_: *mut LeanObject) -> u8 {
    cfg!(target_os = "windows") as u8
}

#[inline]
pub(crate) fn lean_system_platform_osx(_: *mut LeanObject) -> u8 {
    cfg!(target_os = "macos") as u8
}

#[inline]
pub(crate) fn lean_system_platform_emscripten(_: *mut LeanObject) -> u8 {
    cfg!(target_os = "emscripten") as u8
}

static INITIALIZING: core::sync::atomic::AtomicBool = core::sync::atomic::AtomicBool::new(true);

#[inline]
pub(crate) fn lean_io_mark_end_initialization() {
    INITIALIZING.store(false, Ordering::Relaxed);
}

#[inline]
pub(crate) fn lean_io_initializing() -> u8 {
    INITIALIZING.load(Ordering::Relaxed) as u8
}

#[inline]
pub(crate) unsafe fn lean_get_githash(_: *mut LeanObject) -> *mut LeanObject {
    lean_mk_string(concat!(env!("LEAN_RUST_GITHASH"), "\0").as_ptr() as *const c_char)
}

#[inline]
pub(crate) fn lean_internal_has_llvm_backend(_: *mut LeanObject) -> u8 {
    env_flag(env!("LEAN_RUST_HAS_LLVM"))
}

#[inline]
pub(crate) fn lean_internal_has_address_sanitizer(_: *mut LeanObject) -> u8 {
    env_flag(env!("LEAN_RUST_HAS_ADDRESS_SANITIZER"))
}

#[inline]
pub(crate) fn lean_internal_is_multi_thread(_: *mut LeanObject) -> u8 {
    env_flag(env!("LEAN_RUST_MULTI_THREAD"))
}

#[inline]
pub(crate) fn lean_internal_is_debug(_: *mut LeanObject) -> u8 {
    env_flag(env!("LEAN_RUST_DEBUG"))
}

#[inline]
pub(crate) unsafe fn lean_internal_get_build_type(_: *mut LeanObject) -> *mut LeanObject {
    lean_mk_string(concat!(env!("LEAN_RUST_BUILD_TYPE"), "\0").as_ptr() as *const c_char)
}

#[inline]
pub(crate) unsafe fn lean_get_leanc_extra_flags(_: *mut LeanObject) -> *mut LeanObject {
    lean_mk_string(concat!(env!("LEAN_RUST_LEANC_EXTRA_CC_FLAGS"), "\0").as_ptr() as *const c_char)
}

#[inline]
pub(crate) unsafe fn lean_get_leanc_internal_flags(_: *mut LeanObject) -> *mut LeanObject {
    lean_mk_string(concat!(env!("LEAN_RUST_LEANC_INTERNAL_FLAGS"), "\0").as_ptr() as *const c_char)
}

#[inline]
pub(crate) unsafe fn lean_get_linker_flags(link_static: u8) -> *mut LeanObject {
    if link_static != 0 {
        lean_mk_string(
            concat!(
                env!("LEAN_RUST_LEANC_STATIC_LINKER_FLAGS"),
                " ",
                env!("LEAN_RUST_LEAN_EXTRA_LINKER_FLAGS"),
                "\0"
            )
            .as_ptr() as *const c_char,
        )
    } else {
        lean_mk_string(
            concat!(
                env!("LEAN_RUST_LEANC_SHARED_LINKER_FLAGS"),
                " ",
                env!("LEAN_RUST_LEAN_EXTRA_LINKER_FLAGS_WITHOUT_RUST_ARCHIVE"),
                "\0"
            )
            .as_ptr() as *const c_char,
        )
    }
}

#[inline]
pub(crate) unsafe fn lean_get_internal_linker_flags(_: *mut LeanObject) -> *mut LeanObject {
    lean_mk_string(
        concat!(env!("LEAN_RUST_LEANC_INTERNAL_LINKER_FLAGS"), "\0").as_ptr() as *const c_char,
    )
}

type LeanMapForeachFn = extern "C" fn(*mut LeanObject, *mut LeanObject, *mut c_void);

unsafe fn lean_map_foreach_rbmap(m: *mut LeanObject, cb: LeanMapForeachFn, ctx: *mut c_void) {
    if lean_is_scalar(m) {
        return;
    }
    lean_map_foreach_rbmap(lean_ctor_get(m, 0), cb, ctx);
    cb(lean_ctor_get(m, 1), lean_ctor_get(m, 2), ctx);
    lean_map_foreach_rbmap(lean_ctor_get(m, 3), cb, ctx);
}

unsafe fn lean_map_foreach_entry(e: *mut LeanObject, cb: LeanMapForeachFn, ctx: *mut c_void) {
    match lean_obj_tag(e) {
        0 => cb(lean_ctor_get(e, 0), lean_ctor_get(e, 1), ctx),
        1 => lean_map_foreach_node(lean_ctor_get(e, 0), cb, ctx),
        _ => {}
    }
}

unsafe fn lean_map_foreach_collision(
    ks: *mut LeanObject,
    vs: *mut LeanObject,
    cb: LeanMapForeachFn,
    ctx: *mut c_void,
) {
    let size = lean_array_size(ks);
    debug_assert_eq!(size, lean_array_size(vs));
    for i in 0..size {
        cb(lean_array_get_core(ks, i), lean_array_get_core(vs, i), ctx);
    }
}

unsafe fn lean_map_foreach_entries(es: *mut LeanObject, cb: LeanMapForeachFn, ctx: *mut c_void) {
    for i in 0..lean_array_size(es) {
        lean_map_foreach_entry(lean_array_get_core(es, i), cb, ctx);
    }
}

unsafe fn lean_map_foreach_node(n: *mut LeanObject, cb: LeanMapForeachFn, ctx: *mut c_void) {
    if lean_ptr_tag(n) == 0 {
        lean_map_foreach_entries(lean_ctor_get(n, 0), cb, ctx);
    } else {
        lean_map_foreach_collision(lean_ctor_get(n, 0), lean_ctor_get(n, 1), cb, ctx);
    }
}

unsafe fn lean_map_foreach_hashmap(m: *mut LeanObject, cb: LeanMapForeachFn, ctx: *mut c_void) {
    let buckets = lean_ctor_get(m, 1);
    for i in 0..lean_array_size(buckets) {
        let mut lst = lean_array_get_core(buckets, i);
        while !lean_is_scalar(lst) {
            cb(lean_ctor_get(lst, 0), lean_ctor_get(lst, 1), ctx);
            lst = lean_ctor_get(lst, 2);
        }
    }
}

unsafe fn lean_map_foreach_smap(m: *mut LeanObject, cb: LeanMapForeachFn, ctx: *mut c_void) {
    lean_map_foreach_hashmap(lean_ctor_get(m, 0), cb, ctx);
    lean_map_foreach_node(lean_ctor_get(m, 1), cb, ctx);
}

#[inline]
pub(crate) unsafe fn lean_rbmap_foreach(
    m: *mut LeanObject,
    cb: LeanMapForeachFn,
    ctx: *mut c_void,
) {
    lean_map_foreach_rbmap(m, cb, ctx);
}

#[inline]
pub(crate) unsafe fn lean_phashmap_foreach(
    m: *mut LeanObject,
    cb: LeanMapForeachFn,
    ctx: *mut c_void,
) {
    lean_map_foreach_node(lean_ctor_get(m, 0), cb, ctx);
}

#[inline]
pub(crate) unsafe fn lean_hashmap_foreach(
    m: *mut LeanObject,
    cb: LeanMapForeachFn,
    ctx: *mut c_void,
) {
    lean_map_foreach_hashmap(m, cb, ctx);
}

#[inline]
pub(crate) unsafe fn lean_smap_foreach(
    m: *mut LeanObject,
    cb: LeanMapForeachFn,
    ctx: *mut c_void,
) {
    lean_map_foreach_smap(m, cb, ctx);
}

#[inline]
pub(crate) unsafe fn lean_smap_foreach_test(m: *mut LeanObject) -> *mut LeanObject {
    extern "C" fn print_entry(k: *mut LeanObject, v: *mut LeanObject, _: *mut c_void) {
        // The playground test uses boxed natural numbers.
        let key = unsafe { lean_unbox(k) };
        let value = unsafe { lean_unbox(v) };
        use std::io::{self, Write};
        let mut out = io::stdout().lock();
        let _ = out.write_fmt(format_args!(">> {key} |-> {value}\n"));
    }

    lean_map_foreach_smap(m, print_entry, core::ptr::null_mut());
    lean_box(0)
}

#[inline]
pub(crate) unsafe fn lean_io_timeit(
    msg: *mut LeanObject,
    fn_obj: *mut LeanObject,
) -> *mut LeanObject {
    use std::ffi::CStr;
    use std::io::{self, Write};
    use std::time::Instant;

    let start = Instant::now();
    let result = lean_apply_1(fn_obj, lean_box(0));
    let elapsed = start.elapsed().as_secs_f64();

    let prefix = CStr::from_ptr(lean_string_cstr(msg)).to_string_lossy();
    let mut stderr = io::stderr().lock();
    let _ = if elapsed < 1.0 {
        stderr.write_fmt(format_args!("{prefix} {:.3}ms\n", elapsed * 1000.0))
    } else {
        stderr.write_fmt(format_args!("{prefix} {:.3}s\n", elapsed))
    };
    result
}

#[inline]
pub(crate) unsafe fn lean_io_get_num_heartbeats() -> *mut LeanObject {
    lean_uint64_to_nat_rust(lean_get_num_heartbeats())
}

#[inline]
pub(crate) unsafe fn lean_io_set_heartbeats(count: *mut LeanObject) -> *mut LeanObject {
    lean_set_heartbeats(lean_uint64_of_nat_rust(count));
    lean_dec(count);
    lean_box(0)
}

#[inline]
pub(crate) unsafe fn lean_io_mono_ms_now() -> *mut LeanObject {
    use std::sync::OnceLock;
    use std::time::Instant;

    static START: OnceLock<Instant> = OnceLock::new();
    let start = START.get_or_init(Instant::now);
    lean_uint64_to_nat_rust(start.elapsed().as_millis() as u64)
}

#[inline]
pub(crate) unsafe fn lean_io_mono_nanos_now() -> *mut LeanObject {
    use std::sync::OnceLock;
    use std::time::Instant;

    static START: OnceLock<Instant> = OnceLock::new();
    let start = START.get_or_init(Instant::now);
    lean_uint64_to_nat_rust(start.elapsed().as_nanos() as u64)
}

#[inline]
pub(crate) unsafe fn lean_get_current_time() -> *mut LeanObject {
    use std::time::{SystemTime, UNIX_EPOCH};

    let now = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap_or_default();
    let secs = lean_int64_to_int_rust(now.as_secs() as i64);
    let nanos = lean_int64_to_int_rust(now.subsec_nanos() as i64);
    let mut fields = [secs, nanos];
    let timestamp = lean_runtime_mk_cnstr(0, 2, fields.as_mut_ptr(), 0);
    lean_io_result_mk_ok(timestamp)
}

#[inline]
pub(crate) unsafe fn lean_io_getenv(env_var: *mut LeanObject) -> *mut LeanObject {
    use std::ffi::{CStr, CString};

    let name_ptr = lean_string_cstr(env_var);
    if CStr::from_ptr(name_ptr).to_bytes().len() != lean_string_size(env_var) - 1 {
        return lean_box(0);
    }

    let Ok(name) = CStr::from_ptr(name_ptr).to_str() else {
        return lean_box(0);
    };

    match std::env::var(name) {
        Ok(value) => {
            let cstr = CString::new(value).expect("environment values must not contain NUL bytes");
            let mut fields = [lean_mk_string(cstr.as_ptr())];
            lean_runtime_mk_cnstr(1, 1, fields.as_mut_ptr(), 0)
        }
        Err(_) => lean_box(0),
    }
}

#[inline]
pub(crate) unsafe fn lean_byteslice_beq(a: *mut LeanObject, b: *mut LeanObject) -> u8 {
    if ptr::eq(a, b) {
        return 1;
    }

    let bytearray_a = lean_ctor_get(a, 0);
    let start_a = lean_unbox(lean_ctor_get(a, 1));
    let end_a = lean_unbox(lean_ctor_get(a, 2));

    let bytearray_b = lean_ctor_get(b, 0);
    let start_b = lean_unbox(lean_ctor_get(b, 1));
    let end_b = lean_unbox(lean_ctor_get(b, 2));

    let size_a = end_a - start_a;
    let size_b = end_b - start_b;

    if size_a != size_b {
        return 0;
    }

    if size_a == 0 {
        return 1;
    }

    let ptr_a = lean_sarray_cptr(bytearray_a).add(start_a);
    let ptr_b = lean_sarray_cptr(bytearray_b).add(start_b);
    for offset in 0..size_a {
        if *ptr_a.add(offset) != *ptr_b.add(offset) {
            return 0;
        }
    }
    1
}

#[inline]
pub unsafe fn lean_runtime_mk_cnstr(
    tag: c_uint,
    num_objs: c_uint,
    objs: *mut *mut LeanObject,
    scalar_size: c_uint,
) -> *mut LeanObject {
    let obj = lean_runtime_alloc_ctor(tag, num_objs, scalar_size);
    for index in 0..num_objs as Size {
        let val = objs.add(index).read();
        lean_runtime_ctor_set(obj, index as c_uint, val);
    }
    obj
}

#[inline]
pub(crate) unsafe fn lean_io_result_mk_ok(value: *mut LeanObject) -> *mut LeanObject {
    let mut fields = [value];
    lean_runtime_mk_cnstr(0, 1, fields.as_mut_ptr(), 0)
}

#[inline]
pub(crate) unsafe fn lean_io_result_mk_error(error: *mut LeanObject) -> *mut LeanObject {
    let mut fields = [error];
    lean_runtime_mk_cnstr(1, 1, fields.as_mut_ptr(), 0)
}

unsafe fn lean_uint64_to_nat_rust(value: u64) -> *mut LeanObject {
    if value <= usize::MAX as u64 >> 1 {
        lean_box(value as usize)
    } else {
        runtime_object_nat_int_impl::lean_big_uint64_to_nat(value)
    }
}

unsafe fn lean_int64_to_int_rust(value: i64) -> *mut LeanObject {
    runtime_object_nat_int_impl::lean_big_int64_to_int(value)
}

unsafe fn lean_uint64_of_nat_rust(value: *mut LeanObject) -> u64 {
    if lean_is_scalar(value) {
        lean_unbox(value) as u64
    } else {
        runtime_object_nat_int_impl::lean_uint64_of_big_nat(value)
    }
}

#[inline]
pub(crate) fn lean_runtime_is_utf8_next(byte: c_uchar) -> bool {
    byte & 0xC0 == 0x80
}

#[inline]
pub(crate) fn lean_runtime_get_utf8_size(byte: c_uchar) -> c_uint {
    utf8_size(byte) as c_uint
}

#[inline]
pub(crate) unsafe fn lean_utf8_strlen(mut text: *const c_char) -> Size {
    let mut length = 0;
    while *text != 0 {
        let size = utf8_size(*text as c_uchar);
        length += 1;
        text = text.add(size);
    }
    length
}

#[inline]
pub(crate) unsafe fn lean_utf8_n_strlen(text: *const c_char, byte_size: Size) -> Size {
    let mut length = 0;
    let mut offset = 0;
    while offset < byte_size {
        let size = utf8_size(*text.add(offset) as c_uchar);
        length += 1;
        offset += size;
    }
    length
}

#[inline]
pub(crate) unsafe fn lean_runtime_utf8_char_pos(
    mut text: *const c_char,
    mut char_idx: Size,
    out_pos: *mut Size,
) -> bool {
    let mut pos = 0;
    while *text != 0 {
        if char_idx == 0 {
            *out_pos = pos;
            return true;
        }
        char_idx -= 1;
        let size = utf8_size(*text as c_uchar);
        pos += size;
        text = text.add(size);
    }
    false
}

#[inline]
pub(crate) unsafe fn lean_runtime_get_utf8_last_char(mut text: *const c_char) -> *const c_char {
    let mut last = text;
    while *text != 0 {
        last = text;
        text = text.add(utf8_size(*text as c_uchar));
    }
    last
}

#[inline]
pub(crate) unsafe fn lean_runtime_utf8_to_unicode(
    begin: *const c_uchar,
    end: *const c_uchar,
) -> c_uint {
    if begin == end {
        return 0;
    }

    let mut it = begin;
    let mut byte = *it as c_uint;
    it = it.add(1);
    if byte < 0x80 {
        return byte;
    }

    let mask = (1u32 << 6) - 1;
    let mut high_mask = mask;
    let mut shift = 0;
    let mut num_bits = 0;
    let mut result = 0;
    while byte & 0xC0 == 0xC0 {
        byte = (byte << 1) & 0xff;
        num_bits += 6;
        high_mask >>= 1;
        shift += 1;
        result <<= 6;
        if it == end {
            return 0;
        }
        result |= (*it as c_uint) & mask;
        it = it.add(1);
    }
    result | (((byte >> shift) & high_mask) << num_bits)
}

#[inline]
pub(crate) unsafe fn lean_runtime_get_utf8_first_byte_size(
    byte: c_uchar,
    out_size: *mut c_uint,
) -> bool {
    let size = if byte & 0x80 == 0 {
        1
    } else if byte & 0xe0 == 0xc0 {
        2
    } else if byte & 0xf0 == 0xe0 {
        3
    } else if byte & 0xf8 == 0xf0 {
        4
    } else {
        return false;
    };
    *out_size = size;
    true
}

#[inline]
pub(crate) unsafe fn lean_runtime_next_utf8(
    text: *const c_char,
    size: Size,
    pos: *mut Size,
) -> c_uint {
    let i = *pos;
    let byte = *text.add(i) as c_uchar as c_uint;
    if byte & 0x80 == 0 {
        *pos = i + 1;
        return byte;
    }

    if byte & 0xe0 == 0xc0 && i + 1 < size {
        let b1 = *text.add(i + 1) as c_uchar as c_uint;
        let scalar = ((byte & 0x1f) << 6) | (b1 & 0x3f);
        if scalar >= 0x80 {
            *pos = i + 2;
            return scalar;
        }
    }

    if byte & 0xf0 == 0xe0 && i + 2 < size {
        let b1 = *text.add(i + 1) as c_uchar as c_uint;
        let b2 = *text.add(i + 2) as c_uchar as c_uint;
        let scalar = ((byte & 0x0f) << 12) | ((b1 & 0x3f) << 6) | (b2 & 0x3f);
        if scalar >= 0x800 && !(0xD800..=0xDFFF).contains(&scalar) {
            *pos = i + 3;
            return scalar;
        }
    }

    if byte & 0xf8 == 0xf0 && i + 3 < size {
        let b1 = *text.add(i + 1) as c_uchar as c_uint;
        let b2 = *text.add(i + 2) as c_uchar as c_uint;
        let b3 = *text.add(i + 3) as c_uchar as c_uint;
        let scalar = ((byte & 0x07) << 18) | ((b1 & 0x3f) << 12) | ((b2 & 0x3f) << 6) | (b3 & 0x3f);
        if (0x10000..=0x10FFFF).contains(&scalar) {
            *pos = i + 4;
            return scalar;
        }
    }

    *pos = i + 1;
    byte
}

#[inline]
pub(crate) unsafe fn lean_runtime_validate_utf8_one(
    text: *const c_uchar,
    size: Size,
    pos: *mut Size,
) -> bool {
    let i = *pos;
    let byte = *text.add(i) as c_uint;
    if byte & 0x80 == 0 {
        *pos = i + 1;
        return true;
    }

    if byte & 0xe0 == 0xc0 {
        if i + 1 >= size {
            return false;
        }
        let b1 = *text.add(i + 1) as c_uint;
        if b1 & 0xc0 != 0x80 {
            return false;
        }
        let scalar = ((byte & 0x1f) << 6) | (b1 & 0x3f);
        if scalar < 0x80 {
            return false;
        }
        *pos = i + 2;
        return true;
    }

    if byte & 0xf0 == 0xe0 {
        if i + 2 >= size {
            return false;
        }
        let b1 = *text.add(i + 1) as c_uint;
        let b2 = *text.add(i + 2) as c_uint;
        if b1 & 0xc0 != 0x80 || b2 & 0xc0 != 0x80 {
            return false;
        }
        let scalar = ((byte & 0x0f) << 12) | ((b1 & 0x3f) << 6) | (b2 & 0x3f);
        if scalar < 0x800 || (0xD800..=0xDFFF).contains(&scalar) {
            return false;
        }
        *pos = i + 3;
        return true;
    }

    if byte & 0xf8 == 0xf0 {
        if i + 3 >= size {
            return false;
        }
        let b1 = *text.add(i + 1) as c_uint;
        let b2 = *text.add(i + 2) as c_uint;
        let b3 = *text.add(i + 3) as c_uint;
        if b1 & 0xc0 != 0x80 || b2 & 0xc0 != 0x80 || b3 & 0xc0 != 0x80 {
            return false;
        }
        let scalar = ((byte & 0x07) << 18) | ((b1 & 0x3f) << 12) | ((b2 & 0x3f) << 6) | (b3 & 0x3f);
        if !(0x10000..=0x10FFFF).contains(&scalar) {
            return false;
        }
        *pos = i + 4;
        return true;
    }

    false
}

#[inline]
pub(crate) unsafe fn lean_runtime_validate_utf8(
    text: *const c_uchar,
    size: Size,
    pos: *mut Size,
    chars: *mut Size,
) -> bool {
    while *pos < size {
        if !lean_runtime_validate_utf8_one(text, size, pos) {
            return false;
        }
        *chars += 1;
    }
    true
}

#[inline]
pub(crate) unsafe fn lean_runtime_push_unicode_scalar(
    dst: *mut c_char,
    code: c_uint,
) -> c_uint {
    const TAG_CONT: c_uint = 0b10000000;
    const TAG_TWO_B: c_uint = 0b11000000;
    const TAG_THREE_B: c_uint = 0b11100000;
    const TAG_FOUR_B: c_uint = 0b11110000;

    let bytes = if code < 0x80 {
        [code, 0, 0, 0]
    } else if code < 0x800 {
        [
            ((code >> 6) & 0x1F) | TAG_TWO_B,
            (code & 0x3F) | TAG_CONT,
            0,
            0,
        ]
    } else if code < 0x10000 {
        [
            ((code >> 12) & 0x0F) | TAG_THREE_B,
            ((code >> 6) & 0x3F) | TAG_CONT,
            (code & 0x3F) | TAG_CONT,
            0,
        ]
    } else {
        [
            ((code >> 18) & 0x07) | TAG_FOUR_B,
            ((code >> 12) & 0x3F) | TAG_CONT,
            ((code >> 6) & 0x3F) | TAG_CONT,
            (code & 0x3F) | TAG_CONT,
        ]
    };

    let len = if code < 0x80 {
        1
    } else if code < 0x800 {
        2
    } else if code < 0x10000 {
        3
    } else {
        4
    };
    for i in 0..len {
        *dst.add(i) = bytes[i] as c_char;
    }
    len as c_uint
}

#[inline]
pub(crate) unsafe fn lean_runtime_hash_str(len: Size, text: *const c_uchar, seed: u64) -> u64 {
    const M: u64 = 0xc6a4a7935bd1e995;
    const R: u32 = 47;

    let mut hash = seed ^ ((len as u64).wrapping_mul(M));
    let mut offset = 0;
    let end = (len / 8) * 8;

    while offset != end {
        let mut key = ptr::read_unaligned(text.add(offset) as *const u64);
        offset += 8;

        key = key.wrapping_mul(M);
        key ^= key >> R;
        key = key.wrapping_mul(M);

        hash ^= key;
        hash = hash.wrapping_mul(M);
    }

    let tail = text.add(offset);
    match len & 7 {
        7 => {
            hash ^= (*tail.add(6) as u64) << 48;
            hash ^= (*tail.add(5) as u64) << 40;
            hash ^= (*tail.add(4) as u64) << 32;
            hash ^= (*tail.add(3) as u64) << 24;
            hash ^= (*tail.add(2) as u64) << 16;
            hash ^= (*tail.add(1) as u64) << 8;
            hash ^= *tail as u64;
            hash = hash.wrapping_mul(M);
        }
        6 => {
            hash ^= (*tail.add(5) as u64) << 40;
            hash ^= (*tail.add(4) as u64) << 32;
            hash ^= (*tail.add(3) as u64) << 24;
            hash ^= (*tail.add(2) as u64) << 16;
            hash ^= (*tail.add(1) as u64) << 8;
            hash ^= *tail as u64;
            hash = hash.wrapping_mul(M);
        }
        5 => {
            hash ^= (*tail.add(4) as u64) << 32;
            hash ^= (*tail.add(3) as u64) << 24;
            hash ^= (*tail.add(2) as u64) << 16;
            hash ^= (*tail.add(1) as u64) << 8;
            hash ^= *tail as u64;
            hash = hash.wrapping_mul(M);
        }
        4 => {
            hash ^= (*tail.add(3) as u64) << 24;
            hash ^= (*tail.add(2) as u64) << 16;
            hash ^= (*tail.add(1) as u64) << 8;
            hash ^= *tail as u64;
            hash = hash.wrapping_mul(M);
        }
        3 => {
            hash ^= (*tail.add(2) as u64) << 16;
            hash ^= (*tail.add(1) as u64) << 8;
            hash ^= *tail as u64;
            hash = hash.wrapping_mul(M);
        }
        2 => {
            hash ^= (*tail.add(1) as u64) << 8;
            hash ^= *tail as u64;
            hash = hash.wrapping_mul(M);
        }
        1 => {
            hash ^= *tail as u64;
            hash = hash.wrapping_mul(M);
        }
        _ => {}
    }

    hash ^= hash >> R;
    hash = hash.wrapping_mul(M);
    hash ^= hash >> R;
    hash
}

#[cfg(not(feature = "std"))]
#[panic_handler]
fn panic(_: &PanicInfo<'_>) -> ! {
    loop {}
}
