/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

#![cfg_attr(not(feature = "std"), no_std)]
#![allow(
    clashing_extern_declarations,
    non_upper_case_globals,
    private_interfaces,
    static_mut_refs,
    unused,
    unused_attributes
)]

use core::ffi::{c_char, c_int, c_long, c_uchar, c_uint, c_void, CStr};
use core::sync::atomic::{AtomicBool, AtomicI32, AtomicU32, Ordering};
use core::ptr;
#[cfg(not(feature = "std"))]
use core::panic::PanicInfo;

pub mod generated_abi;

type Size = usize;

pub(crate) unsafe fn cstr_lossy_to_string(ptr: *const c_char) -> String {
    if ptr.is_null() {
        return String::new();
    }
    let bytes = CStr::from_ptr(ptr).to_bytes();
    let mut out = String::with_capacity(bytes.len());
    for &b in bytes {
        if b.is_ascii() {
            out.push(b as char);
        } else {
            out.push('\u{FFFD}');
        }
    }
    out
}

#[cfg(feature = "std")]
pub(crate) mod env_caches {
    use std::sync::OnceLock;
    pub(crate) static LEAN_TRACE_RC: OnceLock<bool> = OnceLock::new();
    pub(crate) static LEAN_DEBUG_ARRAY_SIZES: OnceLock<bool> = OnceLock::new();
    pub(crate) static LEAN_DEBUG_NAT_DEC: OnceLock<bool> = OnceLock::new();
    pub(crate) static LEAN_DEBUG_ARRAY_PUSH_RING: OnceLock<bool> = OnceLock::new();
    pub(crate) static LEAN_DEBUG_ARRAY_GET: OnceLock<bool> = OnceLock::new();
    pub(crate) static LEAN_DEBUG_ARRAY_USET: OnceLock<bool> = OnceLock::new();
    pub(crate) static LEAN_DEBUG_ARRAY_GET_SIZE_STACK: OnceLock<bool> = OnceLock::new();
    pub(crate) static LEAN_DEBUG_ARRAY_PUSH: OnceLock<bool> = OnceLock::new();
    pub(crate) static LEAN_TRACE_NAT_INT: OnceLock<bool> = OnceLock::new();
    pub(crate) static LEAN_TRACE_MARK_PERSISTENT: OnceLock<bool> = OnceLock::new();
    pub(crate) static LEAN_TRACE_MARK_MT: OnceLock<bool> = OnceLock::new();
    pub(crate) static LEAN_TRACE_OBJ_ONCE: OnceLock<bool> = OnceLock::new();
    pub(crate) static LEAN_TRACE_INIT: OnceLock<bool> = OnceLock::new();
}

#[cfg(feature = "std")]
macro_rules! get_env_var_cached {
    ("LEAN_TRACE_RC") => {
        *crate::env_caches::LEAN_TRACE_RC.get_or_init(|| std::env::var_os("LEAN_TRACE_RC").is_some())
    };
    ("LEAN_DEBUG_ARRAY_SIZES") => {
        *crate::env_caches::LEAN_DEBUG_ARRAY_SIZES.get_or_init(|| std::env::var_os("LEAN_DEBUG_ARRAY_SIZES").is_some())
    };
    ("LEAN_DEBUG_NAT_DEC") => {
        *crate::env_caches::LEAN_DEBUG_NAT_DEC.get_or_init(|| std::env::var_os("LEAN_DEBUG_NAT_DEC").is_some())
    };
    ("LEAN_DEBUG_ARRAY_PUSH_RING") => {
        *crate::env_caches::LEAN_DEBUG_ARRAY_PUSH_RING.get_or_init(|| std::env::var_os("LEAN_DEBUG_ARRAY_PUSH_RING").is_some())
    };
    ("LEAN_DEBUG_ARRAY_GET") => {
        *crate::env_caches::LEAN_DEBUG_ARRAY_GET.get_or_init(|| std::env::var_os("LEAN_DEBUG_ARRAY_GET").is_some())
    };
    ("LEAN_DEBUG_ARRAY_USET") => {
        *crate::env_caches::LEAN_DEBUG_ARRAY_USET.get_or_init(|| std::env::var_os("LEAN_DEBUG_ARRAY_USET").is_some())
    };
    ("LEAN_DEBUG_ARRAY_GET_SIZE_STACK") => {
        *crate::env_caches::LEAN_DEBUG_ARRAY_GET_SIZE_STACK.get_or_init(|| std::env::var_os("LEAN_DEBUG_ARRAY_GET_SIZE_STACK").is_some())
    };
    ("LEAN_DEBUG_ARRAY_PUSH") => {
        *crate::env_caches::LEAN_DEBUG_ARRAY_PUSH.get_or_init(|| std::env::var_os("LEAN_DEBUG_ARRAY_PUSH").is_some())
    };
    ("LEAN_TRACE_NAT_INT") => {
        *crate::env_caches::LEAN_TRACE_NAT_INT.get_or_init(|| std::env::var_os("LEAN_TRACE_NAT_INT").is_some())
    };
    ("LEAN_TRACE_MARK_PERSISTENT") => {
        *crate::env_caches::LEAN_TRACE_MARK_PERSISTENT.get_or_init(|| std::env::var_os("LEAN_TRACE_MARK_PERSISTENT").is_some())
    };
    ("LEAN_TRACE_MARK_MT") => {
        *crate::env_caches::LEAN_TRACE_MARK_MT.get_or_init(|| std::env::var_os("LEAN_TRACE_MARK_MT").is_some())
    };
    ("LEAN_TRACE_OBJ_ONCE") => {
        *crate::env_caches::LEAN_TRACE_OBJ_ONCE.get_or_init(|| std::env::var_os("LEAN_TRACE_OBJ_ONCE").is_some())
    };
    ("LEAN_TRACE_INIT") => {
        *crate::env_caches::LEAN_TRACE_INIT.get_or_init(|| std::env::var_os("LEAN_TRACE_INIT").is_some())
    };
    ($name:expr) => {
        compile_error!("Unsupported environment variable name")
    };
}

#[cfg(not(feature = "std"))]
macro_rules! get_env_var_cached {
    ($name:expr) => {
        compile_error!("Environment variables are not supported in no_std builds")
    };
}



extern "C" {
    #[link_name = "_ZN4lean5allocEm"]
    fn lean_alloc_export(size: Size) -> *mut u8;
    #[link_name = "_ZN4lean7deallocEPvm"]
    fn lean_dealloc_export(obj: *mut u8, size: Size);
    pub fn lean_mk_string(text: *const c_char) -> *mut LeanObject;
    fn lean_mk_io_user_error(msg: *mut LeanObject) -> *mut LeanObject;
    fn lean_mk_io_error_invalid_argument(errnum: u32, details: *mut LeanObject) -> *mut LeanObject;
    fn lean_alloc_object(size: Size) -> *mut LeanObject;
    fn lean_mk_embedded_nul_error_c(str: *mut LeanObject) -> *mut LeanObject;
    fn lean_array_push(array: *mut LeanObject, value: *mut LeanObject) -> *mut LeanObject;
    fn lean_register_external_class(
        finalize: Option<unsafe extern "C" fn(*mut c_void)>,
        foreach: Option<unsafe extern "C" fn(*mut c_void, *mut LeanObject)>,
    ) -> *mut LeanExternalClass;
    fn lean_runtime_alloc_external(
        class: *mut LeanExternalClass,
        data: *mut c_void,
    ) -> *mut LeanObject;
    fn lean_runtime_get_external_data(obj: *mut LeanObject) -> *mut c_void;
    fn lean_runtime_alloc_ctor(tag: c_uint, num_objs: c_uint, scalar_size: c_uint) -> *mut LeanObject;
    fn lean_runtime_ctor_set(obj: *mut LeanObject, index: c_uint, value: *mut LeanObject);
    fn lean_decode_uv_error(errnum: c_int, fname: *mut LeanObject) -> *mut LeanObject;
    fn lean_big_int64_to_int(n: i64) -> *mut LeanObject;
    fn lean_big_uint64_to_nat(n: u64) -> *mut LeanObject;
    fn lean_uint64_of_big_nat(n: *mut LeanObject) -> u64;
    fn lean_decode_io_error(errnum: c_int, fname: *mut LeanObject) -> *mut LeanObject;
    #[cfg(not(test))]
    fn lean_io_eprintln(msg: *mut LeanObject) -> *mut LeanObject;
    fn lean_io_wrap_handle_c(fp: *mut c_void) -> *mut LeanObject;
    fn lean_io_error_to_string(err: *mut LeanObject) -> *mut LeanObject;
    fn lean_options_get_empty(_: *mut LeanObject) -> *mut LeanObject;
    fn lean_options_get_bool(
        opts: *mut LeanObject,
        name: *mut LeanObject,
        default_value: u8,
    ) -> u8;
    fn lean_options_update_bool(
        opts: *mut LeanObject,
        name: *mut LeanObject,
        value: u8,
    ) -> *mut LeanObject;
    fn lean_get_init_fn_name_for(
        env: *mut LeanObject,
        name: *mut LeanObject,
    ) -> *mut LeanObject;
    fn lean_get_profiler(opts: *mut LeanObject) -> u8;
    fn lean_get_profiler_threshold(opts: *mut LeanObject) -> f64;


    #[link_name = "_ZN4lean16initialize_allocEv"]
    fn initialize_alloc();
    #[link_name = "_ZN4lean14finalize_allocEv"]
    fn finalize_alloc();
    #[link_name = "_ZN4lean17initialize_objectEv"]
    fn initialize_object();
    #[link_name = "_ZN4lean15finalize_objectEv"]
    fn finalize_object();
    #[link_name = "_ZN4lean13initialize_ioEv"]
    fn initialize_io();
    #[link_name = "_ZN4lean11finalize_ioEv"]
    fn finalize_io();
    #[link_name = "_ZN4lean17initialize_threadEv"]
    fn initialize_thread();
    #[link_name = "_ZN4lean15finalize_threadEv"]
    fn finalize_thread();
    // #[link_name = "_ZN4lean16initialize_asciiEv"]
    // fn initialize_ascii_impl();
    // #[link_name = "_ZN4lean14finalize_asciiEv"]
    // fn finalize_ascii_impl();
    #[link_name = "_ZN4lean20initialize_formatterEv"]
    fn initialize_formatter();
    #[link_name = "_ZN4lean18finalize_formatterEv"]
    fn finalize_formatter();
    #[link_name = "_ZN4lean16initialize_printEv"]
    fn initialize_print();
    #[link_name = "_ZN4lean14finalize_printEv"]
    fn finalize_print();
    #[link_name = "_ZN4lean14initialize_numEv"]
    fn initialize_num();
    #[link_name = "_ZN4lean12finalize_numEv"]
    fn finalize_num();
    #[link_name = "_ZN4lean21initialize_annotationEv"]
    fn initialize_annotation();
    #[link_name = "_ZN4lean19finalize_annotationEv"]
    fn finalize_annotation();
    #[link_name = "_ZN4lean23initialize_library_utilEv"]
    fn initialize_library_util();
    #[link_name = "_ZN4lean21finalize_library_utilEv"]
    fn finalize_library_util();
    #[link_name = "_ZN4lean20initialize_time_taskEv"]
    fn initialize_time_task();
    #[link_name = "_ZN4lean18finalize_time_taskEv"]
    fn finalize_time_task();
    #[link_name = "_ZN4lean16initialize_levelEv"]
    fn initialize_level();
    #[link_name = "_ZN4lean14finalize_levelEv"]
    fn finalize_level();
    #[link_name = "_ZN4lean15initialize_exprEv"]
    fn initialize_expr();
    #[link_name = "_ZN4lean13finalize_exprEv"]
    fn finalize_expr();
    #[link_name = "_ZN4lean22initialize_declarationEv"]
    fn initialize_declaration();
    #[link_name = "_ZN4lean20finalize_declarationEv"]
    fn finalize_declaration();
    #[link_name = "_ZN4lean23initialize_type_checkerEv"]
    fn initialize_type_checker();
    #[link_name = "_ZN4lean21finalize_type_checkerEv"]
    fn finalize_type_checker();
    #[link_name = "_ZN4lean22initialize_environmentEv"]
    fn initialize_environment();
    #[link_name = "_ZN4lean20finalize_environmentEv"]
    fn finalize_environment();
    #[link_name = "_ZN4lean20initialize_local_ctxEv"]
    fn initialize_local_ctx();
    #[link_name = "_ZN4lean18finalize_local_ctxEv"]
    fn finalize_local_ctx();
    #[link_name = "_ZN4lean20initialize_inductiveEv"]
    fn initialize_inductive();
    #[link_name = "_ZN4lean18finalize_inductiveEv"]
    fn finalize_inductive();
    #[link_name = "_ZN4lean15initialize_quotEv"]
    fn initialize_quot();
    #[link_name = "_ZN4lean13finalize_quotEv"]
    fn finalize_quot();
    #[link_name = "_ZN4lean16initialize_traceEv"]
    fn initialize_trace();
    #[link_name = "_ZN4lean14finalize_traceEv"]
    fn finalize_trace();
    fn initialize_Init(builtin: u8) -> *mut LeanObject;
    fn initialize_Std(builtin: u8) -> *mut LeanObject;
    fn initialize_Lean_Data(builtin: u8) -> *mut LeanObject;
    fn initialize_Lean(builtin: u8) -> *mut LeanObject;
    fn lean_enable_initializer_execution() -> *mut LeanObject;
}

#[repr(C)]
pub struct LeanObject {
    pub m_rc: i32,
    pub m_cs_sz: u16,
    pub m_other: u8,
    pub m_tag: u8,
}

/// A raw pointer wrapper that is Send. Used to move raw pointers into thread closures
/// when the pointer is known to be safe to use from another thread (e.g., protected by a mutex).
struct SendPtr<T>(*mut T);
unsafe impl<T> Send for SendPtr<T> {}
impl<T> SendPtr<T> {
    #[inline] fn get(&self) -> *mut T { self.0 }
}

#[repr(C)]
pub struct LeanExternalClass {
    pub m_finalize: unsafe extern "C" fn(*mut c_void),
    pub m_foreach: unsafe extern "C" fn(*mut c_void, *mut LeanObject),
}

#[repr(C)]
pub struct LeanExternalObject {
    pub m_header: LeanObject,
    pub m_class: *mut LeanExternalClass,
    pub m_data: *mut c_void,
}

#[repr(C)]
pub struct LeanThunkObject {
    pub m_header: LeanObject,
    pub m_value: *mut LeanObject,
    pub m_closure: *mut LeanObject,
}

#[repr(C)]
pub struct LeanRefObject {
    pub m_header: LeanObject,
    pub m_value: *mut LeanObject,
}

#[repr(C)]
struct LeanListCell {
    rc: AtomicU32,
    head: c_uint,
    tail: *mut LeanListCell,
}

#[repr(C)]
pub struct LeanArrayObject {
    pub m_header: LeanObject,
    pub m_size: Size,
    pub m_capacity: Size,
    // m_data: flexible array — not representable in Rust; accessed via pointer
    // arithmetic as (ptr as *mut *mut LeanObject).add(1) in practice.
    pub m_data: [*mut LeanObject; 0],
}

#[repr(C)]
pub struct LeanStringObject {
    pub m_header: LeanObject,
    pub m_size: Size,
    pub m_capacity: Size,
    pub m_length: Size,
    // m_data: flexible array — not representable in Rust; accessed via pointer
    // arithmetic as (ptr as *mut c_char).add(sizeof(LeanStringObject)) in practice.
    pub m_data: [c_char; 0],
}

#[repr(C)]
pub struct LeanScalarArray {
    pub m_header: LeanObject,
    pub m_size: Size,
    pub m_capacity: Size,
    // m_data: flexible array — not representable in Rust.
    pub m_data: [u8; 0],
}

#[repr(C)]
pub struct LeanPromiseObject {
    pub m_header: LeanObject,
    pub result: *mut LeanObject,
}

#[repr(C)]
pub struct LeanClosureObject {
    pub m_header: LeanObject,
    pub m_fun: *mut c_void,
    pub m_arity: u16,
    pub m_num_fixed: u16,
    // m_objs: flexible array — not representable in Rust.
    pub m_objs: [*mut LeanObject; 0],
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

static mut VERBOSE_OPT: LeanName = LeanName { obj: ptr::null_mut() };
static mut MAX_MEMORY_OPT: LeanName = LeanName { obj: ptr::null_mut() };
static mut TIMEOUT_OPT: LeanName = LeanName { obj: ptr::null_mut() };
static mut CONSTRUCTIONS_FRESH: LeanName = LeanName { obj: ptr::null_mut() };
static INTERNAL_UNIQUE_NAME_ID: std::sync::atomic::AtomicU32 =
    std::sync::atomic::AtomicU32::new(0);

struct NameGeneratorState {
    tmp_prefix: *mut LeanObject,
    prefixes: Vec<*mut LeanObject>,
}

unsafe impl Send for NameGeneratorState {}

static NAME_GENERATOR_STATE: std::sync::Mutex<Option<NameGeneratorState>> =
    std::sync::Mutex::new(None);

pub unsafe fn lean_unbox(obj: *const LeanObject) -> Size {
    (obj as Size) >> 1
}

pub unsafe fn lean_is_scalar(obj: *const LeanObject) -> bool {
    (obj as Size) & 1 == 1
}

pub unsafe fn lean_is_mt(obj: *const LeanObject) -> bool {
    (*obj).m_rc < 0
}

pub unsafe fn lean_is_st(obj: *const LeanObject) -> bool {
    (*obj).m_rc > 0
}

pub unsafe fn lean_is_persistent(obj: *const LeanObject) -> bool {
    (*obj).m_rc == 0
}

pub unsafe fn lean_has_rc(obj: *const LeanObject) -> bool {
    (*obj).m_rc != 0
}

pub unsafe fn lean_ptr_tag(obj: *const LeanObject) -> u8 {
    if lean_is_scalar(obj) {
        lean_unbox(obj) as u8
    } else {
        (*obj).m_tag
    }
}

pub unsafe fn lean_obj_tag(obj: *const LeanObject) -> u8 {
    lean_ptr_tag(obj)
}

#[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
pub unsafe extern "C" fn lean_inc_ref_n(obj: *mut LeanObject, n: usize) {
    if lean_is_scalar(obj) {
        return;
    }
    if (*obj).m_rc > 0 {
        (*obj).m_rc += n as i32;
    } else if (*obj).m_rc != 0 {
        let rc = (&raw mut (*obj).m_rc).cast::<AtomicI32>();
        (*rc).fetch_sub(n as i32, Ordering::Relaxed);
    }
}

#[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
pub unsafe extern "C" fn lean_inc_ref(obj: *mut LeanObject) {
    lean_inc_ref_n(obj, 1);
}

unsafe fn lean_dec_ref(obj: *mut LeanObject) {
    if lean_is_scalar(obj) {
        return;
    }
    if (*obj).m_rc > 1 {
        (*obj).m_rc -= 1;
    } else if (*obj).m_rc != 0 {
        lean_dec_ref_cold(obj);
    }
}

pub unsafe fn lean_inc(obj: *mut LeanObject) {
    if !lean_is_scalar(obj) {
        lean_inc_ref(obj);
    }
}

#[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
pub unsafe extern "C" fn lean_inc_n(obj: *mut LeanObject, n: usize) {
    if !lean_is_scalar(obj) {
        lean_inc_ref_n(obj, n);
    }
}

pub unsafe fn lean_dec(obj: *mut LeanObject) {
    if !lean_is_scalar(obj) {
        lean_dec_ref(obj);
    }
}

unsafe fn lean_ctor_get(obj: *mut LeanObject, idx: usize) -> *mut LeanObject {
    (obj.add(1) as *mut *mut LeanObject).add(idx).read()
}

unsafe fn lean_ctor_get_uint8(obj: *mut LeanObject, offset: usize) -> u8 {
    (obj.add(1) as *mut u8).add(offset).read()
}

unsafe fn lean_ctor_get_uint16(obj: *mut LeanObject, offset: usize) -> u16 {
    (obj.add(1) as *mut u8).add(offset).cast::<u16>().read()
}

unsafe fn lean_ctor_set_uint8(obj: *mut LeanObject, offset: usize, value: u8) {
    (obj.add(1) as *mut u8).add(offset).write(value);
}

unsafe fn lean_ctor_set_uint16(obj: *mut LeanObject, offset: usize, value: u16) {
    (obj.add(1) as *mut u8).add(offset).cast::<u16>().write(value);
}

unsafe fn lean_ctor_get_uint64(obj: *mut LeanObject, offset: usize) -> u64 {
    (obj.add(1) as *mut u8).add(offset).cast::<u64>().read()
}

unsafe fn lean_ctor_set_uint64(obj: *mut LeanObject, offset: usize, value: u64) {
    (obj.add(1) as *mut u8).add(offset).cast::<u64>().write(value);
}

unsafe fn lean_ctor_get_usize(obj: *mut LeanObject, index: usize) -> usize {
    (obj.add(1) as *mut usize).add(index).read()
}

unsafe fn lean_ctor_set_usize(obj: *mut LeanObject, index: usize, value: usize) {
    (obj.add(1) as *mut usize).add(index).write(value);
}

/// Equivalent to lean.h lean_ctor_set — write an object pointer into a ctor field.
pub unsafe fn lean_ctor_set(obj: *mut LeanObject, idx: usize, val: *mut LeanObject) {
    (obj.add(1) as *mut *mut LeanObject).add(idx).write(val);
}

/// Write a u32 scalar into a ctor's scalar area at byte offset.
pub unsafe fn lean_ctor_set_uint32(obj: *mut LeanObject, offset: usize, value: u32) {
    (obj.add(1) as *mut u8).add(offset).cast::<u32>().write(value);
}

/// Thin wrapper around lean_runtime_alloc_ctor (mirrors lean.h lean_alloc_ctor).
#[export_name = "lean_alloc_ctor"]
pub unsafe extern "C" fn lean_alloc_ctor(tag: c_uint, num_objs: c_uint, scalar_sz: c_uint) -> *mut LeanObject {
    lean_runtime_alloc_ctor(tag, num_objs, scalar_sz)
}

/// True iff the object's reference count is exactly 1 (exclusively owned).
pub unsafe fn lean_is_exclusive(o: *mut LeanObject) -> bool {
    !lean_is_scalar(o) && (*o).m_rc == 1
}

#[export_name = "lean_is_exclusive"]
pub unsafe extern "C" fn lean_is_exclusive_export(o: *mut LeanObject) -> bool {
    lean_is_exclusive(o)
}

pub unsafe fn lean_box_uint64(v: u64) -> *mut LeanObject {
    let r = lean_runtime_alloc_ctor(0, 0, core::mem::size_of::<u64>() as c_uint);
    lean_ctor_set_uint64(r, 0, v);
    r
}

pub unsafe fn lean_unbox_uint64(o: *mut LeanObject) -> u64 {
    lean_ctor_get_uint64(o, 0)
}

pub unsafe fn lean_box_usize_rust(v: usize) -> *mut LeanObject {
    let r = lean_runtime_alloc_ctor(0, 0, core::mem::size_of::<usize>() as c_uint);
    lean_ctor_set_usize(r, 0, v);
    r
}

pub unsafe fn lean_unbox_usize_rust(o: *mut LeanObject) -> usize {
    if lean_is_scalar(o) {
        lean_unbox(o)
    } else {
        lean_ctor_get_usize(o, 0)
    }
}


unsafe fn lean_array_get(obj: *mut LeanObject, idx: usize) -> *mut LeanObject {
    lean_array_cptr(obj).add(idx).read()
}

unsafe fn lean_array_size(obj: *mut LeanObject) -> usize {
    let array = obj as *const LeanArrayObject;
    let size = (*array).m_size;
    debug_array_size_log(obj, size);
    size
}

pub(crate) unsafe fn lean_alloc_array(size: usize, capacity: usize) -> *mut LeanObject {
    const LEAN_ARRAY_TAG: u8 = 246;
    let byte_size = core::mem::size_of::<LeanArrayObject>()
        .checked_add(
            core::mem::size_of::<*mut LeanObject>()
                .checked_mul(capacity)
                .expect("array allocation overflow"),
        )
        .expect("array allocation overflow");
    let obj = lean_alloc_object(byte_size) as *mut LeanArrayObject;
    (*obj).m_header.m_rc = 1;
    (*obj).m_header.m_cs_sz = 0;
    (*obj).m_header.m_other = 0;
    (*obj).m_header.m_tag = LEAN_ARRAY_TAG;
    (*obj).m_size = size;
    (*obj).m_capacity = capacity;
    obj as *mut LeanObject
}

unsafe fn lean_mk_empty_array() -> *mut LeanObject {
    lean_alloc_array(0, 0)
}

pub(crate) unsafe fn lean_alloc_sarray(elem_size: c_uint, size: Size, capacity: Size) -> *mut LeanObject {
    const LEAN_SCALAR_ARRAY_TAG: u8 = 248;
    let byte_size = core::mem::size_of::<LeanScalarArray>()
        .checked_add(
            (elem_size as usize)
                .checked_mul(capacity)
                .expect("sarray allocation overflow"),
        )
        .expect("sarray allocation overflow");
    let obj = lean_alloc_object(byte_size) as *mut LeanScalarArray;
    (*obj).m_header.m_rc = 1;
    (*obj).m_header.m_cs_sz = 0;
    (*obj).m_header.m_other = elem_size as u8;
    (*obj).m_header.m_tag = LEAN_SCALAR_ARRAY_TAG;
    (*obj).m_size = size;
    (*obj).m_capacity = capacity;
    obj as *mut LeanObject
}

pub(crate) unsafe fn lean_alloc_string(size: usize, capacity: usize, len: usize) -> *mut LeanObject {
    const LEAN_STRING_TAG: u8 = 249;
    let byte_size = core::mem::size_of::<LeanStringObject>()
        .checked_add(capacity)
        .expect("string allocation overflow");
    let obj = lean_alloc_object(byte_size) as *mut LeanStringObject;
    (*obj).m_header.m_rc = 1;
    (*obj).m_header.m_cs_sz = 0;
    (*obj).m_header.m_other = 0;
    (*obj).m_header.m_tag = LEAN_STRING_TAG;
    (*obj).m_size = size;
    (*obj).m_capacity = capacity;
    (*obj).m_length = len;
    obj as *mut LeanObject
}

unsafe fn lean_sarray_set_size(obj: *mut LeanObject, size: Size) {
    let sarray = obj as *mut LeanScalarArray;
    (*sarray).m_size = size;
}

unsafe fn lean_sarray_size(obj: *mut LeanObject) -> Size {
    let sarray = obj as *const LeanScalarArray;
    (*sarray).m_size
}

#[export_name = "lean_sarray_size"]
pub unsafe extern "C" fn lean_sarray_size_export(obj: *mut LeanObject) -> Size {
    lean_sarray_size(obj)
}

unsafe fn lean_sarray_capacity(obj: *mut LeanObject) -> Size {
    let sarray = obj as *const LeanScalarArray;
    (*sarray).m_capacity
}

#[export_name = "lean_sarray_capacity"]
pub unsafe extern "C" fn lean_sarray_capacity_export(obj: *mut LeanObject) -> Size {
    lean_sarray_capacity(obj)
}

unsafe fn lean_array_capacity(obj: *mut LeanObject) -> Size {
    let array = obj as *const LeanArrayObject;
    (*array).m_capacity
}

#[export_name = "lean_array_capacity"]
pub unsafe extern "C" fn lean_array_capacity_export(obj: *mut LeanObject) -> Size {
    lean_array_capacity(obj)
}

unsafe fn lean_sarray_elem_size(obj: *mut LeanObject) -> c_uint {
    let sarray = obj as *const LeanScalarArray;
    (*sarray).m_header.m_other as c_uint
}

#[export_name = "lean_sarray_elem_size"]
pub unsafe extern "C" fn lean_sarray_elem_size_export(obj: *mut LeanObject) -> c_uint {
    lean_sarray_elem_size(obj)
}

#[export_name = "lean_sarray_cptr"]
pub unsafe extern "C" fn lean_sarray_cptr_export(obj: *mut LeanObject) -> *const u8 {
    lean_sarray_cptr(obj)
}

#[export_name = "hash_str"]
pub unsafe extern "C" fn hash_str_export(len: Size, text: *const u8, seed: u64) -> u64 {
    lean_runtime_hash_str(len, text, seed)
}

unsafe fn lean_box_uint32_rust(v: u32) -> *mut LeanObject {
    #[cfg(target_pointer_width = "64")]
    {
        lean_box(v as usize)
    }
    #[cfg(not(target_pointer_width = "64"))]
    {
        let obj = lean_alloc_ctor(0, 0, core::mem::size_of::<u32>() as c_uint);
        lean_ctor_set_uint32(obj, 0, v);
        obj
    }
}

unsafe fn lean_unbox_uint32_rust(obj: *mut LeanObject) -> u32 {
    #[cfg(target_pointer_width = "64")]
    {
        lean_unbox(obj) as u32
    }
    #[cfg(not(target_pointer_width = "64"))]
    {
        lean_ctor_get_uint32(obj, 0)
    }
}

unsafe fn lean_box_float_rust(v: f64) -> *mut LeanObject {
    let obj = lean_alloc_ctor(0, 0, core::mem::size_of::<f64>() as c_uint);
    let data = (obj as *mut u8).add(core::mem::size_of::<LeanObject>()) as *mut f64;
    data.write_unaligned(v);
    obj
}

unsafe fn lean_unbox_float_rust(obj: *mut LeanObject) -> f64 {
    let data = (obj as *mut u8).add(core::mem::size_of::<LeanObject>()) as *const f64;
    data.read_unaligned()
}

unsafe fn lean_box_float32_rust(v: f32) -> *mut LeanObject {
    let obj = lean_alloc_ctor(0, 0, core::mem::size_of::<f32>() as c_uint);
    let data = (obj as *mut u8).add(core::mem::size_of::<LeanObject>()) as *mut f32;
    data.write_unaligned(v);
    obj
}

unsafe fn lean_unbox_float32_rust(obj: *mut LeanObject) -> f32 {
    let data = (obj as *mut u8).add(core::mem::size_of::<LeanObject>()) as *const f32;
    data.read_unaligned()
}

unsafe fn lean_usize_to_nat_rust(value: usize) -> *mut LeanObject {
    if value <= usize::MAX >> 1 {
        lean_box(value)
    } else {
        lean_big_uint64_to_nat(value as u64)
    }
}

unsafe fn lean_nat_add_rust(a: *mut LeanObject, b: *mut LeanObject) -> *mut LeanObject {
    if lean_is_scalar(a) && lean_is_scalar(b) {
        lean_usize_to_nat_rust(lean_unbox(a) + lean_unbox(b))
    } else {
        runtime_object_nat_int_impl::lean_nat_big_add(a, b)
    }
}

unsafe fn lean_nat_sub_rust(a: *mut LeanObject, b: *mut LeanObject) -> *mut LeanObject {
    if lean_is_scalar(a) && lean_is_scalar(b) {
        let n1 = lean_unbox(a);
        let n2 = lean_unbox(b);
        if n1 < n2 { lean_box(0) } else { lean_box(n1 - n2) }
    } else {
        runtime_object_nat_int_impl::lean_nat_big_sub(a, b)
    }
}

unsafe fn lean_char_default_value_rust() -> u32 {
    b'A' as u32
}

#[export_name = "lean_is_scalar"]
pub unsafe extern "C" fn lean_is_scalar_export(obj: *mut LeanObject) -> u8 {
    lean_is_scalar(obj) as u8
}

#[export_name = "lean_inc"]
pub unsafe extern "C" fn lean_inc_export(obj: *mut LeanObject) {
    lean_inc(obj)
}

#[cfg(not(feature = "export-runtime-ffi"))]
#[export_name = "lean_inc_n"]
pub unsafe extern "C" fn lean_inc_n_export(obj: *mut LeanObject, n: usize) {
    lean_inc_n(obj, n)
}

#[export_name = "lean_dec"]
pub unsafe extern "C" fn lean_dec_export(obj: *mut LeanObject) {
    if get_env_var_cached!("LEAN_TRACE_RC") && !lean_is_scalar(obj) {
        eprintln!(
            "lean_dec {:p} tag={} rc={} cs_sz={} other={}",
            obj,
            lean_ptr_tag(obj),
            (*obj).m_rc,
            (*obj).m_cs_sz,
            (*obj).m_other
        );
    }
    lean_dec(obj)
}

#[export_name = "lean_box_uint32"]
pub unsafe extern "C" fn lean_box_uint32_export(v: u32) -> *mut LeanObject {
    lean_box_uint32_rust(v)
}

#[export_name = "lean_unbox_uint32"]
pub unsafe extern "C" fn lean_unbox_uint32_export(obj: *mut LeanObject) -> u32 {
    lean_unbox_uint32_rust(obj)
}

#[export_name = "lean_box_usize"]
pub unsafe extern "C" fn lean_box_usize_export(v: usize) -> *mut LeanObject {
    lean_box_usize_rust(v)
}

#[export_name = "lean_unbox_usize"]
pub unsafe extern "C" fn lean_unbox_usize_export(obj: *mut LeanObject) -> usize {
    lean_unbox_usize_rust(obj)
}

#[export_name = "lean_box_float"]
pub unsafe extern "C" fn lean_box_float_export(v: f64) -> *mut LeanObject {
    lean_box_float_rust(v)
}

#[export_name = "lean_unbox_float"]
pub unsafe extern "C" fn lean_unbox_float_export(obj: *mut LeanObject) -> f64 {
    lean_unbox_float_rust(obj)
}

#[export_name = "lean_box_float32"]
pub unsafe extern "C" fn lean_box_float32_export(v: f32) -> *mut LeanObject {
    lean_box_float32_rust(v)
}

#[export_name = "lean_unbox_float32"]
pub unsafe extern "C" fn lean_unbox_float32_export(obj: *mut LeanObject) -> f32 {
    lean_unbox_float32_rust(obj)
}

#[export_name = "lean_int64_to_int"]
pub unsafe extern "C" fn lean_int64_to_int_export(value: i64) -> *mut LeanObject {
    lean_int64_to_int_rust(value)
}

#[export_name = "lean_usize_to_nat"]
pub unsafe extern "C" fn lean_usize_to_nat_export(value: usize) -> *mut LeanObject {
    lean_usize_to_nat_rust(value)
}

#[export_name = "lean_nat_add"]
pub unsafe extern "C" fn lean_nat_add_export(a: *mut LeanObject, b: *mut LeanObject) -> *mut LeanObject {
    lean_nat_add_rust(a, b)
}

#[export_name = "lean_nat_sub"]
pub unsafe extern "C" fn lean_nat_sub_export(a: *mut LeanObject, b: *mut LeanObject) -> *mut LeanObject {
    lean_nat_sub_rust(a, b)
}

#[export_name = "lean_char_default_value"]
pub unsafe extern "C" fn lean_char_default_value_export() -> u32 {
    lean_char_default_value_rust()
}

unsafe fn lean_string_capacity(obj: *mut LeanObject) -> Size {
    let string = obj as *const LeanStringObject;
    (*string).m_capacity
}

#[export_name = "lean_string_capacity"]
pub unsafe extern "C" fn lean_string_capacity_export(obj: *mut LeanObject) -> Size {
    lean_string_capacity(obj)
}

#[export_name = "lean_array_size"]
pub unsafe extern "C" fn lean_array_size_export(obj: *mut LeanObject) -> Size {
    lean_array_size(obj)
}

#[export_name = "lean_string_size"]
pub unsafe extern "C" fn lean_string_size_export(obj: *mut LeanObject) -> Size {
    lean_string_size(obj)
}

#[export_name = "lean_alloc_object"]
pub unsafe extern "C" fn lean_alloc_object_export(size: Size) -> *mut LeanObject {
    lean_alloc_export(size) as *mut LeanObject
}

#[export_name = "lean_alloc_small_object"]
pub unsafe extern "C" fn lean_alloc_small_object_export(size: Size) -> *mut LeanObject {
    lean_alloc_object_export(size)
}

#[export_name = "lean_alloc_ctor_memory"]
pub unsafe extern "C" fn lean_alloc_ctor_memory_export_inner(size: Size) -> *mut LeanObject {
    lean_alloc_object_export(size)
}

#[export_name = "lean_alloc_array"]
pub unsafe extern "C" fn lean_alloc_array_export(size: usize, capacity: usize) -> *mut LeanObject {
    lean_alloc_array(size, capacity)
}

#[export_name = "lean_alloc_sarray"]
pub unsafe extern "C" fn lean_alloc_sarray_export(elem_size: c_uint, size: usize, capacity: usize) -> *mut LeanObject {
    lean_alloc_sarray(elem_size, size, capacity)
}

#[export_name = "lean_alloc_string"]
pub unsafe extern "C" fn lean_alloc_string_export(size: usize, capacity: usize, len: usize) -> *mut LeanObject {
    lean_alloc_string(size, capacity, len)
}

#[inline(never)]
#[export_name = "lean_free_small_object"]
pub unsafe extern "C" fn lean_free_small_object_export(obj: *mut LeanObject) {
    // All Lean objects are allocated via malloc (lean_alloc_object → libc::malloc).
    // Call free() directly to avoid linker symbol resolution issues in pure-Rust builds.
    libc::free(obj as *mut _);
}

pub(crate) unsafe fn lean_small_object_size(obj: *mut LeanObject) -> usize {
    match lean_ptr_tag(obj) {
        244 => core::mem::size_of::<LeanPromiseObject>(),
        245 => core::mem::size_of::<LeanClosureObject>(),
        251 => core::mem::size_of::<LeanThunkObject>(),
        252 => core::mem::size_of::<LeanTaskObject>(),
        253 => core::mem::size_of::<LeanRefObject>(),
        254 => core::mem::size_of::<LeanExternalObject>(),
        _ => (*obj).m_cs_sz as usize,
    }
}

#[export_name = "lean_small_object_size"]
pub unsafe extern "C" fn lean_small_object_size_export(obj: *mut LeanObject) -> usize {
    lean_small_object_size(obj)
}

#[export_name = "lean_runtime_free_mpz_object"]
pub unsafe extern "C" fn lean_runtime_free_mpz_object_export(obj: *mut LeanObject) {
    lean_free_small_object_export(obj)
}

#[cfg(lean_use_gmp)]
#[repr(C)]
struct LeanMpzGmp {
    _mp_alloc: i32,
    _mp_size: i32,
    _mp_d: *mut u64,
}

#[cfg(not(lean_use_gmp))]
#[repr(C)]
struct LeanMpzNonGmp {
    m_sign: bool,
    m_size: usize,
    m_digits: *mut u32,
}

#[cfg(lean_use_gmp)]
type LeanMpzRepr = [LeanMpzGmp; 1];

#[cfg(not(lean_use_gmp))]
type LeanMpzRepr = LeanMpzNonGmp;

#[export_name = "_ZNK4lean3mpz9is_size_tEv"]
pub unsafe extern "C" fn lean_mpz_is_size_t_export(self_: *const LeanMpzRepr) -> bool {
    #[cfg(lean_use_gmp)]
    {
        let v = &*self_;
        v[0]._mp_size >= 0 && v[0]._mp_size <= 1
    }
    #[cfg(not(lean_use_gmp))]
    {
        let v = &*self_;
        if core::mem::size_of::<usize>() == 8 {
            !v.m_sign && v.m_size <= 2
        } else {
            !v.m_sign && v.m_size <= 1
        }
    }
}

#[export_name = "_ZNK4lean3mpz10get_size_tEv"]
pub unsafe extern "C" fn lean_mpz_get_size_t_export(self_: *const LeanMpzRepr) -> usize {
    #[cfg(lean_use_gmp)]
    {
        let v = &*self_;
        v[0]._mp_d.read() as usize
    }
    #[cfg(not(lean_use_gmp))]
    {
        let v = &*self_;
        if core::mem::size_of::<usize>() == 8 && v.m_size == 2 {
            (*v.m_digits as usize) | ((*v.m_digits.add(1) as usize) << 32)
        } else {
            *v.m_digits as usize
        }
    }
}

#[export_name = "lean_array_cptr"]
pub unsafe extern "C" fn lean_array_cptr_export(obj: *mut LeanObject) -> *mut *mut LeanObject {
    lean_array_cptr(obj)
}

pub(crate) unsafe fn lean_array_cptr(obj: *mut LeanObject) -> *mut *mut LeanObject {
    (obj as *mut u8).add(core::mem::offset_of!(LeanArrayObject, m_data)) as *mut *mut LeanObject
}

pub(crate) unsafe fn lean_array_byte_size(obj: *mut LeanObject) -> usize {
    core::mem::size_of::<LeanArrayObject>() + lean_array_capacity(obj) * core::mem::size_of::<*mut LeanObject>()
}

pub(crate) unsafe fn lean_sarray_byte_size(obj: *mut LeanObject) -> usize {
    core::mem::size_of::<LeanScalarArray>() + lean_sarray_capacity(obj) * lean_sarray_elem_size(obj) as usize
}

pub(crate) unsafe fn lean_string_byte_size(obj: *mut LeanObject) -> usize {
    core::mem::size_of::<LeanStringObject>() + lean_string_capacity(obj)
}

pub(crate) unsafe fn lean_closure_byte_size(obj: *mut LeanObject) -> usize {
    core::mem::size_of::<LeanClosureObject>() + (*(obj as *mut LeanClosureObject)).m_num_fixed as usize * core::mem::size_of::<*mut LeanObject>()
}

pub(crate) unsafe fn lean_is_string(obj: *mut LeanObject) -> bool {
    lean_ptr_tag(obj) == 249
}

#[export_name = "lean_array_byte_size"]
pub unsafe extern "C" fn lean_array_byte_size_export(obj: *mut LeanObject) -> usize {
    lean_array_byte_size(obj)
}

pub(crate) unsafe fn lean_array_data_byte_size(obj: *mut LeanObject) -> usize {
    lean_array_byte_size(obj) - core::mem::size_of::<LeanArrayObject>()
}

#[export_name = "lean_array_data_byte_size"]
pub unsafe extern "C" fn lean_array_data_byte_size_export(obj: *mut LeanObject) -> usize {
    lean_array_data_byte_size(obj)
}

#[export_name = "lean_sarray_byte_size"]
pub unsafe extern "C" fn lean_sarray_byte_size_export(obj: *mut LeanObject) -> usize {
    lean_sarray_byte_size(obj)
}

pub(crate) unsafe fn lean_sarray_data_byte_size(obj: *mut LeanObject) -> usize {
    lean_sarray_byte_size(obj) - core::mem::size_of::<LeanScalarArray>()
}

#[export_name = "lean_sarray_data_byte_size"]
pub unsafe extern "C" fn lean_sarray_data_byte_size_export(obj: *mut LeanObject) -> usize {
    lean_sarray_data_byte_size(obj)
}

#[export_name = "lean_string_byte_size"]
pub unsafe extern "C" fn lean_string_byte_size_export(obj: *mut LeanObject) -> usize {
    lean_string_byte_size(obj)
}

pub(crate) unsafe fn lean_string_data_byte_size(obj: *mut LeanObject) -> usize {
    lean_string_byte_size(obj) - core::mem::size_of::<LeanStringObject>()
}

#[export_name = "lean_string_data_byte_size"]
pub unsafe extern "C" fn lean_string_data_byte_size_export(obj: *mut LeanObject) -> usize {
    lean_string_data_byte_size(obj)
}

#[export_name = "lean_closure_arg_cptr"]
pub unsafe extern "C" fn lean_closure_arg_cptr_export(obj: *mut LeanObject) -> *mut *mut LeanObject {
    (obj as *mut u8).add(core::mem::size_of::<LeanClosureObject>()) as *mut *mut LeanObject
}

#[export_name = "lean_closure_set"]
pub unsafe extern "C" fn lean_closure_set(obj: *mut LeanObject, i: c_uint, value: *mut LeanObject) {
    *lean_closure_arg_cptr_export(obj).add(i as usize) = value;
}

#[export_name = "lean_closure_num_fixed"]
pub unsafe extern "C" fn lean_closure_num_fixed_export(obj: *mut LeanObject) -> c_uint {
    (*(obj as *mut LeanClosureObject)).m_num_fixed as c_uint
}

#[export_name = "lean_closure_byte_size"]
pub unsafe extern "C" fn lean_closure_byte_size_export(obj: *mut LeanObject) -> usize {
    lean_closure_byte_size(obj)
}

#[export_name = "lean_closure_capacity"]
pub unsafe extern "C" fn lean_closure_capacity_export(obj: *mut LeanObject) -> usize {
    (*(obj as *mut LeanClosureObject)).m_num_fixed as usize
}

pub(crate) unsafe fn lean_closure_data_byte_size(obj: *mut LeanObject) -> usize {
    lean_closure_byte_size(obj) - core::mem::size_of::<LeanClosureObject>()
}

#[export_name = "lean_closure_data_byte_size"]
pub unsafe extern "C" fn lean_closure_data_byte_size_export(obj: *mut LeanObject) -> usize {
    lean_closure_data_byte_size(obj)
}

#[export_name = "lean_ctor_num_objs"]
pub unsafe extern "C" fn lean_ctor_num_objs_export(obj: *mut LeanObject) -> c_uint {
    (*obj).m_other as c_uint
}

#[export_name = "lean_ctor_obj_cptr"]
pub unsafe extern "C" fn lean_ctor_obj_cptr_export(obj: *mut LeanObject) -> *mut *mut LeanObject {
    obj.add(1) as *mut *mut LeanObject
}

#[export_name = "lean_runtime_alloc_ctor"]
pub unsafe extern "C" fn lean_runtime_alloc_ctor_export(tag: c_uint, num_objs: c_uint, scalar_size: c_uint) -> *mut LeanObject {
    let total = core::mem::size_of::<LeanObject>()
        .checked_add(num_objs as usize * core::mem::size_of::<*mut LeanObject>())
        .and_then(|n| n.checked_add(scalar_size as usize))
        .expect("constructor allocation overflow");
    let aligned_total = (total + 7) & !7;
    let obj = lean_alloc_object(aligned_total);
    core::ptr::write_bytes(obj as *mut u8, 0, aligned_total);
    (*obj).m_rc = 1;
    (*obj).m_cs_sz = aligned_total as u16;
    (*obj).m_other = num_objs as u8;
    (*obj).m_tag = tag as u8;
    obj
}

#[export_name = "lean_runtime_ctor_set"]
pub unsafe extern "C" fn lean_runtime_ctor_set_export(obj: *mut LeanObject, index: c_uint, value: *mut LeanObject) {
    *lean_ctor_obj_cptr(obj).add(index as usize) = value;
}

#[export_name = "lean_set_st_header"]
pub unsafe extern "C" fn lean_set_st_header_export(o: *mut LeanObject, tag: u8, other: u8) {
    (*o).m_rc = 1;
    (*o).m_tag = tag;
    (*o).m_other = other;
    (*o).m_cs_sz = 0;
}

#[export_name = "lean_ctor_get"]
pub unsafe extern "C" fn lean_ctor_get_export(obj: *mut LeanObject, idx: c_uint) -> *mut LeanObject {
    lean_ctor_get(obj, idx as usize)
}

#[export_name = "lean_ctor_set"]
pub unsafe extern "C" fn lean_ctor_set_export(obj: *mut LeanObject, idx: c_uint, val: *mut LeanObject) {
    lean_ctor_set(obj, idx as usize, val);
}

#[export_name = "lean_dec_ref"]
pub unsafe extern "C" fn lean_dec_ref_export(obj: *mut LeanObject) {
    if get_env_var_cached!("LEAN_TRACE_RC") && !lean_is_scalar(obj) {
        eprintln!(
            "lean_dec_ref {:p} tag={} rc={} cs_sz={} other={}",
            obj,
            lean_ptr_tag(obj),
            (*obj).m_rc,
            (*obj).m_cs_sz,
            (*obj).m_other
        );
    }
    lean_dec_ref(obj);
}

#[export_name = "lean_string_len"]
pub unsafe extern "C" fn lean_string_len_export(obj: *mut LeanObject) -> usize {
    lean_string_len(obj)
}

#[export_name = "validate_utf8"]
pub unsafe extern "C" fn validate_utf8_export(s: *const u8, sz: usize, pos: *mut usize, i: *mut usize) -> bool {
    lean_runtime_validate_utf8(s, sz, pos, i)
}

#[export_name = "validate_utf8_one"]
pub unsafe extern "C" fn validate_utf8_one_export(s: *const u8, sz: usize, pos: usize) -> bool {
    let mut p = pos;
    lean_runtime_validate_utf8_one(s, sz, &mut p)
}

#[export_name = "push_unicode_scalar"]
pub unsafe extern "C" fn push_unicode_scalar_export(dst: *mut c_char, code: c_uint) -> c_uint {
    lean_runtime_push_unicode_scalar(dst, code)
}


#[export_name = "_ZN4lean14io_wrap_handleEP8_IO_FILE"]
pub unsafe extern "C" fn lean_io_wrap_handle_export(fp: *mut c_void) -> *mut LeanObject {
    lean_io_wrap_handle_c(fp)
}

#[export_name = "_ZN4lean21mk_embedded_nul_errorEP11lean_object"]
pub unsafe extern "C" fn lean_mk_embedded_nul_error_export(str: *mut LeanObject) -> *mut LeanObject {
    lean_mk_embedded_nul_error_c(str)
}

pub unsafe fn mk_embedded_nul_error(str: *mut LeanObject) -> *mut LeanObject {
    lean_mk_embedded_nul_error_c(str)
}

#[export_name = "lean_register_external_class"]
pub unsafe extern "C" fn lean_register_external_class_export(
    finalize: Option<unsafe extern "C" fn(*mut c_void)>,
    foreach: Option<unsafe extern "C" fn(*mut c_void, *mut LeanObject)>,
) -> *mut LeanExternalClass {
    unsafe extern "C" fn noop_finalize(_: *mut c_void) {}
    unsafe extern "C" fn noop_foreach(_: *mut c_void, _: *mut LeanObject) {}
    Box::into_raw(Box::new(LeanExternalClass {
        m_finalize: finalize.unwrap_or(noop_finalize),
        m_foreach: foreach.unwrap_or(noop_foreach),
    }))
}

#[export_name = "lean_runtime_alloc_external"]
pub unsafe extern "C" fn lean_runtime_alloc_external_export(
    class: *mut LeanExternalClass,
    data: *mut c_void,
) -> *mut LeanObject {
    let total = core::mem::size_of::<LeanExternalObject>();
    let obj = lean_alloc_object(total) as *mut LeanExternalObject;
    core::ptr::write_bytes(obj as *mut u8, 0, total);
    (*obj).m_header.m_rc = 1;
    (*obj).m_header.m_cs_sz = 0;
    (*obj).m_header.m_other = 0;
    (*obj).m_header.m_tag = 254;
    (*obj).m_class = class;
    (*obj).m_data = data;
    obj as *mut LeanObject
}

#[export_name = "lean_runtime_get_external_data"]
pub unsafe extern "C" fn lean_runtime_get_external_data_export(obj: *mut LeanObject) -> *mut c_void {
    (*lean_to_external(obj)).m_data
}

#[export_name = "lean_to_external"]
pub unsafe extern "C" fn lean_to_external_export(obj: *mut LeanObject) -> *mut LeanExternalObject {
    obj as *mut LeanExternalObject
}

#[export_name = "lean_to_thunk"]
pub unsafe extern "C" fn lean_to_thunk_export(obj: *mut LeanObject) -> *mut LeanThunkObject {
    obj as *mut LeanThunkObject
}

#[export_name = "lean_to_ref"]
pub unsafe extern "C" fn lean_to_ref_export(obj: *mut LeanObject) -> *mut LeanRefObject {
    obj as *mut LeanRefObject
}

#[export_name = "lean_to_promise"]
pub unsafe extern "C" fn lean_to_promise_export(obj: *mut LeanObject) -> *mut LeanPromiseObject {
    obj as *mut LeanPromiseObject
}

#[export_name = "lean_alloc_closure"]
pub unsafe extern "C" fn lean_alloc_closure_export(fun: *mut c_void, arity: u32, num_fixed: u32) -> *mut LeanObject {
    let total = core::mem::size_of::<LeanClosureObject>()
        .checked_add(num_fixed as usize * core::mem::size_of::<*mut LeanObject>())
        .expect("closure allocation overflow");
    let obj = lean_alloc_object(total) as *mut LeanClosureObject;
    core::ptr::write_bytes(obj as *mut u8, 0, total);
    (*obj).m_header.m_rc = 1;
    (*obj).m_header.m_cs_sz = 0;
    (*obj).m_header.m_other = 0;
    (*obj).m_header.m_tag = 245;
    (*obj).m_fun = fun;
    (*obj).m_arity = arity as u16;
    (*obj).m_num_fixed = num_fixed as u16;
    obj as *mut LeanObject
}

#[export_name = "free_sized"]
pub unsafe extern "C" fn free_sized_export(ptr: *mut c_void, _sz: usize) {
    libc::free(ptr);
}


pub unsafe fn lean_io_result_is_ok(obj: *mut LeanObject) -> bool {
    lean_ptr_tag(obj) == 0
}

pub unsafe fn lean_io_result_is_error(obj: *mut LeanObject) -> bool {
    lean_ptr_tag(obj) == 1
}

pub unsafe fn lean_io_result_get_value(obj: *mut LeanObject) -> *mut LeanObject {
    debug_assert!(lean_io_result_is_ok(obj));
    lean_ctor_get(obj, 0)
}

pub unsafe fn lean_io_result_get_error(obj: *mut LeanObject) -> *mut LeanObject {
    debug_assert!(lean_io_result_is_error(obj));
    lean_ctor_get(obj, 0)
}

pub unsafe fn lean_io_result_take_value(obj: *mut LeanObject) -> *mut LeanObject {
    debug_assert!(lean_io_result_is_ok(obj));
    let v = lean_ctor_get(obj, 0);
    lean_inc(v);
    lean_dec(obj);
    v
}


pub unsafe fn lean_sarray_cptr(obj: *mut LeanObject) -> *const u8 {
    (obj as *const u8).add(core::mem::offset_of!(LeanScalarArray, m_data))
}

#[export_name = "lean_string_cstr"]
pub unsafe extern "C" fn lean_string_cstr(obj: *mut LeanObject) -> *const c_char {
    (obj as *const u8).add(core::mem::offset_of!(LeanStringObject, m_data)) as *const c_char
}

#[inline]
unsafe fn lean_name_hash_ptr_rs(n: *mut LeanObject) -> u64 {
    debug_assert!(!lean_is_scalar(n));
    lean_ctor_get_uint64(n, 2 * core::mem::size_of::<*mut LeanObject>())
}

#[inline]
unsafe fn lean_string_bytes_eq(s1: *mut LeanObject, s2: *mut LeanObject) -> bool {
    let len1 = lean_string_size(s1);
    let len2 = lean_string_size(s2);
    len1 == len2
        && core::slice::from_raw_parts(lean_string_cstr(s1) as *const u8, len1)
            == core::slice::from_raw_parts(lean_string_cstr(s2) as *const u8, len2)
}

#[inline]
fn name_mix_hash(mut h: u64, mut k: u64) -> u64 {
    let m: u64 = 0xc6a4_a793_5bd1_e995;
    let r = 47;
    k = k.wrapping_mul(m);
    k ^= k >> r;
    k ^= m;
    h ^= k;
    h.wrapping_mul(m)
}

pub(crate) unsafe fn lean_name_mk_string(prefix: *mut LeanObject, s: *mut LeanObject) -> *mut LeanObject {
    let obj = lean_alloc_ctor(1, 2, core::mem::size_of::<u64>() as c_uint);
    lean_ctor_set(obj, 0, prefix);
    lean_ctor_set(obj, 1, s);
    let hash = if lean_is_scalar(prefix) {
        name_mix_hash(1723, lean_string_hash_export(s))
    } else {
        name_mix_hash(lean_name_hash_ptr_rs(prefix), lean_string_hash_export(s))
    };
    lean_ctor_set_uint64(obj, 2 * core::mem::size_of::<*mut LeanObject>(), hash);
    obj
}

pub(crate) unsafe fn lean_name_mk_numeral(prefix: *mut LeanObject, n: *mut LeanObject) -> *mut LeanObject {
    let obj = lean_alloc_ctor(2, 2, core::mem::size_of::<u64>() as c_uint);
    lean_ctor_set(obj, 0, prefix);
    lean_ctor_set(obj, 1, n);
    let hash = if lean_is_scalar(prefix) {
        name_mix_hash(1723, lean_uint64_of_big_nat(n))
    } else {
        name_mix_hash(lean_name_hash_ptr_rs(prefix), lean_uint64_of_big_nat(n))
    };
    lean_ctor_set_uint64(obj, 2 * core::mem::size_of::<*mut LeanObject>(), hash);
    obj
}

#[export_name = "lean_string_hash"]
pub unsafe extern "C" fn lean_string_hash_export(s: *mut LeanObject) -> u64 {
    let len = lean_string_size(s).saturating_sub(1);
    lean_runtime_hash_str(len, lean_string_cstr(s) as *const c_uchar, 11)
}

#[export_name = "lean_name_eq"]
pub unsafe extern "C" fn lean_name_eq(mut n1: *mut LeanObject, mut n2: *mut LeanObject) -> u8 {
    if n1 == n2 {
        return 1;
    }
    if lean_is_scalar(n1) != lean_is_scalar(n2) {
        return 0;
    }
    if !lean_is_scalar(n1) && lean_name_hash_ptr_rs(n1) != lean_name_hash_ptr_rs(n2) {
        return 0;
    }
    loop {
        debug_assert!(!lean_is_scalar(n1));
        debug_assert!(!lean_is_scalar(n2));
        if lean_ptr_tag(n1) != lean_ptr_tag(n2) {
            return 0;
        }
        if lean_ptr_tag(n1) == 1 {
            if !lean_string_bytes_eq(lean_ctor_get(n1, 1), lean_ctor_get(n2, 1)) {
                return 0;
            }
        } else if !crate::runtime_object_nat_int_impl::lean_nat_eq(lean_ctor_get(n1, 1), lean_ctor_get(n2, 1)) {
            return 0;
        }
        n1 = lean_ctor_get(n1, 0);
        n2 = lean_ctor_get(n2, 0);
        if n1 == n2 {
            return 1;
        }
        if lean_is_scalar(n1) != lean_is_scalar(n2) {
            return 0;
        }
        /*
        if !lean_is_scalar(n1) && !lean_is_scalar(n2) && lean_name_hash_ptr_rs(n1) != lean_name_hash_ptr_rs(n2) {
            return 0;
        }
        */
    }
}

pub unsafe fn lean_box(value: Size) -> *mut LeanObject {
    ((value << 1) | 1) as *mut LeanObject
}

#[export_name = "lean_unbox"]
pub unsafe extern "C" fn lean_unbox_export(obj: *const LeanObject) -> Size {
    lean_unbox(obj)
}

#[export_name = "lean_io_result_is_ok"]
pub unsafe extern "C" fn lean_io_result_is_ok_export(obj: *mut LeanObject) -> bool {
    lean_io_result_is_ok(obj)
}

#[export_name = "lean_io_result_mk_ok"]
pub unsafe extern "C" fn lean_io_result_mk_ok_export(value: *mut LeanObject) -> *mut LeanObject {
    lean_io_result_mk_ok(value)
}

#[export_name = "lean_io_result_mk_error"]
pub unsafe extern "C" fn lean_io_result_mk_error_export(error: *mut LeanObject) -> *mut LeanObject {
    lean_io_result_mk_error(error)
}

#[export_name = "lean_io_result_get_value"]
pub unsafe extern "C" fn lean_io_result_get_value_export(obj: *mut LeanObject) -> *mut LeanObject {
    lean_io_result_get_value(obj)
}

#[export_name = "lean_io_result_get_error"]
pub unsafe extern "C" fn lean_io_result_get_error_export(obj: *mut LeanObject) -> *mut LeanObject {
    lean_io_result_get_error(obj)
}

#[cfg(test)]
#[no_mangle]
pub unsafe extern "C" fn lean_io_eprintln(msg: *mut LeanObject) -> *mut LeanObject {
    use std::io::Write;
    let size = lean_string_size(msg).saturating_sub(1);
    let bytes = core::slice::from_raw_parts(lean_string_cstr(msg) as *const u8, size);
    let _ = std::io::stderr().write_all(bytes);
    let _ = std::io::stderr().write_all(b"\n");
    lean_io_result_mk_ok(lean_box(0))
}

#[export_name = "lean_box"]
pub unsafe extern "C" fn lean_box_export(value: Size) -> *mut LeanObject {
    lean_box(value)
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

include!("library_constants.rs");
include!("library_dynlib.rs");
include!("library_llvm.rs");
include!("runtime_debug.rs");
include!("runtime_dns.rs");
include!("runtime_event_loop.rs");
include!("runtime_libuv.rs");
include!("runtime_mpn.rs");
include!("runtime_mutex.rs");
include!("runtime_net_addr.rs");
include!("runtime_signal.rs");
include!("runtime_process.rs");
include!("runtime_stack_overflow.rs");
include!("runtime_stack_info.rs");
include!("runtime_interrupt.rs");
include!("runtime_system.rs");
include!("runtime_tcp.rs");
include!("runtime_timer.rs");
include!("runtime_udp.rs");
include!("runtime_alloc.rs");
include!("runtime_memory.rs");
include!("runtime_sharecommon.rs");
include!("runtime_thread.rs");
include!("runtime_once.rs");
include!("runtime_float.rs");
include!("runtime_apply.rs");
include!("runtime_object_panic.rs");
include!("runtime_object_rc.rs");
include!("runtime_exception.rs");
include!("runtime_task.rs");
include!("runtime_object_string.rs");
include!("runtime_object_array.rs");
include!("runtime_object_nat_int.rs");
include!("runtime_compat_cxx.rs");
include!("runtime_compact.rs");
include!("runtime_io.rs");
include!("library_time_task.rs");
include!("library_annotation.rs");
include!("library_expr_lt.rs");
include!("library_formatter.rs");
include!("library_max_sharing.rs");
include!("library_replace_visitor.rs");
include!("library_num.rs");
include!("library_util.rs");
include!("library_print.rs");
include!("library_elab_environment.rs");
include!("library_module.rs");
include!("library_instantiate_mvars.rs");
include!("kernel_level.rs");
include!("kernel_expr_eq_fn.rs");
include!("kernel_expr_cache.rs");
include!("kernel_replace_fn.rs");
include!("kernel_for_each_fn.rs");
include!("kernel_abstract.rs");
include!("kernel_instantiate.rs");
include!("kernel_local_ctx.rs");
include!("kernel_declaration.rs");
include!("kernel_environment.rs");
include!("kernel_equiv_manager.rs");
include!("kernel_quot.rs");
include!("kernel_type_checker.rs");
include!("kernel_inductive.rs");
include!("kernel_expr.rs");
include!("kernel_trace.rs");

#[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
pub extern "C" fn lean_io_mk_world() -> *mut LeanObject {
    unsafe { lean_box(0) }
}

#[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
pub unsafe extern "C" fn lean_io_allocprof(
    msg: *mut LeanObject,
    fn_obj: *mut LeanObject,
) -> *mut LeanObject {
    let label = cstr_lossy_to_string(lean_string_cstr(msg));
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

#[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
pub extern "C" fn lean_util_is_safe_ascii_char(byte: c_char) -> bool {
    is_safe_ascii_byte(byte as u8)
}

#[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
pub unsafe extern "C" fn lean_util_is_safe_ascii(mut text: *const c_char) -> bool {
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

#[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
pub unsafe extern "C" fn lean_util_is_safe_ascii_n(text: *const c_char, size: Size) -> bool {
    for offset in 0..size {
        if !is_safe_ascii_byte(*text.add(offset) as u8) {
            return false;
        }
    }
    true
}

#[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
pub extern "C" fn lean_util_log2(mut value: c_uint) -> c_uint {
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

#[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
pub extern "C" fn lean_util_lbool_name(value: i32) -> *const c_char {
    match value {
        -1 => c"l_false".as_ptr(),
        1 => c"l_true".as_ptr(),
        _ => c"l_undef".as_ptr(),
    }
}

#[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
pub extern "C" fn lean_util_mk_list_range(from: c_uint, to: c_uint) -> *mut c_void {
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
        .any(|p| lean_name_eq(p, n) != 0)
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

extern "C" {
    fn write(fd: i32, buf: *const u8, count: usize) -> isize;
    fn abort() -> !;
}

unsafe fn trace_runtime_init(msg: &'static [u8]) {
    if get_env_var_cached!("LEAN_TRACE_INIT") {
        libc::write(2, msg.as_ptr().cast(), msg.len());
    }
}

unsafe fn consume_io_result(result: *mut LeanObject) {
    if lean_io_result_is_ok(result) {
        lean_dec(result);
    } else {
        let err = lean_io_result_get_error(result);
        lean_inc(err);
        lean_dec(result);
        let msg = lean_io_error_to_string(err);
        let text = core::ffi::CStr::from_ptr(lean_string_cstr(msg));

        let prefix = b"IO Error in lean_initialize: ";
        write(2, prefix.as_ptr(), prefix.len());
        let bytes = text.to_bytes();
        write(2, bytes.as_ptr(), bytes.len());
        write(2, b"\n".as_ptr(), 1);
        abort();
    }
}

unsafe fn initialize_runtime_module_body() {
    trace_runtime_init(b"runtime: alloc\n");
    initialize_alloc();
    trace_runtime_init(b"runtime: debug\n");
    initialize_debug();
    trace_runtime_init(b"runtime: object\n");
    initialize_object();
    trace_runtime_init(b"runtime: io\n");
    initialize_io();
    trace_runtime_init(b"runtime: thread\n");
    initialize_thread();
    trace_runtime_init(b"runtime: mutex\n");
    initialize_mutex();
    trace_runtime_init(b"runtime: process\n");
    initialize_process();
    trace_runtime_init(b"runtime: stack\n");
    initialize_stack_overflow();
    trace_runtime_init(b"runtime: libuv\n");
    initialize_libuv();
    trace_runtime_init(b"runtime: done\n");
}

unsafe fn finalize_runtime_module_body() {
    finalize_stack_overflow();
    finalize_process();
    finalize_mutex();
    finalize_thread();
    finalize_io();
    finalize_object();
    finalize_debug();
    finalize_alloc();
}

unsafe fn initialize_util_module_body() {
    initialize_runtime_module_body();
    initialize_ascii();
    initialize_name();
    initialize_name_generator();
    initialize_options();
}

unsafe fn finalize_util_module_body() {
    finalize_options();
    finalize_name_generator();
    finalize_name();
    finalize_ascii();
    finalize_runtime_module_body();
}

unsafe fn initialize_kernel_module_body() {
    trace_runtime_init(b"kernel: level\n");
    initialize_level();
    trace_runtime_init(b"kernel: expr\n");
    initialize_expr();
    trace_runtime_init(b"kernel: decl\n");
    initialize_declaration();
    trace_runtime_init(b"kernel: typechecker\n");
    initialize_type_checker();
    trace_runtime_init(b"kernel: env\n");
    initialize_environment();
    trace_runtime_init(b"kernel: lctx\n");
    initialize_local_ctx();
    trace_runtime_init(b"kernel: inductive\n");
    initialize_inductive();
    trace_runtime_init(b"kernel: quot\n");
    initialize_quot();
    trace_runtime_init(b"kernel: trace\n");
    initialize_trace();
    trace_runtime_init(b"kernel: done\n");
}

unsafe fn finalize_kernel_module_body() {
    finalize_trace();
    finalize_quot();
    finalize_inductive();
    finalize_local_ctx();
    finalize_environment();
    finalize_type_checker();
    finalize_declaration();
    finalize_expr();
    finalize_level();
}

unsafe fn initialize_library_core_module_body() {
    initialize_formatter();
    initialize_constants();
    initialize_profiling();
}

unsafe fn finalize_library_core_module_body() {
    finalize_profiling();
    finalize_constants();
    finalize_formatter();
}

unsafe fn initialize_library_module_body() {
    initialize_print();
    initialize_num();
    initialize_annotation();
    initialize_library_util();
    initialize_time_task();
    initialize_dynlib();
    initialize_ir_interpreter_export();
}

unsafe fn finalize_library_module_body() {
    finalize_ir_interpreter_export();
    finalize_time_task();
    finalize_library_util();
    finalize_annotation();
    finalize_num();
    finalize_print();
}

unsafe fn initialize_constructions_module_body() {
    initialize_constructions_util();
}

unsafe fn finalize_constructions_module_body() {
    finalize_constructions_util();
}



// initialize_ascii / finalize_ascii are no-ops: the original C++ ascii.h had them as empty
// inline functions. The actual ASCII utility functions are ported to Rust above.
#[cfg_attr(feature = "export-runtime-ffi", export_name = "_ZN4lean16initialize_asciiEv")]
pub extern "C" fn initialize_ascii() {}

#[cfg_attr(feature = "export-runtime-ffi", export_name = "_ZN4lean14finalize_asciiEv")]
pub extern "C" fn finalize_ascii() {}

#[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
pub extern "C" fn lean_initialize_runtime_module() {
    unsafe { initialize_runtime_module_body() }
}

#[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
pub extern "C" fn initialize_runtime_module() {
    unsafe { initialize_runtime_module_body() }
}

#[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
pub extern "C" fn finalize_runtime_module() {
    unsafe { finalize_runtime_module_body() }
}

#[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
pub extern "C" fn initialize_util_module() {
    unsafe { initialize_util_module_body() }
}

#[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
pub extern "C" fn finalize_util_module() {
    unsafe { finalize_util_module_body() }
}

#[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
pub extern "C" fn initialize_kernel_module() {
    unsafe { initialize_kernel_module_body() }
}

#[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
pub extern "C" fn finalize_kernel_module() {
    unsafe { finalize_kernel_module_body() }
}

#[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
pub extern "C" fn initialize_library_core_module() {
    unsafe { initialize_library_core_module_body() }
}

#[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
pub extern "C" fn finalize_library_core_module() {
    unsafe { finalize_library_core_module_body() }
}

#[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
pub extern "C" fn initialize_library_module() {
    unsafe { initialize_library_module_body() }
}

#[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
pub extern "C" fn finalize_library_module() {
    unsafe { finalize_library_module_body() }
}

#[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
pub extern "C" fn initialize_constructions_module() {
    unsafe { initialize_constructions_module_body() }
}

#[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
pub extern "C" fn finalize_constructions_module() {
    unsafe { finalize_constructions_module_body() }
}

#[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
pub extern "C" fn lean_initialize_runtime_for_plugin(_: u8) -> *mut LeanObject {
    unsafe {
        initialize_runtime_module_body();
        lean_io_result_mk_ok(lean_box(0))
    }
}

#[export_name = "_ZN4lean21init_default_print_fnEv"]
pub extern "C" fn init_default_print_fn() {
}

#[no_mangle]
pub extern "C" fn lean_cxx_initialize_quot() {
}

#[no_mangle]
pub extern "C" fn lean_cxx_finalize_quot() {
}

#[no_mangle]
pub extern "C" fn lean_cxx_initialize_inductive() {
}

#[no_mangle]
pub extern "C" fn lean_cxx_finalize_inductive() {
}

#[no_mangle]
pub extern "C" fn lean_cxx_initialize_local_ctx() {
}

#[no_mangle]
pub extern "C" fn lean_cxx_finalize_local_ctx() {
}

#[no_mangle]
pub extern "C" fn lean_cxx_initialize_environment() {
}

#[no_mangle]
pub extern "C" fn lean_cxx_finalize_environment() {
}

#[no_mangle]
pub extern "C" fn lean_cxx_initialize_type_checker() {
}

#[no_mangle]
pub extern "C" fn lean_cxx_finalize_type_checker() {
}

#[no_mangle]
pub extern "C" fn lean_cxx_initialize_declaration() {
}

#[no_mangle]
pub extern "C" fn lean_cxx_finalize_declaration() {
}

#[no_mangle]
pub extern "C" fn lean_cxx_initialize_expr() {
}

#[no_mangle]
pub extern "C" fn lean_cxx_finalize_expr() {
}

#[no_mangle]
pub extern "C" fn lean_cxx_initialize_level() {
}

#[no_mangle]
pub extern "C" fn lean_cxx_finalize_level() {
}

#[no_mangle]
pub extern "C" fn lean_cxx_initialize_formatter() {
}

#[no_mangle]
pub extern "C" fn lean_cxx_finalize_formatter() {
}

#[no_mangle]
pub extern "C" fn lean_cxx_initialize_library_util() {
}

#[no_mangle]
pub extern "C" fn lean_cxx_finalize_library_util() {
}

#[no_mangle]
pub extern "C" fn lean_cxx_initialize_bool() {
}

#[no_mangle]
pub extern "C" fn lean_cxx_finalize_bool() {
}

#[no_mangle]
pub extern "C" fn lean_cxx_initialize_annotation() {
}

#[no_mangle]
pub extern "C" fn lean_cxx_finalize_annotation() {
}

#[no_mangle]
pub extern "C" fn lean_cxx_initialize_num() {
}

#[no_mangle]
pub extern "C" fn lean_cxx_finalize_num() {
}

#[no_mangle]
pub extern "C" fn lean_cxx_initialize_print() {
}

#[no_mangle]
pub extern "C" fn lean_cxx_finalize_print() {
}

#[no_mangle]
pub extern "C" fn lean_cxx_initialize_time_task() {
}

#[no_mangle]
pub extern "C" fn lean_cxx_finalize_time_task() {
}

#[no_mangle]
pub extern "C" fn lean_cxx_display_cumulative_profiling_times() {
    let mut err = std::io::stderr();
    runtime_time_task_impl::display_cumulative(&mut err);
}

#[no_mangle]
pub extern "C" fn lean_cxx_initialize_ir_interpreter() {}

#[no_mangle]
pub extern "C" fn lean_cxx_finalize_ir_interpreter() {}

#[export_name = "_ZN4lean25initialize_ir_interpreterEv"]
pub extern "C" fn initialize_ir_interpreter_export() {}

#[export_name = "_ZN4lean23finalize_ir_interpreterEv"]
pub extern "C" fn finalize_ir_interpreter_export() {}

#[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
pub extern "C" fn run_thread_finalizers() {
    unsafe { run_thread_finalizers_internal() }
}

#[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
pub extern "C" fn run_post_thread_finalizers() {
    unsafe { run_post_thread_finalizers_internal() }
}

#[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
pub extern "C" fn delete_thread_finalizer_manager() {
    unsafe { delete_thread_finalizer_manager_internal() }
}

#[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
pub extern "C" fn lean_initialize() {
    unsafe {
        trace_runtime_init(b"lean_initialize: stack\n");
        save_stack_info(true);
        trace_runtime_init(b"lean_initialize: util\n");
        initialize_util_module();
        let builtin = 1u8;
        trace_runtime_init(b"lean_initialize: Init\n");
        consume_io_result(initialize_Init(builtin));
        trace_runtime_init(b"lean_initialize: Std\n");
        consume_io_result(initialize_Std(builtin));
        trace_runtime_init(b"lean_initialize: Lean.Data\n");
        consume_io_result(initialize_Lean_Data(builtin));
        trace_runtime_init(b"lean_initialize: Lean\n");
        consume_io_result(initialize_Lean(builtin));
        trace_runtime_init(b"lean_initialize: kernel\n");
        initialize_kernel_module();
        trace_runtime_init(b"lean_initialize: print\n");
        init_default_print_fn();
        trace_runtime_init(b"lean_initialize: core\n");
        initialize_library_core_module();
        trace_runtime_init(b"lean_initialize: library\n");
        initialize_library_module();
        trace_runtime_init(b"lean_initialize: constructions\n");
        initialize_constructions_module();
        trace_runtime_init(b"lean_initialize: done\n");
    }
}

#[cfg_attr(feature = "export-runtime-ffi", export_name = "_ZN4lean18initialize_optionsEv")]
pub extern "C" fn initialize_options() {
    unsafe {
        VERBOSE_OPT = mk_name("verbose");
        MAX_MEMORY_OPT = mk_name("max_memory");
        TIMEOUT_OPT = mk_name("timeout");
        if get_env_var_cached!("LEAN_TRACE_MARK_PERSISTENT") {
            eprintln!("initialize_options mark verbose={:p}", VERBOSE_OPT.obj);
            eprintln!("initialize_options mark max_memory={:p}", MAX_MEMORY_OPT.obj);
            eprintln!("initialize_options mark timeout={:p}", TIMEOUT_OPT.obj);
        }
        lean_mark_persistent(VERBOSE_OPT.obj);
        lean_mark_persistent(MAX_MEMORY_OPT.obj);
        lean_mark_persistent(TIMEOUT_OPT.obj);
    }
}

#[cfg_attr(feature = "export-runtime-ffi", export_name = "_ZN4lean16finalize_optionsEv")]
pub extern "C" fn finalize_options() {
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

#[cfg_attr(
    feature = "export-runtime-ffi",
    export_name = "_ZN4lean31mk_constructions_name_generatorEv"
)]
pub unsafe extern "C" fn mk_constructions_name_generator(
    result: *mut LeanNameGenerator,
) -> *mut LeanNameGenerator {
    lean_inc(CONSTRUCTIONS_FRESH.obj);
    result.write(LeanNameGenerator {
        prefix: CONSTRUCTIONS_FRESH,
        next_idx: 0,
    });
    result
}

#[cfg_attr(
    feature = "export-runtime-ffi",
    export_name = "_ZN4lean29initialize_constructions_utilEv"
)]
pub extern "C" fn initialize_constructions_util() {
    unsafe {
        CONSTRUCTIONS_FRESH = mk_name("_cnstr_fresh");
        if get_env_var_cached!("LEAN_TRACE_MARK_PERSISTENT") {
            eprintln!(
                "initialize_constructions_util mark constructions_fresh={:p}",
                CONSTRUCTIONS_FRESH.obj
            );
        }
        lean_mark_persistent(CONSTRUCTIONS_FRESH.obj);
        lean_register_name_generator_prefix(CONSTRUCTIONS_FRESH.obj);
    }
}

#[cfg_attr(
    feature = "export-runtime-ffi",
    export_name = "_ZN4lean27finalize_constructions_utilEv"
)]
pub extern "C" fn finalize_constructions_util() {
    unsafe {
        if !CONSTRUCTIONS_FRESH.obj.is_null() {
            lean_dec(CONSTRUCTIONS_FRESH.obj);
            CONSTRUCTIONS_FRESH.obj = ptr::null_mut();
        }
    }
}

#[cfg_attr(
    feature = "export-runtime-ffi",
    export_name = "_ZN4lean20get_init_fn_name_forERKNS_16elab_environmentERKNS_4nameE"
)]
pub unsafe extern "C" fn get_init_fn_name_for(
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

#[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
pub extern "C" fn lean_name_generator_tmp_prefix() -> *mut LeanObject {
    let guard = NAME_GENERATOR_STATE.lock().unwrap();
    guard.as_ref().map_or(ptr::null_mut(), |state| {
        unsafe {
            lean_inc(state.tmp_prefix);
        }
        state.tmp_prefix
    })
}

#[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
pub unsafe extern "C" fn lean_register_name_generator_prefix(n: *mut LeanObject) {
    let mut guard = NAME_GENERATOR_STATE.lock().unwrap();
    let state = guard.as_mut().expect("name generator registry is not initialized");
    assert!(!name_contains_registered_prefix(state, n));
    lean_inc(n);
    state.prefixes.push(n);
}

#[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
pub unsafe extern "C" fn lean_uses_name_generator_prefix(n: *mut LeanObject) -> bool {
    let guard = NAME_GENERATOR_STATE.lock().unwrap();
    let Some(state) = guard.as_ref() else {
        return false;
    };
    name_uses_registered_prefix(state, n)
}

#[cfg_attr(feature = "export-runtime-ffi", export_name = "_ZN4lean25initialize_name_generatorEv")]
pub extern "C" fn initialize_name_generator() {
    unsafe {
        let c_str = std::ffi::CString::new("_uniq").expect("static string has no NULs");
        let string = lean_mk_string(c_str.as_ptr());
        let tmp = lean_name_mk_string(lean_box(0), string);
        if get_env_var_cached!("LEAN_TRACE_MARK_PERSISTENT") {
            eprintln!("initialize_name_generator mark tmp={:p}", tmp);
        }
        lean_mark_persistent(tmp);
        let mut guard = NAME_GENERATOR_STATE.lock().unwrap();
        let state = NameGeneratorState {
            tmp_prefix: tmp,
            prefixes: vec![tmp],
        };
        *guard = Some(state);
    }
}

#[cfg_attr(feature = "export-runtime-ffi", export_name = "_ZN4lean15initialize_nameEv")]
pub extern "C" fn initialize_name() {
    INTERNAL_UNIQUE_NAME_ID.store(0, Ordering::Relaxed);
}

#[cfg_attr(feature = "export-runtime-ffi", export_name = "_ZN4lean13finalize_nameEv")]
pub extern "C" fn finalize_name() {}

#[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
pub extern "C" fn lean_name_next_internal_unique_id() -> c_uint {
    INTERNAL_UNIQUE_NAME_ID.fetch_add(1, Ordering::Relaxed)
}

#[cfg_attr(feature = "export-runtime-ffi", export_name = "_ZN4lean23finalize_name_generatorEv")]
pub extern "C" fn finalize_name_generator() {
    let mut guard = NAME_GENERATOR_STATE.lock().unwrap();
    if let Some(state) = guard.take() {
        for prefix in state.prefixes {
            unsafe { lean_dec(prefix) };
        }
    }
}

#[cfg_attr(feature = "export-runtime-ffi", export_name = "_ZN4lean20get_verbose_opt_nameEv")]
pub extern "C" fn get_verbose_opt_name() -> *const LeanName {
    core::ptr::addr_of!(VERBOSE_OPT)
}

#[cfg_attr(feature = "export-runtime-ffi", export_name = "_ZN4lean23get_max_memory_opt_nameEv")]
pub extern "C" fn get_max_memory_opt_name() -> *const LeanName {
    core::ptr::addr_of!(MAX_MEMORY_OPT)
}

#[cfg_attr(feature = "export-runtime-ffi", export_name = "_ZN4lean20get_timeout_opt_nameEv")]
pub extern "C" fn get_timeout_opt_name() -> *const LeanName {
    core::ptr::addr_of!(TIMEOUT_OPT)
}

#[cfg_attr(feature = "export-runtime-ffi", export_name = "_ZN4lean11get_verboseERKNS_7optionsE")]
pub unsafe extern "C" fn get_verbose(opts: *const LeanOptions) -> bool {
    let opts = (*opts).obj;
    let name = (*get_verbose_opt_name()).obj;
    lean_inc(opts);
    lean_inc(name);
    lean_options_get_bool(opts, name, 1) != 0
}

#[cfg_attr(feature = "export-runtime-ffi", export_name = "_ZN4lean7optionsC1Ev")]
pub unsafe extern "C" fn options_ctor_c1(this: *mut LeanOptions) {
    (*this).obj = lean_options_get_empty(lean_box(0));
}

#[cfg_attr(feature = "export-runtime-ffi", export_name = "_ZN4lean7optionsC2Ev")]
pub unsafe extern "C" fn options_ctor_c2(this: *mut LeanOptions) {
    options_ctor_c1(this);
}

#[cfg_attr(feature = "export-runtime-ffi", export_name = "_ZNK4lean7options8get_boolERKNS_4nameEb")]
pub unsafe extern "C" fn options_get_bool(
    this: *const LeanOptions,
    name: *const LeanName,
    default_value: bool,
) -> bool {
    let opts = (*this).obj;
    let name = (*name).obj;
    lean_inc(opts);
    lean_inc(name);
    lean_options_get_bool(opts, name, default_value as u8) != 0
}

#[cfg_attr(feature = "export-runtime-ffi", export_name = "_ZNK4lean7options6updateERKNS_4nameEb")]
pub unsafe extern "C" fn options_update(
    this: *const LeanOptions,
    name: *const LeanName,
    value: bool,
) -> LeanOptions {
    let opts = (*this).obj;
    let name = (*name).obj;
    lean_inc(opts);
    lean_inc(name);
    LeanOptions {
        obj: lean_options_update_bool(opts, name, value as u8),
    }
}

#[cfg_attr(feature = "export-runtime-ffi", export_name = "_ZN4lean12get_profilerERKNS_7optionsE")]
pub unsafe extern "C" fn get_profiler(opts: *const LeanOptions) -> bool {
    let opts = (*opts).obj;
    lean_inc(opts);
    lean_get_profiler(opts) != 0
}

#[cfg_attr(
    feature = "export-runtime-ffi",
    export_name = "_ZN4lean23get_profiling_thresholdERKNS_7optionsE"
)]
pub unsafe extern "C" fn get_profiling_threshold(opts: *const LeanOptions) -> f64 {
    let opts = (*opts).obj;
    lean_inc(opts);
    lean_get_profiler_threshold(opts)
}

#[cfg_attr(feature = "export-runtime-ffi", export_name = "_ZN4lean20initialize_profilingEv")]
pub extern "C" fn initialize_profiling() {}

#[cfg_attr(feature = "export-runtime-ffi", export_name = "_ZN4lean18finalize_profilingEv")]
pub extern "C" fn finalize_profiling() {}

#[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
pub extern "C" fn lean_internal_get_default_verbose(_: *mut LeanObject) -> u8 {
    true as u8
}

#[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
pub unsafe extern "C" fn lean_internal_get_default_options(_: *mut LeanObject) -> *mut LeanObject {
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
            opts = lean_options_update_bool(opts, name.obj, value as u8);
        }
    }
    opts
}

#[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
pub extern "C" fn lean_finalize() {
    run_thread_finalizers();
    run_post_thread_finalizers();
    delete_thread_finalizer_manager();
}

#[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
pub unsafe extern "C" fn lean_system_platform_nbits(_: *mut LeanObject) -> *mut LeanObject {
    lean_box(core::mem::size_of::<*const u8>() * 8)
}

#[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
pub extern "C" fn lean_system_platform_windows(_: *mut LeanObject) -> u8 {
    cfg!(target_os = "windows") as u8
}

#[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
pub extern "C" fn lean_system_platform_osx(_: *mut LeanObject) -> u8 {
    cfg!(target_os = "macos") as u8
}

#[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
pub unsafe extern "C" fn lean_system_platform_target(_: *mut LeanObject) -> *mut LeanObject {
    lean_mk_string(concat!(env!("LEAN_RUST_PLATFORM_TARGET"), "\0").as_ptr() as *const c_char)
}


static INITIALIZING: core::sync::atomic::AtomicBool = core::sync::atomic::AtomicBool::new(true);
const LEAN_RUNTIME_INITIALIZING_ENV: &str = "LEAN_RUNTIME_INITIALIZING";

#[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
pub extern "C" fn lean_io_mark_end_initialization() {
    INITIALIZING.store(false, Ordering::Relaxed);
    std::env::set_var(LEAN_RUNTIME_INITIALIZING_ENV, "0");
}

#[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
pub extern "C" fn lean_io_initializing() -> u8 {
    if matches!(std::env::var(LEAN_RUNTIME_INITIALIZING_ENV).as_deref(), Ok("0")) {
        return 0;
    }
    INITIALIZING.load(Ordering::Relaxed) as u8
}

#[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
pub unsafe extern "C" fn lean_version_get_major(_: *mut LeanObject) -> *mut LeanObject {
    lean_box(4)
}

#[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
pub unsafe extern "C" fn lean_version_get_minor(_: *mut LeanObject) -> *mut LeanObject {
    lean_box(32)
}

#[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
pub unsafe extern "C" fn lean_version_get_patch(_: *mut LeanObject) -> *mut LeanObject {
    lean_box(0)
}

#[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
pub extern "C" fn lean_version_get_is_release(_: *mut LeanObject) -> u8 {
    0
}

#[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
pub unsafe extern "C" fn lean_version_get_special_desc(_: *mut LeanObject) -> *mut LeanObject {
    lean_mk_string(b"\0".as_ptr() as *const c_char)
}

#[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
pub unsafe extern "C" fn lean_get_githash(_: *mut LeanObject) -> *mut LeanObject {
    lean_mk_string(concat!(env!("LEAN_RUST_GITHASH"), "\0").as_ptr() as *const c_char)
}

#[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
pub extern "C" fn lean_internal_has_llvm_backend(_: *mut LeanObject) -> u8 {
    env_flag(env!("LEAN_RUST_HAS_LLVM"))
}

#[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
pub extern "C" fn lean_internal_has_address_sanitizer(_: *mut LeanObject) -> u8 {
    env_flag(env!("LEAN_RUST_HAS_ADDRESS_SANITIZER"))
}

#[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
pub extern "C" fn lean_internal_is_multi_thread(_: *mut LeanObject) -> u8 {
    env_flag(env!("LEAN_RUST_MULTI_THREAD"))
}

#[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
pub extern "C" fn lean_internal_is_debug(_: *mut LeanObject) -> u8 {
    env_flag(env!("LEAN_RUST_DEBUG"))
}

#[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
pub unsafe extern "C" fn lean_internal_get_build_type(_: *mut LeanObject) -> *mut LeanObject {
    lean_mk_string(concat!(env!("LEAN_RUST_BUILD_TYPE"), "\0").as_ptr() as *const c_char)
}

#[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
pub unsafe extern "C" fn lean_get_leanc_extra_flags(_: *mut LeanObject) -> *mut LeanObject {
    lean_mk_string(concat!(env!("LEAN_RUST_LEANC_EXTRA_CC_FLAGS"), "\0").as_ptr() as *const c_char)
}

#[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
pub unsafe extern "C" fn lean_get_leanc_internal_flags(_: *mut LeanObject) -> *mut LeanObject {
    lean_mk_string(concat!(env!("LEAN_RUST_LEANC_INTERNAL_FLAGS"), "\0").as_ptr() as *const c_char)
}

#[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
pub unsafe extern "C" fn lean_get_linker_flags(link_static: u8) -> *mut LeanObject {
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
                env!("LEAN_RUST_LEAN_EXTRA_LINKER_FLAGS"),
                "\0"
            )
            .as_ptr() as *const c_char,
        )
    }
}

#[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
pub unsafe extern "C" fn lean_get_internal_linker_flags(_: *mut LeanObject) -> *mut LeanObject {
    lean_mk_string(concat!(env!("LEAN_RUST_LEANC_INTERNAL_LINKER_FLAGS"), "\0").as_ptr() as *const c_char)
}

type LeanMapForeachFn = extern "C" fn(*mut LeanObject, *mut LeanObject, *mut c_void);

unsafe fn lean_map_foreach_rbmap(
    m: *mut LeanObject,
    cb: LeanMapForeachFn,
    ctx: *mut c_void,
) {
    if lean_is_scalar(m) {
        return;
    }
    lean_map_foreach_rbmap(lean_ctor_get(m, 0), cb, ctx);
    cb(lean_ctor_get(m, 1), lean_ctor_get(m, 2), ctx);
    lean_map_foreach_rbmap(lean_ctor_get(m, 3), cb, ctx);
}

unsafe fn lean_map_foreach_entry(
    e: *mut LeanObject,
    cb: LeanMapForeachFn,
    ctx: *mut c_void,
) {
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
        cb(lean_array_get(ks, i), lean_array_get(vs, i), ctx);
    }
}

unsafe fn lean_map_foreach_entries(
    es: *mut LeanObject,
    cb: LeanMapForeachFn,
    ctx: *mut c_void,
) {
    for i in 0..lean_array_size(es) {
        lean_map_foreach_entry(lean_array_get(es, i), cb, ctx);
    }
}

unsafe fn lean_map_foreach_node(
    n: *mut LeanObject,
    cb: LeanMapForeachFn,
    ctx: *mut c_void,
) {
    if lean_ptr_tag(n) == 0 {
        lean_map_foreach_entries(lean_ctor_get(n, 0), cb, ctx);
    } else {
        lean_map_foreach_collision(lean_ctor_get(n, 0), lean_ctor_get(n, 1), cb, ctx);
    }
}

unsafe fn lean_map_foreach_hashmap(
    m: *mut LeanObject,
    cb: LeanMapForeachFn,
    ctx: *mut c_void,
) {
    let buckets = lean_ctor_get(m, 1);
    for i in 0..lean_array_size(buckets) {
        let mut lst = lean_array_get(buckets, i);
        while !lean_is_scalar(lst) {
            cb(lean_ctor_get(lst, 0), lean_ctor_get(lst, 1), ctx);
            lst = lean_ctor_get(lst, 2);
        }
    }
}

unsafe fn lean_map_foreach_smap(
    m: *mut LeanObject,
    cb: LeanMapForeachFn,
    ctx: *mut c_void,
) {
    lean_map_foreach_hashmap(lean_ctor_get(m, 0), cb, ctx);
    lean_map_foreach_node(lean_ctor_get(m, 1), cb, ctx);
}

#[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
pub unsafe extern "C" fn lean_rbmap_foreach(
    m: *mut LeanObject,
    cb: LeanMapForeachFn,
    ctx: *mut c_void,
) {
    lean_map_foreach_rbmap(m, cb, ctx);
}

#[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
pub unsafe extern "C" fn lean_phashmap_foreach(
    m: *mut LeanObject,
    cb: LeanMapForeachFn,
    ctx: *mut c_void,
) {
    lean_map_foreach_node(lean_ctor_get(m, 0), cb, ctx);
}

#[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
pub unsafe extern "C" fn lean_hashmap_foreach(
    m: *mut LeanObject,
    cb: LeanMapForeachFn,
    ctx: *mut c_void,
) {
    lean_map_foreach_hashmap(m, cb, ctx);
}

#[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
pub unsafe extern "C" fn lean_smap_foreach(
    m: *mut LeanObject,
    cb: LeanMapForeachFn,
    ctx: *mut c_void,
) {
    lean_map_foreach_smap(m, cb, ctx);
}

#[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
pub unsafe extern "C" fn lean_smap_foreach_test(m: *mut LeanObject) -> *mut LeanObject {
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

#[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
pub unsafe extern "C" fn lean_io_timeit(
    msg: *mut LeanObject,
    fn_obj: *mut LeanObject,
) -> *mut LeanObject {
    use std::io::{self, Write};
    use std::time::Instant;

    let start = Instant::now();
    let result = lean_apply_1(fn_obj, lean_box(0));
    let elapsed = start.elapsed().as_secs_f64();

    let prefix = cstr_lossy_to_string(lean_string_cstr(msg));
    let mut stderr = io::stderr().lock();
    let _ = if elapsed < 1.0 {
        stderr.write_fmt(format_args!("{prefix} {:.3}ms\n", elapsed * 1000.0))
    } else {
        stderr.write_fmt(format_args!("{prefix} {:.3}s\n", elapsed))
    };
    result
}

#[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
pub unsafe extern "C" fn lean_io_get_num_heartbeats() -> *mut LeanObject {
    extern "C" { fn lean_get_num_heartbeats() -> u64; }
    lean_uint64_to_nat_rust(lean_get_num_heartbeats())
}

#[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
pub unsafe extern "C" fn lean_io_set_heartbeats(count: *mut LeanObject) -> *mut LeanObject {
    extern "C" { fn lean_set_heartbeats(count: u64); }
    lean_set_heartbeats(lean_uint64_of_nat_rust(count));
    lean_dec(count);
    lean_box(0)
}

#[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
pub unsafe extern "C" fn lean_io_mono_ms_now() -> *mut LeanObject {
    use std::mem::MaybeUninit;
    use std::sync::Once;
    use std::time::Instant;

    static START_ONCE: Once = Once::new();
    static mut START: MaybeUninit<Instant> = MaybeUninit::uninit();
    START_ONCE.call_once(|| unsafe {
        START.write(Instant::now());
    });
    let start = unsafe { START.assume_init_ref() };
    lean_uint64_to_nat_rust(start.elapsed().as_millis() as u64)
}

#[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
pub unsafe extern "C" fn lean_io_mono_nanos_now() -> *mut LeanObject {
    use std::mem::MaybeUninit;
    use std::sync::Once;
    use std::time::Instant;

    static START_ONCE: Once = Once::new();
    static mut START: MaybeUninit<Instant> = MaybeUninit::uninit();
    START_ONCE.call_once(|| unsafe {
        START.write(Instant::now());
    });
    let start = unsafe { START.assume_init_ref() };
    lean_uint64_to_nat_rust(start.elapsed().as_nanos() as u64)
}

#[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
pub unsafe extern "C" fn lean_get_current_time() -> *mut LeanObject {
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

#[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
pub unsafe extern "C" fn lean_io_getenv(env_var: *mut LeanObject) -> *mut LeanObject {
    use std::ffi::{CStr, CString};

    let name_ptr = lean_string_cstr(env_var);
    if CStr::from_ptr(name_ptr).to_bytes().len() != lean_string_size(env_var) - 1 {
        return lean_box(0);
    }

    let name = cstr_lossy_to_string(name_ptr);

    match std::env::var(name) {
        Ok(value) => {
            let cstr = CString::new(value).expect("environment values must not contain NUL bytes");
            let mut fields = [lean_mk_string(cstr.as_ptr())];
            lean_runtime_mk_cnstr(1, 1, fields.as_mut_ptr(), 0)
        }
        Err(_) => lean_box(0),
    }
}

#[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
pub unsafe extern "C" fn lean_byteslice_beq(a: *mut LeanObject, b: *mut LeanObject) -> u8 {
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

#[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
pub unsafe extern "C" fn lean_runtime_mk_cnstr(
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

unsafe fn lean_io_result_mk_ok(value: *mut LeanObject) -> *mut LeanObject {
    let mut fields = [value];
    lean_runtime_mk_cnstr(0, 1, fields.as_mut_ptr(), 0)
}

unsafe fn lean_io_result_mk_error(error: *mut LeanObject) -> *mut LeanObject {
    let mut fields = [error];
    lean_runtime_mk_cnstr(1, 1, fields.as_mut_ptr(), 0)
}

unsafe fn lean_uint64_to_nat_rust(value: u64) -> *mut LeanObject {
    if value <= usize::MAX as u64 >> 1 {
        lean_box(value as usize)
    } else {
        lean_big_uint64_to_nat(value)
    }
}

unsafe fn lean_int64_to_int_rust(value: i64) -> *mut LeanObject {
    lean_big_int64_to_int(value)
}

unsafe fn lean_uint64_of_nat_rust(value: *mut LeanObject) -> u64 {
    if lean_is_scalar(value) {
        lean_unbox(value) as u64
    } else {
        lean_uint64_of_big_nat(value)
    }
}

pub(crate) unsafe fn lean_string_size(obj: *mut LeanObject) -> usize {
    let string = obj as *const LeanStringObject;
    (*string).m_size
}

pub(crate) unsafe fn lean_string_len(obj: *mut LeanObject) -> usize {
    let string = obj as *const LeanStringObject;
    (*string).m_length
}

#[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
pub extern "C" fn lean_runtime_is_utf8_next(byte: c_uchar) -> bool {
    byte & 0xC0 == 0x80
}

#[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
pub extern "C" fn lean_runtime_get_utf8_size(byte: c_uchar) -> c_uint {
    utf8_size(byte) as c_uint
}

#[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
pub unsafe extern "C" fn lean_utf8_strlen(mut text: *const c_char) -> Size {
    let mut length = 0;
    while *text != 0 {
        let size = utf8_size(*text as c_uchar);
        length += 1;
        text = text.add(size);
    }
    length
}

#[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
pub unsafe extern "C" fn lean_utf8_n_strlen(text: *const c_char, byte_size: Size) -> Size {
    let mut length = 0;
    let mut offset = 0;
    while offset < byte_size {
        let size = utf8_size(*text.add(offset) as c_uchar);
        length += 1;
        offset += size;
    }
    length
}

#[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
pub unsafe extern "C" fn lean_runtime_utf8_char_pos(
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

#[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
pub unsafe extern "C" fn lean_runtime_get_utf8_last_char(mut text: *const c_char) -> *const c_char {
    let mut last = text;
    while *text != 0 {
        last = text;
        text = text.add(utf8_size(*text as c_uchar));
    }
    last
}

#[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
pub unsafe extern "C" fn lean_runtime_utf8_to_unicode(
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

#[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
pub unsafe extern "C" fn lean_runtime_get_utf8_first_byte_size(
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

#[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
pub unsafe extern "C" fn lean_runtime_next_utf8(
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
        let scalar =
            ((byte & 0x07) << 18) | ((b1 & 0x3f) << 12) | ((b2 & 0x3f) << 6) | (b3 & 0x3f);
        if (0x10000..=0x10FFFF).contains(&scalar) {
            *pos = i + 4;
            return scalar;
        }
    }

    *pos = i + 1;
    byte
}

#[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
pub unsafe extern "C" fn lean_runtime_validate_utf8_one(
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
        let scalar =
            ((byte & 0x07) << 18) | ((b1 & 0x3f) << 12) | ((b2 & 0x3f) << 6) | (b3 & 0x3f);
        if !(0x10000..=0x10FFFF).contains(&scalar) {
            return false;
        }
        *pos = i + 4;
        return true;
    }

    false
}

#[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
pub unsafe extern "C" fn lean_runtime_validate_utf8(
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

#[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
pub unsafe extern "C" fn lean_runtime_push_unicode_scalar(dst: *mut c_char, code: c_uint) -> c_uint {
    const TAG_CONT: c_uint = 0b10000000;
    const TAG_TWO_B: c_uint = 0b11000000;
    const TAG_THREE_B: c_uint = 0b11100000;
    const TAG_FOUR_B: c_uint = 0b11110000;

    let bytes = if code < 0x80 {
        [code, 0, 0, 0]
    } else if code < 0x800 {
        [((code >> 6) & 0x1F) | TAG_TWO_B, (code & 0x3F) | TAG_CONT, 0, 0]
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

#[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
pub unsafe extern "C" fn lean_runtime_hash_str(len: Size, text: *const c_uchar, seed: u64) -> u64 {
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

#[cfg(test)]
mod tests {
    use super::*;
    use std::ffi::CString;

    unsafe fn mk_test_string(text: &str) -> *mut LeanObject {
        let c_text = CString::new(text).unwrap();
        lean_mk_string(c_text.as_ptr())
    }

    unsafe fn mk_test_name(parts: &[&str]) -> *mut LeanObject {
        let mut prefix = lean_box(0);
        for part in parts {
            let string = mk_test_string(part);
            prefix = lean_name_mk_string(prefix, string);
        }
        prefix
    }

    unsafe fn mk_test_numeral_name(parts: &[u64]) -> *mut LeanObject {
        let mut prefix = lean_box(0);
        for part in parts {
            let n = lean_big_uint64_to_nat(*part);
            prefix = lean_name_mk_numeral(prefix, n);
        }
        prefix
    }

    #[test]
    fn flexible_array_tails_match_c_layout_offsets() {
        assert_eq!(
            core::mem::offset_of!(LeanArrayObject, m_data),
            core::mem::size_of::<LeanArrayObject>()
        );
        assert_eq!(
            core::mem::offset_of!(LeanScalarArray, m_data),
            core::mem::size_of::<LeanScalarArray>()
        );
        assert_eq!(
            core::mem::offset_of!(LeanStringObject, m_data),
            core::mem::size_of::<LeanStringObject>()
        );
        assert_eq!(
            core::mem::offset_of!(LeanClosureObject, m_objs),
            core::mem::size_of::<LeanClosureObject>()
        );
    }

    #[test]
    fn object_header_and_tail_offsets_are_stable() {
        assert_eq!(core::mem::size_of::<LeanObject>(), 8);
        assert_eq!(core::mem::offset_of!(LeanArrayObject, m_data), 24);
        assert_eq!(core::mem::offset_of!(LeanScalarArray, m_data), 24);
        assert_eq!(core::mem::offset_of!(LeanStringObject, m_data), 32);
        assert_eq!(core::mem::offset_of!(LeanClosureObject, m_objs), 24);
    }

    #[test]
    fn ctor_scalar_tail_uses_byte_offsets() {
        unsafe {
            let obj = lean_alloc_ctor(0, 4, core::mem::size_of::<u32>() as c_uint);
            lean_ctor_set(obj, 0, lean_box(11));
            lean_ctor_set(obj, 1, lean_box(22));
            lean_ctor_set(obj, 2, lean_box(33));
            lean_ctor_set(obj, 3, lean_box(44));
            lean_ctor_set_uint32(obj, core::mem::size_of::<*mut LeanObject>() * 4, 0xfeed_beefu32);

            assert_eq!(lean_unbox(lean_ctor_get(obj, 0)) as usize, 11);
            assert_eq!(lean_unbox(lean_ctor_get(obj, 1)) as usize, 22);
            assert_eq!(lean_unbox(lean_ctor_get(obj, 2)) as usize, 33);
            assert_eq!(lean_unbox(lean_ctor_get(obj, 3)) as usize, 44);
            let tail = (obj as *const u8).add(
                core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>() * 4,
            ) as *const u32;
            assert_eq!(tail.read_unaligned(), 0xfeed_beefu32);
            lean_dec(obj);
        }
    }

    #[test]
    fn ctor_usize_tail_uses_pointer_field_index() {
        unsafe {
            let obj = lean_alloc_ctor(0, 4, core::mem::size_of::<usize>() as c_uint);
            lean_ctor_set(obj, 0, lean_box(11));
            lean_ctor_set(obj, 1, lean_box(22));
            lean_ctor_set(obj, 2, lean_box(33));
            lean_ctor_set(obj, 3, lean_box(44));
            lean_ctor_set_usize(obj, 4, 0x1234_5678_9abc_def0usize);

            assert_eq!(lean_unbox(lean_ctor_get(obj, 0)) as usize, 11);
            assert_eq!(lean_unbox(lean_ctor_get(obj, 1)) as usize, 22);
            assert_eq!(lean_unbox(lean_ctor_get(obj, 2)) as usize, 33);
            assert_eq!(lean_unbox(lean_ctor_get(obj, 3)) as usize, 44);
            assert_eq!(lean_ctor_get_usize(obj, 4), 0x1234_5678_9abc_def0usize);
            lean_dec(obj);
        }
    }

    #[test]
    fn name_equality_uses_stable_layout() {
        unsafe {
            let n1 = mk_test_name(&["Lean", "Meta", "Expr"]);
            let n2 = mk_test_name(&["Lean", "Meta", "Expr"]);
            let n3 = mk_test_name(&["Lean", "Meta", "Decl"]);
            let n4 = mk_test_numeral_name(&[1, 2, 3]);
            let n5 = mk_test_numeral_name(&[1, 2, 3]);
            let n6 = mk_test_numeral_name(&[1, 2, 4]);
            assert_eq!(lean_name_eq(n1, n2), 1);
            assert_eq!(lean_name_eq(n1, n3), 0);
            assert_eq!(lean_name_eq(n4, n5), 1);
            assert_eq!(lean_name_eq(n4, n6), 0);
        }
    }

    #[test]
    fn string_hash_is_deterministic() {
        unsafe {
            let s = mk_test_string("builtin");
            assert_eq!(lean_string_hash_export(s), lean_string_hash_export(s));
        }
    }

    #[test]
    fn array_pop_updates_size_field_not_payload() {
        unsafe {
            let a = lean_alloc_array(2, 2);
            let data = lean_array_cptr(a);
            data.write(lean_box(11));
            data.add(1).write(lean_box(22));

            let a = lean_array_pop_export(a);
            assert_eq!(lean_array_size(a), 1);
            assert_eq!(lean_unbox(*lean_array_cptr(a)) as usize, 11);
        }
    }

    #[test]
    fn array_uset_on_shared_array_clones_and_preserves_size() {
        unsafe {
            let a = lean_alloc_array(1, 1);
            let data = lean_array_cptr(a);
            data.write(lean_box(11));

            lean_inc_ref(a);
            let b = lean_array_uset_export(a, 0, lean_box(22));

            assert_ne!(a, b);
            assert_eq!(lean_array_size(a), 1);
            assert_eq!(lean_array_size(b), 1);
            assert_eq!(lean_unbox(*lean_array_cptr(a)) as usize, 11);
            assert_eq!(lean_unbox(*lean_array_cptr(b)) as usize, 22);

            lean_dec(a);
            lean_dec(b);
        }
    }

    #[test]
    fn compat_size_exports_return_boxed_nats() {
        unsafe {
            let s = mk_test_string("Lean");
            let a = lean_alloc_array(3, 3);

            let string_len = lean_string_length_export(s);
            let string_bytes = lean_string_utf8_byte_size_export(s);
            let array_size = lean_array_get_size_export(a);

            assert!(lean_is_scalar(string_len));
            assert!(lean_is_scalar(string_bytes));
            assert!(lean_is_scalar(array_size));
            assert_eq!(lean_unbox(string_len) as usize, 4);
            assert_eq!(lean_unbox(string_bytes) as usize, 4);
            assert_eq!(lean_unbox(array_size) as usize, 3);
        }
    }

    #[test]
    fn usize_boxes_use_ctor_scalar_payload() {
        unsafe {
            let value = usize::MAX / 3;
            let boxed = lean_box_usize_export(value);

            assert!(!lean_is_scalar(boxed));
            assert_eq!(lean_obj_tag(boxed), 0);
            assert_eq!(lean_unbox_usize_export(boxed), value);

            lean_dec(boxed);
        }
    }

    #[test]
    fn scalar_objects_are_not_exclusive() {
        unsafe {
            assert!(!lean_is_exclusive(lean_box(0)));
            assert!(!lean_is_exclusive(lean_box(42)));
        }
    }

    // Regression test: lean_unbox_uint64 must NOT call lean_dec internally.
    // The LCNF ExplicitRC pass emits an explicit lean_dec_ref after each unbox
    // when the boxed object is dead.  If the unbox function also calls lean_dec,
    // the result is a double-decrement that corrupts glibc's tcache and causes
    // a crash in the next 16-byte malloc.
    #[test]
    fn unbox_uint64_is_non_consuming() {
        unsafe {
            let boxed = lean_box_uint64(0xDEAD_BEEF_1234_5678u64);
            // RC = 1 after allocation.
            assert_eq!((*boxed).m_rc, 1);

            // Simulates the LCNF pattern where the same boxed value is unboxed
            // twice (e.g. once for a `<` comparison, once for a `==` comparison)
            // before the explicit lean_dec_ref that the compiler emits.
            let v1 = lean_unbox_uint64(boxed);
            assert_eq!(v1, 0xDEAD_BEEF_1234_5678u64);
            // RC must still be 1 — unbox must not consume/free.
            assert_eq!((*boxed).m_rc, 1, "lean_unbox_uint64 must not decrement RC");

            let v2 = lean_unbox_uint64(boxed);
            assert_eq!(v2, 0xDEAD_BEEF_1234_5678u64);
            assert_eq!((*boxed).m_rc, 1, "second unbox must not decrement RC either");

            // Now simulate the explicit LCNF dec.
            lean_dec_ref(boxed);
            // The object is now freed.  We must NOT read (*boxed).m_rc here —
            // that would be a UAF.  The test just verifies we get here without
            // crashing (no double-free / tcache corruption).
        }
    }

    // Regression test: lean_unbox_float must NOT call lean_dec internally.
    #[test]
    fn unbox_float_is_non_consuming() {
        unsafe {
            use crate::generated_abi::{lean_box_float, lean_unbox_float};
            let boxed = lean_box_float(3.14f64);
            assert_eq!((*boxed).m_rc, 1);
            let v1 = lean_unbox_float(boxed);
            assert_eq!(v1, 3.14f64);
            assert_eq!((*boxed).m_rc, 1, "lean_unbox_float must not decrement RC");
            lean_dec_ref(boxed as *mut LeanObject);
        }
    }
}
pub mod runtime_numeric_exports;
pub mod runtime_numeric_exports_int;
pub mod runtime_misc_exports;
