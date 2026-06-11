/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

#![cfg_attr(not(feature = "std"), no_std)]

use core::ffi::{c_char, c_int, c_long, c_uchar, c_uint, c_void, CStr};
use core::sync::atomic::{AtomicBool, AtomicI32, AtomicU32, Ordering};
use core::ptr;
#[cfg(not(feature = "std"))]
use core::panic::PanicInfo;

type Size = usize;

extern "C" {
    pub fn lean_mk_string(text: *const c_char) -> *mut LeanObject;
    fn lean_mk_string_from_bytes(text: *const c_char, size: Size) -> *mut LeanObject;
    fn lean_name_mk_string(prefix: *mut LeanObject, s: *mut LeanObject) -> *mut LeanObject;
    fn lean_dec_ref_cold(obj: *mut LeanObject);
    fn lean_mark_persistent(obj: *mut LeanObject);
    fn lean_mk_io_user_error(msg: *mut LeanObject) -> *mut LeanObject;
    fn lean_mk_io_error_invalid_argument(errnum: u32, details: *mut LeanObject) -> *mut LeanObject;
    fn lean_alloc_object(size: Size) -> *mut LeanObject;
    #[link_name = "_ZN4lean21mk_embedded_nul_errorEP11lean_object"]
    fn mk_embedded_nul_error(str: *mut LeanObject) -> *mut LeanObject;
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
    #[link_name = "_ZN4lean20lean_promise_resolveEP11lean_objectS1_"]
    fn lean_promise_resolve(value: *mut LeanObject, promise: *mut LeanObject);
    fn lean_decode_io_error(errnum: c_int, fname: *mut LeanObject) -> *mut LeanObject;
    fn lean_io_eprintln(msg: *mut LeanObject) -> *mut LeanObject;
    fn lean_io_promise_new() -> *mut LeanObject;
    fn lean_io_promise_resolve(value: *mut LeanObject, promise: *mut LeanObject) -> *mut LeanObject;
    fn lean_io_get_task_state_core(task: *mut LeanObject) -> u8;
    fn lean_mark_mt(obj: *mut LeanObject);
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
    #[link_name = "_ZN4lean25initialize_ir_interpreterEv"]
    fn initialize_ir_interpreter();
    #[link_name = "_ZN4lean23finalize_ir_interpreterEv"]
    fn finalize_ir_interpreter();
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
    #[link_name = "_ZN4lean21init_default_print_fnEv"]
    fn init_default_print_fn_impl();
    fn initialize_Init(builtin: u8) -> *mut LeanObject;
    fn initialize_Std(builtin: u8) -> *mut LeanObject;
    fn initialize_Lean(builtin: u8) -> *mut LeanObject;
    }

#[repr(C)]
pub struct LeanObject {
    rc: i32,
    cs_size: u16,
    other: u8,
    tag: u8,
}

#[repr(C)]
struct LeanListCell {
    rc: AtomicU32,
    head: c_uint,
    tail: *mut LeanListCell,
}

#[repr(C)]
struct LeanArrayObject {
    header: LeanObject,
    size: Size,
    capacity: Size,
    data: [*mut LeanObject; 0],
}

#[repr(C)]
struct LeanStringObject {
    header: LeanObject,
    size: Size,
    capacity: Size,
    len: Size,
    data: [c_char; 0],
}

#[repr(C)]
struct LeanClosureObject {
    header: LeanObject,
    fun: *mut c_void,
    arity: u16,
    num_fixed: u16,
    data: [*mut LeanObject; 0],
}

#[repr(C)]
struct LeanScalarArray {
    header: LeanObject,
    size: Size,
    capacity: Size,
    data: [u8; 0],
}

#[repr(C)]
struct LeanPromiseObject {
    header: LeanObject,
    result: *mut LeanObject,
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

pub unsafe fn lean_unbox(obj: *mut LeanObject) -> Size {
    (obj as Size) >> 1
}

pub unsafe fn lean_is_scalar(obj: *mut LeanObject) -> bool {
    (obj as Size) & 1 == 1
}

pub unsafe fn lean_ptr_tag(obj: *mut LeanObject) -> u8 {
    if lean_is_scalar(obj) {
        lean_unbox(obj) as u8
    } else {
        (*obj).tag
    }
}

pub unsafe fn lean_obj_tag(obj: *mut LeanObject) -> u8 {
    lean_ptr_tag(obj)
}

pub(crate) unsafe fn lean_inc_ref_n(obj: *mut LeanObject, n: usize) {
    if (*obj).rc > 0 {
        (*obj).rc += n as i32;
    } else if (*obj).rc != 0 {
        let rc = (&raw mut (*obj).rc).cast::<AtomicI32>();
        (*rc).fetch_sub(n as i32, Ordering::Relaxed);
    }
}

pub unsafe fn lean_inc_ref(obj: *mut LeanObject) {
    lean_inc_ref_n(obj, 1);
}

unsafe fn lean_dec_ref(obj: *mut LeanObject) {
    if (*obj).rc > 1 {
        (*obj).rc -= 1;
    } else if (*obj).rc != 0 {
        lean_dec_ref_cold(obj);
    }
}

pub unsafe fn lean_inc(obj: *mut LeanObject) {
    if !lean_is_scalar(obj) {
        lean_inc_ref(obj);
    }
}

pub unsafe fn lean_inc_n(obj: *mut LeanObject, n: usize) {
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

pub unsafe fn lean_box_uint64(v: u64) -> *mut LeanObject {
    let r = lean_runtime_alloc_ctor(0, 0, core::mem::size_of::<u64>() as c_uint);
    lean_ctor_set_uint64(r, 0, v);
    r
}

pub unsafe fn lean_unbox_uint64(o: *mut LeanObject) -> u64 {
    lean_ctor_get_uint64(o, 0)
}


unsafe fn lean_array_get(obj: *mut LeanObject, idx: usize) -> *mut LeanObject {
    let array_data_ptr = (obj as *const u8).add(24) as *const *mut LeanObject;
    array_data_ptr.add(idx).read()
}

unsafe fn lean_array_size(obj: *mut LeanObject) -> usize {
    let array = obj as *const LeanArrayObject;
    (*array).size
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
    (*obj).header.rc = 1;
    (*obj).header.cs_size = 0;
    (*obj).header.other = 0;
    (*obj).header.tag = LEAN_ARRAY_TAG;
    (*obj).size = size;
    (*obj).capacity = capacity;
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
    (*obj).header.rc = 1;
    (*obj).header.cs_size = 0;
    (*obj).header.other = elem_size as u8;
    (*obj).header.tag = LEAN_SCALAR_ARRAY_TAG;
    (*obj).size = size;
    (*obj).capacity = capacity;
    obj as *mut LeanObject
}

pub(crate) unsafe fn lean_alloc_string(size: usize, capacity: usize, len: usize) -> *mut LeanObject {
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

unsafe fn lean_sarray_set_size(obj: *mut LeanObject, size: Size) {
    let sarray = obj as *mut LeanScalarArray;
    (*sarray).size = size;
}

unsafe fn lean_sarray_size(obj: *mut LeanObject) -> Size {
    let sarray = obj as *const LeanScalarArray;
    (*sarray).size
}

unsafe fn lean_sarray_capacity(obj: *mut LeanObject) -> Size {
    let sarray = obj as *const LeanScalarArray;
    (*sarray).capacity
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


unsafe fn lean_sarray_cptr(obj: *mut LeanObject) -> *const u8 {
    (obj as *const u8).add(24)
}

pub unsafe fn lean_string_cstr(obj: *mut LeanObject) -> *const c_char {
    (obj as *const u8).add(32) as *const c_char
}

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

include!("library_constants.rs");
include!("library_dynlib.rs");
include!("runtime_apply.rs");
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
include!("runtime_object_panic.rs");
include!("runtime_object_size.rs");
include!("runtime_object_array.rs");
include!("runtime_object_rc.rs");
include!("runtime_sharecommon.rs");
include!("runtime_thread.rs");
include!("runtime_once.rs");
include!("runtime_float.rs");
include!("runtime_mpz.rs");
include!("runtime_object_nat_int.rs");
include!("runtime_object_string.rs");
include!("runtime_object_name.rs");

#[cfg_attr(feature = "export-runtime-ffi", export_name = "lean_name_eq")]
pub unsafe extern "C" fn lean_name_eq_export(n1: *mut LeanObject, n2: *mut LeanObject) -> u8 {
    runtime_object_name_impl::lean_name_eq(n1, n2)
}

#[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
pub extern "C" fn lean_io_mk_world() -> *mut LeanObject {
    unsafe { lean_box(0) }
}

#[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
pub unsafe extern "C" fn lean_io_allocprof(
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

extern "C" {
    fn write(fd: i32, buf: *const u8, count: usize) -> isize;
    fn abort() -> !;
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


    }
}

unsafe fn initialize_runtime_module_body() {
    initialize_alloc();
    initialize_debug();
    initialize_object();
    initialize_io();
    initialize_thread();
    initialize_mutex();
    initialize_process();
    initialize_stack_overflow();
    initialize_libuv();
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
    initialize_level();
    initialize_expr();
    initialize_declaration();
    initialize_type_checker();
    initialize_environment();
    initialize_local_ctx();
    initialize_inductive();
    initialize_quot();
    initialize_trace();
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
    initialize_ir_interpreter();
}

unsafe fn finalize_library_module_body() {
    finalize_ir_interpreter();
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

#[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
pub extern "C" fn init_default_print_fn() {
    unsafe { init_default_print_fn_impl() }
}

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
        save_stack_info(true);
        initialize_util_module();
        let builtin = 1u8;
        consume_io_result(initialize_Init(builtin));
        consume_io_result(initialize_Std(builtin));
        consume_io_result(initialize_Lean(builtin));
        initialize_kernel_module();
        init_default_print_fn();
        initialize_library_core_module();
        initialize_library_module();
        initialize_constructions_module();
    }
}

#[cfg_attr(feature = "export-runtime-ffi", export_name = "_ZN4lean18initialize_optionsEv")]
pub extern "C" fn initialize_options() {
    unsafe {
        VERBOSE_OPT = mk_name("verbose");
        MAX_MEMORY_OPT = mk_name("max_memory");
        TIMEOUT_OPT = mk_name("timeout");
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
    lean_options_get_bool(opts, name, true)
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
    lean_options_get_bool(opts, name, default_value)
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
        obj: lean_options_update_bool(opts, name, value),
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
            opts = lean_options_update_bool(opts, name.obj, value);
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
pub extern "C" fn lean_system_platform_emscripten(_: *mut LeanObject) -> u8 {
    cfg!(target_os = "emscripten") as u8
}

static INITIALIZING: core::sync::atomic::AtomicBool = core::sync::atomic::AtomicBool::new(true);

#[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
pub extern "C" fn lean_io_mark_end_initialization() {
    INITIALIZING.store(false, Ordering::Relaxed);
}

#[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
pub extern "C" fn lean_io_initializing() -> u8 {
    INITIALIZING.load(Ordering::Relaxed) as u8
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

#[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
pub unsafe extern "C" fn lean_io_get_num_heartbeats() -> *mut LeanObject {
    lean_uint64_to_nat_rust(lean_get_num_heartbeats())
}

#[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
pub unsafe extern "C" fn lean_io_set_heartbeats(count: *mut LeanObject) -> *mut LeanObject {
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

pub(crate) unsafe fn lean_string_size(obj: *mut LeanObject) -> usize {
    let string = obj as *const LeanStringObject;
    (*string).size
}

pub(crate) unsafe fn lean_string_len(obj: *mut LeanObject) -> usize {
    let string = obj as *const LeanStringObject;
    (*string).len
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
