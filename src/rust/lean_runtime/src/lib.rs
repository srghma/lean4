/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

#![cfg_attr(not(feature = "std"), no_std)]

use core::ffi::{c_char, c_uchar, c_uint, c_void};
use core::sync::atomic::{AtomicI32, AtomicU32, Ordering};
use core::ptr;
#[cfg(not(feature = "std"))]
use core::panic::PanicInfo;

type Size = usize;

extern "C" {
    pub fn lean_mk_string(text: *const c_char) -> *mut LeanObject;
    fn lean_alloc_ctor_memory_export(size: Size) -> *mut LeanObject;
    fn lean_dec_ref_cold(obj: *mut LeanObject);
    fn lean_big_int64_to_int(n: i64) -> *mut LeanObject;
    fn lean_big_uint64_to_nat(n: u64) -> *mut LeanObject;
    fn lean_uint64_of_big_nat(n: *mut LeanObject) -> u64;
    fn lean_get_num_heartbeats() -> u64;
    fn lean_set_heartbeats(count: u64);
    fn lean_io_eprintln(msg: *mut LeanObject) -> *mut LeanObject;
    fn lean_apply_1(f: *mut LeanObject, a1: *mut LeanObject) -> *mut LeanObject;
    fn lean_io_error_to_string(err: *mut LeanObject) -> *mut LeanObject;
    #[link_name = "_ZN4lean15save_stack_infoEb"]
    fn save_stack_info_impl(main: bool);
    #[link_name = "_ZN4lean16initialize_allocEv"]
    fn initialize_alloc();
    #[link_name = "_ZN4lean14finalize_allocEv"]
    fn finalize_alloc();
    #[link_name = "_ZN4lean16initialize_debugEv"]
    fn initialize_debug();
    #[link_name = "_ZN4lean14finalize_debugEv"]
    fn finalize_debug();
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
    #[link_name = "_ZN4lean16initialize_mutexEv"]
    fn initialize_mutex();
    #[link_name = "_ZN4lean14finalize_mutexEv"]
    fn finalize_mutex();
    #[link_name = "_ZN4lean18initialize_processEv"]
    fn initialize_process();
    #[link_name = "_ZN4lean16finalize_processEv"]
    fn finalize_process();
    #[link_name = "_ZN4lean25initialize_stack_overflowEv"]
    fn initialize_stack_overflow();
    #[link_name = "_ZN4lean23finalize_stack_overflowEv"]
    fn finalize_stack_overflow();
    fn initialize_libuv();
    // #[link_name = "_ZN4lean16initialize_asciiEv"]
    // fn initialize_ascii_impl();
    // #[link_name = "_ZN4lean14finalize_asciiEv"]
    // fn finalize_ascii_impl();
    #[link_name = "_ZN4lean15initialize_nameEv"]
    fn initialize_name();
    #[link_name = "_ZN4lean13finalize_nameEv"]
    fn finalize_name();
    #[link_name = "_ZN4lean25initialize_name_generatorEv"]
    fn initialize_name_generator();
    #[link_name = "_ZN4lean23finalize_name_generatorEv"]
    fn finalize_name_generator();
    #[link_name = "_ZN4lean18initialize_optionsEv"]
    fn initialize_options();
    #[link_name = "_ZN4lean16finalize_optionsEv"]
    fn finalize_options();
    #[link_name = "_ZN4lean20initialize_formatterEv"]
    fn initialize_formatter();
    #[link_name = "_ZN4lean18finalize_formatterEv"]
    fn finalize_formatter();
    #[link_name = "_ZN4lean20initialize_constantsEv"]
    fn initialize_constants();
    #[link_name = "_ZN4lean18finalize_constantsEv"]
    fn finalize_constants();
    #[link_name = "_ZN4lean20initialize_profilingEv"]
    fn initialize_profiling();
    #[link_name = "_ZN4lean18finalize_profilingEv"]
    fn finalize_profiling();
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
    #[link_name = "_ZN4lean17initialize_dynlibEv"]
    fn initialize_dynlib();
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
    #[link_name = "_ZN4lean29initialize_constructions_utilEv"]
    fn initialize_constructions_util();
    #[link_name = "_ZN4lean27finalize_constructions_utilEv"]
    fn finalize_constructions_util();
    #[link_name = "_ZN4lean21init_default_print_fnEv"]
    fn init_default_print_fn_impl();
    #[link_name = "_ZN4lean21run_thread_finalizersEv"]
    fn run_thread_finalizers_impl();
    #[link_name = "_ZN4lean26run_post_thread_finalizersEv"]
    fn run_post_thread_finalizers_impl();
    #[link_name = "_ZN4lean31delete_thread_finalizer_managerEv"]
    fn delete_thread_finalizer_manager_impl();
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
struct LeanScalarArray {
    header: LeanObject,
    size: Size,
    capacity: Size,
    data: [u8; 0],
}

#[repr(C)]
struct LeanCtorObject {
    header: LeanObject,
    objs: [*mut LeanObject; 0],
}

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

unsafe fn lean_inc_ref_n(obj: *mut LeanObject, n: usize) {
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

pub unsafe fn lean_dec(obj: *mut LeanObject) {
    if !lean_is_scalar(obj) {
        lean_dec_ref(obj);
    }
}

unsafe fn lean_ctor_get(obj: *mut LeanObject, idx: usize) -> *mut LeanObject {
    (obj.add(1) as *mut *mut LeanObject).add(idx).read()
}

unsafe fn lean_array_get(obj: *mut LeanObject, idx: usize) -> *mut LeanObject {
    let array = obj as *const LeanArrayObject;
    (*array).data.as_ptr().add(idx).read()
}

unsafe fn lean_array_size(obj: *mut LeanObject) -> usize {
    let array = obj as *const LeanArrayObject;
    (*array).size
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

unsafe fn lean_sarray_cptr(obj: *mut LeanObject) -> *const u8 {
    let array = obj as *const LeanScalarArray;
    (*array).data.as_ptr()
}

pub unsafe fn lean_string_cstr(obj: *mut LeanObject) -> *const c_char {
    let string = obj as *const LeanStringObject;
    (*string).data.as_ptr()
}

pub unsafe fn lean_box(value: Size) -> *mut LeanObject {
    ((value << 1) | 1) as *mut LeanObject
}

fn align(value: Size, alignment: Size) -> Size {
    (value / alignment) * alignment + alignment * Size::from(value % alignment != 0)
}

unsafe fn set_st_header(obj: *mut LeanObject, tag: c_uint, other: c_uint) {
    (*obj).rc = 1;
    (*obj).tag = tag as u8;
    (*obj).other = other as u8;
    if env_flag(env!("LEAN_RUST_HAS_MIMALLOC")) == 0 {
        (*obj).cs_size = 0;
    }
}

fn env_flag(value: &str) -> u8 {
    if value.as_bytes() == b"1" {
        1
    } else {
        0
    }
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

#[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
pub extern "C" fn save_stack_info(main: bool) {
    unsafe { save_stack_info_impl(main) }
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
    unsafe { run_thread_finalizers_impl() }
}

#[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
pub extern "C" fn run_post_thread_finalizers() {
    unsafe { run_post_thread_finalizers_impl() }
}

#[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
pub extern "C" fn delete_thread_finalizer_manager() {
    unsafe { delete_thread_finalizer_manager_impl() }
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

#[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
pub extern "C" fn lean_finalize() {
    unsafe {
        run_thread_finalizers();
        run_post_thread_finalizers();
        delete_thread_finalizer_manager();
    }
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
    const OBJECT_SIZE_DELTA: Size = 8;
    let size = core::mem::size_of::<LeanCtorObject>()
        + core::mem::size_of::<*mut LeanObject>() * num_objs as Size
        + scalar_size as Size;
    let aligned_size = align(size, OBJECT_SIZE_DELTA);
    let obj = lean_alloc_ctor_memory_export(size);
    if aligned_size > size {
        let end = (obj as *mut u8).add(aligned_size) as *mut Size;
        end.sub(1).write(0);
    }
    set_st_header(obj, tag, num_objs);
    let dst = (obj as *mut LeanCtorObject).cast::<u8>().add(core::mem::size_of::<LeanObject>())
        as *mut *mut LeanObject;
    for index in 0..num_objs as Size {
        dst.add(index).write(objs.add(index).read());
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

unsafe fn lean_string_size(obj: *mut LeanObject) -> usize {
    let string = obj as *const LeanStringObject;
    (*string).size
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
