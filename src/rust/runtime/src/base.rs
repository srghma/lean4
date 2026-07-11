/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

#![allow(dead_code, non_upper_case_globals)]

use core::ffi::{CStr, c_char, c_int, c_long, c_uchar, c_uint, c_void};
use core::ptr;
use core::sync::atomic::{AtomicBool, AtomicI32, AtomicPtr, AtomicU32, Ordering};
use leanh::{
    LEAN_ARRAY_TAG, LEAN_CLOSURE_TAG, LEAN_EXTERNAL_TAG, LEAN_MAX_CTOR_TAG, LEAN_OBJECT_SIZE_DELTA,
    LEAN_SCALAR_ARRAY_TAG, LEAN_STRING_TAG, LeanArrayObject, LeanClosureObject, LeanCtorObject,
    LeanExternalClass, LeanExternalFinalizeProc, LeanExternalForeachProc, LeanExternalObject,
    LeanMpzObject, LeanObject, LeanPromiseObject, LeanScalarArray, LeanStringObject, LeanTaskImp,
    LeanTaskObject, Size,
};

unsafe extern "C" {
    pub fn lean_mk_io_user_error(msg: *mut LeanObject) -> *mut LeanObject;
    pub fn lean_alloc_object(size: Size) -> *mut LeanObject; // duplicate in src/rust/leanh/src/not_in_emit_rust.rs at line 459 (🔁)
    pub fn lean_array_push(array: *mut LeanObject, value: *mut LeanObject) -> *mut LeanObject;
    pub fn lean_decode_uv_error(errnum: c_int, fname: *mut LeanObject) -> *mut LeanObject;
    pub fn lean_io_eprintln(msg: *mut LeanObject) -> *mut LeanObject;
    pub fn lean_promise_resolve(value: *mut LeanObject, promise: *mut LeanObject);
    pub fn lean_io_promise_new() -> *mut LeanObject;
    pub fn lean_io_promise_resolve(
        value: *mut LeanObject,
        promise: *mut LeanObject,
    ) -> *mut LeanObject;
    pub fn lean_mark_mt(obj: *mut LeanObject);
    pub fn lean_io_error_to_string(err: *mut LeanObject) -> *mut LeanObject;
    pub fn lean_options_get_empty(_: *mut LeanObject) -> *mut LeanObject;
    pub fn lean_options_get_bool(
        opts: *mut LeanObject,
        name: *mut LeanObject,
        default_value: bool,
    ) -> bool;
    pub fn lean_options_update_bool(
        opts: *mut LeanObject,
        name: *mut LeanObject,
        value: bool,
    ) -> *mut LeanObject;
    pub fn lean_get_init_fn_name_for(
        env: *mut LeanObject,
        name: *mut LeanObject,
    ) -> *mut LeanObject;
    pub fn lean_get_profiler(opts: *mut LeanObject) -> bool;
    pub fn lean_get_profiler_threshold(opts: *mut LeanObject) -> f64;

    pub fn initialize_alloc();
    pub fn finalize_alloc();
    // initialize_object / finalize_object now provided inline (no-op / lean_finalize_external_classes)
    pub fn initialize_io();
    pub fn finalize_io();
    pub fn initialize_thread();
    pub fn finalize_thread();
    // fn initialize_ascii_impl();
    // fn finalize_ascii_impl();

    // initialize_print / finalize_print now provided by library_print.rs (no-ops)
    // initialize_num / finalize_num now provided by kernel_num.rs (empty no-ops)
    // initialize_annotation / finalize_annotation removed (annotation.cpp deleted; no-ops)
    pub fn initialize_library_util();
    pub fn finalize_library_util();
    pub fn initialize_time_task();
    pub fn finalize_time_task();
    pub fn finalize_ir_interpreter();
    pub fn initialize_level();
    pub fn finalize_level();
    pub fn finalize_local_ctx();
    pub fn initialize_quot();
    pub fn finalize_quot();
    // initialize_trace / finalize_trace now provided by kernel_trace.rs
    // init_default_print_fn_impl removed: lean_expr_dbg_to_string now implemented in Rust
    pub fn initialize_Init(builtin: bool) -> *mut LeanObject;
    pub fn initialize_Std(builtin: bool) -> *mut LeanObject;
    pub fn initialize_Lean(builtin: bool) -> *mut LeanObject;
}

#[repr(C)]
struct LeanListCell {
    rc: AtomicU32,
    head: c_uint,
    tail: *mut LeanListCell,
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

pub(crate) unsafe fn lean_array_get(obj: *const LeanObject, idx: usize) -> *mut LeanObject {
    let array = obj as *const LeanArrayObject<0>;
    (*array).m_data.as_ptr().add(idx).read()
}

pub(crate) unsafe fn lean_mk_empty_array() -> *mut LeanObject {
    lean_alloc_array(0, 0)
}

pub(crate) unsafe fn lean_sarray_capacity(obj: *const LeanObject) -> Size {
    let sarray = obj as *const LeanScalarArray<0>;
    (*sarray).m_capacity
}

pub unsafe fn lean_io_result_take_value(obj: *mut LeanObject) -> *mut LeanObject {
    debug_assert!(lean_io_result_is_ok(obj));
    let v = lean_ctor_get(obj, 0);
    lean_inc(v);
    lean_dec(obj);
    v
}

pub unsafe fn lean_io_prim_handle_is_eof(h: *const LeanObject) -> bool {
    let fp = lean_get_external_data(h).cast::<libc::FILE>();
    libc::feof(fp) != 0
}

pub unsafe fn lean_io_prim_handle_rewind(h: *const LeanObject) -> *mut LeanObject {
    let fp = lean_get_external_data(h).cast::<libc::FILE>();
    if libc::fseek(fp, 0, libc::SEEK_SET) == 0 {
        lean_io_result_mk_ok(lean_box(0))
    } else {
        lean_io_result_mk_error(lean_decode_io_error(lean_errno(), core::ptr::null_mut()))
    }
}

pub unsafe fn lean_io_prim_handle_truncate(h: *const LeanObject) -> *mut LeanObject {
    let fp = lean_get_external_data(h).cast::<libc::FILE>();
    if libc::ftruncate(libc::fileno(fp), libc::ftello(fp)) == 0 {
        lean_io_result_mk_ok(lean_box(0))
    } else {
        lean_io_result_mk_error(lean_decode_io_error(lean_errno(), core::ptr::null_mut()))
    }
}

pub unsafe fn lean_io_prim_handle_mk(filename: *mut LeanObject, mode: u8) -> *mut LeanObject {
    let fname = lean_string_cstr(filename);
    if libc::strlen(fname) != lean_string_size(filename) - 1 {
        return mk_embedded_nul_error(filename);
    }

    let mut flags: libc::c_int = libc::O_CLOEXEC;

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
        return lean_io_result_mk_error(lean_decode_io_error(lean_errno(), filename));
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
        lean_io_result_mk_error(lean_decode_io_error(lean_errno(), filename))
    } else {
        lean_io_result_mk_ok(runtime_io_stream_impl::io_wrap_handle(fp))
    }
}

fn env_flag(value: &str) -> bool {
    value.as_bytes() == b"1"
}

include!("library_constants.rs");
include!("library_util.rs");
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
include!("runtime_exception.rs");
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
include!("runtime_object_task.rs");
include!("library_formatter.rs");
include!("runtime_io_ref.rs");
include!("runtime_io_fs.rs");
include!("runtime_io_error.rs");
include!("runtime_io_handle.rs");
include!("runtime_io_task.rs");
include!("runtime_io_stream.rs");
include!("runtime_sharecommon.rs");
include!("runtime_thread.rs");
include!("runtime_once.rs");
include!("runtime_float.rs");
include!("runtime_mpz.rs");
include!("runtime_object_nat_int.rs");
include!("runtime_object_string.rs");
include!("runtime_object_name.rs");
include!("kernel_abstract.rs");
include!("library_expr_lt.rs");
include!("library_time_task.rs");
include!("library_print.rs");
include!("runtime_compact.rs");
include!("runtime_compact_writer.rs");
include!("kernel_replace_fn.rs");
include!("kernel_expr_eq_fn.rs");
include!("kernel_for_each_fn.rs");
include!("kernel_level.rs");
include!("kernel_expr.rs");
include!("kernel_equiv_manager.rs");
include!("kernel_instantiate.rs");
include!("kernel_local_ctx.rs");
include!("kernel_declaration.rs");
include!("kernel_environment.rs");
include!("kernel_quot.rs");
include!("kernel_type_checker.rs");
include!("library_instantiate_mvars.rs");
include!("library_module.rs");
include!("library_elab_environment.rs");
include!("library_ir_interpreter.rs");
include!("library_llvm.rs");
include!("kernel_num.rs");
include!("kernel_trace.rs");

pub unsafe fn lean_name_eq_export(n1: *const LeanObject, n2: *const LeanObject) -> bool {
    runtime_object_name_impl::lean_name_eq(n1, n2)
}

pub unsafe fn lean_finalize_external_classes() {
    let mut classes = EXTERNAL_CLASSES.lock().unwrap();
    for class in classes.drain(..) {
        drop(Box::from_raw(class as *mut LeanExternalClass));
    }
}

pub fn lean_internal_get_hardware_concurrency(_: *mut LeanObject) -> u32 {
    std::thread::available_parallelism()
        .map(|count| count.get() as u32)
        .unwrap_or(1)
}

pub unsafe fn lean_option_get_or_block(opt: *mut LeanObject) -> *mut LeanObject {
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

pub fn lean_io_mk_world() -> *mut LeanObject {
    unsafe { lean_box(0) }
}

pub unsafe fn lean_io_allocprof(msg: *mut LeanObject, fn_obj: *mut LeanObject) -> *mut LeanObject {
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

pub fn lean_util_is_safe_ascii_char(byte: c_char) -> bool {
    is_safe_ascii_byte(byte as u8)
}

pub unsafe fn lean_util_is_safe_ascii(mut text: *const c_char) -> bool {
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

pub unsafe fn lean_util_is_safe_ascii_n(text: *const c_char, size: Size) -> bool {
    for offset in 0..size {
        if !is_safe_ascii_byte(*text.add(offset) as u8) {
            return false;
        }
    }
    true
}

pub fn lean_util_log2(mut value: c_uint) -> c_uint {
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

pub fn lean_util_lbool_name(value: i32) -> *const c_char {
    match value {
        -1 => c"l_false".as_ptr(),
        1 => c"l_true".as_ptr(),
        _ => c"l_undef".as_ptr(),
    }
}

pub fn lean_util_mk_list_range(from: c_uint, to: c_uint) -> *mut c_void {
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

unsafe fn name_is_anonymous(obj: *const LeanObject) -> bool {
    lean_is_scalar(obj)
}

unsafe fn name_prefix(obj: *const LeanObject) -> *mut LeanObject {
    debug_assert!(!lean_is_scalar(obj));
    lean_ctor_get(obj, 0)
}

unsafe fn name_uses_registered_prefix(state: &NameGeneratorState, n: *const LeanObject) -> bool {
    if name_is_anonymous(n) {
        return false;
    }
    if name_contains_registered_prefix(state, n) {
        return true;
    }
    name_uses_registered_prefix(state, name_prefix(n))
}
unsafe fn finalize_runtime_module_body() {
    finalize_stack_overflow();
    finalize_process();
    finalize_mutex();
    finalize_thread();
    finalize_io();
    lean_finalize_external_classes(); // was finalize_object() in object.cpp
    finalize_debug();
    finalize_alloc();
}

unsafe fn finalize_util_module_body() {
    finalize_options();
    finalize_name_generator();
    finalize_name();
    finalize_ascii();
    finalize_runtime_module_body();
}

unsafe fn finalize_kernel_module_body() {
    finalize_quot();
    finalize_inductive();
    finalize_local_ctx();
    finalize_type_checker();
    finalize_declaration();
    finalize_expr();
    finalize_level();
}

unsafe fn finalize_library_core_module_body() {
    finalize_profiling();
    finalize_constants();
    finalize_formatter();
}

unsafe fn finalize_library_module_body() {
    finalize_ir_interpreter();
    finalize_time_task();
    finalize_library_util();
    lean_cxx_finalize_num();
}

unsafe fn finalize_constructions_module_body() {
    finalize_constructions_util();
}

// initialize_ascii / finalize_ascii are no-ops: the original C++ ascii.h had them as empty
// inline functions. The actual ASCII utility functions are ported to Rust above.
pub fn initialize_ascii() {}
pub fn finalize_ascii() {}

pub fn initialize_runtime_module() {
    unsafe { initialize_runtime_module_body() }
}

pub fn finalize_runtime_module() {
    unsafe { finalize_runtime_module_body() }
}

pub fn finalize_util_module() {
    unsafe { finalize_util_module_body() }
}

pub fn finalize_kernel_module() {
    unsafe { finalize_kernel_module_body() }
}

pub fn finalize_library_core_module() {
    unsafe { finalize_library_core_module_body() }
}

pub fn finalize_library_module() {
    unsafe { finalize_library_module_body() }
}

pub fn finalize_constructions_module() {
    unsafe { finalize_constructions_module_body() }
}

pub fn lean_initialize_runtime_for_plugin(_: bool) -> *mut LeanObject {
    unsafe {
        initialize_runtime_module_body();
        lean_io_result_mk_ok(lean_box(0))
    }
}

pub fn run_thread_finalizers() {
    unsafe { run_thread_finalizers_internal() }
}

pub fn run_post_thread_finalizers() {
    unsafe { run_post_thread_finalizers_internal() }
}

pub fn delete_thread_finalizer_manager() {
    unsafe { delete_thread_finalizer_manager_internal() }
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

pub fn lean_name_generator_tmp_prefix() -> *mut LeanObject {
    let guard = NAME_GENERATOR_STATE.lock().unwrap();
    guard.as_ref().map_or(ptr::null_mut(), |state| {
        unsafe {
            lean_inc(state.tmp_prefix);
        }
        state.tmp_prefix
    })
}

pub unsafe fn lean_uses_name_generator_prefix(n: *const LeanObject) -> bool {
    let guard = NAME_GENERATOR_STATE.lock().unwrap();
    let Some(state) = guard.as_ref() else {
        return false;
    };
    name_uses_registered_prefix(state, n)
}
pub fn lean_name_next_internal_unique_id() -> c_uint {
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
    lean_get_profiler(opts)
}
pub unsafe fn get_profiling_threshold(opts: *const LeanOptions) -> f64 {
    let opts = (*opts).obj;
    lean_inc(opts);
    lean_get_profiler_threshold(opts)
}

pub fn lean_internal_get_default_verbose(_: *mut LeanObject) -> bool {
    true
}

pub unsafe fn lean_internal_get_default_options(_: *mut LeanObject) -> *mut LeanObject {
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

pub fn lean_finalize() {
    run_thread_finalizers();
    run_post_thread_finalizers();
    delete_thread_finalizer_manager();
}

pub fn lean_system_platform_windows(_: *mut LeanObject) -> bool {
    false
}

pub fn lean_system_platform_osx(_: *mut LeanObject) -> bool {
    cfg!(target_os = "macos")
}

pub fn lean_system_platform_emscripten(_: *mut LeanObject) -> bool {
    false
}

pub fn lean_io_initializing() -> bool {
    INITIALIZING.load(Ordering::Relaxed)
}

pub unsafe fn lean_get_githash(_: *mut LeanObject) -> *mut LeanObject {
    lean_mk_string(concat!(env!("LEAN_RUST_GITHASH"), "\0").as_ptr() as *const c_char)
}

pub fn lean_internal_has_llvm_backend(_: *mut LeanObject) -> bool {
    env_flag(env!("LEAN_RUST_HAS_LLVM"))
}

pub fn lean_internal_has_address_sanitizer(_: *mut LeanObject) -> bool {
    env_flag(env!("LEAN_RUST_HAS_ADDRESS_SANITIZER"))
}

pub fn lean_internal_is_multi_thread(_: *mut LeanObject) -> bool {
    env_flag(env!("LEAN_RUST_MULTI_THREAD"))
}

pub fn lean_internal_is_debug(_: *mut LeanObject) -> bool {
    env_flag(env!("LEAN_RUST_DEBUG"))
}

pub unsafe fn lean_internal_get_build_type(_: *mut LeanObject) -> *mut LeanObject {
    lean_mk_string(concat!(env!("LEAN_RUST_BUILD_TYPE"), "\0").as_ptr() as *const c_char)
}

pub unsafe fn lean_get_leanc_extra_flags(_: *mut LeanObject) -> *mut LeanObject {
    lean_mk_string(concat!(env!("LEAN_RUST_LEANC_EXTRA_CC_FLAGS"), "\0").as_ptr() as *const c_char)
}

pub unsafe fn lean_get_leanc_internal_flags(_: *mut LeanObject) -> *mut LeanObject {
    lean_mk_string(concat!(env!("LEAN_RUST_LEANC_INTERNAL_FLAGS"), "\0").as_ptr() as *const c_char)
}

pub unsafe fn lean_get_linker_flags(link_static: bool) -> *mut LeanObject {
    if link_static {
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

pub unsafe fn lean_get_internal_linker_flags(_: *mut LeanObject) -> *mut LeanObject {
    lean_mk_string(
        concat!(env!("LEAN_RUST_LEANC_INTERNAL_LINKER_FLAGS"), "\0").as_ptr() as *const c_char,
    )
}

type LeanMapForeachFn = fn(*mut LeanObject, *mut LeanObject, *mut c_void);

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
        cb(lean_array_get(ks, i), lean_array_get(vs, i), ctx);
    }
}

unsafe fn lean_map_foreach_entries(es: *mut LeanObject, cb: LeanMapForeachFn, ctx: *mut c_void) {
    for i in 0..lean_array_size(es) {
        lean_map_foreach_entry(lean_array_get(es, i), cb, ctx);
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
        let mut lst = lean_array_get(buckets, i);
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

pub unsafe fn lean_rbmap_foreach(m: *mut LeanObject, cb: LeanMapForeachFn, ctx: *mut c_void) {
    lean_map_foreach_rbmap(m, cb, ctx);
}

pub unsafe fn lean_phashmap_foreach(m: *mut LeanObject, cb: LeanMapForeachFn, ctx: *mut c_void) {
    lean_map_foreach_node(lean_ctor_get(m, 0), cb, ctx);
}

pub unsafe fn lean_hashmap_foreach(m: *mut LeanObject, cb: LeanMapForeachFn, ctx: *mut c_void) {
    lean_map_foreach_hashmap(m, cb, ctx);
}

pub unsafe fn lean_smap_foreach(m: *mut LeanObject, cb: LeanMapForeachFn, ctx: *mut c_void) {
    lean_map_foreach_smap(m, cb, ctx);
}

pub unsafe fn lean_smap_foreach_test(m: *mut LeanObject) -> *mut LeanObject {
    pub fn print_entry(k: *mut LeanObject, v: *mut LeanObject, _: *mut c_void) {
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

pub unsafe fn lean_io_timeit(msg: *mut LeanObject, fn_obj: *mut LeanObject) -> *mut LeanObject {
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

pub unsafe fn lean_io_get_num_heartbeats() -> *mut LeanObject {
    lean_uint64_to_nat_rust(lean_get_num_heartbeats())
}

pub unsafe fn lean_io_set_heartbeats(count: *mut LeanObject) -> *mut LeanObject {
    lean_set_heartbeats(lean_uint64_of_nat_rust(count));
    lean_dec(count);
    lean_box(0)
}

pub unsafe fn lean_io_mono_ms_now() -> *mut LeanObject {
    use std::sync::OnceLock;
    use std::time::Instant;

    static START: OnceLock<Instant> = OnceLock::new();
    let start = START.get_or_init(Instant::now);
    lean_uint64_to_nat_rust(start.elapsed().as_millis() as u64)
}

pub unsafe fn lean_io_mono_nanos_now() -> *mut LeanObject {
    use std::sync::OnceLock;
    use std::time::Instant;

    static START: OnceLock<Instant> = OnceLock::new();
    let start = START.get_or_init(Instant::now);
    lean_uint64_to_nat_rust(start.elapsed().as_nanos() as u64)
}

pub unsafe fn lean_get_current_time() -> *mut LeanObject {
    use std::time::{SystemTime, UNIX_EPOCH};

    let now = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap_or_default();
    let secs = lean_int64_to_int_rust(now.as_secs() as i64);
    let nanos = lean_int64_to_int_rust(now.subsec_nanos() as i64);
    let mut fields = [secs, nanos];
    let timestamp = lean_mk_cnstr(0, 2, fields.as_mut_ptr(), 0);
    lean_io_result_mk_ok(timestamp)
}

pub unsafe fn lean_io_getenv(env_var: *mut LeanObject) -> *mut LeanObject {
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
            lean_mk_cnstr(1, 1, fields.as_mut_ptr(), 0)
        }
        Err(_) => lean_box(0),
    }
}

pub unsafe fn lean_byteslice_beq(a: *const LeanObject, b: *const LeanObject) -> bool {
    if ptr::eq(a, b) {
        return true;
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
        return false;
    }

    if size_a == 0 {
        return true;
    }

    let ptr_a = lean_sarray_cptr(bytearray_a).add(start_a);
    let ptr_b = lean_sarray_cptr(bytearray_b).add(start_b);
    for offset in 0..size_a {
        if *ptr_a.add(offset) != *ptr_b.add(offset) {
            return false;
        }
    }
    true
}

pub unsafe fn lean_mk_cnstr(
    tag: c_uint,
    num_objs: c_uint,
    objs: *mut *mut LeanObject,
    scalar_size: c_uint,
) -> *mut LeanObject {
    let obj = lean_alloc_ctor(tag, num_objs, scalar_size);
    for index in 0..num_objs as Size {
        let val = objs.add(index).read();
        lean_ctor_set(obj, index as c_uint, val);
    }
    obj
}

pub fn lean_is_utf8_next(byte: c_uchar) -> bool {
    byte & 0xC0 == 0x80
}

pub fn lean_get_utf8_size(byte: c_uchar) -> c_uint {
    utf8_size(byte) as c_uint
}

pub unsafe fn lean_utf8_strlen(mut text: *const c_char) -> Size {
    let mut length = 0;
    while *text != 0 {
        let size = utf8_size(*text as c_uchar);
        length += 1;
        text = text.add(size);
    }
    length
}

pub unsafe fn lean_utf8_char_pos(
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

pub unsafe fn lean_get_utf8_last_char(mut text: *const c_char) -> *const c_char {
    let mut last = text;
    while *text != 0 {
        last = text;
        text = text.add(utf8_size(*text as c_uchar));
    }
    last
}

pub unsafe fn lean_utf8_to_unicode(begin: *const c_uchar, end: *const c_uchar) -> c_uint {
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

pub unsafe fn lean_get_utf8_first_byte_size(byte: c_uchar, out_size: *mut c_uint) -> bool {
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

pub unsafe fn lean_next_utf8(text: *const c_char, size: Size, pos: *mut Size) -> c_uint {
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

pub unsafe fn lean_hash_str(len: Size, text: *const c_uchar, seed: u64) -> u64 {
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

#[panic_handler]
fn panic(_: &PanicInfo<'_>) -> ! {
    loop {}
}
