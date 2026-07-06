/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

#![allow(dead_code, non_upper_case_globals)]

pub use core::ffi::{CStr, c_char, c_int, c_long, c_uchar, c_uint, c_void};
pub use core::ptr;
pub use core::sync::atomic::{AtomicBool, AtomicI32, AtomicPtr, AtomicU32, Ordering};

pub(crate) type Size = usize; // duplicate in undefined at line 13 (🔁)

unsafe extern "C" {
    pub fn lean_mk_string(text: *const c_char) -> *mut LeanObject; // duplicate in undefined at line 16 (🔁)
    pub fn lean_mk_string_from_bytes(text: *const c_char, size: Size) -> *mut LeanObject;
    pub fn lean_name_mk_string(prefix: *mut LeanObject, s: *mut LeanObject) -> *mut LeanObject;
    pub fn lean_dec_ref_cold(obj: *mut LeanObject); // duplicate in undefined at line 19 (🔁)
    pub fn lean_mark_persistent(obj: *mut LeanObject); // duplicate in undefined at line 20 (🔁)
    pub fn lean_mk_io_user_error(msg: *mut LeanObject) -> *mut LeanObject;
    pub fn lean_mk_io_error_invalid_argument(errnum: u32, details: *mut LeanObject) -> *mut LeanObject;
    pub fn lean_alloc_object(size: Size) -> *mut LeanObject; // duplicate in undefined at line 23 (🔁)
    pub fn lean_mk_io_error_invalid_argument_file(
        name: *mut LeanObject,
        errnum: u32,
        details: *mut LeanObject,
    ) -> *mut LeanObject;
    pub fn lean_array_push(array: *mut LeanObject, value: *mut LeanObject) -> *mut LeanObject;
    pub fn lean_decode_uv_error(errnum: c_int, fname: *mut LeanObject) -> *mut LeanObject;
    pub fn lean_decode_io_error(errnum: c_int, fname: *mut LeanObject) -> *mut LeanObject;
    pub fn lean_io_eprintln(msg: *mut LeanObject) -> *mut LeanObject;
    pub fn lean_promise_resolve(value: *mut LeanObject, promise: *mut LeanObject);
    pub fn lean_io_promise_new() -> *mut LeanObject;
    pub fn lean_io_promise_resolve(value: *mut LeanObject, promise: *mut LeanObject)
    -> *mut LeanObject;
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
    pub fn lean_get_init_fn_name_for(env: *mut LeanObject, name: *mut LeanObject) -> *mut LeanObject;
    pub fn lean_get_profiler(opts: *mut LeanObject) -> u8;
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
    pub fn initialize_ir_interpreter();
    pub fn finalize_ir_interpreter();
    pub fn initialize_level();
    pub fn finalize_level();
    pub fn initialize_expr();
    pub fn finalize_expr();
    pub fn initialize_declaration();
    pub fn finalize_declaration();
    // initialize_type_checker / finalize_type_checker now provided by kernel_type_checker.rs
    pub fn initialize_local_ctx();
    pub fn finalize_local_ctx();
    pub fn initialize_quot();
    pub fn finalize_quot();
    // initialize_trace / finalize_trace now provided by kernel_trace.rs
    // init_default_print_fn_impl removed: lean_expr_dbg_to_string now implemented in Rust
    pub fn initialize_Init(builtin: u8) -> *mut LeanObject;
    pub fn initialize_Std(builtin: u8) -> *mut LeanObject;
    pub fn initialize_Lean(builtin: u8) -> *mut LeanObject;
}

#[repr(C)]
pub struct LeanObject {
    // duplicate in undefined at line 92 (🔁)
    rc: i32,
    cs_size: u16,
    other: u8,
    tag: u8,
}

#[repr(C)]
struct LeanCtorObject {
    // duplicate in undefined at line 100 (🔁)
    header: LeanObject,
    data: [*mut LeanObject; 0],
}

type LeanExternalFinalizeProc = unsafe fn(*mut c_void); // duplicate in undefined at line 105 (🔁)
type LeanExternalForeachProc = unsafe fn(*mut c_void, *mut LeanObject); // duplicate in undefined at line 106 (🔁)

#[repr(C)]
pub struct LeanExternalClass {
    // duplicate in undefined at line 109 (🔁)
    finalize: LeanExternalFinalizeProc,
    foreach: LeanExternalForeachProc,
}

#[repr(C)]
struct LeanListCell {
    rc: AtomicU32,
    head: c_uint,
    tail: *mut LeanListCell,
}

#[repr(C)]
struct LeanArrayObject {
    // duplicate in undefined at line 122 (🔁)
    header: LeanObject,
    size: Size,
    capacity: Size,
    data: [*mut LeanObject; 0],
}

#[repr(C)]
struct LeanStringObject {
    // duplicate in undefined at line 130 (🔁)
    header: LeanObject,
    size: Size,
    capacity: Size,
    len: Size,
    data: [c_char; 0],
}

#[repr(C)]
struct LeanClosureObject {
    // duplicate in undefined at line 139 (🔁)
    header: LeanObject,
    fun: *mut c_void,
    arity: u16,
    num_fixed: u16,
    data: [*mut LeanObject; 0],
}

#[repr(C)]
struct LeanScalarArray {
    // duplicate in undefined at line 148 (🔁)
    header: LeanObject,
    size: Size,
    capacity: Size,
    data: [u8; 0],
}

#[repr(C)]
struct LeanPromiseObject {
    // duplicate in undefined at line 156 (🔁)
    header: LeanObject,
    result: *mut LeanObject,
}

#[repr(C)]
struct LeanTaskImp {
    // duplicate in undefined at line 162 (🔁)
    m_closure: *mut LeanObject,
    m_head_dep: *mut LeanTaskObject,
    m_next_dep: *mut LeanTaskObject,
    m_prio: u32,
    m_canceled: bool,
    m_keep_alive: bool,
    m_deleted: bool,
}

#[repr(C)]
struct LeanTaskObject {
    // duplicate in undefined at line 173 (🔁)
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

pub unsafe fn lean_unbox(obj: *mut LeanObject) -> Size {
    // duplicate in undefined at line 234 (🔁)
    (obj as Size) >> 1
}

pub unsafe fn lean_is_scalar(obj: *mut LeanObject) -> bool {
    // duplicate in undefined at line 238 (🔁)
    (obj as Size) & 1 == 1
}

pub unsafe fn lean_ptr_tag(obj: *mut LeanObject) -> u8 {
    // duplicate in undefined at line 242 (🔁)
    if lean_is_scalar(obj) {
        lean_unbox(obj) as u8
    } else {
        (*obj).tag
    }
}

pub unsafe fn lean_obj_tag(obj: *mut LeanObject) -> u8 {
    // duplicate in undefined at line 250 (🔁)
    lean_ptr_tag(obj)
}

pub(crate) unsafe fn lean_inc_ref_n(obj: *mut LeanObject, n: usize) {
    // duplicate in undefined at line 254 (🔁)
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

pub unsafe fn lean_inc_ref(obj: *mut LeanObject) {
    // duplicate in undefined at line 267 (🔁)
    lean_inc_ref_n(obj, 1);
}

pub(crate) unsafe fn lean_dec_ref(obj: *mut LeanObject) {
    // duplicate in undefined at line 271 (🔁)
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

pub unsafe fn lean_inc(obj: *mut LeanObject) {
    // duplicate in undefined at line 283 (🔁)
    if !lean_is_scalar(obj) {
        lean_inc_ref(obj);
    }
}

pub unsafe fn lean_inc_n(obj: *mut LeanObject, n: usize) {
    // duplicate in undefined at line 289 (🔁)
    if !lean_is_scalar(obj) {
        lean_inc_ref_n(obj, n);
    }
}

pub unsafe fn lean_dec(obj: *mut LeanObject) {
    // duplicate in undefined at line 295 (🔁)
    if !lean_is_scalar(obj) {
        lean_dec_ref(obj);
    }
}

pub(crate) unsafe fn lean_ctor_get(obj: *mut LeanObject, idx: usize) -> *mut LeanObject {
    // duplicate in undefined at line 301 (🔁)
    (obj.add(1) as *mut *mut LeanObject).add(idx).read()
}

pub(crate) unsafe fn lean_ctor_get_uint8(obj: *mut LeanObject, offset: usize) -> u8 {
    // duplicate in undefined at line 305 (🔁)
    (obj.add(1) as *mut u8).add(offset).read()
}

pub(crate) unsafe fn lean_ctor_get_uint16(obj: *mut LeanObject, offset: usize) -> u16 {
    // duplicate in undefined at line 309 (🔁)
    (obj.add(1) as *mut u8).add(offset).cast::<u16>().read()
}

pub(crate) unsafe fn lean_ctor_set_uint8(obj: *mut LeanObject, offset: usize, value: u8) {
    // duplicate in undefined at line 313 (🔁)
    (obj.add(1) as *mut u8).add(offset).write(value);
}

pub(crate) unsafe fn lean_ctor_set_uint16(obj: *mut LeanObject, offset: usize, value: u16) {
    // duplicate in undefined at line 317 (🔁)
    (obj.add(1) as *mut u8)
        .add(offset)
        .cast::<u16>()
        .write(value);
}

pub(crate) unsafe fn lean_ctor_get_uint64(obj: *mut LeanObject, offset: usize) -> u64 {
    // duplicate in undefined at line 324 (🔁)
    (obj.add(1) as *mut u8).add(offset).cast::<u64>().read()
}

pub(crate) unsafe fn lean_ctor_set_uint64(obj: *mut LeanObject, offset: usize, value: u64) {
    // duplicate in undefined at line 328 (🔁)
    (obj.add(1) as *mut u8)
        .add(offset)
        .cast::<u64>()
        .write(value);
}

pub unsafe fn lean_runtime_alloc_ctor(
    tag: c_uint,
    num_objs: c_uint,
    scalar_size: c_uint,
) -> *mut LeanObject {
    const LEAN_MAX_CTOR_TAG: c_uint = 243; // duplicate in undefined at line 340 (🔁)
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

pub unsafe fn lean_runtime_ctor_set(obj: *mut LeanObject, index: c_uint, value: *mut LeanObject) {
    debug_assert!(index < (*obj).other as c_uint);
    let fields = (obj as *mut LeanCtorObject)
        .cast::<u8>()
        .add(core::mem::size_of::<LeanCtorObject>()) as *mut *mut LeanObject;
    fields.add(index as Size).write(value);
}

pub unsafe fn lean_box_uint64(v: u64) -> *mut LeanObject {
    // duplicate in undefined at line 375 (🔁)
    let r = lean_runtime_alloc_ctor(0, 0, core::mem::size_of::<u64>() as c_uint);
    lean_ctor_set_uint64(r, 0, v);
    r
}

pub unsafe fn lean_unbox_uint64(o: *mut LeanObject) -> u64 {
    // duplicate in undefined at line 381 (🔁)
    lean_ctor_get_uint64(o, 0)
}

pub(crate) unsafe fn lean_array_get(obj: *mut LeanObject, idx: usize) -> *mut LeanObject {
    let array_data_ptr = (obj as *const u8).add(24) as *const *mut LeanObject;
    array_data_ptr.add(idx).read()
}

pub(crate) unsafe fn lean_array_size(obj: *mut LeanObject) -> usize {
    // duplicate in undefined at line 390 (🔁)
    let array = obj as *const LeanArrayObject;
    (*array).size
}

pub(crate) unsafe fn lean_alloc_array(size: usize, capacity: usize) -> *mut LeanObject {
    const LEAN_ARRAY_TAG: u8 = 246; // duplicate in undefined at line 396 (🔁)
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

pub(crate) unsafe fn lean_mk_empty_array() -> *mut LeanObject {
    lean_alloc_array(0, 0)
}

pub(crate) unsafe fn lean_alloc_sarray(
    elem_size: c_uint,
    size: Size,
    capacity: Size,
) -> *mut LeanObject {
    const LEAN_SCALAR_ARRAY_TAG: u8 = 248; // duplicate in undefined at line 423 (🔁)
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

pub(crate) fn lean_alloc_sarray_would_overflow(elem_size: c_uint, capacity: Size) -> bool {
    match (elem_size as usize).checked_mul(capacity) {
        None => true,
        Some(bytes) => core::mem::size_of::<LeanScalarArray>()
            .checked_add(bytes)
            .is_none(),
    }
}

pub(crate) unsafe fn lean_alloc_string(
    // duplicate in undefined at line 450 (🔁)
    size: usize,
    capacity: usize,
    len: usize,
) -> *mut LeanObject {
    const LEAN_STRING_TAG: u8 = 249; // duplicate in undefined at line 455 (🔁)
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

pub(crate) unsafe fn lean_sarray_set_size(obj: *mut LeanObject, size: Size) {
    let sarray = obj as *mut LeanScalarArray;
    (*sarray).size = size;
}

pub(crate) unsafe fn lean_sarray_size(obj: *mut LeanObject) -> Size {
    let sarray = obj as *const LeanScalarArray;
    (*sarray).size
}

pub(crate) unsafe fn lean_sarray_capacity(obj: *mut LeanObject) -> Size {
    let sarray = obj as *const LeanScalarArray;
    (*sarray).capacity
}

pub unsafe fn lean_io_result_is_ok(obj: *mut LeanObject) -> bool {
    // duplicate in undefined at line 485 (🔁)
    lean_ptr_tag(obj) == 0
}

pub unsafe fn lean_io_result_is_error(obj: *mut LeanObject) -> bool {
    // duplicate in undefined at line 489 (🔁)
    lean_ptr_tag(obj) == 1
}

pub unsafe fn lean_io_result_get_value(obj: *mut LeanObject) -> *mut LeanObject {
    // duplicate in undefined at line 493 (🔁)
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

pub unsafe fn lean_io_result_show_error(r: *mut LeanObject) {
    // duplicate in undefined at line 511 (🔁)
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

pub unsafe fn lean_io_prim_handle_is_tty(h: *mut LeanObject) -> u8 {
    let fp = lean_runtime_get_external_data(h).cast::<libc::FILE>();
    libc::isatty(libc::fileno(fp)) as u8
}

pub unsafe fn lean_io_prim_handle_is_eof(h: *mut LeanObject) -> u8 {
    let fp = lean_runtime_get_external_data(h).cast::<libc::FILE>();
    (libc::feof(fp) != 0) as u8
}

unsafe fn lean_runtime_errno() -> c_int {
    *libc::__errno_location()
}

pub unsafe fn lean_io_prim_handle_flush(h: *mut LeanObject) -> *mut LeanObject {
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

pub unsafe fn lean_io_prim_handle_rewind(h: *mut LeanObject) -> *mut LeanObject {
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

pub unsafe fn lean_io_prim_handle_truncate(h: *mut LeanObject) -> *mut LeanObject {
    let fp = lean_runtime_get_external_data(h).cast::<libc::FILE>();
    if libc::ftruncate(libc::fileno(fp), libc::ftello(fp)) == 0 {
        lean_io_result_mk_ok(lean_box(0))
    } else {
        lean_io_result_mk_error(lean_decode_io_error(
            lean_runtime_errno(),
            core::ptr::null_mut(),
        ))
    }
}

pub unsafe fn lean_io_prim_handle_read(h: *mut LeanObject, nbytes: Size) -> *mut LeanObject {
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

pub unsafe fn lean_io_prim_handle_write(
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

pub unsafe fn lean_io_prim_handle_get_line(h: *mut LeanObject) -> *mut LeanObject {
    let fp = lean_runtime_get_external_data(h).cast::<libc::FILE>();
    let mut result = Vec::<u8>::new();
    unsafe {
        loop {
            let c = libc::fgetc(fp);
            if c == libc::EOF {
                break;
            }
            result.push(c as u8);
            if c == b'\n' as i32 {
                break;
            }
        }
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

pub unsafe fn lean_io_prim_handle_put_str(
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

pub(crate) unsafe fn lean_sarray_cptr(obj: *mut LeanObject) -> *const u8 {
    (obj as *const u8).add(24)
}

pub unsafe fn lean_string_cstr(obj: *mut LeanObject) -> *const c_char {
    (obj as *const u8).add(32) as *const c_char
}

pub unsafe fn lean_box(value: Size) -> *mut LeanObject {
    // duplicate in undefined at line 803 (🔁)
    ((value << 1) | 1) as *mut LeanObject
}

fn env_flag(value: &str) -> u8 {
    if value.as_bytes() == b"1" { 1 } else { 0 }
}

pub(crate) unsafe fn mk_name(text: &str) -> LeanName {
    let c_text = std::ffi::CString::new(text).expect("option names never contain NUL");
    let raw_text = lean_mk_string(c_text.as_ptr());
    let raw_name = lean_name_mk_string(lean_box(0), raw_text);
    LeanName { obj: raw_name }
}

pub(crate) unsafe fn mk_name_path(components: &[&str]) -> LeanName {
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

pub unsafe fn lean_name_eq_export(n1: *mut LeanObject, n2: *mut LeanObject) -> u8 {
    runtime_object_name_impl::lean_name_eq(n1, n2)
}

#[repr(C)]
struct LeanExternalObject {
    // duplicate in undefined at line 903 (🔁)
    header: LeanObject,
    class: *mut LeanExternalClass,
    data: *mut c_void,
}

static EXTERNAL_CLASSES: std::sync::Mutex<Vec<usize>> = std::sync::Mutex::new(Vec::new());

unsafe fn lean_external_noop_finalize(_: *mut c_void) {}

unsafe fn lean_external_noop_foreach(_: *mut c_void, _: *mut LeanObject) {}

pub unsafe fn lean_register_external_class(
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

pub unsafe fn lean_finalize_external_classes() {
    let mut classes = EXTERNAL_CLASSES.lock().unwrap();
    for class in classes.drain(..) {
        drop(Box::from_raw(class as *mut LeanExternalClass));
    }
}

pub unsafe fn lean_runtime_alloc_external(
    class: *mut LeanExternalClass,
    data: *mut c_void,
) -> *mut LeanObject {
    const LEAN_EXTERNAL_TAG: u8 = 254; // duplicate in undefined at line 938 (🔁)
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

pub unsafe fn lean_runtime_get_external_data(obj: *mut LeanObject) -> *mut c_void {
    (*(obj as *mut LeanExternalObject)).data
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

pub unsafe fn lean_runtime_get_lean_num_threads() -> c_uint {
    let name = b"LEAN_NUM_THREADS\0";
    let value = libc::getenv(name.as_ptr().cast());
    if !value.is_null() {
        return libc::atoi(value) as c_uint;
    }
    std::thread::available_parallelism()
        .map(|count| count.get() as c_uint)
        .unwrap_or(1)
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

pub(crate) unsafe fn consume_io_result(result: *mut LeanObject) {
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
        let bytes = text.to_bytes();
        libc::write(2, bytes.as_ptr().cast(), bytes.len());
        libc::write(2, b"\n".as_ptr().cast(), 1);
    }
}

unsafe fn initialize_runtime_module_body() {
    initialize_alloc();
    initialize_debug();
    // initialize_object was a no-op (object.cpp deleted)
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
    lean_finalize_external_classes(); // was finalize_object() in object.cpp
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
    initialize_local_ctx();
    initialize_inductive();
    initialize_quot();
    lean_cxx_initialize_trace();
}

unsafe fn finalize_kernel_module_body() {
    lean_cxx_finalize_trace();
    finalize_quot();
    finalize_inductive();
    finalize_local_ctx();
    finalize_type_checker();
    finalize_declaration();
    finalize_expr();
    finalize_level();
}
pub fn initialize_inductive() {}
pub fn finalize_inductive() {}

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
    lean_cxx_initialize_num();
    initialize_library_util();
    initialize_time_task();
    initialize_dynlib();
    initialize_ir_interpreter();
}

unsafe fn finalize_library_module_body() {
    finalize_ir_interpreter();
    finalize_time_task();
    finalize_library_util();
    lean_cxx_finalize_num();
}

unsafe fn initialize_constructions_module_body() {
    initialize_constructions_util();
}

unsafe fn finalize_constructions_module_body() {
    finalize_constructions_util();
}

// initialize_ascii / finalize_ascii are no-ops: the original C++ ascii.h had them as empty
// inline functions. The actual ASCII utility functions are ported to Rust above.
pub fn initialize_ascii() {}
pub fn finalize_ascii() {}

pub fn lean_initialize_runtime_module() {
    unsafe { initialize_runtime_module_body() }
}

pub fn initialize_runtime_module() {
    unsafe { initialize_runtime_module_body() }
}

pub fn finalize_runtime_module() {
    unsafe { finalize_runtime_module_body() }
}

pub fn initialize_util_module() {
    unsafe { initialize_util_module_body() }
}

pub fn finalize_util_module() {
    unsafe { finalize_util_module_body() }
}

pub fn initialize_kernel_module() {
    unsafe { initialize_kernel_module_body() }
}

pub fn finalize_kernel_module() {
    unsafe { finalize_kernel_module_body() }
}

pub fn initialize_library_core_module() {
    unsafe { initialize_library_core_module_body() }
}

pub fn finalize_library_core_module() {
    unsafe { finalize_library_core_module_body() }
}

pub fn initialize_library_module() {
    unsafe { initialize_library_module_body() }
}

pub fn finalize_library_module() {
    unsafe { finalize_library_module_body() }
}

pub fn initialize_constructions_module() {
    unsafe { initialize_constructions_module_body() }
}

pub fn finalize_constructions_module() {
    unsafe { finalize_constructions_module_body() }
}

pub fn lean_initialize_runtime_for_plugin(_: u8) -> *mut LeanObject {
    unsafe {
        initialize_runtime_module_body();
        lean_io_result_mk_ok(lean_box(0))
    }
}

pub fn init_default_print_fn() {
    // No-op: lean_expr_dbg_to_string (the ToString Expr instance) is now implemented
    // in Rust (library_print.rs), so the C++ formatter.h print function pointer
    // no longer needs to be set.
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

pub fn lean_initialize() {
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

pub fn lean_name_generator_tmp_prefix() -> *mut LeanObject {
    let guard = NAME_GENERATOR_STATE.lock().unwrap();
    guard.as_ref().map_or(ptr::null_mut(), |state| {
        unsafe {
            lean_inc(state.tmp_prefix);
        }
        state.tmp_prefix
    })
}

pub unsafe fn lean_register_name_generator_prefix(n: *mut LeanObject) {
    let mut guard = NAME_GENERATOR_STATE.lock().unwrap();
    let state = guard
        .as_mut()
        .expect("name generator registry is not initialized");
    assert!(!name_contains_registered_prefix(state, n));
    lean_inc(n);
    state.prefixes.push(n);
}

pub unsafe fn lean_uses_name_generator_prefix(n: *mut LeanObject) -> bool {
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
pub fn finalize_name() {}

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
    lean_get_profiler(opts) != 0
}
pub unsafe fn get_profiling_threshold(opts: *const LeanOptions) -> f64 {
    let opts = (*opts).obj;
    lean_inc(opts);
    lean_get_profiler_threshold(opts)
}
pub fn initialize_profiling() {}
pub fn finalize_profiling() {}

pub fn lean_internal_get_default_verbose(_: *mut LeanObject) -> u8 {
    true as u8
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

pub unsafe fn lean_system_platform_nbits(_: *mut LeanObject) -> *mut LeanObject {
    lean_box(core::mem::size_of::<*const u8>() * 8)
}

pub fn lean_system_platform_windows(_: *mut LeanObject) -> u8 {
    0
}

pub fn lean_system_platform_osx(_: *mut LeanObject) -> u8 {
    cfg!(target_os = "macos") as u8
}

pub fn lean_system_platform_emscripten(_: *mut LeanObject) -> u8 {
    0
}

static INITIALIZING: core::sync::atomic::AtomicBool = core::sync::atomic::AtomicBool::new(true);

pub fn lean_io_mark_end_initialization() {
    INITIALIZING.store(false, Ordering::Relaxed);
}

pub fn lean_io_initializing() -> u8 {
    INITIALIZING.load(Ordering::Relaxed) as u8
}

pub unsafe fn lean_get_githash(_: *mut LeanObject) -> *mut LeanObject {
    lean_mk_string(concat!(env!("LEAN_RUST_GITHASH"), "\0").as_ptr() as *const c_char)
}

pub fn lean_internal_has_llvm_backend(_: *mut LeanObject) -> u8 {
    env_flag(env!("LEAN_RUST_HAS_LLVM"))
}

pub fn lean_internal_has_address_sanitizer(_: *mut LeanObject) -> u8 {
    env_flag(env!("LEAN_RUST_HAS_ADDRESS_SANITIZER"))
}

pub fn lean_internal_is_multi_thread(_: *mut LeanObject) -> u8 {
    env_flag(env!("LEAN_RUST_MULTI_THREAD"))
}

pub fn lean_internal_is_debug(_: *mut LeanObject) -> u8 {
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

pub unsafe fn lean_get_linker_flags(link_static: u8) -> *mut LeanObject {
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
    let timestamp = lean_runtime_mk_cnstr(0, 2, fields.as_mut_ptr(), 0);
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
            lean_runtime_mk_cnstr(1, 1, fields.as_mut_ptr(), 0)
        }
        Err(_) => lean_box(0),
    }
}

pub unsafe fn lean_byteslice_beq(a: *mut LeanObject, b: *mut LeanObject) -> u8 {
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

pub unsafe fn lean_io_result_mk_ok(value: *mut LeanObject) -> *mut LeanObject {
    // duplicate in undefined at line 2054 (🔁)
    let mut fields = [value];
    lean_runtime_mk_cnstr(0, 1, fields.as_mut_ptr(), 0)
}

pub unsafe fn lean_io_result_mk_error(error: *mut LeanObject) -> *mut LeanObject {
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

pub fn lean_runtime_is_utf8_next(byte: c_uchar) -> bool {
    byte & 0xC0 == 0x80
}

pub fn lean_runtime_get_utf8_size(byte: c_uchar) -> c_uint {
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

pub unsafe fn lean_utf8_n_strlen(text: *const c_char, byte_size: Size) -> Size {
    let mut length = 0;
    let mut offset = 0;
    while offset < byte_size {
        let size = utf8_size(*text.add(offset) as c_uchar);
        length += 1;
        offset += size;
    }
    length
}

pub unsafe fn lean_runtime_utf8_char_pos(
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

pub unsafe fn lean_runtime_get_utf8_last_char(mut text: *const c_char) -> *const c_char {
    let mut last = text;
    while *text != 0 {
        last = text;
        text = text.add(utf8_size(*text as c_uchar));
    }
    last
}

pub unsafe fn lean_runtime_utf8_to_unicode(begin: *const c_uchar, end: *const c_uchar) -> c_uint {
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

pub unsafe fn lean_runtime_get_utf8_first_byte_size(byte: c_uchar, out_size: *mut c_uint) -> bool {
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

pub unsafe fn lean_runtime_next_utf8(text: *const c_char, size: Size, pos: *mut Size) -> c_uint {
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

pub unsafe fn lean_runtime_validate_utf8_one(
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

pub unsafe fn lean_runtime_validate_utf8(
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

pub unsafe fn lean_runtime_push_unicode_scalar(dst: *mut c_char, code: c_uint) -> c_uint {
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

pub unsafe fn lean_runtime_hash_str(len: Size, text: *const c_uchar, seed: u64) -> u64 {
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
