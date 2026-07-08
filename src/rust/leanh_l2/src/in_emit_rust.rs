/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

use core::ffi::{c_char, c_int, c_uint, c_void, CStr};
use core::ptr;
use core::sync::atomic::{AtomicI32, Ordering};

use crate::datatypes::{
    F32InitFn, F64InitFn, LeanClosureObject, LeanCtorObject, LeanObject, LeanOnceCell, ObjInitFn,
    Size, U16InitFn, U32InitFn, U64InitFn, U8InitFn, UsizeInitFn, LEAN_CLOSURE_TAG,
    LEAN_MAX_CTOR_TAG,
};
use crate::not_in_emit_rust::{
    lean_alloc_ctor, lean_alloc_ctor_memory, lean_box, lean_closure_arg_cptr,
    lean_closure_num_fixed, lean_ctor_num_objs, lean_ctor_obj_cptr, lean_ctor_scalar_cptr,
    lean_is_ref, lean_is_scalar_bool, lean_obj_once_cold, lean_ptr_tag, lean_usize_to_nat,
    quar_report_uaf, run_once, LEAN_UAF_POISON_RC, UAF_DETECT,
};
use crate::runtime_io_stream::initialize_io;
use crate::runtime_libuv::initialize_libuv;
use crate::runtime_mutex::initialize_mutex;
use crate::runtime_object_panic::lean_string_cstr;
use crate::runtime_object_rc::{
    lean_alloc_object, lean_dec_ref_cold, lean_free_object, lean_mark_persistent,
};
use crate::runtime_object_string::lean_mk_string_unchecked;
use crate::runtime_process::initialize_process;
use crate::runtime_stack_info::save_stack_info;
use crate::runtime_stack_overflow::initialize_stack_overflow;

#[inline]
pub unsafe fn lean_init_task_manager() {}

unsafe fn initialize_runtime_module_body() {
    // initialize_alloc();
    // initialize_debug();
    // initialize_object was a no-op (object.cpp deleted)
    initialize_io();
    // initialize_thread();
    initialize_mutex();
    initialize_process();
    initialize_stack_overflow();
    initialize_libuv();
}

#[inline]
pub unsafe fn lean_initialize_runtime_module() {
    unsafe { initialize_runtime_module_body() }
}

unsafe fn initialize_util_module_body() {
    initialize_runtime_module_body();
    // initialize_ascii();
    initialize_name();
    initialize_name_generator();
    initialize_options();
}

#[repr(C)]
#[derive(Copy, Clone)]
pub struct LeanName {
    obj: *mut LeanObject,
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

pub unsafe fn lean_name_mk_string(
    // [lean-audit] Rust should import from Lean ([export]): Function is found in rust code, but is defined in rust (defined) (🛠️) | Lean: src/Init/Prelude.lean:4729
    mut _v_p_9004_: *mut LeanObject,
    mut _v_s_9005_: *mut LeanObject,
) -> *mut LeanObject {
    todo!("src/rust/gen_init/src/gen/Init/Prelude.rs")
}

pub(crate) unsafe fn mk_name(text: &str) -> LeanName {
    let c_text = std::ffi::CString::new(text).expect("option names never contain NUL");
    let raw_text = lean_mk_string(c_text.as_ptr());
    let raw_name = lean_name_mk_string(lean_box(0), raw_text);
    LeanName { obj: raw_name }
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

struct NameGeneratorState {
    tmp_prefix: *mut LeanObject,
    prefixes: Vec<*mut LeanObject>,
}

unsafe impl Send for NameGeneratorState {}

static NAME_GENERATOR_STATE: std::sync::Mutex<Option<NameGeneratorState>> =
    std::sync::Mutex::new(None);

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

static INTERNAL_UNIQUE_NAME_ID: std::sync::atomic::AtomicU32 = std::sync::atomic::AtomicU32::new(0);
pub fn initialize_name() {
    INTERNAL_UNIQUE_NAME_ID.store(0, Ordering::Relaxed);
}
pub fn finalize_name() {}
pub fn initialize_util_module() {
    unsafe { initialize_util_module_body() }
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

pub fn initialize_kernel_module() {
    initialize_type_checker();
    initialize_local_ctx();
    initialize_inductive();
    initialize_quot();
}

pub fn initialize_library_core_module() {
    unsafe { initialize_library_core_module_body() }
}

pub fn initialize_library_module() {
    unsafe { initialize_library_module_body() }
}

pub unsafe fn initialize_Init(builtin: u8) -> *mut LeanObject {
    todo!("src/rust/gen_init/src/gen/Init.rs")
}

pub unsafe fn initialize_Std(builtin: u8) -> *mut LeanObject {
    todo!("src/rust/gen_std/src/gen/Std.rs")
}

pub unsafe fn initialize_Lean(builtin: u8) -> *mut LeanObject {
    todo!("src/rust/gen_lean_part_5/src/gen/Lean.rs")
}

pub fn init_default_print_fn() {
    // No-op: lean_expr_dbg_to_string (the ToString Expr instance) is now implemented
    // in Rust (library_print.rs), so the C++ formatter.h print function pointer
    // no longer needs to be set.
}

static mut CONSTRUCTIONS_FRESH: LeanName = LeanName {
    obj: ptr::null_mut(),
};

unsafe fn name_contains_registered_prefix(state: &NameGeneratorState, n: *mut LeanObject) -> bool {
    state
        .prefixes
        .iter()
        .copied()
        .any(|p| lean_name_eq(p, n) != 0)
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
pub fn initialize_constructions_util() {
    unsafe {
        CONSTRUCTIONS_FRESH = mk_name("_cnstr_fresh");
        lean_mark_persistent(CONSTRUCTIONS_FRESH.obj);
        lean_register_name_generator_prefix(CONSTRUCTIONS_FRESH.obj);
    }
}

unsafe fn initialize_constructions_module_body() {
    initialize_constructions_util();
}

pub fn initialize_constructions_module() {
    unsafe { initialize_constructions_module_body() }
}

#[inline]
pub fn lean_initialize() {
    // duplicate in src/rust/leanh/src/in_emit_rust.rs at line 231 (🔁)
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
pub unsafe fn lean_io_result_is_error(obj: *mut LeanObject) -> bool {
    unsafe { lean_ptr_tag(obj) == 1 }
}

#[inline]
pub unsafe fn lean_io_result_is_ok(obj: *mut LeanObject) -> bool {
    unsafe { lean_ptr_tag(obj) == 0 }
}

#[inline]
pub unsafe fn lean_io_result_get_value(obj: *mut LeanObject) -> *mut LeanObject {
    unsafe {
        debug_assert!(lean_io_result_is_ok(obj));
        lean_ctor_get(obj, 0)
    }
}

pub unsafe fn lean_io_result_get_error(obj: *mut LeanObject) -> *mut LeanObject {
    debug_assert!(lean_io_result_is_error(obj));
    lean_ctor_get(obj, 0)
}

// src/rust/gen_init/src/gen/Init/System/IOError.rs
pub unsafe fn lean_io_error_to_string(mut _v_x_1214_: *mut LeanObject) -> *mut LeanObject {
    // [lean-audit] Rust should import from Lean ([export]): Function is found in rust code, but is defined in rust (defined) (🛠️) | Lean: src/Init/System/IOError.lean:271
    todo!("asdfasd")
}

#[inline]
pub unsafe fn lean_io_result_show_error(r: *mut LeanObject) {
    unsafe {
        let err = lean_io_result_get_error(r);
        lean_inc(err);
        let msg = lean_io_error_to_string(err);
        let text = CStr::from_ptr(lean_string_cstr(msg));
        eprintln!("uncaught exception: {}", text.to_string_lossy());
        lean_dec(msg);
        lean_dec(err);
    }
}
