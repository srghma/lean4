/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

This crate exists solely so cbindgen can generate lean.h from Rust type definitions.
It contains ONLY the #[repr(C)] structs that need to be exported to C — no logic.
cbindgen is run against this crate, not against lean_runtime (which contains
complex generic types that panic cbindgen).
*/

#![no_std]
#![allow(dead_code)]

use core::ffi::{c_char, c_void};

/// The base Lean object header.
/// cbindgen:field-names=[m_rc, m_cs_sz, m_other, m_tag]
#[repr(C)]
pub struct LeanObject {
    pub m_rc:     i32,
    pub m_cs_sz:  u16,
    pub m_other:  u8,
    pub m_tag:    u8,
}

/// External class (vtable for finalizer + foreach).
/// cbindgen:field-names=[m_finalize, m_foreach]
#[repr(C)]
pub struct LeanExternalClass {
    pub m_finalize: Option<unsafe extern "C" fn(*mut c_void)>,
    pub m_foreach:  Option<unsafe extern "C" fn(*mut c_void, *mut LeanObject)>,
}

/// External object (wraps a C pointer with class vtable).
/// cbindgen:field-names=[m_header, m_class, m_data]
#[repr(C)]
pub struct LeanExternalObject {
    pub m_header: LeanObject,
    pub m_class:  *mut LeanExternalClass,
    pub m_data:   *mut c_void,
}

/// Lean Array object (lean_array_object in C).
/// cbindgen:field-names=[m_header, m_size, m_capacity, m_data]
#[repr(C)]
pub struct LeanArrayObject {
    pub m_header:   LeanObject,
    pub m_size:     usize,
    pub m_capacity: usize,
    pub m_data:     [*mut LeanObject; 0],
}

/// Lean constructor object (lean_ctor_object in C).
/// cbindgen:field-names=[m_header, m_objs]
#[repr(C)]
pub struct LeanCtorObject {
    pub m_header: LeanObject,
    pub m_objs:   [*mut LeanObject; 0],
}

/// Lean String object (lean_string_object in C).
/// cbindgen:field-names=[m_header, m_size, m_capacity, m_length, m_data]
#[repr(C)]
pub struct LeanStringObject {
    pub m_header:   LeanObject,
    pub m_size:     usize,   // byte length including '\0' terminator
    pub m_capacity: usize,
    pub m_length:   usize,   // UTF-8 codepoint length
    pub m_data:     [c_char; 0],
}

/// Lean Closure object (lean_closure_object in C).
/// cbindgen:field-names=[m_header, m_fun, m_arity, m_num_fixed, m_objs]
#[repr(C)]
pub struct LeanClosureObject {
    pub m_header:    LeanObject,
    pub m_fun:       *mut c_void,
    pub m_arity:     u16,
    pub m_num_fixed: u16,
    pub m_objs:      [*mut LeanObject; 0],
}

/// Lean Scalar Array object (lean_sarray_object in C).
/// cbindgen:field-names=[m_header, m_size, m_capacity, m_data]
#[repr(C)]
pub struct LeanScalarArray {
    pub m_header:   LeanObject,
    pub m_size:     usize,
    pub m_capacity: usize,
    pub m_data:     [u8; 0],
}

/// Lean Promise object (lean_promise_object in C).
/// cbindgen:field-names=[m_header, m_result]
#[repr(C)]
pub struct LeanPromiseObject {
    pub m_header: LeanObject,
    pub m_result: *mut LeanTaskObject,
}

/// Lean Thunk object (lean_thunk_object in C).
/// The m_value and m_closure fields are _Atomic(lean_object *) in C;
/// they are emitted as lean_object* here. The after_includes block in
/// the generated header must add `#define _Atomic(T) T` if not using C11.
/// cbindgen:field-names=[m_header, m_value, m_closure]
#[repr(C)]
pub struct LeanThunkObject {
    pub m_header:  LeanObject,
    pub m_value:   *mut LeanObject,
    pub m_closure: *mut LeanObject,
}

/// Lean Ref object (lean_ref_object in C).
/// cbindgen:field-names=[m_header, m_value]
#[repr(C)]
pub struct LeanRefObject {
    pub m_header: LeanObject,
    pub m_value:  *mut LeanObject,
}

/// Lean task implementation data (lean_task_imp in C).
/// cbindgen:field-names=[m_closure, m_head_dep, m_next_dep, m_prio, m_canceled, m_keep_alive, m_deleted]
#[repr(C)]
pub struct LeanTaskImp {
    pub m_closure:    *mut LeanObject,
    pub m_head_dep:   *mut LeanTaskObject,
    pub m_next_dep:   *mut LeanTaskObject,
    pub m_prio:       u32,
    pub m_canceled:   u8,
    pub m_keep_alive: u8,
    pub m_deleted:    u8,
}

/// Lean task object (lean_task_object in C).
/// cbindgen:field-names=[m_header, m_value, m_imp]
#[repr(C)]
pub struct LeanTaskObject {
    pub m_header: LeanObject,
    pub m_value:  *mut LeanObject,
    pub m_imp:    *mut LeanTaskImp,
}

/// Lean once-cell synchronization token (lean_once_cell_t in C).
/// The state and lock fields are _Atomic(int) in C; emitted as int32_t here.
/// cbindgen:field-names=[state, lock]
#[repr(C)]
pub struct LeanOnceCell {
    pub state: i32,
    pub lock:  i32,
}
