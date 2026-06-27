/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

#![no_std]
#![forbid(unsafe_code)]
#![allow(non_snake_case)]

use core::ffi::{c_char, c_uint, c_void};

/// cbindgen:field-names=[m_rc, m_cs_sz, m_other, m_tag]
#[repr(C)]
pub struct LeanObject {
    pub rc: i32,
    pub cs_size: u16,
    pub other: u8,
    pub tag: u8,
}

/// cbindgen:field-names=[m_header, m_objs]
#[repr(C)]
pub struct LeanCtorObject {
    pub header: LeanObject,
    pub objs: [*mut LeanObject; 0],
}

/// cbindgen:field-names=[m_header, m_size, m_capacity, m_data]
#[repr(C)]
pub struct LeanArrayObject {
    pub header: LeanObject,
    pub size: usize,
    pub capacity: usize,
    pub data: [*mut LeanObject; 0],
}

/// cbindgen:field-names=[m_header, m_size, m_capacity, m_data]
#[repr(C)]
pub struct LeanScalarArray {
    pub header: LeanObject,
    pub size: usize,
    pub capacity: usize,
    pub data: [u8; 0],
}

/// cbindgen:field-names=[m_header, m_size, m_capacity, m_length, m_data]
#[repr(C)]
pub struct LeanStringObject {
    pub header: LeanObject,
    pub size: usize,
    pub capacity: usize,
    pub length: usize,
    pub data: [c_char; 0],
}

/// cbindgen:field-names=[m_header, m_fun, m_arity, m_num_fixed, m_objs]
#[repr(C)]
pub struct LeanClosureObject {
    pub header: LeanObject,
    pub fun: *mut c_void,
    pub arity: u16,
    pub num_fixed: u16,
    pub objs: [*mut LeanObject; 0],
}

/// cbindgen:field-names=[m_header, m_value]
#[repr(C)]
pub struct LeanRefObject {
    pub header: LeanObject,
    pub value: *mut LeanObject,
}

/// cbindgen:field-names=[m_header, m_value, m_closure]
#[repr(C)]
pub struct LeanThunkObject {
    pub header: LeanObject,
    pub value: *mut LeanObject,
    pub closure: *mut LeanObject,
}

/// cbindgen:field-names=[m_closure, m_head_dep, m_next_dep, m_prio, m_canceled, m_keep_alive, m_deleted]
#[repr(C)]
pub struct LeanTaskImp {
    pub closure: *mut LeanObject,
    pub head_dep: *mut LeanTaskObject,
    pub next_dep: *mut LeanTaskObject,
    pub prio: c_uint,
    pub canceled: u8,
    pub keep_alive: u8,
    pub deleted: u8,
}

/// cbindgen:field-names=[m_header, m_value, m_imp]
#[repr(C)]
pub struct LeanTaskObject {
    pub header: LeanObject,
    pub value: *mut LeanObject,
    pub imp: *mut LeanTaskImp,
}

/// cbindgen:field-names=[m_header, m_result]
#[repr(C)]
pub struct LeanPromiseObject {
    pub header: LeanObject,
    pub result: *mut LeanTaskObject,
}

pub type LeanExternalFinalizeProc = unsafe fn(*mut c_void);
pub type LeanExternalForeachProc = unsafe fn(*mut c_void, *mut LeanObject);

/// cbindgen:field-names=[m_finalize, m_foreach]
#[repr(C)]
pub struct LeanExternalClass {
    pub finalize: LeanExternalFinalizeProc,
    pub foreach: LeanExternalForeachProc,
}

/// cbindgen:field-names=[m_header, m_class, m_data]
#[repr(C)]
pub struct LeanExternalObject {
    pub header: LeanObject,
    pub class: *mut LeanExternalClass,
    pub data: *mut c_void,
}

#[repr(C)]
pub struct LeanOnceCell {
    pub state: i32,
    pub lock: i32,
}
