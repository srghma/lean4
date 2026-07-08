use core::ffi::c_void;
use core::sync::atomic::{AtomicI32, AtomicPtr};
use gmp_mpfr_sys::gmp::mpz_t;

// This module is the Rust equivalent of upstream `lean.h` for ABI layouts and
// helpers hardcoded by EmitRust. Do not import runtime modules here; runtime
// modules may depend on `leanh`, but `leanh` must stay the top-level ABI layer.
pub type Size = usize;
pub const LEAN_CLOSURE_MAX_ARGS: u32 = 16; // not used in this file
pub const LEAN_MAX_SMALL_NAT: usize = usize::MAX >> 1; // not used in this file

#[repr(C)]
pub struct LeanObject {
    pub rc: i32,
    pub cs_size: u16,
    pub other: u8,
    pub tag: u8,
}

#[repr(C)]
// not used in this file
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
    pub m_fun: *mut c_void,
    pub m_arity: u16,
    pub m_num_fixed: u16,
    // 4 bytes of padding on 64-bit; zero-size array marks start of data
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
pub struct LeanTaskObject {
    pub m_header: LeanObject,
    pub m_value: AtomicPtr<LeanObject>,
    pub m_imp: *mut c_void,
}

#[repr(C)]
pub struct LeanPromiseObject {
    pub m_header: LeanObject,
    pub m_result: *mut LeanTaskObject,
}

#[repr(C)]
pub struct LeanTaskImp {
    pub m_closure: *mut LeanObject,
    pub m_head_dep: *mut LeanTaskObject,
    pub m_next_dep: *mut LeanTaskObject,
    pub m_prio: u32,
    pub m_canceled: bool,
    pub m_keep_alive: bool,
    pub m_deleted: bool,
}

#[repr(C)]
pub struct LeanExternalObject {
    pub m_header: LeanObject,
    pub m_class: *mut LeanExternalClass,
    pub m_data: *mut c_void,
}

#[repr(C)]
pub struct LeanMpzObject {
    pub m_header: LeanObject,
    pub m_value: mpz_t,
}

pub const LEAN_MAX_CTOR_TAG: u8 = 243;
pub const LEAN_PROMISE_TAG: u8 = 244;
pub const LEAN_CLOSURE_TAG: u8 = 245;
pub const LEAN_ARRAY_TAG: u8 = 246;
pub const LEAN_STRUCT_ARRAY_TAG: u8 = 247;
pub const LEAN_SCALAR_ARRAY_TAG: u8 = 248;
pub const LEAN_STRING_TAG: u8 = 249;
pub const LEAN_MPZ_TAG: u8 = 250;
pub const LEAN_THUNK_TAG: u8 = 251;
pub const LEAN_TASK_TAG: u8 = 252;
pub const LEAN_REF_TAG: u8 = 253;
pub const LEAN_EXTERNAL_TAG: u8 = 254;
pub const LEAN_RESERVED_TAG: u8 = 255;
pub const LEAN_OBJECT_SIZE_DELTA: usize = 8;
pub const LEAN_MAX_CTOR_FIELDS: u32 = 256;
pub const LEAN_MAX_CTOR_SCALARS_SIZE: u32 = 1024;
