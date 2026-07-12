use core::ffi::c_void;
use core::sync::atomic::{AtomicI32, AtomicPtr};
use gmp_mpfr_sys::gmp::mpz_t;

// This module is the Rust equivalent of upstream `lean.h` for ABI layouts and
// helpers hardcoded by EmitRust. Do not import runtime modules here; runtime
// modules may depend on `leanh`, but `leanh` must stay the top-level ABI layer.
pub const LEAN_CLOSURE_MAX_ARGS: u32 = 16; // not used in this file
pub const LEAN_MAX_SMALL_NAT: usize = usize::MAX >> 1; // not used in this file

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum LeanObjectTag {
    Ctor(u8),
    Promise,
    Closure,
    Array,
    StructArray,
    ScalarArray,
    String,
    Mpz,
    Thunk,
    Task,
    Ref,
    External,
    Reserved,
}

#[repr(u8)]
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum LeanTaskState {
    Waiting = 0,
    Running = 1,
    Finished = 2,
}

#[repr(u8)]
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum LeanIoResultTag {
    Ok = 0,
    Error = 1,
}

impl LeanIoResultTag {
    #[inline]
    pub fn from_u8(tag: u8) -> Self {
        match tag {
            0 => LeanIoResultTag::Ok,
            1 => LeanIoResultTag::Error,
            n => panic!("invalid LeanIoResultTag {n}"),
        }
    }
}

#[repr(u8)]
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum LeanOptionTag {
    None = 0,
    Some = 1,
}

impl LeanOptionTag {
    #[inline]
    pub fn from_u8(tag: u8) -> Self {
        match tag {
            0 => LeanOptionTag::None,
            1 => LeanOptionTag::Some,
            n => panic!("invalid LeanOptionTag {n}"),
        }
    }
}

impl LeanObjectTag {
    #[inline]
    pub const fn from_u8(tag: u8) -> Self {
        match tag {
            0..=243 => LeanObjectTag::Ctor(tag),
            244 => LeanObjectTag::Promise,
            245 => LeanObjectTag::Closure,
            246 => LeanObjectTag::Array,
            247 => LeanObjectTag::StructArray,
            248 => LeanObjectTag::ScalarArray,
            249 => LeanObjectTag::String,
            250 => LeanObjectTag::Mpz,
            251 => LeanObjectTag::Thunk,
            252 => LeanObjectTag::Task,
            253 => LeanObjectTag::Ref,
            254 => LeanObjectTag::External,
            255 => LeanObjectTag::Reserved,
        }
    }

    #[inline]
    pub const fn as_u8(self) -> u8 {
        match self {
            LeanObjectTag::Ctor(tag) => tag,
            LeanObjectTag::Promise => 244,
            LeanObjectTag::Closure => 245,
            LeanObjectTag::Array => 246,
            LeanObjectTag::StructArray => 247,
            LeanObjectTag::ScalarArray => 248,
            LeanObjectTag::String => 249,
            LeanObjectTag::Mpz => 250,
            LeanObjectTag::Thunk => 251,
            LeanObjectTag::Task => 252,
            LeanObjectTag::Ref => 253,
            LeanObjectTag::External => 254,
            LeanObjectTag::Reserved => 255,
        }
    }
}

impl From<u8> for LeanObjectTag {
    #[inline]
    fn from(tag: u8) -> Self {
        LeanObjectTag::from_u8(tag)
    }
}

impl From<u32> for LeanObjectTag {
    #[inline]
    fn from(tag: u32) -> Self {
        LeanObjectTag::from_u8(tag as u8)
    }
}

impl From<i32> for LeanObjectTag {
    #[inline]
    fn from(tag: i32) -> Self {
        LeanObjectTag::from_u8(tag as u8)
    }
}

#[repr(C)]
pub struct LeanObject {
    pub rc: i32,
    pub cs_size: u16,
    pub other: u8,
    // Stored as a byte to preserve the Lean object ABI/layout.
    // Use `tag()` / `set_tag()` for typed access.
    tag: u8,
}

impl LeanObject {
    #[inline]
    pub const fn new(rc: i32, cs_size: u16, other: u8, tag: LeanObjectTag) -> Self {
        Self {
            rc,
            cs_size,
            other,
            tag: tag.as_u8(),
        }
    }

    #[inline]
    pub fn tag(&self) -> LeanObjectTag {
        LeanObjectTag::from_u8(self.tag)
    }

    #[inline]
    pub fn set_tag(&mut self, tag: LeanObjectTag) {
        self.tag = tag.as_u8();
    }
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
pub type BoolInitFn = unsafe fn() -> bool;
pub type U8InitFn = unsafe fn() -> u8;
pub type U16InitFn = unsafe fn() -> u16;
pub type U32InitFn = unsafe fn() -> u32;
pub type U64InitFn = unsafe fn() -> u64;
pub type UsizeInitFn = unsafe fn() -> usize;
pub type F32InitFn = unsafe fn() -> f32;
pub type F64InitFn = unsafe fn() -> f64;

#[repr(C)]
pub struct LeanExternalClass {
    pub m_finalize: LeanExternalFinalizeProc, // TODO: make Option
    pub m_foreach: LeanExternalForeachProc,   // TODO: make Option
}

#[repr(C)]
pub struct LeanArrayObject<const N: usize> {
    pub m_header: LeanObject,
    pub m_size: usize,
    pub m_capacity: usize,
    pub m_data: [*mut LeanObject; N],
}

unsafe impl<const N: usize> Sync for LeanArrayObject<N> {}

#[repr(C)]
pub struct LeanStringObject<const N: usize> {
    pub m_header: LeanObject,
    pub m_size: usize,
    pub m_capacity: usize,
    pub m_length: usize,
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
    pub m_size: usize,
    pub m_capacity: usize,
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

pub const LEAN_OBJECT_SIZE_DELTA: usize = 8;
pub const LEAN_MAX_CTOR_FIELDS: u32 = 256;
pub const LEAN_MAX_CTOR_SCALARS_SIZE: u32 = 1024;
