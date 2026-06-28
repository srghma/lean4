// Lean compiler output
// Module: Init.Data.SInt.Basic
// Imports: Init.Data.UInt.Basic Init.Data.ToString.Extra
use crate::r#gen::Init::Data::BitVec::Basic::{l_BitVec_sle, l_BitVec_slt};
use crate::r#gen::Init::Data::Int::Basic::{l_Int_pow, l_Int_toNat};
use crate::r#gen::Init::Data::Int::Repr::l_Int_repr;
use crate::r#gen::Init::Data::Repr::l_Repr_addAppParen;
use crate::r#gen::Init::Data::ToString::Extra::{
    initialize_Init_Data_ToString_Extra, runtime_initialize_Init_Data_ToString_Extra,
};
use crate::r#gen::Init::Data::UInt::Basic::{
    initialize_Init_Data_UInt_Basic, l_USize_toUInt64___boxed,
    runtime_initialize_Init_Data_UInt_Basic,
};
use crate::r#gen::Init::Data::UInt::BasicAux::{
    l_UInt8_toUInt64___boxed, l_UInt16_toUInt64___boxed, l_UInt32_toUInt64___boxed,
};
use crate::r#gen::Init::Prelude::l_System_Platform_numBits;
use crate::lean_imports_rs::Init::Data::Int::Basic::{
    lean_int_dec_le, lean_int_dec_lt, lean_int_neg, lean_int_sub, lean_nat_to_int,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_nat_dec_eq, lean_nat_pow, lean_nat_sub, lean_uint8_of_nat_mk, lean_uint8_to_nat,
    lean_uint16_of_nat_mk, lean_uint16_to_nat, lean_uint32_of_nat_mk, lean_uint32_to_nat,
    lean_uint64_of_nat_mk, lean_uint64_to_nat, lean_usize_of_nat_mk, lean_usize_to_nat,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_box_uint32, lean_box_uint64,
    lean_box_usize, lean_cstr_to_nat, lean_ctor_set, lean_dec, lean_dec_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_mark_persistent, lean_obj_once,
    lean_uint8_once, lean_uint16_once, lean_uint32_once, lean_uint64_once, lean_unbox,
    lean_unbox_uint32, lean_unbox_uint64, lean_unbox_usize, lean_unsigned_to_nat, lean_usize_once,
};
pub static mut l_Int8_size: *mut LeanObject = core::ptr::null_mut();
pub static l_instToStringInt8___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instToStringInt8___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instToStringInt8___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instToStringInt8___closed__0_value) as *mut LeanObject;
pub static mut l_instToStringInt8: *mut LeanObject =
    core::ptr::addr_of!(l_instToStringInt8___closed__0_value) as *mut LeanObject;
static mut l_instReprInt8___lam__0___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_instReprInt8___lam__0___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_instReprInt8___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instReprInt8___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instReprInt8___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instReprInt8___closed__0_value) as *mut LeanObject;
pub static mut l_instReprInt8: *mut LeanObject =
    core::ptr::addr_of!(l_instReprInt8___closed__0_value) as *mut LeanObject;
pub static mut l_instReprAtomInt8: *mut LeanObject = core::ptr::null_mut();
pub static l_instHashableInt8___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_UInt8_toUInt64___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instHashableInt8___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instHashableInt8___closed__0_value) as *mut LeanObject;
pub static mut l_instHashableInt8: *mut LeanObject =
    core::ptr::addr_of!(l_instHashableInt8___closed__0_value) as *mut LeanObject;
pub static l_Int8_instNeg___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Int8_neg___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Int8_instNeg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Int8_instNeg___closed__0_value) as *mut LeanObject;
pub static mut l_Int8_instNeg: *mut LeanObject =
    core::ptr::addr_of!(l_Int8_instNeg___closed__0_value) as *mut LeanObject;
static mut l_Int8_maxValue___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Int8_maxValue___closed__0: u8 = 0;
pub static mut l_Int8_maxValue: u8 = 0;
static mut l_Int8_minValue___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Int8_minValue___closed__0: u8 = 0;
static mut l_Int8_minValue___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Int8_minValue___closed__1: u8 = 0;
pub static mut l_Int8_minValue: u8 = 0;
static mut l_Int8_ofIntClamp___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Int8_ofIntClamp___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Int8_ofIntClamp___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Int8_ofIntClamp___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Int8_pow___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Int8_pow___closed__0: u8 = 0;
static mut l_instInhabitedInt8___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_instInhabitedInt8___closed__0: u8 = 0;
pub static mut l_instInhabitedInt8: u8 = 0;
pub static l_instAddInt8___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Int8_add___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instAddInt8___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instAddInt8___closed__0_value) as *mut LeanObject;
pub static mut l_instAddInt8: *mut LeanObject =
    core::ptr::addr_of!(l_instAddInt8___closed__0_value) as *mut LeanObject;
pub static l_instSubInt8___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Int8_sub___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instSubInt8___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instSubInt8___closed__0_value) as *mut LeanObject;
pub static mut l_instSubInt8: *mut LeanObject =
    core::ptr::addr_of!(l_instSubInt8___closed__0_value) as *mut LeanObject;
pub static l_instMulInt8___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Int8_mul___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instMulInt8___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instMulInt8___closed__0_value) as *mut LeanObject;
pub static mut l_instMulInt8: *mut LeanObject =
    core::ptr::addr_of!(l_instMulInt8___closed__0_value) as *mut LeanObject;
pub static l_instPowInt8Nat___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Int8_pow___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instPowInt8Nat___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instPowInt8Nat___closed__0_value) as *mut LeanObject;
pub static mut l_instPowInt8Nat: *mut LeanObject =
    core::ptr::addr_of!(l_instPowInt8Nat___closed__0_value) as *mut LeanObject;
pub static l_instModInt8___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Int8_mod___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instModInt8___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instModInt8___closed__0_value) as *mut LeanObject;
pub static mut l_instModInt8: *mut LeanObject =
    core::ptr::addr_of!(l_instModInt8___closed__0_value) as *mut LeanObject;
pub static l_instDivInt8___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Int8_div___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instDivInt8___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instDivInt8___closed__0_value) as *mut LeanObject;
pub static mut l_instDivInt8: *mut LeanObject =
    core::ptr::addr_of!(l_instDivInt8___closed__0_value) as *mut LeanObject;
pub static mut l_instLTInt8: *mut LeanObject = core::ptr::null_mut();
pub static mut l_instLEInt8: *mut LeanObject = core::ptr::null_mut();
pub static l_instComplementInt8___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Int8_complement___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instComplementInt8___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instComplementInt8___closed__0_value) as *mut LeanObject;
pub static mut l_instComplementInt8: *mut LeanObject =
    core::ptr::addr_of!(l_instComplementInt8___closed__0_value) as *mut LeanObject;
pub static l_instAndOpInt8___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Int8_land___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instAndOpInt8___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instAndOpInt8___closed__0_value) as *mut LeanObject;
pub static mut l_instAndOpInt8: *mut LeanObject =
    core::ptr::addr_of!(l_instAndOpInt8___closed__0_value) as *mut LeanObject;
pub static l_instOrOpInt8___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Int8_lor___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instOrOpInt8___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instOrOpInt8___closed__0_value) as *mut LeanObject;
pub static mut l_instOrOpInt8: *mut LeanObject =
    core::ptr::addr_of!(l_instOrOpInt8___closed__0_value) as *mut LeanObject;
pub static l_instXorOpInt8___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Int8_xor___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instXorOpInt8___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instXorOpInt8___closed__0_value) as *mut LeanObject;
pub static mut l_instXorOpInt8: *mut LeanObject =
    core::ptr::addr_of!(l_instXorOpInt8___closed__0_value) as *mut LeanObject;
pub static l_instShiftLeftInt8___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Int8_shiftLeft___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instShiftLeftInt8___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instShiftLeftInt8___closed__0_value) as *mut LeanObject;
pub static mut l_instShiftLeftInt8: *mut LeanObject =
    core::ptr::addr_of!(l_instShiftLeftInt8___closed__0_value) as *mut LeanObject;
pub static l_instShiftRightInt8___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Int8_shiftRight___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instShiftRightInt8___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instShiftRightInt8___closed__0_value) as *mut LeanObject;
pub static mut l_instShiftRightInt8: *mut LeanObject =
    core::ptr::addr_of!(l_instShiftRightInt8___closed__0_value) as *mut LeanObject;
pub static l_instMaxInt8___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instMaxInt8___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instMaxInt8___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instMaxInt8___closed__0_value) as *mut LeanObject;
pub static mut l_instMaxInt8: *mut LeanObject =
    core::ptr::addr_of!(l_instMaxInt8___closed__0_value) as *mut LeanObject;
pub static l_instMinInt8___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instMinInt8___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instMinInt8___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instMinInt8___closed__0_value) as *mut LeanObject;
pub static mut l_instMinInt8: *mut LeanObject =
    core::ptr::addr_of!(l_instMinInt8___closed__0_value) as *mut LeanObject;
pub static mut l_Int16_size: *mut LeanObject = core::ptr::null_mut();
pub static l_instToStringInt16___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instToStringInt16___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instToStringInt16___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instToStringInt16___closed__0_value) as *mut LeanObject;
pub static mut l_instToStringInt16: *mut LeanObject =
    core::ptr::addr_of!(l_instToStringInt16___closed__0_value) as *mut LeanObject;
pub static l_instReprInt16___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instReprInt16___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instReprInt16___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instReprInt16___closed__0_value) as *mut LeanObject;
pub static mut l_instReprInt16: *mut LeanObject =
    core::ptr::addr_of!(l_instReprInt16___closed__0_value) as *mut LeanObject;
pub static mut l_instReprAtomInt16: *mut LeanObject = core::ptr::null_mut();
pub static l_instHashableInt16___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_UInt16_toUInt64___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instHashableInt16___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instHashableInt16___closed__0_value) as *mut LeanObject;
pub static mut l_instHashableInt16: *mut LeanObject =
    core::ptr::addr_of!(l_instHashableInt16___closed__0_value) as *mut LeanObject;
pub static l_Int16_instNeg___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Int16_neg___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Int16_instNeg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Int16_instNeg___closed__0_value) as *mut LeanObject;
pub static mut l_Int16_instNeg: *mut LeanObject =
    core::ptr::addr_of!(l_Int16_instNeg___closed__0_value) as *mut LeanObject;
static mut l_Int16_maxValue___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Int16_maxValue___closed__0: u16 = 0;
pub static mut l_Int16_maxValue: u16 = 0;
static mut l_Int16_minValue___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Int16_minValue___closed__0: u16 = 0;
static mut l_Int16_minValue___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Int16_minValue___closed__1: u16 = 0;
pub static mut l_Int16_minValue: u16 = 0;
static mut l_Int16_ofIntClamp___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Int16_ofIntClamp___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Int16_ofIntClamp___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Int16_ofIntClamp___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Int16_pow___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Int16_pow___closed__0: u16 = 0;
static mut l_instInhabitedInt16___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_instInhabitedInt16___closed__0: u16 = 0;
pub static mut l_instInhabitedInt16: u16 = 0;
pub static l_instAddInt16___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Int16_add___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instAddInt16___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instAddInt16___closed__0_value) as *mut LeanObject;
pub static mut l_instAddInt16: *mut LeanObject =
    core::ptr::addr_of!(l_instAddInt16___closed__0_value) as *mut LeanObject;
pub static l_instSubInt16___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Int16_sub___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instSubInt16___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instSubInt16___closed__0_value) as *mut LeanObject;
pub static mut l_instSubInt16: *mut LeanObject =
    core::ptr::addr_of!(l_instSubInt16___closed__0_value) as *mut LeanObject;
pub static l_instMulInt16___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Int16_mul___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instMulInt16___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instMulInt16___closed__0_value) as *mut LeanObject;
pub static mut l_instMulInt16: *mut LeanObject =
    core::ptr::addr_of!(l_instMulInt16___closed__0_value) as *mut LeanObject;
pub static l_instPowInt16Nat___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Int16_pow___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instPowInt16Nat___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instPowInt16Nat___closed__0_value) as *mut LeanObject;
pub static mut l_instPowInt16Nat: *mut LeanObject =
    core::ptr::addr_of!(l_instPowInt16Nat___closed__0_value) as *mut LeanObject;
pub static l_instModInt16___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Int16_mod___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instModInt16___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instModInt16___closed__0_value) as *mut LeanObject;
pub static mut l_instModInt16: *mut LeanObject =
    core::ptr::addr_of!(l_instModInt16___closed__0_value) as *mut LeanObject;
pub static l_instDivInt16___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Int16_div___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instDivInt16___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instDivInt16___closed__0_value) as *mut LeanObject;
pub static mut l_instDivInt16: *mut LeanObject =
    core::ptr::addr_of!(l_instDivInt16___closed__0_value) as *mut LeanObject;
pub static mut l_instLTInt16: *mut LeanObject = core::ptr::null_mut();
pub static mut l_instLEInt16: *mut LeanObject = core::ptr::null_mut();
pub static l_instComplementInt16___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Int16_complement___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instComplementInt16___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instComplementInt16___closed__0_value) as *mut LeanObject;
pub static mut l_instComplementInt16: *mut LeanObject =
    core::ptr::addr_of!(l_instComplementInt16___closed__0_value) as *mut LeanObject;
pub static l_instAndOpInt16___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Int16_land___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instAndOpInt16___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instAndOpInt16___closed__0_value) as *mut LeanObject;
pub static mut l_instAndOpInt16: *mut LeanObject =
    core::ptr::addr_of!(l_instAndOpInt16___closed__0_value) as *mut LeanObject;
pub static l_instOrOpInt16___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Int16_lor___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instOrOpInt16___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instOrOpInt16___closed__0_value) as *mut LeanObject;
pub static mut l_instOrOpInt16: *mut LeanObject =
    core::ptr::addr_of!(l_instOrOpInt16___closed__0_value) as *mut LeanObject;
pub static l_instXorOpInt16___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Int16_xor___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instXorOpInt16___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instXorOpInt16___closed__0_value) as *mut LeanObject;
pub static mut l_instXorOpInt16: *mut LeanObject =
    core::ptr::addr_of!(l_instXorOpInt16___closed__0_value) as *mut LeanObject;
pub static l_instShiftLeftInt16___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Int16_shiftLeft___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instShiftLeftInt16___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instShiftLeftInt16___closed__0_value) as *mut LeanObject;
pub static mut l_instShiftLeftInt16: *mut LeanObject =
    core::ptr::addr_of!(l_instShiftLeftInt16___closed__0_value) as *mut LeanObject;
pub static l_instShiftRightInt16___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Int16_shiftRight___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instShiftRightInt16___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instShiftRightInt16___closed__0_value) as *mut LeanObject;
pub static mut l_instShiftRightInt16: *mut LeanObject =
    core::ptr::addr_of!(l_instShiftRightInt16___closed__0_value) as *mut LeanObject;
pub static l_instMaxInt16___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instMaxInt16___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instMaxInt16___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instMaxInt16___closed__0_value) as *mut LeanObject;
pub static mut l_instMaxInt16: *mut LeanObject =
    core::ptr::addr_of!(l_instMaxInt16___closed__0_value) as *mut LeanObject;
pub static l_instMinInt16___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instMinInt16___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instMinInt16___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instMinInt16___closed__0_value) as *mut LeanObject;
pub static mut l_instMinInt16: *mut LeanObject =
    core::ptr::addr_of!(l_instMinInt16___closed__0_value) as *mut LeanObject;
pub static mut l_Int32_size: *mut LeanObject = core::ptr::null_mut();
pub static l_instToStringInt32___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instToStringInt32___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instToStringInt32___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instToStringInt32___closed__0_value) as *mut LeanObject;
pub static mut l_instToStringInt32: *mut LeanObject =
    core::ptr::addr_of!(l_instToStringInt32___closed__0_value) as *mut LeanObject;
pub static l_instReprInt32___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instReprInt32___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instReprInt32___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instReprInt32___closed__0_value) as *mut LeanObject;
pub static mut l_instReprInt32: *mut LeanObject =
    core::ptr::addr_of!(l_instReprInt32___closed__0_value) as *mut LeanObject;
pub static mut l_instReprAtomInt32: *mut LeanObject = core::ptr::null_mut();
pub static l_instHashableInt32___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_UInt32_toUInt64___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instHashableInt32___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instHashableInt32___closed__0_value) as *mut LeanObject;
pub static mut l_instHashableInt32: *mut LeanObject =
    core::ptr::addr_of!(l_instHashableInt32___closed__0_value) as *mut LeanObject;
pub static l_Int32_instNeg___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Int32_neg___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Int32_instNeg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Int32_instNeg___closed__0_value) as *mut LeanObject;
pub static mut l_Int32_instNeg: *mut LeanObject =
    core::ptr::addr_of!(l_Int32_instNeg___closed__0_value) as *mut LeanObject;
static mut l_Int32_maxValue___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Int32_maxValue___closed__0: u32 = 0;
pub static mut l_Int32_maxValue: u32 = 0;
static mut l_Int32_minValue___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Int32_minValue___closed__0: u32 = 0;
static mut l_Int32_minValue___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Int32_minValue___closed__1: u32 = 0;
pub static mut l_Int32_minValue: u32 = 0;
static mut l_Int32_ofIntClamp___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Int32_ofIntClamp___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Int32_ofIntClamp___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Int32_ofIntClamp___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Int32_pow___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Int32_pow___closed__0: u32 = 0;
static mut l_instInhabitedInt32___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_instInhabitedInt32___closed__0: u32 = 0;
pub static mut l_instInhabitedInt32: u32 = 0;
pub static l_instAddInt32___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Int32_add___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instAddInt32___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instAddInt32___closed__0_value) as *mut LeanObject;
pub static mut l_instAddInt32: *mut LeanObject =
    core::ptr::addr_of!(l_instAddInt32___closed__0_value) as *mut LeanObject;
pub static l_instSubInt32___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Int32_sub___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instSubInt32___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instSubInt32___closed__0_value) as *mut LeanObject;
pub static mut l_instSubInt32: *mut LeanObject =
    core::ptr::addr_of!(l_instSubInt32___closed__0_value) as *mut LeanObject;
pub static l_instMulInt32___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Int32_mul___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instMulInt32___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instMulInt32___closed__0_value) as *mut LeanObject;
pub static mut l_instMulInt32: *mut LeanObject =
    core::ptr::addr_of!(l_instMulInt32___closed__0_value) as *mut LeanObject;
pub static l_instPowInt32Nat___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Int32_pow___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instPowInt32Nat___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instPowInt32Nat___closed__0_value) as *mut LeanObject;
pub static mut l_instPowInt32Nat: *mut LeanObject =
    core::ptr::addr_of!(l_instPowInt32Nat___closed__0_value) as *mut LeanObject;
pub static l_instModInt32___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Int32_mod___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instModInt32___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instModInt32___closed__0_value) as *mut LeanObject;
pub static mut l_instModInt32: *mut LeanObject =
    core::ptr::addr_of!(l_instModInt32___closed__0_value) as *mut LeanObject;
pub static l_instDivInt32___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Int32_div___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instDivInt32___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instDivInt32___closed__0_value) as *mut LeanObject;
pub static mut l_instDivInt32: *mut LeanObject =
    core::ptr::addr_of!(l_instDivInt32___closed__0_value) as *mut LeanObject;
pub static mut l_instLTInt32: *mut LeanObject = core::ptr::null_mut();
pub static mut l_instLEInt32: *mut LeanObject = core::ptr::null_mut();
pub static l_instComplementInt32___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Int32_complement___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instComplementInt32___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instComplementInt32___closed__0_value) as *mut LeanObject;
pub static mut l_instComplementInt32: *mut LeanObject =
    core::ptr::addr_of!(l_instComplementInt32___closed__0_value) as *mut LeanObject;
pub static l_instAndOpInt32___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Int32_land___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instAndOpInt32___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instAndOpInt32___closed__0_value) as *mut LeanObject;
pub static mut l_instAndOpInt32: *mut LeanObject =
    core::ptr::addr_of!(l_instAndOpInt32___closed__0_value) as *mut LeanObject;
pub static l_instOrOpInt32___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Int32_lor___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instOrOpInt32___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instOrOpInt32___closed__0_value) as *mut LeanObject;
pub static mut l_instOrOpInt32: *mut LeanObject =
    core::ptr::addr_of!(l_instOrOpInt32___closed__0_value) as *mut LeanObject;
pub static l_instXorOpInt32___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Int32_xor___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instXorOpInt32___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instXorOpInt32___closed__0_value) as *mut LeanObject;
pub static mut l_instXorOpInt32: *mut LeanObject =
    core::ptr::addr_of!(l_instXorOpInt32___closed__0_value) as *mut LeanObject;
pub static l_instShiftLeftInt32___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Int32_shiftLeft___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instShiftLeftInt32___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instShiftLeftInt32___closed__0_value) as *mut LeanObject;
pub static mut l_instShiftLeftInt32: *mut LeanObject =
    core::ptr::addr_of!(l_instShiftLeftInt32___closed__0_value) as *mut LeanObject;
pub static l_instShiftRightInt32___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Int32_shiftRight___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instShiftRightInt32___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instShiftRightInt32___closed__0_value) as *mut LeanObject;
pub static mut l_instShiftRightInt32: *mut LeanObject =
    core::ptr::addr_of!(l_instShiftRightInt32___closed__0_value) as *mut LeanObject;
pub static l_instMaxInt32___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instMaxInt32___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instMaxInt32___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instMaxInt32___closed__0_value) as *mut LeanObject;
pub static mut l_instMaxInt32: *mut LeanObject =
    core::ptr::addr_of!(l_instMaxInt32___closed__0_value) as *mut LeanObject;
pub static l_instMinInt32___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instMinInt32___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instMinInt32___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instMinInt32___closed__0_value) as *mut LeanObject;
pub static mut l_instMinInt32: *mut LeanObject =
    core::ptr::addr_of!(l_instMinInt32___closed__0_value) as *mut LeanObject;
static mut l_Int64_size___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Int64_size___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Int64_size: *mut LeanObject = core::ptr::null_mut();
pub static l_instToStringInt64___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instToStringInt64___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instToStringInt64___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instToStringInt64___closed__0_value) as *mut LeanObject;
pub static mut l_instToStringInt64: *mut LeanObject =
    core::ptr::addr_of!(l_instToStringInt64___closed__0_value) as *mut LeanObject;
pub static l_instReprInt64___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instReprInt64___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instReprInt64___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instReprInt64___closed__0_value) as *mut LeanObject;
pub static mut l_instReprInt64: *mut LeanObject =
    core::ptr::addr_of!(l_instReprInt64___closed__0_value) as *mut LeanObject;
pub static mut l_instReprAtomInt64: *mut LeanObject = core::ptr::null_mut();
pub static l_instHashableInt64___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instHashableInt64___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instHashableInt64___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instHashableInt64___closed__0_value) as *mut LeanObject;
pub static mut l_instHashableInt64: *mut LeanObject =
    core::ptr::addr_of!(l_instHashableInt64___closed__0_value) as *mut LeanObject;
pub static l_Int64_instNeg___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Int64_neg___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Int64_instNeg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Int64_instNeg___closed__0_value) as *mut LeanObject;
pub static mut l_Int64_instNeg: *mut LeanObject =
    core::ptr::addr_of!(l_Int64_instNeg___closed__0_value) as *mut LeanObject;
static mut l_Int64_maxValue___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Int64_maxValue___closed__0: u64 = 0;
pub static mut l_Int64_maxValue: u64 = 0;
static mut l_Int64_minValue___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Int64_minValue___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Int64_minValue___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Int64_minValue___closed__1: u64 = 0;
static mut l_Int64_minValue___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Int64_minValue___closed__2: u64 = 0;
pub static mut l_Int64_minValue: u64 = 0;
static mut l_Int64_ofIntClamp___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Int64_ofIntClamp___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Int64_ofIntClamp___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Int64_ofIntClamp___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Int64_pow___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Int64_pow___closed__0: u64 = 0;
static mut l_instInhabitedInt64___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_instInhabitedInt64___closed__0: u64 = 0;
pub static mut l_instInhabitedInt64: u64 = 0;
pub static l_instAddInt64___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Int64_add___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instAddInt64___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instAddInt64___closed__0_value) as *mut LeanObject;
pub static mut l_instAddInt64: *mut LeanObject =
    core::ptr::addr_of!(l_instAddInt64___closed__0_value) as *mut LeanObject;
pub static l_instSubInt64___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Int64_sub___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instSubInt64___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instSubInt64___closed__0_value) as *mut LeanObject;
pub static mut l_instSubInt64: *mut LeanObject =
    core::ptr::addr_of!(l_instSubInt64___closed__0_value) as *mut LeanObject;
pub static l_instMulInt64___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Int64_mul___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instMulInt64___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instMulInt64___closed__0_value) as *mut LeanObject;
pub static mut l_instMulInt64: *mut LeanObject =
    core::ptr::addr_of!(l_instMulInt64___closed__0_value) as *mut LeanObject;
pub static l_instPowInt64Nat___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Int64_pow___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instPowInt64Nat___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instPowInt64Nat___closed__0_value) as *mut LeanObject;
pub static mut l_instPowInt64Nat: *mut LeanObject =
    core::ptr::addr_of!(l_instPowInt64Nat___closed__0_value) as *mut LeanObject;
pub static l_instModInt64___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Int64_mod___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instModInt64___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instModInt64___closed__0_value) as *mut LeanObject;
pub static mut l_instModInt64: *mut LeanObject =
    core::ptr::addr_of!(l_instModInt64___closed__0_value) as *mut LeanObject;
pub static l_instDivInt64___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Int64_div___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instDivInt64___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instDivInt64___closed__0_value) as *mut LeanObject;
pub static mut l_instDivInt64: *mut LeanObject =
    core::ptr::addr_of!(l_instDivInt64___closed__0_value) as *mut LeanObject;
pub static mut l_instLTInt64: *mut LeanObject = core::ptr::null_mut();
pub static mut l_instLEInt64: *mut LeanObject = core::ptr::null_mut();
pub static l_instComplementInt64___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Int64_complement___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instComplementInt64___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instComplementInt64___closed__0_value) as *mut LeanObject;
pub static mut l_instComplementInt64: *mut LeanObject =
    core::ptr::addr_of!(l_instComplementInt64___closed__0_value) as *mut LeanObject;
pub static l_instAndOpInt64___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Int64_land___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instAndOpInt64___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instAndOpInt64___closed__0_value) as *mut LeanObject;
pub static mut l_instAndOpInt64: *mut LeanObject =
    core::ptr::addr_of!(l_instAndOpInt64___closed__0_value) as *mut LeanObject;
pub static l_instOrOpInt64___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Int64_lor___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instOrOpInt64___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instOrOpInt64___closed__0_value) as *mut LeanObject;
pub static mut l_instOrOpInt64: *mut LeanObject =
    core::ptr::addr_of!(l_instOrOpInt64___closed__0_value) as *mut LeanObject;
pub static l_instXorOpInt64___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Int64_xor___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instXorOpInt64___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instXorOpInt64___closed__0_value) as *mut LeanObject;
pub static mut l_instXorOpInt64: *mut LeanObject =
    core::ptr::addr_of!(l_instXorOpInt64___closed__0_value) as *mut LeanObject;
pub static l_instShiftLeftInt64___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Int64_shiftLeft___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instShiftLeftInt64___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instShiftLeftInt64___closed__0_value) as *mut LeanObject;
pub static mut l_instShiftLeftInt64: *mut LeanObject =
    core::ptr::addr_of!(l_instShiftLeftInt64___closed__0_value) as *mut LeanObject;
pub static l_instShiftRightInt64___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Int64_shiftRight___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instShiftRightInt64___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instShiftRightInt64___closed__0_value) as *mut LeanObject;
pub static mut l_instShiftRightInt64: *mut LeanObject =
    core::ptr::addr_of!(l_instShiftRightInt64___closed__0_value) as *mut LeanObject;
pub static l_instMaxInt64___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instMaxInt64___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instMaxInt64___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instMaxInt64___closed__0_value) as *mut LeanObject;
pub static mut l_instMaxInt64: *mut LeanObject =
    core::ptr::addr_of!(l_instMaxInt64___closed__0_value) as *mut LeanObject;
pub static l_instMinInt64___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instMinInt64___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instMinInt64___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instMinInt64___closed__0_value) as *mut LeanObject;
pub static mut l_instMinInt64: *mut LeanObject =
    core::ptr::addr_of!(l_instMinInt64___closed__0_value) as *mut LeanObject;
static mut l_ISize_size___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_ISize_size___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static mut l_ISize_size: *mut LeanObject = core::ptr::null_mut();
pub static l_instToStringISize___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instToStringISize___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instToStringISize___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instToStringISize___closed__0_value) as *mut LeanObject;
pub static mut l_instToStringISize: *mut LeanObject =
    core::ptr::addr_of!(l_instToStringISize___closed__0_value) as *mut LeanObject;
pub static l_instReprISize___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instReprISize___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instReprISize___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instReprISize___closed__0_value) as *mut LeanObject;
pub static mut l_instReprISize: *mut LeanObject =
    core::ptr::addr_of!(l_instReprISize___closed__0_value) as *mut LeanObject;
pub static mut l_instReprAtomISize: *mut LeanObject = core::ptr::null_mut();
pub static l_instHashableISize___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_USize_toUInt64___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instHashableISize___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instHashableISize___closed__0_value) as *mut LeanObject;
pub static mut l_instHashableISize: *mut LeanObject =
    core::ptr::addr_of!(l_instHashableISize___closed__0_value) as *mut LeanObject;
pub static l_ISize_instNeg___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_ISize_neg___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_ISize_instNeg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_ISize_instNeg___closed__0_value) as *mut LeanObject;
pub static mut l_ISize_instNeg: *mut LeanObject =
    core::ptr::addr_of!(l_ISize_instNeg___closed__0_value) as *mut LeanObject;
static mut l_ISize_maxValue___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_ISize_maxValue___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_ISize_maxValue___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_ISize_maxValue___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_ISize_maxValue___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_ISize_maxValue___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_ISize_maxValue___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_ISize_maxValue___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_ISize_maxValue___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_ISize_maxValue___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_ISize_maxValue___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_ISize_maxValue___closed__5: usize = 0;
pub static mut l_ISize_maxValue: usize = 0;
static mut l_ISize_minValue___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_ISize_minValue___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_ISize_minValue___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_ISize_minValue___closed__1: usize = 0;
pub static mut l_ISize_minValue: usize = 0;
static mut l_ISize_ofIntClamp___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_ISize_ofIntClamp___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_ISize_ofIntClamp___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_ISize_ofIntClamp___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_ISize_pow___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_ISize_pow___closed__0: usize = 0;
static mut l_instInhabitedISize___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_instInhabitedISize___closed__0: usize = 0;
pub static mut l_instInhabitedISize: usize = 0;
pub static l_instAddISize___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_ISize_add___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instAddISize___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instAddISize___closed__0_value) as *mut LeanObject;
pub static mut l_instAddISize: *mut LeanObject =
    core::ptr::addr_of!(l_instAddISize___closed__0_value) as *mut LeanObject;
pub static l_instSubISize___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_ISize_sub___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instSubISize___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instSubISize___closed__0_value) as *mut LeanObject;
pub static mut l_instSubISize: *mut LeanObject =
    core::ptr::addr_of!(l_instSubISize___closed__0_value) as *mut LeanObject;
pub static l_instMulISize___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_ISize_mul___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instMulISize___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instMulISize___closed__0_value) as *mut LeanObject;
pub static mut l_instMulISize: *mut LeanObject =
    core::ptr::addr_of!(l_instMulISize___closed__0_value) as *mut LeanObject;
pub static l_instPowISizeNat___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_ISize_pow___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instPowISizeNat___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instPowISizeNat___closed__0_value) as *mut LeanObject;
pub static mut l_instPowISizeNat: *mut LeanObject =
    core::ptr::addr_of!(l_instPowISizeNat___closed__0_value) as *mut LeanObject;
pub static l_instModISize___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_ISize_mod___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instModISize___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instModISize___closed__0_value) as *mut LeanObject;
pub static mut l_instModISize: *mut LeanObject =
    core::ptr::addr_of!(l_instModISize___closed__0_value) as *mut LeanObject;
pub static l_instDivISize___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_ISize_div___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instDivISize___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instDivISize___closed__0_value) as *mut LeanObject;
pub static mut l_instDivISize: *mut LeanObject =
    core::ptr::addr_of!(l_instDivISize___closed__0_value) as *mut LeanObject;
pub static mut l_instLTISize: *mut LeanObject = core::ptr::null_mut();
pub static mut l_instLEISize: *mut LeanObject = core::ptr::null_mut();
pub static l_instComplementISize___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_ISize_complement___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instComplementISize___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instComplementISize___closed__0_value) as *mut LeanObject;
pub static mut l_instComplementISize: *mut LeanObject =
    core::ptr::addr_of!(l_instComplementISize___closed__0_value) as *mut LeanObject;
pub static l_instAndOpISize___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_ISize_land___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instAndOpISize___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instAndOpISize___closed__0_value) as *mut LeanObject;
pub static mut l_instAndOpISize: *mut LeanObject =
    core::ptr::addr_of!(l_instAndOpISize___closed__0_value) as *mut LeanObject;
pub static l_instOrOpISize___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_ISize_lor___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instOrOpISize___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instOrOpISize___closed__0_value) as *mut LeanObject;
pub static mut l_instOrOpISize: *mut LeanObject =
    core::ptr::addr_of!(l_instOrOpISize___closed__0_value) as *mut LeanObject;
pub static l_instXorOpISize___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_ISize_xor___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instXorOpISize___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instXorOpISize___closed__0_value) as *mut LeanObject;
pub static mut l_instXorOpISize: *mut LeanObject =
    core::ptr::addr_of!(l_instXorOpISize___closed__0_value) as *mut LeanObject;
pub static l_instShiftLeftISize___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_ISize_shiftLeft___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instShiftLeftISize___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instShiftLeftISize___closed__0_value) as *mut LeanObject;
pub static mut l_instShiftLeftISize: *mut LeanObject =
    core::ptr::addr_of!(l_instShiftLeftISize___closed__0_value) as *mut LeanObject;
pub static l_instShiftRightISize___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_ISize_shiftRight___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instShiftRightISize___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instShiftRightISize___closed__0_value) as *mut LeanObject;
pub static mut l_instShiftRightISize: *mut LeanObject =
    core::ptr::addr_of!(l_instShiftRightISize___closed__0_value) as *mut LeanObject;
pub static l_instMaxISize___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instMaxISize___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instMaxISize___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instMaxISize___closed__0_value) as *mut LeanObject;
pub static mut l_instMaxISize: *mut LeanObject =
    core::ptr::addr_of!(l_instMaxISize___closed__0_value) as *mut LeanObject;
pub static l_instMinISize___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instMinISize___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instMinISize___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instMinISize___closed__0_value) as *mut LeanObject;
pub static mut l_instMinISize: *mut LeanObject =
    core::ptr::addr_of!(l_instMinISize___closed__0_value) as *mut LeanObject;
pub unsafe fn _init_l_Int8_size() -> *mut LeanObject {
    let mut v___x_1841_: *mut LeanObject = core::ptr::null_mut();
    v___x_1841_ = lean_unsigned_to_nat(256);
    return v___x_1841_;
}
pub unsafe fn l_Int8_toBitVec(mut v_x_1842_: u8) -> *mut LeanObject {
    let mut v___x_1843_: *mut LeanObject = core::ptr::null_mut();
    v___x_1843_ = lean_uint8_to_nat(v_x_1842_);
    return v___x_1843_;
}
pub unsafe fn l_Int8_toBitVec___boxed(mut v_x_1844_: *mut LeanObject) -> *mut LeanObject {
    let mut v_x_boxed_1845_: u8 = 0;
    let mut v_res_1846_: *mut LeanObject = core::ptr::null_mut();
    v_x_boxed_1845_ = (lean_unbox(v_x_1844_) as u8);
    v_res_1846_ = l_Int8_toBitVec(v_x_boxed_1845_);
    return v_res_1846_;
}
pub unsafe fn l_UInt8_toInt8(mut v_i_1847_: u8) -> u8 {
    return v_i_1847_;
}
pub unsafe fn l_UInt8_toInt8___boxed(mut v_i_1848_: *mut LeanObject) -> *mut LeanObject {
    let mut v_i_boxed_1849_: u8 = 0;
    let mut v_res_1850_: u8 = 0;
    let mut v_r_1851_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_1849_ = (lean_unbox(v_i_1848_) as u8);
    v_res_1850_ = l_UInt8_toInt8(v_i_boxed_1849_);
    v_r_1851_ = lean_box((v_res_1850_) as usize);
    return v_r_1851_;
}
pub unsafe fn l_Int8_ofInt___boxed(mut v_i_1853_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_1854_: u8 = 0;
    let mut v_r_1855_: *mut LeanObject = core::ptr::null_mut();
    v_res_1854_ = lean_int8_of_int(v_i_1853_);
    lean_dec(v_i_1853_);
    v_r_1855_ = lean_box((v_res_1854_) as usize);
    return v_r_1855_;
}
pub unsafe fn l_Int8_ofNat___boxed(mut v_n_1857_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_1858_: u8 = 0;
    let mut v_r_1859_: *mut LeanObject = core::ptr::null_mut();
    v_res_1858_ = lean_int8_of_nat(v_n_1857_);
    lean_dec(v_n_1857_);
    v_r_1859_ = lean_box((v_res_1858_) as usize);
    return v_r_1859_;
}
pub unsafe fn l_Int_toInt8(mut v_i_1860_: *mut LeanObject) -> u8 {
    let mut v___x_1861_: u8 = 0;
    v___x_1861_ = lean_int8_of_int(v_i_1860_);
    return v___x_1861_;
}
pub unsafe fn l_Int_toInt8___boxed(mut v_i_1862_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_1863_: u8 = 0;
    let mut v_r_1864_: *mut LeanObject = core::ptr::null_mut();
    v_res_1863_ = l_Int_toInt8(v_i_1862_);
    lean_dec(v_i_1862_);
    v_r_1864_ = lean_box((v_res_1863_) as usize);
    return v_r_1864_;
}
pub unsafe fn l_Nat_toInt8(mut v_n_1865_: *mut LeanObject) -> u8 {
    let mut v___x_1866_: u8 = 0;
    v___x_1866_ = lean_int8_of_nat(v_n_1865_);
    return v___x_1866_;
}
pub unsafe fn l_Nat_toInt8___boxed(mut v_n_1867_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_1868_: u8 = 0;
    let mut v_r_1869_: *mut LeanObject = core::ptr::null_mut();
    v_res_1868_ = l_Nat_toInt8(v_n_1867_);
    lean_dec(v_n_1867_);
    v_r_1869_ = lean_box((v_res_1868_) as usize);
    return v_r_1869_;
}
pub unsafe fn l_Int8_toInt___boxed(mut v_i_1871_: *mut LeanObject) -> *mut LeanObject {
    let mut v_i_boxed_1872_: u8 = 0;
    let mut v_res_1873_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_1872_ = (lean_unbox(v_i_1871_) as u8);
    v_res_1873_ = lean_int8_to_int(v_i_boxed_1872_);
    return v_res_1873_;
}
pub unsafe fn l_Int8_toNatClampNeg(mut v_i_1874_: u8) -> *mut LeanObject {
    let mut v___x_1875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1876_: *mut LeanObject = core::ptr::null_mut();
    v___x_1875_ = lean_int8_to_int(v_i_1874_);
    v___x_1876_ = l_Int_toNat(v___x_1875_);
    return v___x_1876_;
}
pub unsafe fn l_Int8_toNatClampNeg___boxed(mut v_i_1877_: *mut LeanObject) -> *mut LeanObject {
    let mut v_i_boxed_1878_: u8 = 0;
    let mut v_res_1879_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_1878_ = (lean_unbox(v_i_1877_) as u8);
    v_res_1879_ = l_Int8_toNatClampNeg(v_i_boxed_1878_);
    return v_res_1879_;
}
pub unsafe fn l_Int8_ofBitVec(mut v_b_1880_: *mut LeanObject) -> u8 {
    let mut v___x_1881_: u8 = 0;
    v___x_1881_ = lean_uint8_of_nat_mk(v_b_1880_);
    return v___x_1881_;
}
pub unsafe fn l_Int8_ofBitVec___boxed(mut v_b_1882_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_1883_: u8 = 0;
    let mut v_r_1884_: *mut LeanObject = core::ptr::null_mut();
    v_res_1883_ = l_Int8_ofBitVec(v_b_1882_);
    v_r_1884_ = lean_box((v_res_1883_) as usize);
    return v_r_1884_;
}
pub unsafe fn l_Int8_neg___boxed(mut v_i_1886_: *mut LeanObject) -> *mut LeanObject {
    let mut v_i_boxed_1887_: u8 = 0;
    let mut v_res_1888_: u8 = 0;
    let mut v_r_1889_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_1887_ = (lean_unbox(v_i_1886_) as u8);
    v_res_1888_ = lean_int8_neg(v_i_boxed_1887_);
    v_r_1889_ = lean_box((v_res_1888_) as usize);
    return v_r_1889_;
}
pub unsafe fn l_instToStringInt8___lam__0(mut v_i_1890_: u8) -> *mut LeanObject {
    let mut v___x_1891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1892_: *mut LeanObject = core::ptr::null_mut();
    v___x_1891_ = lean_int8_to_int(v_i_1890_);
    v___x_1892_ = l_Int_repr(v___x_1891_);
    return v___x_1892_;
}
pub unsafe fn l_instToStringInt8___lam__0___boxed(
    mut v_i_1893_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_1894_: u8 = 0;
    let mut v_res_1895_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_1894_ = (lean_unbox(v_i_1893_) as u8);
    v_res_1895_ = l_instToStringInt8___lam__0(v_i_boxed_1894_);
    return v_res_1895_;
}
pub unsafe fn _init_l_instReprInt8___lam__0___closed__0() -> *mut LeanObject {
    let mut v___x_1898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1899_: *mut LeanObject = core::ptr::null_mut();
    v___x_1898_ = lean_unsigned_to_nat(0);
    v___x_1899_ = lean_nat_to_int(v___x_1898_);
    return v___x_1899_;
}
pub unsafe fn l_instReprInt8___lam__0(
    mut v_i_1900_: u8,
    mut v_prec_1901_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1904_: u8 = 0;
    v___x_1902_ = lean_int8_to_int(v_i_1900_);
    v___x_1903_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_instReprInt8___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_instReprInt8___lam__0___closed__0_once),
        _init_l_instReprInt8___lam__0___closed__0,
    );
    v___x_1904_ = lean_int_dec_lt(v___x_1902_, v___x_1903_);
    if v___x_1904_ == 0 {
        let mut v___x_1905_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1906_: *mut LeanObject = core::ptr::null_mut();
        v___x_1905_ = l_Int_repr(v___x_1902_);
        v___x_1906_ = lean_alloc_ctor(3, 1, (0) as u32);
        lean_ctor_set(v___x_1906_, 0, v___x_1905_);
        return v___x_1906_;
    } else {
        let mut v___x_1907_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1908_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1909_: *mut LeanObject = core::ptr::null_mut();
        v___x_1907_ = l_Int_repr(v___x_1902_);
        v___x_1908_ = lean_alloc_ctor(3, 1, (0) as u32);
        lean_ctor_set(v___x_1908_, 0, v___x_1907_);
        v___x_1909_ = l_Repr_addAppParen(v___x_1908_, v_prec_1901_);
        return v___x_1909_;
    }
}
pub unsafe fn l_instReprInt8___lam__0___boxed(
    mut v_i_1910_: *mut LeanObject,
    mut v_prec_1911_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_1912_: u8 = 0;
    let mut v_res_1913_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_1912_ = (lean_unbox(v_i_1910_) as u8);
    v_res_1913_ = l_instReprInt8___lam__0(v_i_boxed_1912_, v_prec_1911_);
    lean_dec(v_prec_1911_);
    return v_res_1913_;
}
pub unsafe fn _init_l_instReprAtomInt8() -> *mut LeanObject {
    let mut v___x_1916_: *mut LeanObject = core::ptr::null_mut();
    v___x_1916_ = lean_box(0);
    return v___x_1916_;
}
pub unsafe fn l_Int8_instOfNat(mut v_n_1919_: *mut LeanObject) -> u8 {
    let mut v___x_1920_: u8 = 0;
    v___x_1920_ = lean_int8_of_nat(v_n_1919_);
    return v___x_1920_;
}
pub unsafe fn l_Int8_instOfNat___boxed(mut v_n_1921_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_1922_: u8 = 0;
    let mut v_r_1923_: *mut LeanObject = core::ptr::null_mut();
    v_res_1922_ = l_Int8_instOfNat(v_n_1921_);
    lean_dec(v_n_1921_);
    v_r_1923_ = lean_box((v_res_1922_) as usize);
    return v_r_1923_;
}
pub unsafe fn _init_l_Int8_maxValue___closed__0() -> u8 {
    let mut v___x_1926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1927_: u8 = 0;
    v___x_1926_ = lean_unsigned_to_nat(127);
    v___x_1927_ = lean_int8_of_nat(v___x_1926_);
    return v___x_1927_;
}
pub unsafe fn _init_l_Int8_maxValue() -> u8 {
    let mut v___x_1928_: u8 = 0;
    v___x_1928_ = lean_uint8_once(
        core::ptr::addr_of_mut!(l_Int8_maxValue___closed__0),
        core::ptr::addr_of_mut!(l_Int8_maxValue___closed__0_once),
        _init_l_Int8_maxValue___closed__0,
    );
    return v___x_1928_;
}
pub unsafe fn _init_l_Int8_minValue___closed__0() -> u8 {
    let mut v___x_1929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1930_: u8 = 0;
    v___x_1929_ = lean_unsigned_to_nat(128);
    v___x_1930_ = lean_int8_of_nat(v___x_1929_);
    return v___x_1930_;
}
pub unsafe fn _init_l_Int8_minValue___closed__1() -> u8 {
    let mut v___x_1931_: u8 = 0;
    let mut v___x_1932_: u8 = 0;
    v___x_1931_ = lean_uint8_once(
        core::ptr::addr_of_mut!(l_Int8_minValue___closed__0),
        core::ptr::addr_of_mut!(l_Int8_minValue___closed__0_once),
        _init_l_Int8_minValue___closed__0,
    );
    v___x_1932_ = lean_int8_neg(v___x_1931_);
    return v___x_1932_;
}
pub unsafe fn _init_l_Int8_minValue() -> u8 {
    let mut v___x_1933_: u8 = 0;
    v___x_1933_ = lean_uint8_once(
        core::ptr::addr_of_mut!(l_Int8_minValue___closed__1),
        core::ptr::addr_of_mut!(l_Int8_minValue___closed__1_once),
        _init_l_Int8_minValue___closed__1,
    );
    return v___x_1933_;
}
pub unsafe fn l_Int8_ofIntLE___redArg(mut v_i_1934_: *mut LeanObject) -> u8 {
    let mut v___x_1935_: u8 = 0;
    v___x_1935_ = lean_int8_of_int(v_i_1934_);
    return v___x_1935_;
}
pub unsafe fn l_Int8_ofIntLE___redArg___boxed(mut v_i_1936_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_1937_: u8 = 0;
    let mut v_r_1938_: *mut LeanObject = core::ptr::null_mut();
    v_res_1937_ = l_Int8_ofIntLE___redArg(v_i_1936_);
    lean_dec(v_i_1936_);
    v_r_1938_ = lean_box((v_res_1937_) as usize);
    return v_r_1938_;
}
pub unsafe fn l_Int8_ofIntLE(
    mut v_i_1939_: *mut LeanObject,
    mut v___hl_1940_: *mut LeanObject,
    mut v___hr_1941_: *mut LeanObject,
) -> u8 {
    let mut v___x_1942_: u8 = 0;
    v___x_1942_ = lean_int8_of_int(v_i_1939_);
    return v___x_1942_;
}
pub unsafe fn l_Int8_ofIntLE___boxed(
    mut v_i_1943_: *mut LeanObject,
    mut v___hl_1944_: *mut LeanObject,
    mut v___hr_1945_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1946_: u8 = 0;
    let mut v_r_1947_: *mut LeanObject = core::ptr::null_mut();
    v_res_1946_ = l_Int8_ofIntLE(v_i_1943_, v___hl_1944_, v___hr_1945_);
    lean_dec(v_i_1943_);
    v_r_1947_ = lean_box((v_res_1946_) as usize);
    return v_r_1947_;
}
pub unsafe fn _init_l_Int8_ofIntClamp___closed__0() -> *mut LeanObject {
    let mut v___x_1948_: u8 = 0;
    let mut v___x_1949_: *mut LeanObject = core::ptr::null_mut();
    v___x_1948_ = lean_uint8_once(
        core::ptr::addr_of_mut!(l_Int8_minValue___closed__1),
        core::ptr::addr_of_mut!(l_Int8_minValue___closed__1_once),
        _init_l_Int8_minValue___closed__1,
    );
    v___x_1949_ = lean_int8_to_int(v___x_1948_);
    return v___x_1949_;
}
pub unsafe fn _init_l_Int8_ofIntClamp___closed__1() -> *mut LeanObject {
    let mut v___x_1950_: u8 = 0;
    let mut v___x_1951_: *mut LeanObject = core::ptr::null_mut();
    v___x_1950_ = lean_uint8_once(
        core::ptr::addr_of_mut!(l_Int8_maxValue___closed__0),
        core::ptr::addr_of_mut!(l_Int8_maxValue___closed__0_once),
        _init_l_Int8_maxValue___closed__0,
    );
    v___x_1951_ = lean_int8_to_int(v___x_1950_);
    return v___x_1951_;
}
pub unsafe fn l_Int8_ofIntClamp(mut v_i_1952_: *mut LeanObject) -> u8 {
    let mut v___x_1953_: u8 = 0;
    let mut v___x_1954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1955_: u8 = 0;
    v___x_1953_ = lean_uint8_once(
        core::ptr::addr_of_mut!(l_Int8_minValue___closed__1),
        core::ptr::addr_of_mut!(l_Int8_minValue___closed__1_once),
        _init_l_Int8_minValue___closed__1,
    );
    v___x_1954_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Int8_ofIntClamp___closed__0),
        core::ptr::addr_of_mut!(l_Int8_ofIntClamp___closed__0_once),
        _init_l_Int8_ofIntClamp___closed__0,
    );
    v___x_1955_ = lean_int_dec_le(v___x_1954_, v_i_1952_);
    if v___x_1955_ == 0 {
        return v___x_1953_;
    } else {
        let mut v___x_1956_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1957_: u8 = 0;
        v___x_1956_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Int8_ofIntClamp___closed__1),
            core::ptr::addr_of_mut!(l_Int8_ofIntClamp___closed__1_once),
            _init_l_Int8_ofIntClamp___closed__1,
        );
        v___x_1957_ = lean_int_dec_le(v_i_1952_, v___x_1956_);
        if v___x_1957_ == 0 {
            return v___x_1953_;
        } else {
            let mut v___x_1958_: u8 = 0;
            v___x_1958_ = lean_int8_of_int(v_i_1952_);
            return v___x_1958_;
        }
    }
}
pub unsafe fn l_Int8_ofIntClamp___boxed(mut v_i_1959_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_1960_: u8 = 0;
    let mut v_r_1961_: *mut LeanObject = core::ptr::null_mut();
    v_res_1960_ = l_Int8_ofIntClamp(v_i_1959_);
    lean_dec(v_i_1959_);
    v_r_1961_ = lean_box((v_res_1960_) as usize);
    return v_r_1961_;
}
pub unsafe fn l_Int8_ofIntTruncate(mut v_i_1962_: *mut LeanObject) -> u8 {
    let mut v___x_1963_: u8 = 0;
    v___x_1963_ = l_Int8_ofIntClamp(v_i_1962_);
    return v___x_1963_;
}
pub unsafe fn l_Int8_ofIntTruncate___boxed(mut v_i_1964_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_1965_: u8 = 0;
    let mut v_r_1966_: *mut LeanObject = core::ptr::null_mut();
    v_res_1965_ = l_Int8_ofIntTruncate(v_i_1964_);
    lean_dec(v_i_1964_);
    v_r_1966_ = lean_box((v_res_1965_) as usize);
    return v_r_1966_;
}
pub unsafe fn l_Int8_add___boxed(
    mut v_a_1969_: *mut LeanObject,
    mut v_b_1970_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_1971_: u8 = 0;
    let mut v_b_boxed_1972_: u8 = 0;
    let mut v_res_1973_: u8 = 0;
    let mut v_r_1974_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_1971_ = (lean_unbox(v_a_1969_) as u8);
    v_b_boxed_1972_ = (lean_unbox(v_b_1970_) as u8);
    v_res_1973_ = lean_int8_add(v_a_boxed_1971_, v_b_boxed_1972_);
    v_r_1974_ = lean_box((v_res_1973_) as usize);
    return v_r_1974_;
}
pub unsafe fn l_Int8_sub___boxed(
    mut v_a_1977_: *mut LeanObject,
    mut v_b_1978_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_1979_: u8 = 0;
    let mut v_b_boxed_1980_: u8 = 0;
    let mut v_res_1981_: u8 = 0;
    let mut v_r_1982_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_1979_ = (lean_unbox(v_a_1977_) as u8);
    v_b_boxed_1980_ = (lean_unbox(v_b_1978_) as u8);
    v_res_1981_ = lean_int8_sub(v_a_boxed_1979_, v_b_boxed_1980_);
    v_r_1982_ = lean_box((v_res_1981_) as usize);
    return v_r_1982_;
}
pub unsafe fn l_Int8_mul___boxed(
    mut v_a_1985_: *mut LeanObject,
    mut v_b_1986_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_1987_: u8 = 0;
    let mut v_b_boxed_1988_: u8 = 0;
    let mut v_res_1989_: u8 = 0;
    let mut v_r_1990_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_1987_ = (lean_unbox(v_a_1985_) as u8);
    v_b_boxed_1988_ = (lean_unbox(v_b_1986_) as u8);
    v_res_1989_ = lean_int8_mul(v_a_boxed_1987_, v_b_boxed_1988_);
    v_r_1990_ = lean_box((v_res_1989_) as usize);
    return v_r_1990_;
}
pub unsafe fn l_Int8_div___boxed(
    mut v_a_1993_: *mut LeanObject,
    mut v_b_1994_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_1995_: u8 = 0;
    let mut v_b_boxed_1996_: u8 = 0;
    let mut v_res_1997_: u8 = 0;
    let mut v_r_1998_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_1995_ = (lean_unbox(v_a_1993_) as u8);
    v_b_boxed_1996_ = (lean_unbox(v_b_1994_) as u8);
    v_res_1997_ = lean_int8_div(v_a_boxed_1995_, v_b_boxed_1996_);
    v_r_1998_ = lean_box((v_res_1997_) as usize);
    return v_r_1998_;
}
pub unsafe fn _init_l_Int8_pow___closed__0() -> u8 {
    let mut v___x_1999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2000_: u8 = 0;
    v___x_1999_ = lean_unsigned_to_nat(1);
    v___x_2000_ = lean_int8_of_nat(v___x_1999_);
    return v___x_2000_;
}
pub unsafe fn l_Int8_pow(mut v_x_2001_: u8, mut v_n_2002_: *mut LeanObject) -> u8 {
    let mut v_zero_2003_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_2004_: u8 = 0;
    v_zero_2003_ = lean_unsigned_to_nat(0);
    v_isZero_2004_ = lean_nat_dec_eq(v_n_2002_, v_zero_2003_);
    if v_isZero_2004_ == 1 {
        let mut v___x_2005_: u8 = 0;
        v___x_2005_ = lean_uint8_once(
            core::ptr::addr_of_mut!(l_Int8_pow___closed__0),
            core::ptr::addr_of_mut!(l_Int8_pow___closed__0_once),
            _init_l_Int8_pow___closed__0,
        );
        return v___x_2005_;
    } else {
        let mut v_one_2006_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_2007_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2008_: u8 = 0;
        let mut v___x_2009_: u8 = 0;
        v_one_2006_ = lean_unsigned_to_nat(1);
        v_n_2007_ = lean_nat_sub(v_n_2002_, v_one_2006_);
        v___x_2008_ = l_Int8_pow(v_x_2001_, v_n_2007_);
        lean_dec(v_n_2007_);
        v___x_2009_ = lean_int8_mul(v___x_2008_, v_x_2001_);
        return v___x_2009_;
    }
}
pub unsafe fn l_Int8_pow___boxed(
    mut v_x_2010_: *mut LeanObject,
    mut v_n_2011_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_boxed_2012_: u8 = 0;
    let mut v_res_2013_: u8 = 0;
    let mut v_r_2014_: *mut LeanObject = core::ptr::null_mut();
    v_x_boxed_2012_ = (lean_unbox(v_x_2010_) as u8);
    v_res_2013_ = l_Int8_pow(v_x_boxed_2012_, v_n_2011_);
    lean_dec(v_n_2011_);
    v_r_2014_ = lean_box((v_res_2013_) as usize);
    return v_r_2014_;
}
pub unsafe fn l_Int8_mod___boxed(
    mut v_a_2017_: *mut LeanObject,
    mut v_b_2018_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_2019_: u8 = 0;
    let mut v_b_boxed_2020_: u8 = 0;
    let mut v_res_2021_: u8 = 0;
    let mut v_r_2022_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_2019_ = (lean_unbox(v_a_2017_) as u8);
    v_b_boxed_2020_ = (lean_unbox(v_b_2018_) as u8);
    v_res_2021_ = lean_int8_mod(v_a_boxed_2019_, v_b_boxed_2020_);
    v_r_2022_ = lean_box((v_res_2021_) as usize);
    return v_r_2022_;
}
pub unsafe fn l_Int8_land___boxed(
    mut v_a_2025_: *mut LeanObject,
    mut v_b_2026_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_2027_: u8 = 0;
    let mut v_b_boxed_2028_: u8 = 0;
    let mut v_res_2029_: u8 = 0;
    let mut v_r_2030_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_2027_ = (lean_unbox(v_a_2025_) as u8);
    v_b_boxed_2028_ = (lean_unbox(v_b_2026_) as u8);
    v_res_2029_ = lean_int8_land(v_a_boxed_2027_, v_b_boxed_2028_);
    v_r_2030_ = lean_box((v_res_2029_) as usize);
    return v_r_2030_;
}
pub unsafe fn l_Int8_lor___boxed(
    mut v_a_2033_: *mut LeanObject,
    mut v_b_2034_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_2035_: u8 = 0;
    let mut v_b_boxed_2036_: u8 = 0;
    let mut v_res_2037_: u8 = 0;
    let mut v_r_2038_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_2035_ = (lean_unbox(v_a_2033_) as u8);
    v_b_boxed_2036_ = (lean_unbox(v_b_2034_) as u8);
    v_res_2037_ = lean_int8_lor(v_a_boxed_2035_, v_b_boxed_2036_);
    v_r_2038_ = lean_box((v_res_2037_) as usize);
    return v_r_2038_;
}
pub unsafe fn l_Int8_xor___boxed(
    mut v_a_2041_: *mut LeanObject,
    mut v_b_2042_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_2043_: u8 = 0;
    let mut v_b_boxed_2044_: u8 = 0;
    let mut v_res_2045_: u8 = 0;
    let mut v_r_2046_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_2043_ = (lean_unbox(v_a_2041_) as u8);
    v_b_boxed_2044_ = (lean_unbox(v_b_2042_) as u8);
    v_res_2045_ = lean_int8_xor(v_a_boxed_2043_, v_b_boxed_2044_);
    v_r_2046_ = lean_box((v_res_2045_) as usize);
    return v_r_2046_;
}
pub unsafe fn l_Int8_shiftLeft___boxed(
    mut v_a_2049_: *mut LeanObject,
    mut v_b_2050_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_2051_: u8 = 0;
    let mut v_b_boxed_2052_: u8 = 0;
    let mut v_res_2053_: u8 = 0;
    let mut v_r_2054_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_2051_ = (lean_unbox(v_a_2049_) as u8);
    v_b_boxed_2052_ = (lean_unbox(v_b_2050_) as u8);
    v_res_2053_ = lean_int8_shift_left(v_a_boxed_2051_, v_b_boxed_2052_);
    v_r_2054_ = lean_box((v_res_2053_) as usize);
    return v_r_2054_;
}
pub unsafe fn l_Int8_shiftRight___boxed(
    mut v_a_2057_: *mut LeanObject,
    mut v_b_2058_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_2059_: u8 = 0;
    let mut v_b_boxed_2060_: u8 = 0;
    let mut v_res_2061_: u8 = 0;
    let mut v_r_2062_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_2059_ = (lean_unbox(v_a_2057_) as u8);
    v_b_boxed_2060_ = (lean_unbox(v_b_2058_) as u8);
    v_res_2061_ = lean_int8_shift_right(v_a_boxed_2059_, v_b_boxed_2060_);
    v_r_2062_ = lean_box((v_res_2061_) as usize);
    return v_r_2062_;
}
pub unsafe fn l_Int8_complement___boxed(mut v_a_2064_: *mut LeanObject) -> *mut LeanObject {
    let mut v_a_boxed_2065_: u8 = 0;
    let mut v_res_2066_: u8 = 0;
    let mut v_r_2067_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_2065_ = (lean_unbox(v_a_2064_) as u8);
    v_res_2066_ = lean_int8_complement(v_a_boxed_2065_);
    v_r_2067_ = lean_box((v_res_2066_) as usize);
    return v_r_2067_;
}
pub unsafe fn l_Int8_abs___boxed(mut v_a_2069_: *mut LeanObject) -> *mut LeanObject {
    let mut v_a_boxed_2070_: u8 = 0;
    let mut v_res_2071_: u8 = 0;
    let mut v_r_2072_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_2070_ = (lean_unbox(v_a_2069_) as u8);
    v_res_2071_ = lean_int8_abs(v_a_boxed_2070_);
    v_r_2072_ = lean_box((v_res_2071_) as usize);
    return v_r_2072_;
}
pub unsafe fn l_Int8_decEq___boxed(
    mut v_a_2075_: *mut LeanObject,
    mut v_b_2076_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_2077_: u8 = 0;
    let mut v_b_boxed_2078_: u8 = 0;
    let mut v_res_2079_: u8 = 0;
    let mut v_r_2080_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_2077_ = (lean_unbox(v_a_2075_) as u8);
    v_b_boxed_2078_ = (lean_unbox(v_b_2076_) as u8);
    v_res_2079_ = lean_int8_dec_eq(v_a_boxed_2077_, v_b_boxed_2078_);
    v_r_2080_ = lean_box((v_res_2079_) as usize);
    return v_r_2080_;
}
pub unsafe fn _init_l_instInhabitedInt8___closed__0() -> u8 {
    let mut v___x_2081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2082_: u8 = 0;
    v___x_2081_ = lean_unsigned_to_nat(0);
    v___x_2082_ = lean_int8_of_nat(v___x_2081_);
    return v___x_2082_;
}
pub unsafe fn _init_l_instInhabitedInt8() -> u8 {
    let mut v___x_2083_: u8 = 0;
    v___x_2083_ = lean_uint8_once(
        core::ptr::addr_of_mut!(l_instInhabitedInt8___closed__0),
        core::ptr::addr_of_mut!(l_instInhabitedInt8___closed__0_once),
        _init_l_instInhabitedInt8___closed__0,
    );
    return v___x_2083_;
}
pub unsafe fn _init_l_instLTInt8() -> *mut LeanObject {
    let mut v___x_2096_: *mut LeanObject = core::ptr::null_mut();
    v___x_2096_ = lean_box(0);
    return v___x_2096_;
}
pub unsafe fn _init_l_instLEInt8() -> *mut LeanObject {
    let mut v___x_2097_: *mut LeanObject = core::ptr::null_mut();
    v___x_2097_ = lean_box(0);
    return v___x_2097_;
}
pub unsafe fn l_instDecidableEqInt8(mut v_a_2110_: u8, mut v_b_2111_: u8) -> u8 {
    let mut v___x_2112_: u8 = 0;
    v___x_2112_ = lean_int8_dec_eq(v_a_2110_, v_b_2111_);
    return v___x_2112_;
}
pub unsafe fn l_instDecidableEqInt8___boxed(
    mut v_a_2113_: *mut LeanObject,
    mut v_b_2114_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_2115_: u8 = 0;
    let mut v_b_boxed_2116_: u8 = 0;
    let mut v_res_2117_: u8 = 0;
    let mut v_r_2118_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_2115_ = (lean_unbox(v_a_2113_) as u8);
    v_b_boxed_2116_ = (lean_unbox(v_b_2114_) as u8);
    v_res_2117_ = l_instDecidableEqInt8(v_a_boxed_2115_, v_b_boxed_2116_);
    v_r_2118_ = lean_box((v_res_2117_) as usize);
    return v_r_2118_;
}
pub unsafe fn l_Bool_toInt8___boxed(mut v_b_2120_: *mut LeanObject) -> *mut LeanObject {
    let mut v_b_boxed_2121_: u8 = 0;
    let mut v_res_2122_: u8 = 0;
    let mut v_r_2123_: *mut LeanObject = core::ptr::null_mut();
    v_b_boxed_2121_ = (lean_unbox(v_b_2120_) as u8);
    v_res_2122_ = lean_bool_to_int8(v_b_boxed_2121_);
    v_r_2123_ = lean_box((v_res_2122_) as usize);
    return v_r_2123_;
}
pub unsafe fn l_Int8_decLt___aux__1(mut v_a_2124_: u8, mut v_b_2125_: u8) -> u8 {
    let mut v___x_2126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2129_: u8 = 0;
    v___x_2126_ = lean_unsigned_to_nat(8);
    v___x_2127_ = lean_uint8_to_nat(v_a_2124_);
    v___x_2128_ = lean_uint8_to_nat(v_b_2125_);
    v___x_2129_ = l_BitVec_slt(v___x_2126_, v___x_2127_, v___x_2128_);
    return v___x_2129_;
}
pub unsafe fn l_Int8_decLt___aux__1___boxed(
    mut v_a_2130_: *mut LeanObject,
    mut v_b_2131_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_2132_: u8 = 0;
    let mut v_b_boxed_2133_: u8 = 0;
    let mut v_res_2134_: u8 = 0;
    let mut v_r_2135_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_2132_ = (lean_unbox(v_a_2130_) as u8);
    v_b_boxed_2133_ = (lean_unbox(v_b_2131_) as u8);
    v_res_2134_ = l_Int8_decLt___aux__1(v_a_boxed_2132_, v_b_boxed_2133_);
    v_r_2135_ = lean_box((v_res_2134_) as usize);
    return v_r_2135_;
}
pub unsafe fn l_Int8_decLt___boxed(
    mut v_a_2138_: *mut LeanObject,
    mut v_b_2139_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_2140_: u8 = 0;
    let mut v_b_boxed_2141_: u8 = 0;
    let mut v_res_2142_: u8 = 0;
    let mut v_r_2143_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_2140_ = (lean_unbox(v_a_2138_) as u8);
    v_b_boxed_2141_ = (lean_unbox(v_b_2139_) as u8);
    v_res_2142_ = lean_int8_dec_lt(v_a_boxed_2140_, v_b_boxed_2141_);
    v_r_2143_ = lean_box((v_res_2142_) as usize);
    return v_r_2143_;
}
pub unsafe fn l_Int8_decLe___aux__1(mut v_a_2144_: u8, mut v_b_2145_: u8) -> u8 {
    let mut v___x_2146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2149_: u8 = 0;
    v___x_2146_ = lean_unsigned_to_nat(8);
    v___x_2147_ = lean_uint8_to_nat(v_a_2144_);
    v___x_2148_ = lean_uint8_to_nat(v_b_2145_);
    v___x_2149_ = l_BitVec_sle(v___x_2146_, v___x_2147_, v___x_2148_);
    return v___x_2149_;
}
pub unsafe fn l_Int8_decLe___aux__1___boxed(
    mut v_a_2150_: *mut LeanObject,
    mut v_b_2151_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_2152_: u8 = 0;
    let mut v_b_boxed_2153_: u8 = 0;
    let mut v_res_2154_: u8 = 0;
    let mut v_r_2155_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_2152_ = (lean_unbox(v_a_2150_) as u8);
    v_b_boxed_2153_ = (lean_unbox(v_b_2151_) as u8);
    v_res_2154_ = l_Int8_decLe___aux__1(v_a_boxed_2152_, v_b_boxed_2153_);
    v_r_2155_ = lean_box((v_res_2154_) as usize);
    return v_r_2155_;
}
pub unsafe fn l_Int8_decLe___boxed(
    mut v_a_2158_: *mut LeanObject,
    mut v_b_2159_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_2160_: u8 = 0;
    let mut v_b_boxed_2161_: u8 = 0;
    let mut v_res_2162_: u8 = 0;
    let mut v_r_2163_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_2160_ = (lean_unbox(v_a_2158_) as u8);
    v_b_boxed_2161_ = (lean_unbox(v_b_2159_) as u8);
    v_res_2162_ = lean_int8_dec_le(v_a_boxed_2160_, v_b_boxed_2161_);
    v_r_2163_ = lean_box((v_res_2162_) as usize);
    return v_r_2163_;
}
pub unsafe fn l_instMaxInt8___lam__0(mut v_x_2164_: u8, mut v_y_2165_: u8) -> u8 {
    let mut v___x_2166_: u8 = 0;
    v___x_2166_ = lean_int8_dec_le(v_x_2164_, v_y_2165_);
    if v___x_2166_ == 0 {
        return v_x_2164_;
    } else {
        return v_y_2165_;
    }
}
pub unsafe fn l_instMaxInt8___lam__0___boxed(
    mut v_x_2167_: *mut LeanObject,
    mut v_y_2168_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_boxed_2169_: u8 = 0;
    let mut v_y_boxed_2170_: u8 = 0;
    let mut v_res_2171_: u8 = 0;
    let mut v_r_2172_: *mut LeanObject = core::ptr::null_mut();
    v_x_boxed_2169_ = (lean_unbox(v_x_2167_) as u8);
    v_y_boxed_2170_ = (lean_unbox(v_y_2168_) as u8);
    v_res_2171_ = l_instMaxInt8___lam__0(v_x_boxed_2169_, v_y_boxed_2170_);
    v_r_2172_ = lean_box((v_res_2171_) as usize);
    return v_r_2172_;
}
pub unsafe fn l_instMinInt8___lam__0(mut v_x_2175_: u8, mut v_y_2176_: u8) -> u8 {
    let mut v___x_2177_: u8 = 0;
    v___x_2177_ = lean_int8_dec_le(v_x_2175_, v_y_2176_);
    if v___x_2177_ == 0 {
        return v_y_2176_;
    } else {
        return v_x_2175_;
    }
}
pub unsafe fn l_instMinInt8___lam__0___boxed(
    mut v_x_2178_: *mut LeanObject,
    mut v_y_2179_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_boxed_2180_: u8 = 0;
    let mut v_y_boxed_2181_: u8 = 0;
    let mut v_res_2182_: u8 = 0;
    let mut v_r_2183_: *mut LeanObject = core::ptr::null_mut();
    v_x_boxed_2180_ = (lean_unbox(v_x_2178_) as u8);
    v_y_boxed_2181_ = (lean_unbox(v_y_2179_) as u8);
    v_res_2182_ = l_instMinInt8___lam__0(v_x_boxed_2180_, v_y_boxed_2181_);
    v_r_2183_ = lean_box((v_res_2182_) as usize);
    return v_r_2183_;
}
pub unsafe fn _init_l_Int16_size() -> *mut LeanObject {
    let mut v___x_2186_: *mut LeanObject = core::ptr::null_mut();
    v___x_2186_ = lean_unsigned_to_nat(65536);
    return v___x_2186_;
}
pub unsafe fn l_Int16_toBitVec(mut v_x_2187_: u16) -> *mut LeanObject {
    let mut v___x_2188_: *mut LeanObject = core::ptr::null_mut();
    v___x_2188_ = lean_uint16_to_nat(v_x_2187_);
    return v___x_2188_;
}
pub unsafe fn l_Int16_toBitVec___boxed(mut v_x_2189_: *mut LeanObject) -> *mut LeanObject {
    let mut v_x_boxed_2190_: u16 = 0;
    let mut v_res_2191_: *mut LeanObject = core::ptr::null_mut();
    v_x_boxed_2190_ = (lean_unbox(v_x_2189_) as u16);
    v_res_2191_ = l_Int16_toBitVec(v_x_boxed_2190_);
    return v_res_2191_;
}
pub unsafe fn l_UInt16_toInt16(mut v_i_2192_: u16) -> u16 {
    return v_i_2192_;
}
pub unsafe fn l_UInt16_toInt16___boxed(mut v_i_2193_: *mut LeanObject) -> *mut LeanObject {
    let mut v_i_boxed_2194_: u16 = 0;
    let mut v_res_2195_: u16 = 0;
    let mut v_r_2196_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_2194_ = (lean_unbox(v_i_2193_) as u16);
    v_res_2195_ = l_UInt16_toInt16(v_i_boxed_2194_);
    v_r_2196_ = lean_box((v_res_2195_) as usize);
    return v_r_2196_;
}
pub unsafe fn l_Int16_ofInt___boxed(mut v_i_2198_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_2199_: u16 = 0;
    let mut v_r_2200_: *mut LeanObject = core::ptr::null_mut();
    v_res_2199_ = lean_int16_of_int(v_i_2198_);
    lean_dec(v_i_2198_);
    v_r_2200_ = lean_box((v_res_2199_) as usize);
    return v_r_2200_;
}
pub unsafe fn l_Int16_ofNat___boxed(mut v_n_2202_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_2203_: u16 = 0;
    let mut v_r_2204_: *mut LeanObject = core::ptr::null_mut();
    v_res_2203_ = lean_int16_of_nat(v_n_2202_);
    lean_dec(v_n_2202_);
    v_r_2204_ = lean_box((v_res_2203_) as usize);
    return v_r_2204_;
}
pub unsafe fn l_Int_toInt16(mut v_i_2205_: *mut LeanObject) -> u16 {
    let mut v___x_2206_: u16 = 0;
    v___x_2206_ = lean_int16_of_int(v_i_2205_);
    return v___x_2206_;
}
pub unsafe fn l_Int_toInt16___boxed(mut v_i_2207_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_2208_: u16 = 0;
    let mut v_r_2209_: *mut LeanObject = core::ptr::null_mut();
    v_res_2208_ = l_Int_toInt16(v_i_2207_);
    lean_dec(v_i_2207_);
    v_r_2209_ = lean_box((v_res_2208_) as usize);
    return v_r_2209_;
}
pub unsafe fn l_Nat_toInt16(mut v_n_2210_: *mut LeanObject) -> u16 {
    let mut v___x_2211_: u16 = 0;
    v___x_2211_ = lean_int16_of_nat(v_n_2210_);
    return v___x_2211_;
}
pub unsafe fn l_Nat_toInt16___boxed(mut v_n_2212_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_2213_: u16 = 0;
    let mut v_r_2214_: *mut LeanObject = core::ptr::null_mut();
    v_res_2213_ = l_Nat_toInt16(v_n_2212_);
    lean_dec(v_n_2212_);
    v_r_2214_ = lean_box((v_res_2213_) as usize);
    return v_r_2214_;
}
pub unsafe fn l_Int16_toInt___boxed(mut v_i_2216_: *mut LeanObject) -> *mut LeanObject {
    let mut v_i_boxed_2217_: u16 = 0;
    let mut v_res_2218_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_2217_ = (lean_unbox(v_i_2216_) as u16);
    v_res_2218_ = lean_int16_to_int(v_i_boxed_2217_);
    return v_res_2218_;
}
pub unsafe fn l_Int16_toNatClampNeg(mut v_i_2219_: u16) -> *mut LeanObject {
    let mut v___x_2220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2221_: *mut LeanObject = core::ptr::null_mut();
    v___x_2220_ = lean_int16_to_int(v_i_2219_);
    v___x_2221_ = l_Int_toNat(v___x_2220_);
    return v___x_2221_;
}
pub unsafe fn l_Int16_toNatClampNeg___boxed(mut v_i_2222_: *mut LeanObject) -> *mut LeanObject {
    let mut v_i_boxed_2223_: u16 = 0;
    let mut v_res_2224_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_2223_ = (lean_unbox(v_i_2222_) as u16);
    v_res_2224_ = l_Int16_toNatClampNeg(v_i_boxed_2223_);
    return v_res_2224_;
}
pub unsafe fn l_Int16_ofBitVec(mut v_b_2225_: *mut LeanObject) -> u16 {
    let mut v___x_2226_: u16 = 0;
    v___x_2226_ = lean_uint16_of_nat_mk(v_b_2225_);
    return v___x_2226_;
}
pub unsafe fn l_Int16_ofBitVec___boxed(mut v_b_2227_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_2228_: u16 = 0;
    let mut v_r_2229_: *mut LeanObject = core::ptr::null_mut();
    v_res_2228_ = l_Int16_ofBitVec(v_b_2227_);
    v_r_2229_ = lean_box((v_res_2228_) as usize);
    return v_r_2229_;
}
pub unsafe fn l_Int16_toInt8___boxed(mut v_a_2231_: *mut LeanObject) -> *mut LeanObject {
    let mut v_a_boxed_2232_: u16 = 0;
    let mut v_res_2233_: u8 = 0;
    let mut v_r_2234_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_2232_ = (lean_unbox(v_a_2231_) as u16);
    v_res_2233_ = lean_int16_to_int8(v_a_boxed_2232_);
    v_r_2234_ = lean_box((v_res_2233_) as usize);
    return v_r_2234_;
}
pub unsafe fn l_Int8_toInt16___boxed(mut v_a_2236_: *mut LeanObject) -> *mut LeanObject {
    let mut v_a_boxed_2237_: u8 = 0;
    let mut v_res_2238_: u16 = 0;
    let mut v_r_2239_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_2237_ = (lean_unbox(v_a_2236_) as u8);
    v_res_2238_ = lean_int8_to_int16(v_a_boxed_2237_);
    v_r_2239_ = lean_box((v_res_2238_) as usize);
    return v_r_2239_;
}
pub unsafe fn l_Int16_neg___boxed(mut v_i_2241_: *mut LeanObject) -> *mut LeanObject {
    let mut v_i_boxed_2242_: u16 = 0;
    let mut v_res_2243_: u16 = 0;
    let mut v_r_2244_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_2242_ = (lean_unbox(v_i_2241_) as u16);
    v_res_2243_ = lean_int16_neg(v_i_boxed_2242_);
    v_r_2244_ = lean_box((v_res_2243_) as usize);
    return v_r_2244_;
}
pub unsafe fn l_instToStringInt16___lam__0(mut v_i_2245_: u16) -> *mut LeanObject {
    let mut v___x_2246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2247_: *mut LeanObject = core::ptr::null_mut();
    v___x_2246_ = lean_int16_to_int(v_i_2245_);
    v___x_2247_ = l_Int_repr(v___x_2246_);
    return v___x_2247_;
}
pub unsafe fn l_instToStringInt16___lam__0___boxed(
    mut v_i_2248_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_2249_: u16 = 0;
    let mut v_res_2250_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_2249_ = (lean_unbox(v_i_2248_) as u16);
    v_res_2250_ = l_instToStringInt16___lam__0(v_i_boxed_2249_);
    return v_res_2250_;
}
pub unsafe fn l_instReprInt16___lam__0(
    mut v_i_2253_: u16,
    mut v_prec_2254_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2257_: u8 = 0;
    v___x_2255_ = lean_int16_to_int(v_i_2253_);
    v___x_2256_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_instReprInt8___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_instReprInt8___lam__0___closed__0_once),
        _init_l_instReprInt8___lam__0___closed__0,
    );
    v___x_2257_ = lean_int_dec_lt(v___x_2255_, v___x_2256_);
    if v___x_2257_ == 0 {
        let mut v___x_2258_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2259_: *mut LeanObject = core::ptr::null_mut();
        v___x_2258_ = l_Int_repr(v___x_2255_);
        v___x_2259_ = lean_alloc_ctor(3, 1, (0) as u32);
        lean_ctor_set(v___x_2259_, 0, v___x_2258_);
        return v___x_2259_;
    } else {
        let mut v___x_2260_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2261_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2262_: *mut LeanObject = core::ptr::null_mut();
        v___x_2260_ = l_Int_repr(v___x_2255_);
        v___x_2261_ = lean_alloc_ctor(3, 1, (0) as u32);
        lean_ctor_set(v___x_2261_, 0, v___x_2260_);
        v___x_2262_ = l_Repr_addAppParen(v___x_2261_, v_prec_2254_);
        return v___x_2262_;
    }
}
pub unsafe fn l_instReprInt16___lam__0___boxed(
    mut v_i_2263_: *mut LeanObject,
    mut v_prec_2264_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_2265_: u16 = 0;
    let mut v_res_2266_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_2265_ = (lean_unbox(v_i_2263_) as u16);
    v_res_2266_ = l_instReprInt16___lam__0(v_i_boxed_2265_, v_prec_2264_);
    lean_dec(v_prec_2264_);
    return v_res_2266_;
}
pub unsafe fn _init_l_instReprAtomInt16() -> *mut LeanObject {
    let mut v___x_2269_: *mut LeanObject = core::ptr::null_mut();
    v___x_2269_ = lean_box(0);
    return v___x_2269_;
}
pub unsafe fn l_Int16_instOfNat(mut v_n_2272_: *mut LeanObject) -> u16 {
    let mut v___x_2273_: u16 = 0;
    v___x_2273_ = lean_int16_of_nat(v_n_2272_);
    return v___x_2273_;
}
pub unsafe fn l_Int16_instOfNat___boxed(mut v_n_2274_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_2275_: u16 = 0;
    let mut v_r_2276_: *mut LeanObject = core::ptr::null_mut();
    v_res_2275_ = l_Int16_instOfNat(v_n_2274_);
    lean_dec(v_n_2274_);
    v_r_2276_ = lean_box((v_res_2275_) as usize);
    return v_r_2276_;
}
pub unsafe fn _init_l_Int16_maxValue___closed__0() -> u16 {
    let mut v___x_2279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2280_: u16 = 0;
    v___x_2279_ = lean_unsigned_to_nat(32767);
    v___x_2280_ = lean_int16_of_nat(v___x_2279_);
    return v___x_2280_;
}
pub unsafe fn _init_l_Int16_maxValue() -> u16 {
    let mut v___x_2281_: u16 = 0;
    v___x_2281_ = lean_uint16_once(
        core::ptr::addr_of_mut!(l_Int16_maxValue___closed__0),
        core::ptr::addr_of_mut!(l_Int16_maxValue___closed__0_once),
        _init_l_Int16_maxValue___closed__0,
    );
    return v___x_2281_;
}
pub unsafe fn _init_l_Int16_minValue___closed__0() -> u16 {
    let mut v___x_2282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2283_: u16 = 0;
    v___x_2282_ = lean_unsigned_to_nat(32768);
    v___x_2283_ = lean_int16_of_nat(v___x_2282_);
    return v___x_2283_;
}
pub unsafe fn _init_l_Int16_minValue___closed__1() -> u16 {
    let mut v___x_2284_: u16 = 0;
    let mut v___x_2285_: u16 = 0;
    v___x_2284_ = lean_uint16_once(
        core::ptr::addr_of_mut!(l_Int16_minValue___closed__0),
        core::ptr::addr_of_mut!(l_Int16_minValue___closed__0_once),
        _init_l_Int16_minValue___closed__0,
    );
    v___x_2285_ = lean_int16_neg(v___x_2284_);
    return v___x_2285_;
}
pub unsafe fn _init_l_Int16_minValue() -> u16 {
    let mut v___x_2286_: u16 = 0;
    v___x_2286_ = lean_uint16_once(
        core::ptr::addr_of_mut!(l_Int16_minValue___closed__1),
        core::ptr::addr_of_mut!(l_Int16_minValue___closed__1_once),
        _init_l_Int16_minValue___closed__1,
    );
    return v___x_2286_;
}
pub unsafe fn l_Int16_ofIntLE___redArg(mut v_i_2287_: *mut LeanObject) -> u16 {
    let mut v___x_2288_: u16 = 0;
    v___x_2288_ = lean_int16_of_int(v_i_2287_);
    return v___x_2288_;
}
pub unsafe fn l_Int16_ofIntLE___redArg___boxed(mut v_i_2289_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_2290_: u16 = 0;
    let mut v_r_2291_: *mut LeanObject = core::ptr::null_mut();
    v_res_2290_ = l_Int16_ofIntLE___redArg(v_i_2289_);
    lean_dec(v_i_2289_);
    v_r_2291_ = lean_box((v_res_2290_) as usize);
    return v_r_2291_;
}
pub unsafe fn l_Int16_ofIntLE(
    mut v_i_2292_: *mut LeanObject,
    mut v___hl_2293_: *mut LeanObject,
    mut v___hr_2294_: *mut LeanObject,
) -> u16 {
    let mut v___x_2295_: u16 = 0;
    v___x_2295_ = lean_int16_of_int(v_i_2292_);
    return v___x_2295_;
}
pub unsafe fn l_Int16_ofIntLE___boxed(
    mut v_i_2296_: *mut LeanObject,
    mut v___hl_2297_: *mut LeanObject,
    mut v___hr_2298_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2299_: u16 = 0;
    let mut v_r_2300_: *mut LeanObject = core::ptr::null_mut();
    v_res_2299_ = l_Int16_ofIntLE(v_i_2296_, v___hl_2297_, v___hr_2298_);
    lean_dec(v_i_2296_);
    v_r_2300_ = lean_box((v_res_2299_) as usize);
    return v_r_2300_;
}
pub unsafe fn _init_l_Int16_ofIntClamp___closed__0() -> *mut LeanObject {
    let mut v___x_2301_: u16 = 0;
    let mut v___x_2302_: *mut LeanObject = core::ptr::null_mut();
    v___x_2301_ = lean_uint16_once(
        core::ptr::addr_of_mut!(l_Int16_minValue___closed__1),
        core::ptr::addr_of_mut!(l_Int16_minValue___closed__1_once),
        _init_l_Int16_minValue___closed__1,
    );
    v___x_2302_ = lean_int16_to_int(v___x_2301_);
    return v___x_2302_;
}
pub unsafe fn _init_l_Int16_ofIntClamp___closed__1() -> *mut LeanObject {
    let mut v___x_2303_: u16 = 0;
    let mut v___x_2304_: *mut LeanObject = core::ptr::null_mut();
    v___x_2303_ = lean_uint16_once(
        core::ptr::addr_of_mut!(l_Int16_maxValue___closed__0),
        core::ptr::addr_of_mut!(l_Int16_maxValue___closed__0_once),
        _init_l_Int16_maxValue___closed__0,
    );
    v___x_2304_ = lean_int16_to_int(v___x_2303_);
    return v___x_2304_;
}
pub unsafe fn l_Int16_ofIntClamp(mut v_i_2305_: *mut LeanObject) -> u16 {
    let mut v___x_2306_: u16 = 0;
    let mut v___x_2307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2308_: u8 = 0;
    v___x_2306_ = lean_uint16_once(
        core::ptr::addr_of_mut!(l_Int16_minValue___closed__1),
        core::ptr::addr_of_mut!(l_Int16_minValue___closed__1_once),
        _init_l_Int16_minValue___closed__1,
    );
    v___x_2307_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Int16_ofIntClamp___closed__0),
        core::ptr::addr_of_mut!(l_Int16_ofIntClamp___closed__0_once),
        _init_l_Int16_ofIntClamp___closed__0,
    );
    v___x_2308_ = lean_int_dec_le(v___x_2307_, v_i_2305_);
    if v___x_2308_ == 0 {
        return v___x_2306_;
    } else {
        let mut v___x_2309_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2310_: u8 = 0;
        v___x_2309_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Int16_ofIntClamp___closed__1),
            core::ptr::addr_of_mut!(l_Int16_ofIntClamp___closed__1_once),
            _init_l_Int16_ofIntClamp___closed__1,
        );
        v___x_2310_ = lean_int_dec_le(v_i_2305_, v___x_2309_);
        if v___x_2310_ == 0 {
            return v___x_2306_;
        } else {
            let mut v___x_2311_: u16 = 0;
            v___x_2311_ = lean_int16_of_int(v_i_2305_);
            return v___x_2311_;
        }
    }
}
pub unsafe fn l_Int16_ofIntClamp___boxed(mut v_i_2312_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_2313_: u16 = 0;
    let mut v_r_2314_: *mut LeanObject = core::ptr::null_mut();
    v_res_2313_ = l_Int16_ofIntClamp(v_i_2312_);
    lean_dec(v_i_2312_);
    v_r_2314_ = lean_box((v_res_2313_) as usize);
    return v_r_2314_;
}
pub unsafe fn l_Int16_ofIntTruncate(mut v_i_2315_: *mut LeanObject) -> u16 {
    let mut v___x_2316_: u16 = 0;
    v___x_2316_ = l_Int16_ofIntClamp(v_i_2315_);
    return v___x_2316_;
}
pub unsafe fn l_Int16_ofIntTruncate___boxed(mut v_i_2317_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_2318_: u16 = 0;
    let mut v_r_2319_: *mut LeanObject = core::ptr::null_mut();
    v_res_2318_ = l_Int16_ofIntTruncate(v_i_2317_);
    lean_dec(v_i_2317_);
    v_r_2319_ = lean_box((v_res_2318_) as usize);
    return v_r_2319_;
}
pub unsafe fn l_Int16_add___boxed(
    mut v_a_2322_: *mut LeanObject,
    mut v_b_2323_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_2324_: u16 = 0;
    let mut v_b_boxed_2325_: u16 = 0;
    let mut v_res_2326_: u16 = 0;
    let mut v_r_2327_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_2324_ = (lean_unbox(v_a_2322_) as u16);
    v_b_boxed_2325_ = (lean_unbox(v_b_2323_) as u16);
    v_res_2326_ = lean_int16_add(v_a_boxed_2324_, v_b_boxed_2325_);
    v_r_2327_ = lean_box((v_res_2326_) as usize);
    return v_r_2327_;
}
pub unsafe fn l_Int16_sub___boxed(
    mut v_a_2330_: *mut LeanObject,
    mut v_b_2331_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_2332_: u16 = 0;
    let mut v_b_boxed_2333_: u16 = 0;
    let mut v_res_2334_: u16 = 0;
    let mut v_r_2335_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_2332_ = (lean_unbox(v_a_2330_) as u16);
    v_b_boxed_2333_ = (lean_unbox(v_b_2331_) as u16);
    v_res_2334_ = lean_int16_sub(v_a_boxed_2332_, v_b_boxed_2333_);
    v_r_2335_ = lean_box((v_res_2334_) as usize);
    return v_r_2335_;
}
pub unsafe fn l_Int16_mul___boxed(
    mut v_a_2338_: *mut LeanObject,
    mut v_b_2339_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_2340_: u16 = 0;
    let mut v_b_boxed_2341_: u16 = 0;
    let mut v_res_2342_: u16 = 0;
    let mut v_r_2343_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_2340_ = (lean_unbox(v_a_2338_) as u16);
    v_b_boxed_2341_ = (lean_unbox(v_b_2339_) as u16);
    v_res_2342_ = lean_int16_mul(v_a_boxed_2340_, v_b_boxed_2341_);
    v_r_2343_ = lean_box((v_res_2342_) as usize);
    return v_r_2343_;
}
pub unsafe fn l_Int16_div___boxed(
    mut v_a_2346_: *mut LeanObject,
    mut v_b_2347_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_2348_: u16 = 0;
    let mut v_b_boxed_2349_: u16 = 0;
    let mut v_res_2350_: u16 = 0;
    let mut v_r_2351_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_2348_ = (lean_unbox(v_a_2346_) as u16);
    v_b_boxed_2349_ = (lean_unbox(v_b_2347_) as u16);
    v_res_2350_ = lean_int16_div(v_a_boxed_2348_, v_b_boxed_2349_);
    v_r_2351_ = lean_box((v_res_2350_) as usize);
    return v_r_2351_;
}
pub unsafe fn _init_l_Int16_pow___closed__0() -> u16 {
    let mut v___x_2352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2353_: u16 = 0;
    v___x_2352_ = lean_unsigned_to_nat(1);
    v___x_2353_ = lean_int16_of_nat(v___x_2352_);
    return v___x_2353_;
}
pub unsafe fn l_Int16_pow(mut v_x_2354_: u16, mut v_n_2355_: *mut LeanObject) -> u16 {
    let mut v_zero_2356_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_2357_: u8 = 0;
    v_zero_2356_ = lean_unsigned_to_nat(0);
    v_isZero_2357_ = lean_nat_dec_eq(v_n_2355_, v_zero_2356_);
    if v_isZero_2357_ == 1 {
        let mut v___x_2358_: u16 = 0;
        v___x_2358_ = lean_uint16_once(
            core::ptr::addr_of_mut!(l_Int16_pow___closed__0),
            core::ptr::addr_of_mut!(l_Int16_pow___closed__0_once),
            _init_l_Int16_pow___closed__0,
        );
        return v___x_2358_;
    } else {
        let mut v_one_2359_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_2360_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2361_: u16 = 0;
        let mut v___x_2362_: u16 = 0;
        v_one_2359_ = lean_unsigned_to_nat(1);
        v_n_2360_ = lean_nat_sub(v_n_2355_, v_one_2359_);
        v___x_2361_ = l_Int16_pow(v_x_2354_, v_n_2360_);
        lean_dec(v_n_2360_);
        v___x_2362_ = lean_int16_mul(v___x_2361_, v_x_2354_);
        return v___x_2362_;
    }
}
pub unsafe fn l_Int16_pow___boxed(
    mut v_x_2363_: *mut LeanObject,
    mut v_n_2364_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_boxed_2365_: u16 = 0;
    let mut v_res_2366_: u16 = 0;
    let mut v_r_2367_: *mut LeanObject = core::ptr::null_mut();
    v_x_boxed_2365_ = (lean_unbox(v_x_2363_) as u16);
    v_res_2366_ = l_Int16_pow(v_x_boxed_2365_, v_n_2364_);
    lean_dec(v_n_2364_);
    v_r_2367_ = lean_box((v_res_2366_) as usize);
    return v_r_2367_;
}
pub unsafe fn l_Int16_mod___boxed(
    mut v_a_2370_: *mut LeanObject,
    mut v_b_2371_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_2372_: u16 = 0;
    let mut v_b_boxed_2373_: u16 = 0;
    let mut v_res_2374_: u16 = 0;
    let mut v_r_2375_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_2372_ = (lean_unbox(v_a_2370_) as u16);
    v_b_boxed_2373_ = (lean_unbox(v_b_2371_) as u16);
    v_res_2374_ = lean_int16_mod(v_a_boxed_2372_, v_b_boxed_2373_);
    v_r_2375_ = lean_box((v_res_2374_) as usize);
    return v_r_2375_;
}
pub unsafe fn l_Int16_land___boxed(
    mut v_a_2378_: *mut LeanObject,
    mut v_b_2379_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_2380_: u16 = 0;
    let mut v_b_boxed_2381_: u16 = 0;
    let mut v_res_2382_: u16 = 0;
    let mut v_r_2383_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_2380_ = (lean_unbox(v_a_2378_) as u16);
    v_b_boxed_2381_ = (lean_unbox(v_b_2379_) as u16);
    v_res_2382_ = lean_int16_land(v_a_boxed_2380_, v_b_boxed_2381_);
    v_r_2383_ = lean_box((v_res_2382_) as usize);
    return v_r_2383_;
}
pub unsafe fn l_Int16_lor___boxed(
    mut v_a_2386_: *mut LeanObject,
    mut v_b_2387_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_2388_: u16 = 0;
    let mut v_b_boxed_2389_: u16 = 0;
    let mut v_res_2390_: u16 = 0;
    let mut v_r_2391_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_2388_ = (lean_unbox(v_a_2386_) as u16);
    v_b_boxed_2389_ = (lean_unbox(v_b_2387_) as u16);
    v_res_2390_ = lean_int16_lor(v_a_boxed_2388_, v_b_boxed_2389_);
    v_r_2391_ = lean_box((v_res_2390_) as usize);
    return v_r_2391_;
}
pub unsafe fn l_Int16_xor___boxed(
    mut v_a_2394_: *mut LeanObject,
    mut v_b_2395_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_2396_: u16 = 0;
    let mut v_b_boxed_2397_: u16 = 0;
    let mut v_res_2398_: u16 = 0;
    let mut v_r_2399_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_2396_ = (lean_unbox(v_a_2394_) as u16);
    v_b_boxed_2397_ = (lean_unbox(v_b_2395_) as u16);
    v_res_2398_ = lean_int16_xor(v_a_boxed_2396_, v_b_boxed_2397_);
    v_r_2399_ = lean_box((v_res_2398_) as usize);
    return v_r_2399_;
}
pub unsafe fn l_Int16_shiftLeft___boxed(
    mut v_a_2402_: *mut LeanObject,
    mut v_b_2403_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_2404_: u16 = 0;
    let mut v_b_boxed_2405_: u16 = 0;
    let mut v_res_2406_: u16 = 0;
    let mut v_r_2407_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_2404_ = (lean_unbox(v_a_2402_) as u16);
    v_b_boxed_2405_ = (lean_unbox(v_b_2403_) as u16);
    v_res_2406_ = lean_int16_shift_left(v_a_boxed_2404_, v_b_boxed_2405_);
    v_r_2407_ = lean_box((v_res_2406_) as usize);
    return v_r_2407_;
}
pub unsafe fn l_Int16_shiftRight___boxed(
    mut v_a_2410_: *mut LeanObject,
    mut v_b_2411_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_2412_: u16 = 0;
    let mut v_b_boxed_2413_: u16 = 0;
    let mut v_res_2414_: u16 = 0;
    let mut v_r_2415_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_2412_ = (lean_unbox(v_a_2410_) as u16);
    v_b_boxed_2413_ = (lean_unbox(v_b_2411_) as u16);
    v_res_2414_ = lean_int16_shift_right(v_a_boxed_2412_, v_b_boxed_2413_);
    v_r_2415_ = lean_box((v_res_2414_) as usize);
    return v_r_2415_;
}
pub unsafe fn l_Int16_complement___boxed(mut v_a_2417_: *mut LeanObject) -> *mut LeanObject {
    let mut v_a_boxed_2418_: u16 = 0;
    let mut v_res_2419_: u16 = 0;
    let mut v_r_2420_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_2418_ = (lean_unbox(v_a_2417_) as u16);
    v_res_2419_ = lean_int16_complement(v_a_boxed_2418_);
    v_r_2420_ = lean_box((v_res_2419_) as usize);
    return v_r_2420_;
}
pub unsafe fn l_Int16_abs___boxed(mut v_a_2422_: *mut LeanObject) -> *mut LeanObject {
    let mut v_a_boxed_2423_: u16 = 0;
    let mut v_res_2424_: u16 = 0;
    let mut v_r_2425_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_2423_ = (lean_unbox(v_a_2422_) as u16);
    v_res_2424_ = lean_int16_abs(v_a_boxed_2423_);
    v_r_2425_ = lean_box((v_res_2424_) as usize);
    return v_r_2425_;
}
pub unsafe fn l_Int16_decEq___boxed(
    mut v_a_2428_: *mut LeanObject,
    mut v_b_2429_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_2430_: u16 = 0;
    let mut v_b_boxed_2431_: u16 = 0;
    let mut v_res_2432_: u8 = 0;
    let mut v_r_2433_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_2430_ = (lean_unbox(v_a_2428_) as u16);
    v_b_boxed_2431_ = (lean_unbox(v_b_2429_) as u16);
    v_res_2432_ = lean_int16_dec_eq(v_a_boxed_2430_, v_b_boxed_2431_);
    v_r_2433_ = lean_box((v_res_2432_) as usize);
    return v_r_2433_;
}
pub unsafe fn _init_l_instInhabitedInt16___closed__0() -> u16 {
    let mut v___x_2434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2435_: u16 = 0;
    v___x_2434_ = lean_unsigned_to_nat(0);
    v___x_2435_ = lean_int16_of_nat(v___x_2434_);
    return v___x_2435_;
}
pub unsafe fn _init_l_instInhabitedInt16() -> u16 {
    let mut v___x_2436_: u16 = 0;
    v___x_2436_ = lean_uint16_once(
        core::ptr::addr_of_mut!(l_instInhabitedInt16___closed__0),
        core::ptr::addr_of_mut!(l_instInhabitedInt16___closed__0_once),
        _init_l_instInhabitedInt16___closed__0,
    );
    return v___x_2436_;
}
pub unsafe fn _init_l_instLTInt16() -> *mut LeanObject {
    let mut v___x_2449_: *mut LeanObject = core::ptr::null_mut();
    v___x_2449_ = lean_box(0);
    return v___x_2449_;
}
pub unsafe fn _init_l_instLEInt16() -> *mut LeanObject {
    let mut v___x_2450_: *mut LeanObject = core::ptr::null_mut();
    v___x_2450_ = lean_box(0);
    return v___x_2450_;
}
pub unsafe fn l_instDecidableEqInt16(mut v_a_2463_: u16, mut v_b_2464_: u16) -> u8 {
    let mut v___x_2465_: u8 = 0;
    v___x_2465_ = lean_int16_dec_eq(v_a_2463_, v_b_2464_);
    return v___x_2465_;
}
pub unsafe fn l_instDecidableEqInt16___boxed(
    mut v_a_2466_: *mut LeanObject,
    mut v_b_2467_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_2468_: u16 = 0;
    let mut v_b_boxed_2469_: u16 = 0;
    let mut v_res_2470_: u8 = 0;
    let mut v_r_2471_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_2468_ = (lean_unbox(v_a_2466_) as u16);
    v_b_boxed_2469_ = (lean_unbox(v_b_2467_) as u16);
    v_res_2470_ = l_instDecidableEqInt16(v_a_boxed_2468_, v_b_boxed_2469_);
    v_r_2471_ = lean_box((v_res_2470_) as usize);
    return v_r_2471_;
}
pub unsafe fn l_Bool_toInt16___boxed(mut v_b_2473_: *mut LeanObject) -> *mut LeanObject {
    let mut v_b_boxed_2474_: u8 = 0;
    let mut v_res_2475_: u16 = 0;
    let mut v_r_2476_: *mut LeanObject = core::ptr::null_mut();
    v_b_boxed_2474_ = (lean_unbox(v_b_2473_) as u8);
    v_res_2475_ = lean_bool_to_int16(v_b_boxed_2474_);
    v_r_2476_ = lean_box((v_res_2475_) as usize);
    return v_r_2476_;
}
pub unsafe fn l_Int16_decLt___aux__1(mut v_a_2477_: u16, mut v_b_2478_: u16) -> u8 {
    let mut v___x_2479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2482_: u8 = 0;
    v___x_2479_ = lean_unsigned_to_nat(16);
    v___x_2480_ = lean_uint16_to_nat(v_a_2477_);
    v___x_2481_ = lean_uint16_to_nat(v_b_2478_);
    v___x_2482_ = l_BitVec_slt(v___x_2479_, v___x_2480_, v___x_2481_);
    return v___x_2482_;
}
pub unsafe fn l_Int16_decLt___aux__1___boxed(
    mut v_a_2483_: *mut LeanObject,
    mut v_b_2484_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_2485_: u16 = 0;
    let mut v_b_boxed_2486_: u16 = 0;
    let mut v_res_2487_: u8 = 0;
    let mut v_r_2488_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_2485_ = (lean_unbox(v_a_2483_) as u16);
    v_b_boxed_2486_ = (lean_unbox(v_b_2484_) as u16);
    v_res_2487_ = l_Int16_decLt___aux__1(v_a_boxed_2485_, v_b_boxed_2486_);
    v_r_2488_ = lean_box((v_res_2487_) as usize);
    return v_r_2488_;
}
pub unsafe fn l_Int16_decLt___boxed(
    mut v_a_2491_: *mut LeanObject,
    mut v_b_2492_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_2493_: u16 = 0;
    let mut v_b_boxed_2494_: u16 = 0;
    let mut v_res_2495_: u8 = 0;
    let mut v_r_2496_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_2493_ = (lean_unbox(v_a_2491_) as u16);
    v_b_boxed_2494_ = (lean_unbox(v_b_2492_) as u16);
    v_res_2495_ = lean_int16_dec_lt(v_a_boxed_2493_, v_b_boxed_2494_);
    v_r_2496_ = lean_box((v_res_2495_) as usize);
    return v_r_2496_;
}
pub unsafe fn l_Int16_decLe___aux__1(mut v_a_2497_: u16, mut v_b_2498_: u16) -> u8 {
    let mut v___x_2499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2502_: u8 = 0;
    v___x_2499_ = lean_unsigned_to_nat(16);
    v___x_2500_ = lean_uint16_to_nat(v_a_2497_);
    v___x_2501_ = lean_uint16_to_nat(v_b_2498_);
    v___x_2502_ = l_BitVec_sle(v___x_2499_, v___x_2500_, v___x_2501_);
    return v___x_2502_;
}
pub unsafe fn l_Int16_decLe___aux__1___boxed(
    mut v_a_2503_: *mut LeanObject,
    mut v_b_2504_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_2505_: u16 = 0;
    let mut v_b_boxed_2506_: u16 = 0;
    let mut v_res_2507_: u8 = 0;
    let mut v_r_2508_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_2505_ = (lean_unbox(v_a_2503_) as u16);
    v_b_boxed_2506_ = (lean_unbox(v_b_2504_) as u16);
    v_res_2507_ = l_Int16_decLe___aux__1(v_a_boxed_2505_, v_b_boxed_2506_);
    v_r_2508_ = lean_box((v_res_2507_) as usize);
    return v_r_2508_;
}
pub unsafe fn l_Int16_decLe___boxed(
    mut v_a_2511_: *mut LeanObject,
    mut v_b_2512_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_2513_: u16 = 0;
    let mut v_b_boxed_2514_: u16 = 0;
    let mut v_res_2515_: u8 = 0;
    let mut v_r_2516_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_2513_ = (lean_unbox(v_a_2511_) as u16);
    v_b_boxed_2514_ = (lean_unbox(v_b_2512_) as u16);
    v_res_2515_ = lean_int16_dec_le(v_a_boxed_2513_, v_b_boxed_2514_);
    v_r_2516_ = lean_box((v_res_2515_) as usize);
    return v_r_2516_;
}
pub unsafe fn l_instMaxInt16___lam__0(mut v_x_2517_: u16, mut v_y_2518_: u16) -> u16 {
    let mut v___x_2519_: u8 = 0;
    v___x_2519_ = lean_int16_dec_le(v_x_2517_, v_y_2518_);
    if v___x_2519_ == 0 {
        return v_x_2517_;
    } else {
        return v_y_2518_;
    }
}
pub unsafe fn l_instMaxInt16___lam__0___boxed(
    mut v_x_2520_: *mut LeanObject,
    mut v_y_2521_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_boxed_2522_: u16 = 0;
    let mut v_y_boxed_2523_: u16 = 0;
    let mut v_res_2524_: u16 = 0;
    let mut v_r_2525_: *mut LeanObject = core::ptr::null_mut();
    v_x_boxed_2522_ = (lean_unbox(v_x_2520_) as u16);
    v_y_boxed_2523_ = (lean_unbox(v_y_2521_) as u16);
    v_res_2524_ = l_instMaxInt16___lam__0(v_x_boxed_2522_, v_y_boxed_2523_);
    v_r_2525_ = lean_box((v_res_2524_) as usize);
    return v_r_2525_;
}
pub unsafe fn l_instMinInt16___lam__0(mut v_x_2528_: u16, mut v_y_2529_: u16) -> u16 {
    let mut v___x_2530_: u8 = 0;
    v___x_2530_ = lean_int16_dec_le(v_x_2528_, v_y_2529_);
    if v___x_2530_ == 0 {
        return v_y_2529_;
    } else {
        return v_x_2528_;
    }
}
pub unsafe fn l_instMinInt16___lam__0___boxed(
    mut v_x_2531_: *mut LeanObject,
    mut v_y_2532_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_boxed_2533_: u16 = 0;
    let mut v_y_boxed_2534_: u16 = 0;
    let mut v_res_2535_: u16 = 0;
    let mut v_r_2536_: *mut LeanObject = core::ptr::null_mut();
    v_x_boxed_2533_ = (lean_unbox(v_x_2531_) as u16);
    v_y_boxed_2534_ = (lean_unbox(v_y_2532_) as u16);
    v_res_2535_ = l_instMinInt16___lam__0(v_x_boxed_2533_, v_y_boxed_2534_);
    v_r_2536_ = lean_box((v_res_2535_) as usize);
    return v_r_2536_;
}
pub unsafe fn _init_l_Int32_size() -> *mut LeanObject {
    let mut v___x_2539_: *mut LeanObject = core::ptr::null_mut();
    v___x_2539_ = lean_cstr_to_nat(b"4294967296\0".as_ptr().cast());
    return v___x_2539_;
}
pub unsafe fn l_Int32_toBitVec(mut v_x_2540_: u32) -> *mut LeanObject {
    let mut v___x_2541_: *mut LeanObject = core::ptr::null_mut();
    v___x_2541_ = lean_uint32_to_nat(v_x_2540_);
    return v___x_2541_;
}
pub unsafe fn l_Int32_toBitVec___boxed(mut v_x_2542_: *mut LeanObject) -> *mut LeanObject {
    let mut v_x_boxed_2543_: u32 = 0;
    let mut v_res_2544_: *mut LeanObject = core::ptr::null_mut();
    v_x_boxed_2543_ = lean_unbox_uint32(v_x_2542_);
    lean_dec(v_x_2542_);
    v_res_2544_ = l_Int32_toBitVec(v_x_boxed_2543_);
    return v_res_2544_;
}
pub unsafe fn l_UInt32_toInt32(mut v_i_2545_: u32) -> u32 {
    return v_i_2545_;
}
pub unsafe fn l_UInt32_toInt32___boxed(mut v_i_2546_: *mut LeanObject) -> *mut LeanObject {
    let mut v_i_boxed_2547_: u32 = 0;
    let mut v_res_2548_: u32 = 0;
    let mut v_r_2549_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_2547_ = lean_unbox_uint32(v_i_2546_);
    lean_dec(v_i_2546_);
    v_res_2548_ = l_UInt32_toInt32(v_i_boxed_2547_);
    v_r_2549_ = lean_box_uint32(v_res_2548_);
    return v_r_2549_;
}
pub unsafe fn l_Int32_ofInt___boxed(mut v_i_2551_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_2552_: u32 = 0;
    let mut v_r_2553_: *mut LeanObject = core::ptr::null_mut();
    v_res_2552_ = lean_int32_of_int(v_i_2551_);
    lean_dec(v_i_2551_);
    v_r_2553_ = lean_box_uint32(v_res_2552_);
    return v_r_2553_;
}
pub unsafe fn l_Int32_ofNat___boxed(mut v_n_2555_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_2556_: u32 = 0;
    let mut v_r_2557_: *mut LeanObject = core::ptr::null_mut();
    v_res_2556_ = lean_int32_of_nat(v_n_2555_);
    lean_dec(v_n_2555_);
    v_r_2557_ = lean_box_uint32(v_res_2556_);
    return v_r_2557_;
}
pub unsafe fn l_Int_toInt32(mut v_i_2558_: *mut LeanObject) -> u32 {
    let mut v___x_2559_: u32 = 0;
    v___x_2559_ = lean_int32_of_int(v_i_2558_);
    return v___x_2559_;
}
pub unsafe fn l_Int_toInt32___boxed(mut v_i_2560_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_2561_: u32 = 0;
    let mut v_r_2562_: *mut LeanObject = core::ptr::null_mut();
    v_res_2561_ = l_Int_toInt32(v_i_2560_);
    lean_dec(v_i_2560_);
    v_r_2562_ = lean_box_uint32(v_res_2561_);
    return v_r_2562_;
}
pub unsafe fn l_Nat_toInt32(mut v_n_2563_: *mut LeanObject) -> u32 {
    let mut v___x_2564_: u32 = 0;
    v___x_2564_ = lean_int32_of_nat(v_n_2563_);
    return v___x_2564_;
}
pub unsafe fn l_Nat_toInt32___boxed(mut v_n_2565_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_2566_: u32 = 0;
    let mut v_r_2567_: *mut LeanObject = core::ptr::null_mut();
    v_res_2566_ = l_Nat_toInt32(v_n_2565_);
    lean_dec(v_n_2565_);
    v_r_2567_ = lean_box_uint32(v_res_2566_);
    return v_r_2567_;
}
pub unsafe fn l_Int32_toInt___boxed(mut v_i_2569_: *mut LeanObject) -> *mut LeanObject {
    let mut v_i_boxed_2570_: u32 = 0;
    let mut v_res_2571_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_2570_ = lean_unbox_uint32(v_i_2569_);
    lean_dec(v_i_2569_);
    v_res_2571_ = lean_int32_to_int(v_i_boxed_2570_);
    return v_res_2571_;
}
pub unsafe fn l_Int32_toNatClampNeg(mut v_i_2572_: u32) -> *mut LeanObject {
    let mut v___x_2573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2574_: *mut LeanObject = core::ptr::null_mut();
    v___x_2573_ = lean_int32_to_int(v_i_2572_);
    v___x_2574_ = l_Int_toNat(v___x_2573_);
    lean_dec(v___x_2573_);
    return v___x_2574_;
}
pub unsafe fn l_Int32_toNatClampNeg___boxed(mut v_i_2575_: *mut LeanObject) -> *mut LeanObject {
    let mut v_i_boxed_2576_: u32 = 0;
    let mut v_res_2577_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_2576_ = lean_unbox_uint32(v_i_2575_);
    lean_dec(v_i_2575_);
    v_res_2577_ = l_Int32_toNatClampNeg(v_i_boxed_2576_);
    return v_res_2577_;
}
pub unsafe fn l_Int32_ofBitVec(mut v_b_2578_: *mut LeanObject) -> u32 {
    let mut v___x_2579_: u32 = 0;
    v___x_2579_ = lean_uint32_of_nat_mk(v_b_2578_);
    return v___x_2579_;
}
pub unsafe fn l_Int32_ofBitVec___boxed(mut v_b_2580_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_2581_: u32 = 0;
    let mut v_r_2582_: *mut LeanObject = core::ptr::null_mut();
    v_res_2581_ = l_Int32_ofBitVec(v_b_2580_);
    v_r_2582_ = lean_box_uint32(v_res_2581_);
    return v_r_2582_;
}
pub unsafe fn l_Int32_toInt8___boxed(mut v_a_2584_: *mut LeanObject) -> *mut LeanObject {
    let mut v_a_boxed_2585_: u32 = 0;
    let mut v_res_2586_: u8 = 0;
    let mut v_r_2587_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_2585_ = lean_unbox_uint32(v_a_2584_);
    lean_dec(v_a_2584_);
    v_res_2586_ = lean_int32_to_int8(v_a_boxed_2585_);
    v_r_2587_ = lean_box((v_res_2586_) as usize);
    return v_r_2587_;
}
pub unsafe fn l_Int32_toInt16___boxed(mut v_a_2589_: *mut LeanObject) -> *mut LeanObject {
    let mut v_a_boxed_2590_: u32 = 0;
    let mut v_res_2591_: u16 = 0;
    let mut v_r_2592_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_2590_ = lean_unbox_uint32(v_a_2589_);
    lean_dec(v_a_2589_);
    v_res_2591_ = lean_int32_to_int16(v_a_boxed_2590_);
    v_r_2592_ = lean_box((v_res_2591_) as usize);
    return v_r_2592_;
}
pub unsafe fn l_Int8_toInt32___boxed(mut v_a_2594_: *mut LeanObject) -> *mut LeanObject {
    let mut v_a_boxed_2595_: u8 = 0;
    let mut v_res_2596_: u32 = 0;
    let mut v_r_2597_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_2595_ = (lean_unbox(v_a_2594_) as u8);
    v_res_2596_ = lean_int8_to_int32(v_a_boxed_2595_);
    v_r_2597_ = lean_box_uint32(v_res_2596_);
    return v_r_2597_;
}
pub unsafe fn l_Int16_toInt32___boxed(mut v_a_2599_: *mut LeanObject) -> *mut LeanObject {
    let mut v_a_boxed_2600_: u16 = 0;
    let mut v_res_2601_: u32 = 0;
    let mut v_r_2602_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_2600_ = (lean_unbox(v_a_2599_) as u16);
    v_res_2601_ = lean_int16_to_int32(v_a_boxed_2600_);
    v_r_2602_ = lean_box_uint32(v_res_2601_);
    return v_r_2602_;
}
pub unsafe fn l_Int32_neg___boxed(mut v_i_2604_: *mut LeanObject) -> *mut LeanObject {
    let mut v_i_boxed_2605_: u32 = 0;
    let mut v_res_2606_: u32 = 0;
    let mut v_r_2607_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_2605_ = lean_unbox_uint32(v_i_2604_);
    lean_dec(v_i_2604_);
    v_res_2606_ = lean_int32_neg(v_i_boxed_2605_);
    v_r_2607_ = lean_box_uint32(v_res_2606_);
    return v_r_2607_;
}
pub unsafe fn l_instToStringInt32___lam__0(mut v_i_2608_: u32) -> *mut LeanObject {
    let mut v___x_2609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2610_: *mut LeanObject = core::ptr::null_mut();
    v___x_2609_ = lean_int32_to_int(v_i_2608_);
    v___x_2610_ = l_Int_repr(v___x_2609_);
    lean_dec(v___x_2609_);
    return v___x_2610_;
}
pub unsafe fn l_instToStringInt32___lam__0___boxed(
    mut v_i_2611_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_2612_: u32 = 0;
    let mut v_res_2613_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_2612_ = lean_unbox_uint32(v_i_2611_);
    lean_dec(v_i_2611_);
    v_res_2613_ = l_instToStringInt32___lam__0(v_i_boxed_2612_);
    return v_res_2613_;
}
pub unsafe fn l_instReprInt32___lam__0(
    mut v_i_2616_: u32,
    mut v_prec_2617_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2620_: u8 = 0;
    v___x_2618_ = lean_int32_to_int(v_i_2616_);
    v___x_2619_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_instReprInt8___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_instReprInt8___lam__0___closed__0_once),
        _init_l_instReprInt8___lam__0___closed__0,
    );
    v___x_2620_ = lean_int_dec_lt(v___x_2618_, v___x_2619_);
    if v___x_2620_ == 0 {
        let mut v___x_2621_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2622_: *mut LeanObject = core::ptr::null_mut();
        v___x_2621_ = l_Int_repr(v___x_2618_);
        lean_dec(v___x_2618_);
        v___x_2622_ = lean_alloc_ctor(3, 1, (0) as u32);
        lean_ctor_set(v___x_2622_, 0, v___x_2621_);
        return v___x_2622_;
    } else {
        let mut v___x_2623_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2624_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2625_: *mut LeanObject = core::ptr::null_mut();
        v___x_2623_ = l_Int_repr(v___x_2618_);
        lean_dec(v___x_2618_);
        v___x_2624_ = lean_alloc_ctor(3, 1, (0) as u32);
        lean_ctor_set(v___x_2624_, 0, v___x_2623_);
        v___x_2625_ = l_Repr_addAppParen(v___x_2624_, v_prec_2617_);
        return v___x_2625_;
    }
}
pub unsafe fn l_instReprInt32___lam__0___boxed(
    mut v_i_2626_: *mut LeanObject,
    mut v_prec_2627_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_2628_: u32 = 0;
    let mut v_res_2629_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_2628_ = lean_unbox_uint32(v_i_2626_);
    lean_dec(v_i_2626_);
    v_res_2629_ = l_instReprInt32___lam__0(v_i_boxed_2628_, v_prec_2627_);
    lean_dec(v_prec_2627_);
    return v_res_2629_;
}
pub unsafe fn _init_l_instReprAtomInt32() -> *mut LeanObject {
    let mut v___x_2632_: *mut LeanObject = core::ptr::null_mut();
    v___x_2632_ = lean_box(0);
    return v___x_2632_;
}
pub unsafe fn l_Int32_instOfNat(mut v_n_2635_: *mut LeanObject) -> u32 {
    let mut v___x_2636_: u32 = 0;
    v___x_2636_ = lean_int32_of_nat(v_n_2635_);
    return v___x_2636_;
}
pub unsafe fn l_Int32_instOfNat___boxed(mut v_n_2637_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_2638_: u32 = 0;
    let mut v_r_2639_: *mut LeanObject = core::ptr::null_mut();
    v_res_2638_ = l_Int32_instOfNat(v_n_2637_);
    lean_dec(v_n_2637_);
    v_r_2639_ = lean_box_uint32(v_res_2638_);
    return v_r_2639_;
}
pub unsafe fn _init_l_Int32_maxValue___closed__0() -> u32 {
    let mut v___x_2642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2643_: u32 = 0;
    v___x_2642_ = lean_unsigned_to_nat(2147483647);
    v___x_2643_ = lean_int32_of_nat(v___x_2642_);
    return v___x_2643_;
}
pub unsafe fn _init_l_Int32_maxValue() -> u32 {
    let mut v___x_2644_: u32 = 0;
    v___x_2644_ = lean_uint32_once(
        core::ptr::addr_of_mut!(l_Int32_maxValue___closed__0),
        core::ptr::addr_of_mut!(l_Int32_maxValue___closed__0_once),
        _init_l_Int32_maxValue___closed__0,
    );
    return v___x_2644_;
}
pub unsafe fn _init_l_Int32_minValue___closed__0() -> u32 {
    let mut v___x_2645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2646_: u32 = 0;
    v___x_2645_ = lean_unsigned_to_nat(2147483648);
    v___x_2646_ = lean_int32_of_nat(v___x_2645_);
    return v___x_2646_;
}
pub unsafe fn _init_l_Int32_minValue___closed__1() -> u32 {
    let mut v___x_2647_: u32 = 0;
    let mut v___x_2648_: u32 = 0;
    v___x_2647_ = lean_uint32_once(
        core::ptr::addr_of_mut!(l_Int32_minValue___closed__0),
        core::ptr::addr_of_mut!(l_Int32_minValue___closed__0_once),
        _init_l_Int32_minValue___closed__0,
    );
    v___x_2648_ = lean_int32_neg(v___x_2647_);
    return v___x_2648_;
}
pub unsafe fn _init_l_Int32_minValue() -> u32 {
    let mut v___x_2649_: u32 = 0;
    v___x_2649_ = lean_uint32_once(
        core::ptr::addr_of_mut!(l_Int32_minValue___closed__1),
        core::ptr::addr_of_mut!(l_Int32_minValue___closed__1_once),
        _init_l_Int32_minValue___closed__1,
    );
    return v___x_2649_;
}
pub unsafe fn l_Int32_ofIntLE___redArg(mut v_i_2650_: *mut LeanObject) -> u32 {
    let mut v___x_2651_: u32 = 0;
    v___x_2651_ = lean_int32_of_int(v_i_2650_);
    return v___x_2651_;
}
pub unsafe fn l_Int32_ofIntLE___redArg___boxed(mut v_i_2652_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_2653_: u32 = 0;
    let mut v_r_2654_: *mut LeanObject = core::ptr::null_mut();
    v_res_2653_ = l_Int32_ofIntLE___redArg(v_i_2652_);
    lean_dec(v_i_2652_);
    v_r_2654_ = lean_box_uint32(v_res_2653_);
    return v_r_2654_;
}
pub unsafe fn l_Int32_ofIntLE(
    mut v_i_2655_: *mut LeanObject,
    mut v___hl_2656_: *mut LeanObject,
    mut v___hr_2657_: *mut LeanObject,
) -> u32 {
    let mut v___x_2658_: u32 = 0;
    v___x_2658_ = lean_int32_of_int(v_i_2655_);
    return v___x_2658_;
}
pub unsafe fn l_Int32_ofIntLE___boxed(
    mut v_i_2659_: *mut LeanObject,
    mut v___hl_2660_: *mut LeanObject,
    mut v___hr_2661_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2662_: u32 = 0;
    let mut v_r_2663_: *mut LeanObject = core::ptr::null_mut();
    v_res_2662_ = l_Int32_ofIntLE(v_i_2659_, v___hl_2660_, v___hr_2661_);
    lean_dec(v_i_2659_);
    v_r_2663_ = lean_box_uint32(v_res_2662_);
    return v_r_2663_;
}
pub unsafe fn _init_l_Int32_ofIntClamp___closed__0() -> *mut LeanObject {
    let mut v___x_2664_: u32 = 0;
    let mut v___x_2665_: *mut LeanObject = core::ptr::null_mut();
    v___x_2664_ = lean_uint32_once(
        core::ptr::addr_of_mut!(l_Int32_minValue___closed__1),
        core::ptr::addr_of_mut!(l_Int32_minValue___closed__1_once),
        _init_l_Int32_minValue___closed__1,
    );
    v___x_2665_ = lean_int32_to_int(v___x_2664_);
    return v___x_2665_;
}
pub unsafe fn _init_l_Int32_ofIntClamp___closed__1() -> *mut LeanObject {
    let mut v___x_2666_: u32 = 0;
    let mut v___x_2667_: *mut LeanObject = core::ptr::null_mut();
    v___x_2666_ = lean_uint32_once(
        core::ptr::addr_of_mut!(l_Int32_maxValue___closed__0),
        core::ptr::addr_of_mut!(l_Int32_maxValue___closed__0_once),
        _init_l_Int32_maxValue___closed__0,
    );
    v___x_2667_ = lean_int32_to_int(v___x_2666_);
    return v___x_2667_;
}
pub unsafe fn l_Int32_ofIntClamp(mut v_i_2668_: *mut LeanObject) -> u32 {
    let mut v___x_2669_: u32 = 0;
    let mut v___x_2670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2671_: u8 = 0;
    v___x_2669_ = lean_uint32_once(
        core::ptr::addr_of_mut!(l_Int32_minValue___closed__1),
        core::ptr::addr_of_mut!(l_Int32_minValue___closed__1_once),
        _init_l_Int32_minValue___closed__1,
    );
    v___x_2670_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Int32_ofIntClamp___closed__0),
        core::ptr::addr_of_mut!(l_Int32_ofIntClamp___closed__0_once),
        _init_l_Int32_ofIntClamp___closed__0,
    );
    v___x_2671_ = lean_int_dec_le(v___x_2670_, v_i_2668_);
    if v___x_2671_ == 0 {
        return v___x_2669_;
    } else {
        let mut v___x_2672_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2673_: u8 = 0;
        v___x_2672_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Int32_ofIntClamp___closed__1),
            core::ptr::addr_of_mut!(l_Int32_ofIntClamp___closed__1_once),
            _init_l_Int32_ofIntClamp___closed__1,
        );
        v___x_2673_ = lean_int_dec_le(v_i_2668_, v___x_2672_);
        if v___x_2673_ == 0 {
            return v___x_2669_;
        } else {
            let mut v___x_2674_: u32 = 0;
            v___x_2674_ = lean_int32_of_int(v_i_2668_);
            return v___x_2674_;
        }
    }
}
pub unsafe fn l_Int32_ofIntClamp___boxed(mut v_i_2675_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_2676_: u32 = 0;
    let mut v_r_2677_: *mut LeanObject = core::ptr::null_mut();
    v_res_2676_ = l_Int32_ofIntClamp(v_i_2675_);
    lean_dec(v_i_2675_);
    v_r_2677_ = lean_box_uint32(v_res_2676_);
    return v_r_2677_;
}
pub unsafe fn l_Int32_ofIntTruncate(mut v_i_2678_: *mut LeanObject) -> u32 {
    let mut v___x_2679_: u32 = 0;
    v___x_2679_ = l_Int32_ofIntClamp(v_i_2678_);
    return v___x_2679_;
}
pub unsafe fn l_Int32_ofIntTruncate___boxed(mut v_i_2680_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_2681_: u32 = 0;
    let mut v_r_2682_: *mut LeanObject = core::ptr::null_mut();
    v_res_2681_ = l_Int32_ofIntTruncate(v_i_2680_);
    lean_dec(v_i_2680_);
    v_r_2682_ = lean_box_uint32(v_res_2681_);
    return v_r_2682_;
}
pub unsafe fn l_Int32_add___boxed(
    mut v_a_2685_: *mut LeanObject,
    mut v_b_2686_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_2687_: u32 = 0;
    let mut v_b_boxed_2688_: u32 = 0;
    let mut v_res_2689_: u32 = 0;
    let mut v_r_2690_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_2687_ = lean_unbox_uint32(v_a_2685_);
    lean_dec(v_a_2685_);
    v_b_boxed_2688_ = lean_unbox_uint32(v_b_2686_);
    lean_dec(v_b_2686_);
    v_res_2689_ = lean_int32_add(v_a_boxed_2687_, v_b_boxed_2688_);
    v_r_2690_ = lean_box_uint32(v_res_2689_);
    return v_r_2690_;
}
pub unsafe fn l_Int32_sub___boxed(
    mut v_a_2693_: *mut LeanObject,
    mut v_b_2694_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_2695_: u32 = 0;
    let mut v_b_boxed_2696_: u32 = 0;
    let mut v_res_2697_: u32 = 0;
    let mut v_r_2698_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_2695_ = lean_unbox_uint32(v_a_2693_);
    lean_dec(v_a_2693_);
    v_b_boxed_2696_ = lean_unbox_uint32(v_b_2694_);
    lean_dec(v_b_2694_);
    v_res_2697_ = lean_int32_sub(v_a_boxed_2695_, v_b_boxed_2696_);
    v_r_2698_ = lean_box_uint32(v_res_2697_);
    return v_r_2698_;
}
pub unsafe fn l_Int32_mul___boxed(
    mut v_a_2701_: *mut LeanObject,
    mut v_b_2702_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_2703_: u32 = 0;
    let mut v_b_boxed_2704_: u32 = 0;
    let mut v_res_2705_: u32 = 0;
    let mut v_r_2706_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_2703_ = lean_unbox_uint32(v_a_2701_);
    lean_dec(v_a_2701_);
    v_b_boxed_2704_ = lean_unbox_uint32(v_b_2702_);
    lean_dec(v_b_2702_);
    v_res_2705_ = lean_int32_mul(v_a_boxed_2703_, v_b_boxed_2704_);
    v_r_2706_ = lean_box_uint32(v_res_2705_);
    return v_r_2706_;
}
pub unsafe fn l_Int32_div___boxed(
    mut v_a_2709_: *mut LeanObject,
    mut v_b_2710_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_2711_: u32 = 0;
    let mut v_b_boxed_2712_: u32 = 0;
    let mut v_res_2713_: u32 = 0;
    let mut v_r_2714_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_2711_ = lean_unbox_uint32(v_a_2709_);
    lean_dec(v_a_2709_);
    v_b_boxed_2712_ = lean_unbox_uint32(v_b_2710_);
    lean_dec(v_b_2710_);
    v_res_2713_ = lean_int32_div(v_a_boxed_2711_, v_b_boxed_2712_);
    v_r_2714_ = lean_box_uint32(v_res_2713_);
    return v_r_2714_;
}
pub unsafe fn _init_l_Int32_pow___closed__0() -> u32 {
    let mut v___x_2715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2716_: u32 = 0;
    v___x_2715_ = lean_unsigned_to_nat(1);
    v___x_2716_ = lean_int32_of_nat(v___x_2715_);
    return v___x_2716_;
}
pub unsafe fn l_Int32_pow(mut v_x_2717_: u32, mut v_n_2718_: *mut LeanObject) -> u32 {
    let mut v_zero_2719_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_2720_: u8 = 0;
    v_zero_2719_ = lean_unsigned_to_nat(0);
    v_isZero_2720_ = lean_nat_dec_eq(v_n_2718_, v_zero_2719_);
    if v_isZero_2720_ == 1 {
        let mut v___x_2721_: u32 = 0;
        v___x_2721_ = lean_uint32_once(
            core::ptr::addr_of_mut!(l_Int32_pow___closed__0),
            core::ptr::addr_of_mut!(l_Int32_pow___closed__0_once),
            _init_l_Int32_pow___closed__0,
        );
        return v___x_2721_;
    } else {
        let mut v_one_2722_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_2723_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2724_: u32 = 0;
        let mut v___x_2725_: u32 = 0;
        v_one_2722_ = lean_unsigned_to_nat(1);
        v_n_2723_ = lean_nat_sub(v_n_2718_, v_one_2722_);
        v___x_2724_ = l_Int32_pow(v_x_2717_, v_n_2723_);
        lean_dec(v_n_2723_);
        v___x_2725_ = lean_int32_mul(v___x_2724_, v_x_2717_);
        return v___x_2725_;
    }
}
pub unsafe fn l_Int32_pow___boxed(
    mut v_x_2726_: *mut LeanObject,
    mut v_n_2727_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_boxed_2728_: u32 = 0;
    let mut v_res_2729_: u32 = 0;
    let mut v_r_2730_: *mut LeanObject = core::ptr::null_mut();
    v_x_boxed_2728_ = lean_unbox_uint32(v_x_2726_);
    lean_dec(v_x_2726_);
    v_res_2729_ = l_Int32_pow(v_x_boxed_2728_, v_n_2727_);
    lean_dec(v_n_2727_);
    v_r_2730_ = lean_box_uint32(v_res_2729_);
    return v_r_2730_;
}
pub unsafe fn l_Int32_mod___boxed(
    mut v_a_2733_: *mut LeanObject,
    mut v_b_2734_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_2735_: u32 = 0;
    let mut v_b_boxed_2736_: u32 = 0;
    let mut v_res_2737_: u32 = 0;
    let mut v_r_2738_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_2735_ = lean_unbox_uint32(v_a_2733_);
    lean_dec(v_a_2733_);
    v_b_boxed_2736_ = lean_unbox_uint32(v_b_2734_);
    lean_dec(v_b_2734_);
    v_res_2737_ = lean_int32_mod(v_a_boxed_2735_, v_b_boxed_2736_);
    v_r_2738_ = lean_box_uint32(v_res_2737_);
    return v_r_2738_;
}
pub unsafe fn l_Int32_land___boxed(
    mut v_a_2741_: *mut LeanObject,
    mut v_b_2742_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_2743_: u32 = 0;
    let mut v_b_boxed_2744_: u32 = 0;
    let mut v_res_2745_: u32 = 0;
    let mut v_r_2746_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_2743_ = lean_unbox_uint32(v_a_2741_);
    lean_dec(v_a_2741_);
    v_b_boxed_2744_ = lean_unbox_uint32(v_b_2742_);
    lean_dec(v_b_2742_);
    v_res_2745_ = lean_int32_land(v_a_boxed_2743_, v_b_boxed_2744_);
    v_r_2746_ = lean_box_uint32(v_res_2745_);
    return v_r_2746_;
}
pub unsafe fn l_Int32_lor___boxed(
    mut v_a_2749_: *mut LeanObject,
    mut v_b_2750_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_2751_: u32 = 0;
    let mut v_b_boxed_2752_: u32 = 0;
    let mut v_res_2753_: u32 = 0;
    let mut v_r_2754_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_2751_ = lean_unbox_uint32(v_a_2749_);
    lean_dec(v_a_2749_);
    v_b_boxed_2752_ = lean_unbox_uint32(v_b_2750_);
    lean_dec(v_b_2750_);
    v_res_2753_ = lean_int32_lor(v_a_boxed_2751_, v_b_boxed_2752_);
    v_r_2754_ = lean_box_uint32(v_res_2753_);
    return v_r_2754_;
}
pub unsafe fn l_Int32_xor___boxed(
    mut v_a_2757_: *mut LeanObject,
    mut v_b_2758_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_2759_: u32 = 0;
    let mut v_b_boxed_2760_: u32 = 0;
    let mut v_res_2761_: u32 = 0;
    let mut v_r_2762_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_2759_ = lean_unbox_uint32(v_a_2757_);
    lean_dec(v_a_2757_);
    v_b_boxed_2760_ = lean_unbox_uint32(v_b_2758_);
    lean_dec(v_b_2758_);
    v_res_2761_ = lean_int32_xor(v_a_boxed_2759_, v_b_boxed_2760_);
    v_r_2762_ = lean_box_uint32(v_res_2761_);
    return v_r_2762_;
}
pub unsafe fn l_Int32_shiftLeft___boxed(
    mut v_a_2765_: *mut LeanObject,
    mut v_b_2766_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_2767_: u32 = 0;
    let mut v_b_boxed_2768_: u32 = 0;
    let mut v_res_2769_: u32 = 0;
    let mut v_r_2770_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_2767_ = lean_unbox_uint32(v_a_2765_);
    lean_dec(v_a_2765_);
    v_b_boxed_2768_ = lean_unbox_uint32(v_b_2766_);
    lean_dec(v_b_2766_);
    v_res_2769_ = lean_int32_shift_left(v_a_boxed_2767_, v_b_boxed_2768_);
    v_r_2770_ = lean_box_uint32(v_res_2769_);
    return v_r_2770_;
}
pub unsafe fn l_Int32_shiftRight___boxed(
    mut v_a_2773_: *mut LeanObject,
    mut v_b_2774_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_2775_: u32 = 0;
    let mut v_b_boxed_2776_: u32 = 0;
    let mut v_res_2777_: u32 = 0;
    let mut v_r_2778_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_2775_ = lean_unbox_uint32(v_a_2773_);
    lean_dec(v_a_2773_);
    v_b_boxed_2776_ = lean_unbox_uint32(v_b_2774_);
    lean_dec(v_b_2774_);
    v_res_2777_ = lean_int32_shift_right(v_a_boxed_2775_, v_b_boxed_2776_);
    v_r_2778_ = lean_box_uint32(v_res_2777_);
    return v_r_2778_;
}
pub unsafe fn l_Int32_complement___boxed(mut v_a_2780_: *mut LeanObject) -> *mut LeanObject {
    let mut v_a_boxed_2781_: u32 = 0;
    let mut v_res_2782_: u32 = 0;
    let mut v_r_2783_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_2781_ = lean_unbox_uint32(v_a_2780_);
    lean_dec(v_a_2780_);
    v_res_2782_ = lean_int32_complement(v_a_boxed_2781_);
    v_r_2783_ = lean_box_uint32(v_res_2782_);
    return v_r_2783_;
}
pub unsafe fn l_Int32_abs___boxed(mut v_a_2785_: *mut LeanObject) -> *mut LeanObject {
    let mut v_a_boxed_2786_: u32 = 0;
    let mut v_res_2787_: u32 = 0;
    let mut v_r_2788_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_2786_ = lean_unbox_uint32(v_a_2785_);
    lean_dec(v_a_2785_);
    v_res_2787_ = lean_int32_abs(v_a_boxed_2786_);
    v_r_2788_ = lean_box_uint32(v_res_2787_);
    return v_r_2788_;
}
pub unsafe fn l_Int32_decEq___boxed(
    mut v_a_2791_: *mut LeanObject,
    mut v_b_2792_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_2793_: u32 = 0;
    let mut v_b_boxed_2794_: u32 = 0;
    let mut v_res_2795_: u8 = 0;
    let mut v_r_2796_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_2793_ = lean_unbox_uint32(v_a_2791_);
    lean_dec(v_a_2791_);
    v_b_boxed_2794_ = lean_unbox_uint32(v_b_2792_);
    lean_dec(v_b_2792_);
    v_res_2795_ = lean_int32_dec_eq(v_a_boxed_2793_, v_b_boxed_2794_);
    v_r_2796_ = lean_box((v_res_2795_) as usize);
    return v_r_2796_;
}
pub unsafe fn _init_l_instInhabitedInt32___closed__0() -> u32 {
    let mut v___x_2797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2798_: u32 = 0;
    v___x_2797_ = lean_unsigned_to_nat(0);
    v___x_2798_ = lean_int32_of_nat(v___x_2797_);
    return v___x_2798_;
}
pub unsafe fn _init_l_instInhabitedInt32() -> u32 {
    let mut v___x_2799_: u32 = 0;
    v___x_2799_ = lean_uint32_once(
        core::ptr::addr_of_mut!(l_instInhabitedInt32___closed__0),
        core::ptr::addr_of_mut!(l_instInhabitedInt32___closed__0_once),
        _init_l_instInhabitedInt32___closed__0,
    );
    return v___x_2799_;
}
pub unsafe fn _init_l_instLTInt32() -> *mut LeanObject {
    let mut v___x_2812_: *mut LeanObject = core::ptr::null_mut();
    v___x_2812_ = lean_box(0);
    return v___x_2812_;
}
pub unsafe fn _init_l_instLEInt32() -> *mut LeanObject {
    let mut v___x_2813_: *mut LeanObject = core::ptr::null_mut();
    v___x_2813_ = lean_box(0);
    return v___x_2813_;
}
pub unsafe fn l_instDecidableEqInt32(mut v_a_2826_: u32, mut v_b_2827_: u32) -> u8 {
    let mut v___x_2828_: u8 = 0;
    v___x_2828_ = lean_int32_dec_eq(v_a_2826_, v_b_2827_);
    return v___x_2828_;
}
pub unsafe fn l_instDecidableEqInt32___boxed(
    mut v_a_2829_: *mut LeanObject,
    mut v_b_2830_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_2831_: u32 = 0;
    let mut v_b_boxed_2832_: u32 = 0;
    let mut v_res_2833_: u8 = 0;
    let mut v_r_2834_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_2831_ = lean_unbox_uint32(v_a_2829_);
    lean_dec(v_a_2829_);
    v_b_boxed_2832_ = lean_unbox_uint32(v_b_2830_);
    lean_dec(v_b_2830_);
    v_res_2833_ = l_instDecidableEqInt32(v_a_boxed_2831_, v_b_boxed_2832_);
    v_r_2834_ = lean_box((v_res_2833_) as usize);
    return v_r_2834_;
}
pub unsafe fn l_Bool_toInt32___boxed(mut v_b_2836_: *mut LeanObject) -> *mut LeanObject {
    let mut v_b_boxed_2837_: u8 = 0;
    let mut v_res_2838_: u32 = 0;
    let mut v_r_2839_: *mut LeanObject = core::ptr::null_mut();
    v_b_boxed_2837_ = (lean_unbox(v_b_2836_) as u8);
    v_res_2838_ = lean_bool_to_int32(v_b_boxed_2837_);
    v_r_2839_ = lean_box_uint32(v_res_2838_);
    return v_r_2839_;
}
pub unsafe fn l_Int32_decLt___aux__1(mut v_a_2840_: u32, mut v_b_2841_: u32) -> u8 {
    let mut v___x_2842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2845_: u8 = 0;
    v___x_2842_ = lean_unsigned_to_nat(32);
    v___x_2843_ = lean_uint32_to_nat(v_a_2840_);
    v___x_2844_ = lean_uint32_to_nat(v_b_2841_);
    v___x_2845_ = l_BitVec_slt(v___x_2842_, v___x_2843_, v___x_2844_);
    return v___x_2845_;
}
pub unsafe fn l_Int32_decLt___aux__1___boxed(
    mut v_a_2846_: *mut LeanObject,
    mut v_b_2847_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_2848_: u32 = 0;
    let mut v_b_boxed_2849_: u32 = 0;
    let mut v_res_2850_: u8 = 0;
    let mut v_r_2851_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_2848_ = lean_unbox_uint32(v_a_2846_);
    lean_dec(v_a_2846_);
    v_b_boxed_2849_ = lean_unbox_uint32(v_b_2847_);
    lean_dec(v_b_2847_);
    v_res_2850_ = l_Int32_decLt___aux__1(v_a_boxed_2848_, v_b_boxed_2849_);
    v_r_2851_ = lean_box((v_res_2850_) as usize);
    return v_r_2851_;
}
pub unsafe fn l_Int32_decLt___boxed(
    mut v_a_2854_: *mut LeanObject,
    mut v_b_2855_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_2856_: u32 = 0;
    let mut v_b_boxed_2857_: u32 = 0;
    let mut v_res_2858_: u8 = 0;
    let mut v_r_2859_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_2856_ = lean_unbox_uint32(v_a_2854_);
    lean_dec(v_a_2854_);
    v_b_boxed_2857_ = lean_unbox_uint32(v_b_2855_);
    lean_dec(v_b_2855_);
    v_res_2858_ = lean_int32_dec_lt(v_a_boxed_2856_, v_b_boxed_2857_);
    v_r_2859_ = lean_box((v_res_2858_) as usize);
    return v_r_2859_;
}
pub unsafe fn l_Int32_decLe___aux__1(mut v_a_2860_: u32, mut v_b_2861_: u32) -> u8 {
    let mut v___x_2862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2865_: u8 = 0;
    v___x_2862_ = lean_unsigned_to_nat(32);
    v___x_2863_ = lean_uint32_to_nat(v_a_2860_);
    v___x_2864_ = lean_uint32_to_nat(v_b_2861_);
    v___x_2865_ = l_BitVec_sle(v___x_2862_, v___x_2863_, v___x_2864_);
    return v___x_2865_;
}
pub unsafe fn l_Int32_decLe___aux__1___boxed(
    mut v_a_2866_: *mut LeanObject,
    mut v_b_2867_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_2868_: u32 = 0;
    let mut v_b_boxed_2869_: u32 = 0;
    let mut v_res_2870_: u8 = 0;
    let mut v_r_2871_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_2868_ = lean_unbox_uint32(v_a_2866_);
    lean_dec(v_a_2866_);
    v_b_boxed_2869_ = lean_unbox_uint32(v_b_2867_);
    lean_dec(v_b_2867_);
    v_res_2870_ = l_Int32_decLe___aux__1(v_a_boxed_2868_, v_b_boxed_2869_);
    v_r_2871_ = lean_box((v_res_2870_) as usize);
    return v_r_2871_;
}
pub unsafe fn l_Int32_decLe___boxed(
    mut v_a_2874_: *mut LeanObject,
    mut v_b_2875_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_2876_: u32 = 0;
    let mut v_b_boxed_2877_: u32 = 0;
    let mut v_res_2878_: u8 = 0;
    let mut v_r_2879_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_2876_ = lean_unbox_uint32(v_a_2874_);
    lean_dec(v_a_2874_);
    v_b_boxed_2877_ = lean_unbox_uint32(v_b_2875_);
    lean_dec(v_b_2875_);
    v_res_2878_ = lean_int32_dec_le(v_a_boxed_2876_, v_b_boxed_2877_);
    v_r_2879_ = lean_box((v_res_2878_) as usize);
    return v_r_2879_;
}
pub unsafe fn l_instMaxInt32___lam__0(mut v_x_2880_: u32, mut v_y_2881_: u32) -> u32 {
    let mut v___x_2882_: u8 = 0;
    v___x_2882_ = lean_int32_dec_le(v_x_2880_, v_y_2881_);
    if v___x_2882_ == 0 {
        return v_x_2880_;
    } else {
        return v_y_2881_;
    }
}
pub unsafe fn l_instMaxInt32___lam__0___boxed(
    mut v_x_2883_: *mut LeanObject,
    mut v_y_2884_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_boxed_2885_: u32 = 0;
    let mut v_y_boxed_2886_: u32 = 0;
    let mut v_res_2887_: u32 = 0;
    let mut v_r_2888_: *mut LeanObject = core::ptr::null_mut();
    v_x_boxed_2885_ = lean_unbox_uint32(v_x_2883_);
    lean_dec(v_x_2883_);
    v_y_boxed_2886_ = lean_unbox_uint32(v_y_2884_);
    lean_dec(v_y_2884_);
    v_res_2887_ = l_instMaxInt32___lam__0(v_x_boxed_2885_, v_y_boxed_2886_);
    v_r_2888_ = lean_box_uint32(v_res_2887_);
    return v_r_2888_;
}
pub unsafe fn l_instMinInt32___lam__0(mut v_x_2891_: u32, mut v_y_2892_: u32) -> u32 {
    let mut v___x_2893_: u8 = 0;
    v___x_2893_ = lean_int32_dec_le(v_x_2891_, v_y_2892_);
    if v___x_2893_ == 0 {
        return v_y_2892_;
    } else {
        return v_x_2891_;
    }
}
pub unsafe fn l_instMinInt32___lam__0___boxed(
    mut v_x_2894_: *mut LeanObject,
    mut v_y_2895_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_boxed_2896_: u32 = 0;
    let mut v_y_boxed_2897_: u32 = 0;
    let mut v_res_2898_: u32 = 0;
    let mut v_r_2899_: *mut LeanObject = core::ptr::null_mut();
    v_x_boxed_2896_ = lean_unbox_uint32(v_x_2894_);
    lean_dec(v_x_2894_);
    v_y_boxed_2897_ = lean_unbox_uint32(v_y_2895_);
    lean_dec(v_y_2895_);
    v_res_2898_ = l_instMinInt32___lam__0(v_x_boxed_2896_, v_y_boxed_2897_);
    v_r_2899_ = lean_box_uint32(v_res_2898_);
    return v_r_2899_;
}
pub unsafe fn _init_l_Int64_size___closed__0() -> *mut LeanObject {
    let mut v___x_2902_: *mut LeanObject = core::ptr::null_mut();
    v___x_2902_ = lean_cstr_to_nat(b"18446744073709551616\0".as_ptr().cast());
    return v___x_2902_;
}
pub unsafe fn _init_l_Int64_size() -> *mut LeanObject {
    let mut v___x_2903_: *mut LeanObject = core::ptr::null_mut();
    v___x_2903_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Int64_size___closed__0),
        core::ptr::addr_of_mut!(l_Int64_size___closed__0_once),
        _init_l_Int64_size___closed__0,
    );
    return v___x_2903_;
}
pub unsafe fn l_Int64_toBitVec(mut v_x_2904_: u64) -> *mut LeanObject {
    let mut v___x_2905_: *mut LeanObject = core::ptr::null_mut();
    v___x_2905_ = lean_uint64_to_nat(v_x_2904_);
    return v___x_2905_;
}
pub unsafe fn l_Int64_toBitVec___boxed(mut v_x_2906_: *mut LeanObject) -> *mut LeanObject {
    let mut v_x_boxed_2907_: u64 = 0;
    let mut v_res_2908_: *mut LeanObject = core::ptr::null_mut();
    v_x_boxed_2907_ = lean_unbox_uint64(v_x_2906_);
    lean_dec_ref(v_x_2906_);
    v_res_2908_ = l_Int64_toBitVec(v_x_boxed_2907_);
    return v_res_2908_;
}
pub unsafe fn l_UInt64_toInt64(mut v_i_2909_: u64) -> u64 {
    return v_i_2909_;
}
pub unsafe fn l_UInt64_toInt64___boxed(mut v_i_2910_: *mut LeanObject) -> *mut LeanObject {
    let mut v_i_boxed_2911_: u64 = 0;
    let mut v_res_2912_: u64 = 0;
    let mut v_r_2913_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_2911_ = lean_unbox_uint64(v_i_2910_);
    lean_dec_ref(v_i_2910_);
    v_res_2912_ = l_UInt64_toInt64(v_i_boxed_2911_);
    v_r_2913_ = lean_box_uint64(v_res_2912_);
    return v_r_2913_;
}
pub unsafe fn l_Int64_ofInt___boxed(mut v_i_2915_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_2916_: u64 = 0;
    let mut v_r_2917_: *mut LeanObject = core::ptr::null_mut();
    v_res_2916_ = lean_int64_of_int(v_i_2915_);
    lean_dec(v_i_2915_);
    v_r_2917_ = lean_box_uint64(v_res_2916_);
    return v_r_2917_;
}
pub unsafe fn l_Int64_ofNat___boxed(mut v_n_2919_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_2920_: u64 = 0;
    let mut v_r_2921_: *mut LeanObject = core::ptr::null_mut();
    v_res_2920_ = lean_int64_of_nat(v_n_2919_);
    lean_dec(v_n_2919_);
    v_r_2921_ = lean_box_uint64(v_res_2920_);
    return v_r_2921_;
}
pub unsafe fn l_Int_toInt64(mut v_i_2922_: *mut LeanObject) -> u64 {
    let mut v___x_2923_: u64 = 0;
    v___x_2923_ = lean_int64_of_int(v_i_2922_);
    return v___x_2923_;
}
pub unsafe fn l_Int_toInt64___boxed(mut v_i_2924_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_2925_: u64 = 0;
    let mut v_r_2926_: *mut LeanObject = core::ptr::null_mut();
    v_res_2925_ = l_Int_toInt64(v_i_2924_);
    lean_dec(v_i_2924_);
    v_r_2926_ = lean_box_uint64(v_res_2925_);
    return v_r_2926_;
}
pub unsafe fn l_Nat_toInt64(mut v_n_2927_: *mut LeanObject) -> u64 {
    let mut v___x_2928_: u64 = 0;
    v___x_2928_ = lean_int64_of_nat(v_n_2927_);
    return v___x_2928_;
}
pub unsafe fn l_Nat_toInt64___boxed(mut v_n_2929_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_2930_: u64 = 0;
    let mut v_r_2931_: *mut LeanObject = core::ptr::null_mut();
    v_res_2930_ = l_Nat_toInt64(v_n_2929_);
    lean_dec(v_n_2929_);
    v_r_2931_ = lean_box_uint64(v_res_2930_);
    return v_r_2931_;
}
pub unsafe fn l_Int64_toInt___boxed(mut v_i_2933_: *mut LeanObject) -> *mut LeanObject {
    let mut v_i_boxed_2934_: u64 = 0;
    let mut v_res_2935_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_2934_ = lean_unbox_uint64(v_i_2933_);
    lean_dec_ref(v_i_2933_);
    v_res_2935_ = lean_int64_to_int_sint(v_i_boxed_2934_);
    return v_res_2935_;
}
pub unsafe fn l_Int64_toNatClampNeg(mut v_i_2936_: u64) -> *mut LeanObject {
    let mut v___x_2937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2938_: *mut LeanObject = core::ptr::null_mut();
    v___x_2937_ = lean_int64_to_int_sint(v_i_2936_);
    v___x_2938_ = l_Int_toNat(v___x_2937_);
    lean_dec(v___x_2937_);
    return v___x_2938_;
}
pub unsafe fn l_Int64_toNatClampNeg___boxed(mut v_i_2939_: *mut LeanObject) -> *mut LeanObject {
    let mut v_i_boxed_2940_: u64 = 0;
    let mut v_res_2941_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_2940_ = lean_unbox_uint64(v_i_2939_);
    lean_dec_ref(v_i_2939_);
    v_res_2941_ = l_Int64_toNatClampNeg(v_i_boxed_2940_);
    return v_res_2941_;
}
pub unsafe fn l_Int64_ofBitVec(mut v_b_2942_: *mut LeanObject) -> u64 {
    let mut v___x_2943_: u64 = 0;
    v___x_2943_ = lean_uint64_of_nat_mk(v_b_2942_);
    return v___x_2943_;
}
pub unsafe fn l_Int64_ofBitVec___boxed(mut v_b_2944_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_2945_: u64 = 0;
    let mut v_r_2946_: *mut LeanObject = core::ptr::null_mut();
    v_res_2945_ = l_Int64_ofBitVec(v_b_2944_);
    v_r_2946_ = lean_box_uint64(v_res_2945_);
    return v_r_2946_;
}
pub unsafe fn l_Int64_toInt8___boxed(mut v_a_2948_: *mut LeanObject) -> *mut LeanObject {
    let mut v_a_boxed_2949_: u64 = 0;
    let mut v_res_2950_: u8 = 0;
    let mut v_r_2951_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_2949_ = lean_unbox_uint64(v_a_2948_);
    lean_dec_ref(v_a_2948_);
    v_res_2950_ = lean_int64_to_int8(v_a_boxed_2949_);
    v_r_2951_ = lean_box((v_res_2950_) as usize);
    return v_r_2951_;
}
pub unsafe fn l_Int64_toInt16___boxed(mut v_a_2953_: *mut LeanObject) -> *mut LeanObject {
    let mut v_a_boxed_2954_: u64 = 0;
    let mut v_res_2955_: u16 = 0;
    let mut v_r_2956_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_2954_ = lean_unbox_uint64(v_a_2953_);
    lean_dec_ref(v_a_2953_);
    v_res_2955_ = lean_int64_to_int16(v_a_boxed_2954_);
    v_r_2956_ = lean_box((v_res_2955_) as usize);
    return v_r_2956_;
}
pub unsafe fn l_Int64_toInt32___boxed(mut v_a_2958_: *mut LeanObject) -> *mut LeanObject {
    let mut v_a_boxed_2959_: u64 = 0;
    let mut v_res_2960_: u32 = 0;
    let mut v_r_2961_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_2959_ = lean_unbox_uint64(v_a_2958_);
    lean_dec_ref(v_a_2958_);
    v_res_2960_ = lean_int64_to_int32(v_a_boxed_2959_);
    v_r_2961_ = lean_box_uint32(v_res_2960_);
    return v_r_2961_;
}
pub unsafe fn l_Int8_toInt64___boxed(mut v_a_2963_: *mut LeanObject) -> *mut LeanObject {
    let mut v_a_boxed_2964_: u8 = 0;
    let mut v_res_2965_: u64 = 0;
    let mut v_r_2966_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_2964_ = (lean_unbox(v_a_2963_) as u8);
    v_res_2965_ = lean_int8_to_int64(v_a_boxed_2964_);
    v_r_2966_ = lean_box_uint64(v_res_2965_);
    return v_r_2966_;
}
pub unsafe fn l_Int16_toInt64___boxed(mut v_a_2968_: *mut LeanObject) -> *mut LeanObject {
    let mut v_a_boxed_2969_: u16 = 0;
    let mut v_res_2970_: u64 = 0;
    let mut v_r_2971_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_2969_ = (lean_unbox(v_a_2968_) as u16);
    v_res_2970_ = lean_int16_to_int64(v_a_boxed_2969_);
    v_r_2971_ = lean_box_uint64(v_res_2970_);
    return v_r_2971_;
}
pub unsafe fn l_Int32_toInt64___boxed(mut v_a_2973_: *mut LeanObject) -> *mut LeanObject {
    let mut v_a_boxed_2974_: u32 = 0;
    let mut v_res_2975_: u64 = 0;
    let mut v_r_2976_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_2974_ = lean_unbox_uint32(v_a_2973_);
    lean_dec(v_a_2973_);
    v_res_2975_ = lean_int32_to_int64(v_a_boxed_2974_);
    v_r_2976_ = lean_box_uint64(v_res_2975_);
    return v_r_2976_;
}
pub unsafe fn l_Int64_neg___boxed(mut v_i_2978_: *mut LeanObject) -> *mut LeanObject {
    let mut v_i_boxed_2979_: u64 = 0;
    let mut v_res_2980_: u64 = 0;
    let mut v_r_2981_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_2979_ = lean_unbox_uint64(v_i_2978_);
    lean_dec_ref(v_i_2978_);
    v_res_2980_ = lean_int64_neg(v_i_boxed_2979_);
    v_r_2981_ = lean_box_uint64(v_res_2980_);
    return v_r_2981_;
}
pub unsafe fn l_instToStringInt64___lam__0(mut v_i_2982_: u64) -> *mut LeanObject {
    let mut v___x_2983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2984_: *mut LeanObject = core::ptr::null_mut();
    v___x_2983_ = lean_int64_to_int_sint(v_i_2982_);
    v___x_2984_ = l_Int_repr(v___x_2983_);
    lean_dec(v___x_2983_);
    return v___x_2984_;
}
pub unsafe fn l_instToStringInt64___lam__0___boxed(
    mut v_i_2985_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_2986_: u64 = 0;
    let mut v_res_2987_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_2986_ = lean_unbox_uint64(v_i_2985_);
    lean_dec_ref(v_i_2985_);
    v_res_2987_ = l_instToStringInt64___lam__0(v_i_boxed_2986_);
    return v_res_2987_;
}
pub unsafe fn l_instReprInt64___lam__0(
    mut v_i_2990_: u64,
    mut v_prec_2991_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2994_: u8 = 0;
    v___x_2992_ = lean_int64_to_int_sint(v_i_2990_);
    v___x_2993_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_instReprInt8___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_instReprInt8___lam__0___closed__0_once),
        _init_l_instReprInt8___lam__0___closed__0,
    );
    v___x_2994_ = lean_int_dec_lt(v___x_2992_, v___x_2993_);
    if v___x_2994_ == 0 {
        let mut v___x_2995_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2996_: *mut LeanObject = core::ptr::null_mut();
        v___x_2995_ = l_Int_repr(v___x_2992_);
        lean_dec(v___x_2992_);
        v___x_2996_ = lean_alloc_ctor(3, 1, (0) as u32);
        lean_ctor_set(v___x_2996_, 0, v___x_2995_);
        return v___x_2996_;
    } else {
        let mut v___x_2997_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2998_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2999_: *mut LeanObject = core::ptr::null_mut();
        v___x_2997_ = l_Int_repr(v___x_2992_);
        lean_dec(v___x_2992_);
        v___x_2998_ = lean_alloc_ctor(3, 1, (0) as u32);
        lean_ctor_set(v___x_2998_, 0, v___x_2997_);
        v___x_2999_ = l_Repr_addAppParen(v___x_2998_, v_prec_2991_);
        return v___x_2999_;
    }
}
pub unsafe fn l_instReprInt64___lam__0___boxed(
    mut v_i_3000_: *mut LeanObject,
    mut v_prec_3001_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_3002_: u64 = 0;
    let mut v_res_3003_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_3002_ = lean_unbox_uint64(v_i_3000_);
    lean_dec_ref(v_i_3000_);
    v_res_3003_ = l_instReprInt64___lam__0(v_i_boxed_3002_, v_prec_3001_);
    lean_dec(v_prec_3001_);
    return v_res_3003_;
}
pub unsafe fn _init_l_instReprAtomInt64() -> *mut LeanObject {
    let mut v___x_3006_: *mut LeanObject = core::ptr::null_mut();
    v___x_3006_ = lean_box(0);
    return v___x_3006_;
}
pub unsafe fn l_instHashableInt64___lam__0(mut v_i_3007_: u64) -> u64 {
    return v_i_3007_;
}
pub unsafe fn l_instHashableInt64___lam__0___boxed(
    mut v_i_3008_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_3009_: u64 = 0;
    let mut v_res_3010_: u64 = 0;
    let mut v_r_3011_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_3009_ = lean_unbox_uint64(v_i_3008_);
    lean_dec_ref(v_i_3008_);
    v_res_3010_ = l_instHashableInt64___lam__0(v_i_boxed_3009_);
    v_r_3011_ = lean_box_uint64(v_res_3010_);
    return v_r_3011_;
}
pub unsafe fn l_Int64_instOfNat(mut v_n_3014_: *mut LeanObject) -> u64 {
    let mut v___x_3015_: u64 = 0;
    v___x_3015_ = lean_int64_of_nat(v_n_3014_);
    return v___x_3015_;
}
pub unsafe fn l_Int64_instOfNat___boxed(mut v_n_3016_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_3017_: u64 = 0;
    let mut v_r_3018_: *mut LeanObject = core::ptr::null_mut();
    v_res_3017_ = l_Int64_instOfNat(v_n_3016_);
    lean_dec(v_n_3016_);
    v_r_3018_ = lean_box_uint64(v_res_3017_);
    return v_r_3018_;
}
pub unsafe fn _init_l_Int64_maxValue___closed__0() -> u64 {
    let mut v___x_3021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3022_: u64 = 0;
    v___x_3021_ = lean_cstr_to_nat(b"9223372036854775807\0".as_ptr().cast());
    v___x_3022_ = lean_int64_of_nat(v___x_3021_);
    return v___x_3022_;
}
pub unsafe fn _init_l_Int64_maxValue() -> u64 {
    let mut v___x_3023_: u64 = 0;
    v___x_3023_ = lean_uint64_once(
        core::ptr::addr_of_mut!(l_Int64_maxValue___closed__0),
        core::ptr::addr_of_mut!(l_Int64_maxValue___closed__0_once),
        _init_l_Int64_maxValue___closed__0,
    );
    return v___x_3023_;
}
pub unsafe fn _init_l_Int64_minValue___closed__0() -> *mut LeanObject {
    let mut v___x_3024_: *mut LeanObject = core::ptr::null_mut();
    v___x_3024_ = lean_cstr_to_nat(b"9223372036854775808\0".as_ptr().cast());
    return v___x_3024_;
}
pub unsafe fn _init_l_Int64_minValue___closed__1() -> u64 {
    let mut v___x_3025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3026_: u64 = 0;
    v___x_3025_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Int64_minValue___closed__0),
        core::ptr::addr_of_mut!(l_Int64_minValue___closed__0_once),
        _init_l_Int64_minValue___closed__0,
    );
    v___x_3026_ = lean_int64_of_nat(v___x_3025_);
    return v___x_3026_;
}
pub unsafe fn _init_l_Int64_minValue___closed__2() -> u64 {
    let mut v___x_3027_: u64 = 0;
    let mut v___x_3028_: u64 = 0;
    v___x_3027_ = lean_uint64_once(
        core::ptr::addr_of_mut!(l_Int64_minValue___closed__1),
        core::ptr::addr_of_mut!(l_Int64_minValue___closed__1_once),
        _init_l_Int64_minValue___closed__1,
    );
    v___x_3028_ = lean_int64_neg(v___x_3027_);
    return v___x_3028_;
}
pub unsafe fn _init_l_Int64_minValue() -> u64 {
    let mut v___x_3029_: u64 = 0;
    v___x_3029_ = lean_uint64_once(
        core::ptr::addr_of_mut!(l_Int64_minValue___closed__2),
        core::ptr::addr_of_mut!(l_Int64_minValue___closed__2_once),
        _init_l_Int64_minValue___closed__2,
    );
    return v___x_3029_;
}
pub unsafe fn l_Int64_ofIntLE___redArg(mut v_i_3030_: *mut LeanObject) -> u64 {
    let mut v___x_3031_: u64 = 0;
    v___x_3031_ = lean_int64_of_int(v_i_3030_);
    return v___x_3031_;
}
pub unsafe fn l_Int64_ofIntLE___redArg___boxed(mut v_i_3032_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_3033_: u64 = 0;
    let mut v_r_3034_: *mut LeanObject = core::ptr::null_mut();
    v_res_3033_ = l_Int64_ofIntLE___redArg(v_i_3032_);
    lean_dec(v_i_3032_);
    v_r_3034_ = lean_box_uint64(v_res_3033_);
    return v_r_3034_;
}
pub unsafe fn l_Int64_ofIntLE(
    mut v_i_3035_: *mut LeanObject,
    mut v___hl_3036_: *mut LeanObject,
    mut v___hr_3037_: *mut LeanObject,
) -> u64 {
    let mut v___x_3038_: u64 = 0;
    v___x_3038_ = lean_int64_of_int(v_i_3035_);
    return v___x_3038_;
}
pub unsafe fn l_Int64_ofIntLE___boxed(
    mut v_i_3039_: *mut LeanObject,
    mut v___hl_3040_: *mut LeanObject,
    mut v___hr_3041_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3042_: u64 = 0;
    let mut v_r_3043_: *mut LeanObject = core::ptr::null_mut();
    v_res_3042_ = l_Int64_ofIntLE(v_i_3039_, v___hl_3040_, v___hr_3041_);
    lean_dec(v_i_3039_);
    v_r_3043_ = lean_box_uint64(v_res_3042_);
    return v_r_3043_;
}
pub unsafe fn _init_l_Int64_ofIntClamp___closed__0() -> *mut LeanObject {
    let mut v___x_3044_: u64 = 0;
    let mut v___x_3045_: *mut LeanObject = core::ptr::null_mut();
    v___x_3044_ = lean_uint64_once(
        core::ptr::addr_of_mut!(l_Int64_minValue___closed__2),
        core::ptr::addr_of_mut!(l_Int64_minValue___closed__2_once),
        _init_l_Int64_minValue___closed__2,
    );
    v___x_3045_ = lean_int64_to_int_sint(v___x_3044_);
    return v___x_3045_;
}
pub unsafe fn _init_l_Int64_ofIntClamp___closed__1() -> *mut LeanObject {
    let mut v___x_3046_: u64 = 0;
    let mut v___x_3047_: *mut LeanObject = core::ptr::null_mut();
    v___x_3046_ = lean_uint64_once(
        core::ptr::addr_of_mut!(l_Int64_maxValue___closed__0),
        core::ptr::addr_of_mut!(l_Int64_maxValue___closed__0_once),
        _init_l_Int64_maxValue___closed__0,
    );
    v___x_3047_ = lean_int64_to_int_sint(v___x_3046_);
    return v___x_3047_;
}
pub unsafe fn l_Int64_ofIntClamp(mut v_i_3048_: *mut LeanObject) -> u64 {
    let mut v___x_3049_: u64 = 0;
    let mut v___x_3050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3051_: u8 = 0;
    v___x_3049_ = lean_uint64_once(
        core::ptr::addr_of_mut!(l_Int64_minValue___closed__2),
        core::ptr::addr_of_mut!(l_Int64_minValue___closed__2_once),
        _init_l_Int64_minValue___closed__2,
    );
    v___x_3050_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Int64_ofIntClamp___closed__0),
        core::ptr::addr_of_mut!(l_Int64_ofIntClamp___closed__0_once),
        _init_l_Int64_ofIntClamp___closed__0,
    );
    v___x_3051_ = lean_int_dec_le(v___x_3050_, v_i_3048_);
    if v___x_3051_ == 0 {
        return v___x_3049_;
    } else {
        let mut v___x_3052_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3053_: u8 = 0;
        v___x_3052_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Int64_ofIntClamp___closed__1),
            core::ptr::addr_of_mut!(l_Int64_ofIntClamp___closed__1_once),
            _init_l_Int64_ofIntClamp___closed__1,
        );
        v___x_3053_ = lean_int_dec_le(v_i_3048_, v___x_3052_);
        if v___x_3053_ == 0 {
            return v___x_3049_;
        } else {
            let mut v___x_3054_: u64 = 0;
            v___x_3054_ = lean_int64_of_int(v_i_3048_);
            return v___x_3054_;
        }
    }
}
pub unsafe fn l_Int64_ofIntClamp___boxed(mut v_i_3055_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_3056_: u64 = 0;
    let mut v_r_3057_: *mut LeanObject = core::ptr::null_mut();
    v_res_3056_ = l_Int64_ofIntClamp(v_i_3055_);
    lean_dec(v_i_3055_);
    v_r_3057_ = lean_box_uint64(v_res_3056_);
    return v_r_3057_;
}
pub unsafe fn l_Int64_ofIntTruncate(mut v_i_3058_: *mut LeanObject) -> u64 {
    let mut v___x_3059_: u64 = 0;
    v___x_3059_ = l_Int64_ofIntClamp(v_i_3058_);
    return v___x_3059_;
}
pub unsafe fn l_Int64_ofIntTruncate___boxed(mut v_i_3060_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_3061_: u64 = 0;
    let mut v_r_3062_: *mut LeanObject = core::ptr::null_mut();
    v_res_3061_ = l_Int64_ofIntTruncate(v_i_3060_);
    lean_dec(v_i_3060_);
    v_r_3062_ = lean_box_uint64(v_res_3061_);
    return v_r_3062_;
}
pub unsafe fn l_Int64_add___boxed(
    mut v_a_3065_: *mut LeanObject,
    mut v_b_3066_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_3067_: u64 = 0;
    let mut v_b_boxed_3068_: u64 = 0;
    let mut v_res_3069_: u64 = 0;
    let mut v_r_3070_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_3067_ = lean_unbox_uint64(v_a_3065_);
    lean_dec_ref(v_a_3065_);
    v_b_boxed_3068_ = lean_unbox_uint64(v_b_3066_);
    lean_dec_ref(v_b_3066_);
    v_res_3069_ = lean_int64_add(v_a_boxed_3067_, v_b_boxed_3068_);
    v_r_3070_ = lean_box_uint64(v_res_3069_);
    return v_r_3070_;
}
pub unsafe fn l_Int64_sub___boxed(
    mut v_a_3073_: *mut LeanObject,
    mut v_b_3074_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_3075_: u64 = 0;
    let mut v_b_boxed_3076_: u64 = 0;
    let mut v_res_3077_: u64 = 0;
    let mut v_r_3078_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_3075_ = lean_unbox_uint64(v_a_3073_);
    lean_dec_ref(v_a_3073_);
    v_b_boxed_3076_ = lean_unbox_uint64(v_b_3074_);
    lean_dec_ref(v_b_3074_);
    v_res_3077_ = lean_int64_sub(v_a_boxed_3075_, v_b_boxed_3076_);
    v_r_3078_ = lean_box_uint64(v_res_3077_);
    return v_r_3078_;
}
pub unsafe fn l_Int64_mul___boxed(
    mut v_a_3081_: *mut LeanObject,
    mut v_b_3082_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_3083_: u64 = 0;
    let mut v_b_boxed_3084_: u64 = 0;
    let mut v_res_3085_: u64 = 0;
    let mut v_r_3086_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_3083_ = lean_unbox_uint64(v_a_3081_);
    lean_dec_ref(v_a_3081_);
    v_b_boxed_3084_ = lean_unbox_uint64(v_b_3082_);
    lean_dec_ref(v_b_3082_);
    v_res_3085_ = lean_int64_mul(v_a_boxed_3083_, v_b_boxed_3084_);
    v_r_3086_ = lean_box_uint64(v_res_3085_);
    return v_r_3086_;
}
pub unsafe fn l_Int64_div___boxed(
    mut v_a_3089_: *mut LeanObject,
    mut v_b_3090_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_3091_: u64 = 0;
    let mut v_b_boxed_3092_: u64 = 0;
    let mut v_res_3093_: u64 = 0;
    let mut v_r_3094_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_3091_ = lean_unbox_uint64(v_a_3089_);
    lean_dec_ref(v_a_3089_);
    v_b_boxed_3092_ = lean_unbox_uint64(v_b_3090_);
    lean_dec_ref(v_b_3090_);
    v_res_3093_ = lean_int64_div(v_a_boxed_3091_, v_b_boxed_3092_);
    v_r_3094_ = lean_box_uint64(v_res_3093_);
    return v_r_3094_;
}
pub unsafe fn _init_l_Int64_pow___closed__0() -> u64 {
    let mut v___x_3095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3096_: u64 = 0;
    v___x_3095_ = lean_unsigned_to_nat(1);
    v___x_3096_ = lean_int64_of_nat(v___x_3095_);
    return v___x_3096_;
}
pub unsafe fn l_Int64_pow(mut v_x_3097_: u64, mut v_n_3098_: *mut LeanObject) -> u64 {
    let mut v_zero_3099_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_3100_: u8 = 0;
    v_zero_3099_ = lean_unsigned_to_nat(0);
    v_isZero_3100_ = lean_nat_dec_eq(v_n_3098_, v_zero_3099_);
    if v_isZero_3100_ == 1 {
        let mut v___x_3101_: u64 = 0;
        v___x_3101_ = lean_uint64_once(
            core::ptr::addr_of_mut!(l_Int64_pow___closed__0),
            core::ptr::addr_of_mut!(l_Int64_pow___closed__0_once),
            _init_l_Int64_pow___closed__0,
        );
        return v___x_3101_;
    } else {
        let mut v_one_3102_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_3103_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3104_: u64 = 0;
        let mut v___x_3105_: u64 = 0;
        v_one_3102_ = lean_unsigned_to_nat(1);
        v_n_3103_ = lean_nat_sub(v_n_3098_, v_one_3102_);
        v___x_3104_ = l_Int64_pow(v_x_3097_, v_n_3103_);
        lean_dec(v_n_3103_);
        v___x_3105_ = lean_int64_mul(v___x_3104_, v_x_3097_);
        return v___x_3105_;
    }
}
pub unsafe fn l_Int64_pow___boxed(
    mut v_x_3106_: *mut LeanObject,
    mut v_n_3107_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_boxed_3108_: u64 = 0;
    let mut v_res_3109_: u64 = 0;
    let mut v_r_3110_: *mut LeanObject = core::ptr::null_mut();
    v_x_boxed_3108_ = lean_unbox_uint64(v_x_3106_);
    lean_dec_ref(v_x_3106_);
    v_res_3109_ = l_Int64_pow(v_x_boxed_3108_, v_n_3107_);
    lean_dec(v_n_3107_);
    v_r_3110_ = lean_box_uint64(v_res_3109_);
    return v_r_3110_;
}
pub unsafe fn l_Int64_mod___boxed(
    mut v_a_3113_: *mut LeanObject,
    mut v_b_3114_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_3115_: u64 = 0;
    let mut v_b_boxed_3116_: u64 = 0;
    let mut v_res_3117_: u64 = 0;
    let mut v_r_3118_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_3115_ = lean_unbox_uint64(v_a_3113_);
    lean_dec_ref(v_a_3113_);
    v_b_boxed_3116_ = lean_unbox_uint64(v_b_3114_);
    lean_dec_ref(v_b_3114_);
    v_res_3117_ = lean_int64_mod(v_a_boxed_3115_, v_b_boxed_3116_);
    v_r_3118_ = lean_box_uint64(v_res_3117_);
    return v_r_3118_;
}
pub unsafe fn l_Int64_land___boxed(
    mut v_a_3121_: *mut LeanObject,
    mut v_b_3122_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_3123_: u64 = 0;
    let mut v_b_boxed_3124_: u64 = 0;
    let mut v_res_3125_: u64 = 0;
    let mut v_r_3126_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_3123_ = lean_unbox_uint64(v_a_3121_);
    lean_dec_ref(v_a_3121_);
    v_b_boxed_3124_ = lean_unbox_uint64(v_b_3122_);
    lean_dec_ref(v_b_3122_);
    v_res_3125_ = lean_int64_land(v_a_boxed_3123_, v_b_boxed_3124_);
    v_r_3126_ = lean_box_uint64(v_res_3125_);
    return v_r_3126_;
}
pub unsafe fn l_Int64_lor___boxed(
    mut v_a_3129_: *mut LeanObject,
    mut v_b_3130_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_3131_: u64 = 0;
    let mut v_b_boxed_3132_: u64 = 0;
    let mut v_res_3133_: u64 = 0;
    let mut v_r_3134_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_3131_ = lean_unbox_uint64(v_a_3129_);
    lean_dec_ref(v_a_3129_);
    v_b_boxed_3132_ = lean_unbox_uint64(v_b_3130_);
    lean_dec_ref(v_b_3130_);
    v_res_3133_ = lean_int64_lor(v_a_boxed_3131_, v_b_boxed_3132_);
    v_r_3134_ = lean_box_uint64(v_res_3133_);
    return v_r_3134_;
}
pub unsafe fn l_Int64_xor___boxed(
    mut v_a_3137_: *mut LeanObject,
    mut v_b_3138_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_3139_: u64 = 0;
    let mut v_b_boxed_3140_: u64 = 0;
    let mut v_res_3141_: u64 = 0;
    let mut v_r_3142_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_3139_ = lean_unbox_uint64(v_a_3137_);
    lean_dec_ref(v_a_3137_);
    v_b_boxed_3140_ = lean_unbox_uint64(v_b_3138_);
    lean_dec_ref(v_b_3138_);
    v_res_3141_ = lean_int64_xor(v_a_boxed_3139_, v_b_boxed_3140_);
    v_r_3142_ = lean_box_uint64(v_res_3141_);
    return v_r_3142_;
}
pub unsafe fn l_Int64_shiftLeft___boxed(
    mut v_a_3145_: *mut LeanObject,
    mut v_b_3146_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_3147_: u64 = 0;
    let mut v_b_boxed_3148_: u64 = 0;
    let mut v_res_3149_: u64 = 0;
    let mut v_r_3150_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_3147_ = lean_unbox_uint64(v_a_3145_);
    lean_dec_ref(v_a_3145_);
    v_b_boxed_3148_ = lean_unbox_uint64(v_b_3146_);
    lean_dec_ref(v_b_3146_);
    v_res_3149_ = lean_int64_shift_left(v_a_boxed_3147_, v_b_boxed_3148_);
    v_r_3150_ = lean_box_uint64(v_res_3149_);
    return v_r_3150_;
}
pub unsafe fn l_Int64_shiftRight___boxed(
    mut v_a_3153_: *mut LeanObject,
    mut v_b_3154_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_3155_: u64 = 0;
    let mut v_b_boxed_3156_: u64 = 0;
    let mut v_res_3157_: u64 = 0;
    let mut v_r_3158_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_3155_ = lean_unbox_uint64(v_a_3153_);
    lean_dec_ref(v_a_3153_);
    v_b_boxed_3156_ = lean_unbox_uint64(v_b_3154_);
    lean_dec_ref(v_b_3154_);
    v_res_3157_ = lean_int64_shift_right(v_a_boxed_3155_, v_b_boxed_3156_);
    v_r_3158_ = lean_box_uint64(v_res_3157_);
    return v_r_3158_;
}
pub unsafe fn l_Int64_complement___boxed(mut v_a_3160_: *mut LeanObject) -> *mut LeanObject {
    let mut v_a_boxed_3161_: u64 = 0;
    let mut v_res_3162_: u64 = 0;
    let mut v_r_3163_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_3161_ = lean_unbox_uint64(v_a_3160_);
    lean_dec_ref(v_a_3160_);
    v_res_3162_ = lean_int64_complement(v_a_boxed_3161_);
    v_r_3163_ = lean_box_uint64(v_res_3162_);
    return v_r_3163_;
}
pub unsafe fn l_Int64_abs___boxed(mut v_a_3165_: *mut LeanObject) -> *mut LeanObject {
    let mut v_a_boxed_3166_: u64 = 0;
    let mut v_res_3167_: u64 = 0;
    let mut v_r_3168_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_3166_ = lean_unbox_uint64(v_a_3165_);
    lean_dec_ref(v_a_3165_);
    v_res_3167_ = lean_int64_abs(v_a_boxed_3166_);
    v_r_3168_ = lean_box_uint64(v_res_3167_);
    return v_r_3168_;
}
pub unsafe fn l_Int64_decEq___boxed(
    mut v_a_3171_: *mut LeanObject,
    mut v_b_3172_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_3173_: u64 = 0;
    let mut v_b_boxed_3174_: u64 = 0;
    let mut v_res_3175_: u8 = 0;
    let mut v_r_3176_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_3173_ = lean_unbox_uint64(v_a_3171_);
    lean_dec_ref(v_a_3171_);
    v_b_boxed_3174_ = lean_unbox_uint64(v_b_3172_);
    lean_dec_ref(v_b_3172_);
    v_res_3175_ = lean_int64_dec_eq(v_a_boxed_3173_, v_b_boxed_3174_);
    v_r_3176_ = lean_box((v_res_3175_) as usize);
    return v_r_3176_;
}
pub unsafe fn _init_l_instInhabitedInt64___closed__0() -> u64 {
    let mut v___x_3177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3178_: u64 = 0;
    v___x_3177_ = lean_unsigned_to_nat(0);
    v___x_3178_ = lean_int64_of_nat(v___x_3177_);
    return v___x_3178_;
}
pub unsafe fn _init_l_instInhabitedInt64() -> u64 {
    let mut v___x_3179_: u64 = 0;
    v___x_3179_ = lean_uint64_once(
        core::ptr::addr_of_mut!(l_instInhabitedInt64___closed__0),
        core::ptr::addr_of_mut!(l_instInhabitedInt64___closed__0_once),
        _init_l_instInhabitedInt64___closed__0,
    );
    return v___x_3179_;
}
pub unsafe fn _init_l_instLTInt64() -> *mut LeanObject {
    let mut v___x_3192_: *mut LeanObject = core::ptr::null_mut();
    v___x_3192_ = lean_box(0);
    return v___x_3192_;
}
pub unsafe fn _init_l_instLEInt64() -> *mut LeanObject {
    let mut v___x_3193_: *mut LeanObject = core::ptr::null_mut();
    v___x_3193_ = lean_box(0);
    return v___x_3193_;
}
pub unsafe fn l_instDecidableEqInt64(mut v_a_3206_: u64, mut v_b_3207_: u64) -> u8 {
    let mut v___x_3208_: u8 = 0;
    v___x_3208_ = lean_int64_dec_eq(v_a_3206_, v_b_3207_);
    return v___x_3208_;
}
pub unsafe fn l_instDecidableEqInt64___boxed(
    mut v_a_3209_: *mut LeanObject,
    mut v_b_3210_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_3211_: u64 = 0;
    let mut v_b_boxed_3212_: u64 = 0;
    let mut v_res_3213_: u8 = 0;
    let mut v_r_3214_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_3211_ = lean_unbox_uint64(v_a_3209_);
    lean_dec_ref(v_a_3209_);
    v_b_boxed_3212_ = lean_unbox_uint64(v_b_3210_);
    lean_dec_ref(v_b_3210_);
    v_res_3213_ = l_instDecidableEqInt64(v_a_boxed_3211_, v_b_boxed_3212_);
    v_r_3214_ = lean_box((v_res_3213_) as usize);
    return v_r_3214_;
}
pub unsafe fn l_Bool_toInt64___boxed(mut v_b_3216_: *mut LeanObject) -> *mut LeanObject {
    let mut v_b_boxed_3217_: u8 = 0;
    let mut v_res_3218_: u64 = 0;
    let mut v_r_3219_: *mut LeanObject = core::ptr::null_mut();
    v_b_boxed_3217_ = (lean_unbox(v_b_3216_) as u8);
    v_res_3218_ = lean_bool_to_int64(v_b_boxed_3217_);
    v_r_3219_ = lean_box_uint64(v_res_3218_);
    return v_r_3219_;
}
pub unsafe fn l_Int64_decLt___aux__1(mut v_a_3220_: u64, mut v_b_3221_: u64) -> u8 {
    let mut v___x_3222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3225_: u8 = 0;
    v___x_3222_ = lean_unsigned_to_nat(64);
    v___x_3223_ = lean_uint64_to_nat(v_a_3220_);
    v___x_3224_ = lean_uint64_to_nat(v_b_3221_);
    v___x_3225_ = l_BitVec_slt(v___x_3222_, v___x_3223_, v___x_3224_);
    return v___x_3225_;
}
pub unsafe fn l_Int64_decLt___aux__1___boxed(
    mut v_a_3226_: *mut LeanObject,
    mut v_b_3227_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_3228_: u64 = 0;
    let mut v_b_boxed_3229_: u64 = 0;
    let mut v_res_3230_: u8 = 0;
    let mut v_r_3231_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_3228_ = lean_unbox_uint64(v_a_3226_);
    lean_dec_ref(v_a_3226_);
    v_b_boxed_3229_ = lean_unbox_uint64(v_b_3227_);
    lean_dec_ref(v_b_3227_);
    v_res_3230_ = l_Int64_decLt___aux__1(v_a_boxed_3228_, v_b_boxed_3229_);
    v_r_3231_ = lean_box((v_res_3230_) as usize);
    return v_r_3231_;
}
pub unsafe fn l_Int64_decLt___boxed(
    mut v_a_3234_: *mut LeanObject,
    mut v_b_3235_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_3236_: u64 = 0;
    let mut v_b_boxed_3237_: u64 = 0;
    let mut v_res_3238_: u8 = 0;
    let mut v_r_3239_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_3236_ = lean_unbox_uint64(v_a_3234_);
    lean_dec_ref(v_a_3234_);
    v_b_boxed_3237_ = lean_unbox_uint64(v_b_3235_);
    lean_dec_ref(v_b_3235_);
    v_res_3238_ = lean_int64_dec_lt(v_a_boxed_3236_, v_b_boxed_3237_);
    v_r_3239_ = lean_box((v_res_3238_) as usize);
    return v_r_3239_;
}
pub unsafe fn l_Int64_decLe___aux__1(mut v_a_3240_: u64, mut v_b_3241_: u64) -> u8 {
    let mut v___x_3242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3245_: u8 = 0;
    v___x_3242_ = lean_unsigned_to_nat(64);
    v___x_3243_ = lean_uint64_to_nat(v_a_3240_);
    v___x_3244_ = lean_uint64_to_nat(v_b_3241_);
    v___x_3245_ = l_BitVec_sle(v___x_3242_, v___x_3243_, v___x_3244_);
    return v___x_3245_;
}
pub unsafe fn l_Int64_decLe___aux__1___boxed(
    mut v_a_3246_: *mut LeanObject,
    mut v_b_3247_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_3248_: u64 = 0;
    let mut v_b_boxed_3249_: u64 = 0;
    let mut v_res_3250_: u8 = 0;
    let mut v_r_3251_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_3248_ = lean_unbox_uint64(v_a_3246_);
    lean_dec_ref(v_a_3246_);
    v_b_boxed_3249_ = lean_unbox_uint64(v_b_3247_);
    lean_dec_ref(v_b_3247_);
    v_res_3250_ = l_Int64_decLe___aux__1(v_a_boxed_3248_, v_b_boxed_3249_);
    v_r_3251_ = lean_box((v_res_3250_) as usize);
    return v_r_3251_;
}
pub unsafe fn l_Int64_decLe___boxed(
    mut v_a_3254_: *mut LeanObject,
    mut v_b_3255_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_3256_: u64 = 0;
    let mut v_b_boxed_3257_: u64 = 0;
    let mut v_res_3258_: u8 = 0;
    let mut v_r_3259_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_3256_ = lean_unbox_uint64(v_a_3254_);
    lean_dec_ref(v_a_3254_);
    v_b_boxed_3257_ = lean_unbox_uint64(v_b_3255_);
    lean_dec_ref(v_b_3255_);
    v_res_3258_ = lean_int64_dec_le(v_a_boxed_3256_, v_b_boxed_3257_);
    v_r_3259_ = lean_box((v_res_3258_) as usize);
    return v_r_3259_;
}
pub unsafe fn l_instMaxInt64___lam__0(mut v_x_3260_: u64, mut v_y_3261_: u64) -> u64 {
    let mut v___x_3262_: u8 = 0;
    v___x_3262_ = lean_int64_dec_le(v_x_3260_, v_y_3261_);
    if v___x_3262_ == 0 {
        return v_x_3260_;
    } else {
        return v_y_3261_;
    }
}
pub unsafe fn l_instMaxInt64___lam__0___boxed(
    mut v_x_3263_: *mut LeanObject,
    mut v_y_3264_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_boxed_3265_: u64 = 0;
    let mut v_y_boxed_3266_: u64 = 0;
    let mut v_res_3267_: u64 = 0;
    let mut v_r_3268_: *mut LeanObject = core::ptr::null_mut();
    v_x_boxed_3265_ = lean_unbox_uint64(v_x_3263_);
    lean_dec_ref(v_x_3263_);
    v_y_boxed_3266_ = lean_unbox_uint64(v_y_3264_);
    lean_dec_ref(v_y_3264_);
    v_res_3267_ = l_instMaxInt64___lam__0(v_x_boxed_3265_, v_y_boxed_3266_);
    v_r_3268_ = lean_box_uint64(v_res_3267_);
    return v_r_3268_;
}
pub unsafe fn l_instMinInt64___lam__0(mut v_x_3271_: u64, mut v_y_3272_: u64) -> u64 {
    let mut v___x_3273_: u8 = 0;
    v___x_3273_ = lean_int64_dec_le(v_x_3271_, v_y_3272_);
    if v___x_3273_ == 0 {
        return v_y_3272_;
    } else {
        return v_x_3271_;
    }
}
pub unsafe fn l_instMinInt64___lam__0___boxed(
    mut v_x_3274_: *mut LeanObject,
    mut v_y_3275_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_boxed_3276_: u64 = 0;
    let mut v_y_boxed_3277_: u64 = 0;
    let mut v_res_3278_: u64 = 0;
    let mut v_r_3279_: *mut LeanObject = core::ptr::null_mut();
    v_x_boxed_3276_ = lean_unbox_uint64(v_x_3274_);
    lean_dec_ref(v_x_3274_);
    v_y_boxed_3277_ = lean_unbox_uint64(v_y_3275_);
    lean_dec_ref(v_y_3275_);
    v_res_3278_ = l_instMinInt64___lam__0(v_x_boxed_3276_, v_y_boxed_3277_);
    v_r_3279_ = lean_box_uint64(v_res_3278_);
    return v_r_3279_;
}
pub unsafe fn _init_l_ISize_size___closed__0() -> *mut LeanObject {
    let mut v___x_3282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3284_: *mut LeanObject = core::ptr::null_mut();
    v___x_3282_ = l_System_Platform_numBits;
    v___x_3283_ = lean_unsigned_to_nat(2);
    v___x_3284_ = lean_nat_pow(v___x_3283_, v___x_3282_);
    return v___x_3284_;
}
pub unsafe fn _init_l_ISize_size() -> *mut LeanObject {
    let mut v___x_3285_: *mut LeanObject = core::ptr::null_mut();
    v___x_3285_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_ISize_size___closed__0),
        core::ptr::addr_of_mut!(l_ISize_size___closed__0_once),
        _init_l_ISize_size___closed__0,
    );
    return v___x_3285_;
}
pub unsafe fn l_ISize_toBitVec(mut v_x_3286_: usize) -> *mut LeanObject {
    let mut v___x_3287_: *mut LeanObject = core::ptr::null_mut();
    v___x_3287_ = lean_usize_to_nat(v_x_3286_);
    return v___x_3287_;
}
pub unsafe fn l_ISize_toBitVec___boxed(mut v_x_3288_: *mut LeanObject) -> *mut LeanObject {
    let mut v_x_boxed_3289_: usize = 0;
    let mut v_res_3290_: *mut LeanObject = core::ptr::null_mut();
    v_x_boxed_3289_ = lean_unbox_usize(v_x_3288_);
    lean_dec(v_x_3288_);
    v_res_3290_ = l_ISize_toBitVec(v_x_boxed_3289_);
    return v_res_3290_;
}
pub unsafe fn l_USize_toISize(mut v_i_3291_: usize) -> usize {
    return v_i_3291_;
}
pub unsafe fn l_USize_toISize___boxed(mut v_i_3292_: *mut LeanObject) -> *mut LeanObject {
    let mut v_i_boxed_3293_: usize = 0;
    let mut v_res_3294_: usize = 0;
    let mut v_r_3295_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_3293_ = lean_unbox_usize(v_i_3292_);
    lean_dec(v_i_3292_);
    v_res_3294_ = l_USize_toISize(v_i_boxed_3293_);
    v_r_3295_ = lean_box_usize(v_res_3294_);
    return v_r_3295_;
}
pub unsafe fn l_ISize_ofInt___boxed(mut v_i_3297_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_3298_: usize = 0;
    let mut v_r_3299_: *mut LeanObject = core::ptr::null_mut();
    v_res_3298_ = lean_isize_of_int(v_i_3297_);
    lean_dec(v_i_3297_);
    v_r_3299_ = lean_box_usize(v_res_3298_);
    return v_r_3299_;
}
pub unsafe fn l_ISize_ofNat___boxed(mut v_n_3301_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_3302_: usize = 0;
    let mut v_r_3303_: *mut LeanObject = core::ptr::null_mut();
    v_res_3302_ = lean_isize_of_nat(v_n_3301_);
    lean_dec(v_n_3301_);
    v_r_3303_ = lean_box_usize(v_res_3302_);
    return v_r_3303_;
}
pub unsafe fn l_Int_toISize(mut v_i_3304_: *mut LeanObject) -> usize {
    let mut v___x_3305_: usize = 0;
    v___x_3305_ = lean_isize_of_int(v_i_3304_);
    return v___x_3305_;
}
pub unsafe fn l_Int_toISize___boxed(mut v_i_3306_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_3307_: usize = 0;
    let mut v_r_3308_: *mut LeanObject = core::ptr::null_mut();
    v_res_3307_ = l_Int_toISize(v_i_3306_);
    lean_dec(v_i_3306_);
    v_r_3308_ = lean_box_usize(v_res_3307_);
    return v_r_3308_;
}
pub unsafe fn l_Nat_toISize(mut v_n_3309_: *mut LeanObject) -> usize {
    let mut v___x_3310_: usize = 0;
    v___x_3310_ = lean_isize_of_nat(v_n_3309_);
    return v___x_3310_;
}
pub unsafe fn l_Nat_toISize___boxed(mut v_n_3311_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_3312_: usize = 0;
    let mut v_r_3313_: *mut LeanObject = core::ptr::null_mut();
    v_res_3312_ = l_Nat_toISize(v_n_3311_);
    lean_dec(v_n_3311_);
    v_r_3313_ = lean_box_usize(v_res_3312_);
    return v_r_3313_;
}
pub unsafe fn l_ISize_toInt___boxed(mut v_i_3315_: *mut LeanObject) -> *mut LeanObject {
    let mut v_i_boxed_3316_: usize = 0;
    let mut v_res_3317_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_3316_ = lean_unbox_usize(v_i_3315_);
    lean_dec(v_i_3315_);
    v_res_3317_ = lean_isize_to_int(v_i_boxed_3316_);
    return v_res_3317_;
}
pub unsafe fn l_ISize_toNatClampNeg(mut v_i_3318_: usize) -> *mut LeanObject {
    let mut v___x_3319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3320_: *mut LeanObject = core::ptr::null_mut();
    v___x_3319_ = lean_isize_to_int(v_i_3318_);
    v___x_3320_ = l_Int_toNat(v___x_3319_);
    lean_dec(v___x_3319_);
    return v___x_3320_;
}
pub unsafe fn l_ISize_toNatClampNeg___boxed(mut v_i_3321_: *mut LeanObject) -> *mut LeanObject {
    let mut v_i_boxed_3322_: usize = 0;
    let mut v_res_3323_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_3322_ = lean_unbox_usize(v_i_3321_);
    lean_dec(v_i_3321_);
    v_res_3323_ = l_ISize_toNatClampNeg(v_i_boxed_3322_);
    return v_res_3323_;
}
pub unsafe fn l_ISize_ofBitVec(mut v_b_3324_: *mut LeanObject) -> usize {
    let mut v___x_3325_: usize = 0;
    v___x_3325_ = lean_usize_of_nat_mk(v_b_3324_);
    return v___x_3325_;
}
pub unsafe fn l_ISize_ofBitVec___boxed(mut v_b_3326_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_3327_: usize = 0;
    let mut v_r_3328_: *mut LeanObject = core::ptr::null_mut();
    v_res_3327_ = l_ISize_ofBitVec(v_b_3326_);
    v_r_3328_ = lean_box_usize(v_res_3327_);
    return v_r_3328_;
}
pub unsafe fn l_ISize_toInt8___boxed(mut v_a_3330_: *mut LeanObject) -> *mut LeanObject {
    let mut v_a_boxed_3331_: usize = 0;
    let mut v_res_3332_: u8 = 0;
    let mut v_r_3333_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_3331_ = lean_unbox_usize(v_a_3330_);
    lean_dec(v_a_3330_);
    v_res_3332_ = lean_isize_to_int8(v_a_boxed_3331_);
    v_r_3333_ = lean_box((v_res_3332_) as usize);
    return v_r_3333_;
}
pub unsafe fn l_ISize_toInt16___boxed(mut v_a_3335_: *mut LeanObject) -> *mut LeanObject {
    let mut v_a_boxed_3336_: usize = 0;
    let mut v_res_3337_: u16 = 0;
    let mut v_r_3338_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_3336_ = lean_unbox_usize(v_a_3335_);
    lean_dec(v_a_3335_);
    v_res_3337_ = lean_isize_to_int16(v_a_boxed_3336_);
    v_r_3338_ = lean_box((v_res_3337_) as usize);
    return v_r_3338_;
}
pub unsafe fn l_ISize_toInt32___boxed(mut v_a_3340_: *mut LeanObject) -> *mut LeanObject {
    let mut v_a_boxed_3341_: usize = 0;
    let mut v_res_3342_: u32 = 0;
    let mut v_r_3343_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_3341_ = lean_unbox_usize(v_a_3340_);
    lean_dec(v_a_3340_);
    v_res_3342_ = lean_isize_to_int32(v_a_boxed_3341_);
    v_r_3343_ = lean_box_uint32(v_res_3342_);
    return v_r_3343_;
}
pub unsafe fn l_ISize_toInt64___boxed(mut v_a_3345_: *mut LeanObject) -> *mut LeanObject {
    let mut v_a_boxed_3346_: usize = 0;
    let mut v_res_3347_: u64 = 0;
    let mut v_r_3348_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_3346_ = lean_unbox_usize(v_a_3345_);
    lean_dec(v_a_3345_);
    v_res_3347_ = lean_isize_to_int64(v_a_boxed_3346_);
    v_r_3348_ = lean_box_uint64(v_res_3347_);
    return v_r_3348_;
}
pub unsafe fn l_Int8_toISize___boxed(mut v_a_3350_: *mut LeanObject) -> *mut LeanObject {
    let mut v_a_boxed_3351_: u8 = 0;
    let mut v_res_3352_: usize = 0;
    let mut v_r_3353_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_3351_ = (lean_unbox(v_a_3350_) as u8);
    v_res_3352_ = lean_int8_to_isize(v_a_boxed_3351_);
    v_r_3353_ = lean_box_usize(v_res_3352_);
    return v_r_3353_;
}
pub unsafe fn l_Int16_toISize___boxed(mut v_a_3355_: *mut LeanObject) -> *mut LeanObject {
    let mut v_a_boxed_3356_: u16 = 0;
    let mut v_res_3357_: usize = 0;
    let mut v_r_3358_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_3356_ = (lean_unbox(v_a_3355_) as u16);
    v_res_3357_ = lean_int16_to_isize(v_a_boxed_3356_);
    v_r_3358_ = lean_box_usize(v_res_3357_);
    return v_r_3358_;
}
pub unsafe fn l_Int32_toISize___boxed(mut v_a_3360_: *mut LeanObject) -> *mut LeanObject {
    let mut v_a_boxed_3361_: u32 = 0;
    let mut v_res_3362_: usize = 0;
    let mut v_r_3363_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_3361_ = lean_unbox_uint32(v_a_3360_);
    lean_dec(v_a_3360_);
    v_res_3362_ = lean_int32_to_isize(v_a_boxed_3361_);
    v_r_3363_ = lean_box_usize(v_res_3362_);
    return v_r_3363_;
}
pub unsafe fn l_Int64_toISize___boxed(mut v_a_3365_: *mut LeanObject) -> *mut LeanObject {
    let mut v_a_boxed_3366_: u64 = 0;
    let mut v_res_3367_: usize = 0;
    let mut v_r_3368_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_3366_ = lean_unbox_uint64(v_a_3365_);
    lean_dec_ref(v_a_3365_);
    v_res_3367_ = lean_int64_to_isize(v_a_boxed_3366_);
    v_r_3368_ = lean_box_usize(v_res_3367_);
    return v_r_3368_;
}
pub unsafe fn l_ISize_neg___boxed(mut v_i_3370_: *mut LeanObject) -> *mut LeanObject {
    let mut v_i_boxed_3371_: usize = 0;
    let mut v_res_3372_: usize = 0;
    let mut v_r_3373_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_3371_ = lean_unbox_usize(v_i_3370_);
    lean_dec(v_i_3370_);
    v_res_3372_ = lean_isize_neg(v_i_boxed_3371_);
    v_r_3373_ = lean_box_usize(v_res_3372_);
    return v_r_3373_;
}
pub unsafe fn l_instToStringISize___lam__0(mut v_i_3374_: usize) -> *mut LeanObject {
    let mut v___x_3375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3376_: *mut LeanObject = core::ptr::null_mut();
    v___x_3375_ = lean_isize_to_int(v_i_3374_);
    v___x_3376_ = l_Int_repr(v___x_3375_);
    lean_dec(v___x_3375_);
    return v___x_3376_;
}
pub unsafe fn l_instToStringISize___lam__0___boxed(
    mut v_i_3377_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_3378_: usize = 0;
    let mut v_res_3379_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_3378_ = lean_unbox_usize(v_i_3377_);
    lean_dec(v_i_3377_);
    v_res_3379_ = l_instToStringISize___lam__0(v_i_boxed_3378_);
    return v_res_3379_;
}
pub unsafe fn l_instReprISize___lam__0(
    mut v_i_3382_: usize,
    mut v_prec_3383_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3386_: u8 = 0;
    v___x_3384_ = lean_isize_to_int(v_i_3382_);
    v___x_3385_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_instReprInt8___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_instReprInt8___lam__0___closed__0_once),
        _init_l_instReprInt8___lam__0___closed__0,
    );
    v___x_3386_ = lean_int_dec_lt(v___x_3384_, v___x_3385_);
    if v___x_3386_ == 0 {
        let mut v___x_3387_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3388_: *mut LeanObject = core::ptr::null_mut();
        v___x_3387_ = l_Int_repr(v___x_3384_);
        lean_dec(v___x_3384_);
        v___x_3388_ = lean_alloc_ctor(3, 1, (0) as u32);
        lean_ctor_set(v___x_3388_, 0, v___x_3387_);
        return v___x_3388_;
    } else {
        let mut v___x_3389_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3390_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3391_: *mut LeanObject = core::ptr::null_mut();
        v___x_3389_ = l_Int_repr(v___x_3384_);
        lean_dec(v___x_3384_);
        v___x_3390_ = lean_alloc_ctor(3, 1, (0) as u32);
        lean_ctor_set(v___x_3390_, 0, v___x_3389_);
        v___x_3391_ = l_Repr_addAppParen(v___x_3390_, v_prec_3383_);
        return v___x_3391_;
    }
}
pub unsafe fn l_instReprISize___lam__0___boxed(
    mut v_i_3392_: *mut LeanObject,
    mut v_prec_3393_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_3394_: usize = 0;
    let mut v_res_3395_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_3394_ = lean_unbox_usize(v_i_3392_);
    lean_dec(v_i_3392_);
    v_res_3395_ = l_instReprISize___lam__0(v_i_boxed_3394_, v_prec_3393_);
    lean_dec(v_prec_3393_);
    return v_res_3395_;
}
pub unsafe fn _init_l_instReprAtomISize() -> *mut LeanObject {
    let mut v___x_3398_: *mut LeanObject = core::ptr::null_mut();
    v___x_3398_ = lean_box(0);
    return v___x_3398_;
}
pub unsafe fn l_ISize_instOfNat(mut v_n_3401_: *mut LeanObject) -> usize {
    let mut v___x_3402_: usize = 0;
    v___x_3402_ = lean_isize_of_nat(v_n_3401_);
    return v___x_3402_;
}
pub unsafe fn l_ISize_instOfNat___boxed(mut v_n_3403_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_3404_: usize = 0;
    let mut v_r_3405_: *mut LeanObject = core::ptr::null_mut();
    v_res_3404_ = l_ISize_instOfNat(v_n_3403_);
    lean_dec(v_n_3403_);
    v_r_3405_ = lean_box_usize(v_res_3404_);
    return v_r_3405_;
}
pub unsafe fn _init_l_ISize_maxValue___closed__0() -> *mut LeanObject {
    let mut v___x_3408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3409_: *mut LeanObject = core::ptr::null_mut();
    v___x_3408_ = lean_unsigned_to_nat(2);
    v___x_3409_ = lean_nat_to_int(v___x_3408_);
    return v___x_3409_;
}
pub unsafe fn _init_l_ISize_maxValue___closed__1() -> *mut LeanObject {
    let mut v___x_3410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3412_: *mut LeanObject = core::ptr::null_mut();
    v___x_3410_ = lean_unsigned_to_nat(1);
    v___x_3411_ = l_System_Platform_numBits;
    v___x_3412_ = lean_nat_sub(v___x_3411_, v___x_3410_);
    return v___x_3412_;
}
pub unsafe fn _init_l_ISize_maxValue___closed__2() -> *mut LeanObject {
    let mut v___x_3413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3415_: *mut LeanObject = core::ptr::null_mut();
    v___x_3413_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_ISize_maxValue___closed__1),
        core::ptr::addr_of_mut!(l_ISize_maxValue___closed__1_once),
        _init_l_ISize_maxValue___closed__1,
    );
    v___x_3414_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_ISize_maxValue___closed__0),
        core::ptr::addr_of_mut!(l_ISize_maxValue___closed__0_once),
        _init_l_ISize_maxValue___closed__0,
    );
    v___x_3415_ = l_Int_pow(v___x_3414_, v___x_3413_);
    return v___x_3415_;
}
pub unsafe fn _init_l_ISize_maxValue___closed__3() -> *mut LeanObject {
    let mut v___x_3416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3417_: *mut LeanObject = core::ptr::null_mut();
    v___x_3416_ = lean_unsigned_to_nat(1);
    v___x_3417_ = lean_nat_to_int(v___x_3416_);
    return v___x_3417_;
}
pub unsafe fn _init_l_ISize_maxValue___closed__4() -> *mut LeanObject {
    let mut v___x_3418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3420_: *mut LeanObject = core::ptr::null_mut();
    v___x_3418_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_ISize_maxValue___closed__3),
        core::ptr::addr_of_mut!(l_ISize_maxValue___closed__3_once),
        _init_l_ISize_maxValue___closed__3,
    );
    v___x_3419_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_ISize_maxValue___closed__2),
        core::ptr::addr_of_mut!(l_ISize_maxValue___closed__2_once),
        _init_l_ISize_maxValue___closed__2,
    );
    v___x_3420_ = lean_int_sub(v___x_3419_, v___x_3418_);
    return v___x_3420_;
}
pub unsafe fn _init_l_ISize_maxValue___closed__5() -> usize {
    let mut v___x_3421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3422_: usize = 0;
    v___x_3421_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_ISize_maxValue___closed__4),
        core::ptr::addr_of_mut!(l_ISize_maxValue___closed__4_once),
        _init_l_ISize_maxValue___closed__4,
    );
    v___x_3422_ = lean_isize_of_int(v___x_3421_);
    return v___x_3422_;
}
pub unsafe fn _init_l_ISize_maxValue() -> usize {
    let mut v___x_3423_: usize = 0;
    v___x_3423_ = lean_usize_once(
        core::ptr::addr_of_mut!(l_ISize_maxValue___closed__5),
        core::ptr::addr_of_mut!(l_ISize_maxValue___closed__5_once),
        _init_l_ISize_maxValue___closed__5,
    );
    return v___x_3423_;
}
pub unsafe fn _init_l_ISize_minValue___closed__0() -> *mut LeanObject {
    let mut v___x_3424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3425_: *mut LeanObject = core::ptr::null_mut();
    v___x_3424_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_ISize_maxValue___closed__2),
        core::ptr::addr_of_mut!(l_ISize_maxValue___closed__2_once),
        _init_l_ISize_maxValue___closed__2,
    );
    v___x_3425_ = lean_int_neg(v___x_3424_);
    return v___x_3425_;
}
pub unsafe fn _init_l_ISize_minValue___closed__1() -> usize {
    let mut v___x_3426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3427_: usize = 0;
    v___x_3426_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_ISize_minValue___closed__0),
        core::ptr::addr_of_mut!(l_ISize_minValue___closed__0_once),
        _init_l_ISize_minValue___closed__0,
    );
    v___x_3427_ = lean_isize_of_int(v___x_3426_);
    return v___x_3427_;
}
pub unsafe fn _init_l_ISize_minValue() -> usize {
    let mut v___x_3428_: usize = 0;
    v___x_3428_ = lean_usize_once(
        core::ptr::addr_of_mut!(l_ISize_minValue___closed__1),
        core::ptr::addr_of_mut!(l_ISize_minValue___closed__1_once),
        _init_l_ISize_minValue___closed__1,
    );
    return v___x_3428_;
}
pub unsafe fn l_ISize_ofIntLE___redArg(mut v_i_3429_: *mut LeanObject) -> usize {
    let mut v___x_3430_: usize = 0;
    v___x_3430_ = lean_isize_of_int(v_i_3429_);
    return v___x_3430_;
}
pub unsafe fn l_ISize_ofIntLE___redArg___boxed(mut v_i_3431_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_3432_: usize = 0;
    let mut v_r_3433_: *mut LeanObject = core::ptr::null_mut();
    v_res_3432_ = l_ISize_ofIntLE___redArg(v_i_3431_);
    lean_dec(v_i_3431_);
    v_r_3433_ = lean_box_usize(v_res_3432_);
    return v_r_3433_;
}
pub unsafe fn l_ISize_ofIntLE(
    mut v_i_3434_: *mut LeanObject,
    mut v___hl_3435_: *mut LeanObject,
    mut v___hr_3436_: *mut LeanObject,
) -> usize {
    let mut v___x_3437_: usize = 0;
    v___x_3437_ = lean_isize_of_int(v_i_3434_);
    return v___x_3437_;
}
pub unsafe fn l_ISize_ofIntLE___boxed(
    mut v_i_3438_: *mut LeanObject,
    mut v___hl_3439_: *mut LeanObject,
    mut v___hr_3440_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3441_: usize = 0;
    let mut v_r_3442_: *mut LeanObject = core::ptr::null_mut();
    v_res_3441_ = l_ISize_ofIntLE(v_i_3438_, v___hl_3439_, v___hr_3440_);
    lean_dec(v_i_3438_);
    v_r_3442_ = lean_box_usize(v_res_3441_);
    return v_r_3442_;
}
pub unsafe fn _init_l_ISize_ofIntClamp___closed__0() -> *mut LeanObject {
    let mut v___x_3443_: usize = 0;
    let mut v___x_3444_: *mut LeanObject = core::ptr::null_mut();
    v___x_3443_ = lean_usize_once(
        core::ptr::addr_of_mut!(l_ISize_minValue___closed__1),
        core::ptr::addr_of_mut!(l_ISize_minValue___closed__1_once),
        _init_l_ISize_minValue___closed__1,
    );
    v___x_3444_ = lean_isize_to_int(v___x_3443_);
    return v___x_3444_;
}
pub unsafe fn _init_l_ISize_ofIntClamp___closed__1() -> *mut LeanObject {
    let mut v___x_3445_: usize = 0;
    let mut v___x_3446_: *mut LeanObject = core::ptr::null_mut();
    v___x_3445_ = lean_usize_once(
        core::ptr::addr_of_mut!(l_ISize_maxValue___closed__5),
        core::ptr::addr_of_mut!(l_ISize_maxValue___closed__5_once),
        _init_l_ISize_maxValue___closed__5,
    );
    v___x_3446_ = lean_isize_to_int(v___x_3445_);
    return v___x_3446_;
}
pub unsafe fn l_ISize_ofIntClamp(mut v_i_3447_: *mut LeanObject) -> usize {
    let mut v___x_3448_: usize = 0;
    let mut v___x_3449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3450_: u8 = 0;
    v___x_3448_ = lean_usize_once(
        core::ptr::addr_of_mut!(l_ISize_minValue___closed__1),
        core::ptr::addr_of_mut!(l_ISize_minValue___closed__1_once),
        _init_l_ISize_minValue___closed__1,
    );
    v___x_3449_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_ISize_ofIntClamp___closed__0),
        core::ptr::addr_of_mut!(l_ISize_ofIntClamp___closed__0_once),
        _init_l_ISize_ofIntClamp___closed__0,
    );
    v___x_3450_ = lean_int_dec_le(v___x_3449_, v_i_3447_);
    if v___x_3450_ == 0 {
        return v___x_3448_;
    } else {
        let mut v___x_3451_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3452_: u8 = 0;
        v___x_3451_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_ISize_ofIntClamp___closed__1),
            core::ptr::addr_of_mut!(l_ISize_ofIntClamp___closed__1_once),
            _init_l_ISize_ofIntClamp___closed__1,
        );
        v___x_3452_ = lean_int_dec_le(v_i_3447_, v___x_3451_);
        if v___x_3452_ == 0 {
            return v___x_3448_;
        } else {
            let mut v___x_3453_: usize = 0;
            v___x_3453_ = lean_isize_of_int(v_i_3447_);
            return v___x_3453_;
        }
    }
}
pub unsafe fn l_ISize_ofIntClamp___boxed(mut v_i_3454_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_3455_: usize = 0;
    let mut v_r_3456_: *mut LeanObject = core::ptr::null_mut();
    v_res_3455_ = l_ISize_ofIntClamp(v_i_3454_);
    lean_dec(v_i_3454_);
    v_r_3456_ = lean_box_usize(v_res_3455_);
    return v_r_3456_;
}
pub unsafe fn l_ISize_ofIntTruncate(mut v_i_3457_: *mut LeanObject) -> usize {
    let mut v___x_3458_: usize = 0;
    v___x_3458_ = l_ISize_ofIntClamp(v_i_3457_);
    return v___x_3458_;
}
pub unsafe fn l_ISize_ofIntTruncate___boxed(mut v_i_3459_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_3460_: usize = 0;
    let mut v_r_3461_: *mut LeanObject = core::ptr::null_mut();
    v_res_3460_ = l_ISize_ofIntTruncate(v_i_3459_);
    lean_dec(v_i_3459_);
    v_r_3461_ = lean_box_usize(v_res_3460_);
    return v_r_3461_;
}
pub unsafe fn l_ISize_add___boxed(
    mut v_a_3464_: *mut LeanObject,
    mut v_b_3465_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_3466_: usize = 0;
    let mut v_b_boxed_3467_: usize = 0;
    let mut v_res_3468_: usize = 0;
    let mut v_r_3469_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_3466_ = lean_unbox_usize(v_a_3464_);
    lean_dec(v_a_3464_);
    v_b_boxed_3467_ = lean_unbox_usize(v_b_3465_);
    lean_dec(v_b_3465_);
    v_res_3468_ = lean_isize_add(v_a_boxed_3466_, v_b_boxed_3467_);
    v_r_3469_ = lean_box_usize(v_res_3468_);
    return v_r_3469_;
}
pub unsafe fn l_ISize_sub___boxed(
    mut v_a_3472_: *mut LeanObject,
    mut v_b_3473_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_3474_: usize = 0;
    let mut v_b_boxed_3475_: usize = 0;
    let mut v_res_3476_: usize = 0;
    let mut v_r_3477_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_3474_ = lean_unbox_usize(v_a_3472_);
    lean_dec(v_a_3472_);
    v_b_boxed_3475_ = lean_unbox_usize(v_b_3473_);
    lean_dec(v_b_3473_);
    v_res_3476_ = lean_isize_sub(v_a_boxed_3474_, v_b_boxed_3475_);
    v_r_3477_ = lean_box_usize(v_res_3476_);
    return v_r_3477_;
}
pub unsafe fn l_ISize_mul___boxed(
    mut v_a_3480_: *mut LeanObject,
    mut v_b_3481_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_3482_: usize = 0;
    let mut v_b_boxed_3483_: usize = 0;
    let mut v_res_3484_: usize = 0;
    let mut v_r_3485_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_3482_ = lean_unbox_usize(v_a_3480_);
    lean_dec(v_a_3480_);
    v_b_boxed_3483_ = lean_unbox_usize(v_b_3481_);
    lean_dec(v_b_3481_);
    v_res_3484_ = lean_isize_mul(v_a_boxed_3482_, v_b_boxed_3483_);
    v_r_3485_ = lean_box_usize(v_res_3484_);
    return v_r_3485_;
}
pub unsafe fn l_ISize_div___boxed(
    mut v_a_3488_: *mut LeanObject,
    mut v_b_3489_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_3490_: usize = 0;
    let mut v_b_boxed_3491_: usize = 0;
    let mut v_res_3492_: usize = 0;
    let mut v_r_3493_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_3490_ = lean_unbox_usize(v_a_3488_);
    lean_dec(v_a_3488_);
    v_b_boxed_3491_ = lean_unbox_usize(v_b_3489_);
    lean_dec(v_b_3489_);
    v_res_3492_ = lean_isize_div(v_a_boxed_3490_, v_b_boxed_3491_);
    v_r_3493_ = lean_box_usize(v_res_3492_);
    return v_r_3493_;
}
pub unsafe fn _init_l_ISize_pow___closed__0() -> usize {
    let mut v___x_3494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3495_: usize = 0;
    v___x_3494_ = lean_unsigned_to_nat(1);
    v___x_3495_ = lean_isize_of_nat(v___x_3494_);
    return v___x_3495_;
}
pub unsafe fn l_ISize_pow(mut v_x_3496_: usize, mut v_n_3497_: *mut LeanObject) -> usize {
    let mut v_zero_3498_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_3499_: u8 = 0;
    v_zero_3498_ = lean_unsigned_to_nat(0);
    v_isZero_3499_ = lean_nat_dec_eq(v_n_3497_, v_zero_3498_);
    if v_isZero_3499_ == 1 {
        let mut v___x_3500_: usize = 0;
        v___x_3500_ = lean_usize_once(
            core::ptr::addr_of_mut!(l_ISize_pow___closed__0),
            core::ptr::addr_of_mut!(l_ISize_pow___closed__0_once),
            _init_l_ISize_pow___closed__0,
        );
        return v___x_3500_;
    } else {
        let mut v_one_3501_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_3502_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3503_: usize = 0;
        let mut v___x_3504_: usize = 0;
        v_one_3501_ = lean_unsigned_to_nat(1);
        v_n_3502_ = lean_nat_sub(v_n_3497_, v_one_3501_);
        v___x_3503_ = l_ISize_pow(v_x_3496_, v_n_3502_);
        lean_dec(v_n_3502_);
        v___x_3504_ = lean_isize_mul(v___x_3503_, v_x_3496_);
        return v___x_3504_;
    }
}
pub unsafe fn l_ISize_pow___boxed(
    mut v_x_3505_: *mut LeanObject,
    mut v_n_3506_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_boxed_3507_: usize = 0;
    let mut v_res_3508_: usize = 0;
    let mut v_r_3509_: *mut LeanObject = core::ptr::null_mut();
    v_x_boxed_3507_ = lean_unbox_usize(v_x_3505_);
    lean_dec(v_x_3505_);
    v_res_3508_ = l_ISize_pow(v_x_boxed_3507_, v_n_3506_);
    lean_dec(v_n_3506_);
    v_r_3509_ = lean_box_usize(v_res_3508_);
    return v_r_3509_;
}
pub unsafe fn l_ISize_mod___boxed(
    mut v_a_3512_: *mut LeanObject,
    mut v_b_3513_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_3514_: usize = 0;
    let mut v_b_boxed_3515_: usize = 0;
    let mut v_res_3516_: usize = 0;
    let mut v_r_3517_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_3514_ = lean_unbox_usize(v_a_3512_);
    lean_dec(v_a_3512_);
    v_b_boxed_3515_ = lean_unbox_usize(v_b_3513_);
    lean_dec(v_b_3513_);
    v_res_3516_ = lean_isize_mod(v_a_boxed_3514_, v_b_boxed_3515_);
    v_r_3517_ = lean_box_usize(v_res_3516_);
    return v_r_3517_;
}
pub unsafe fn l_ISize_land___boxed(
    mut v_a_3520_: *mut LeanObject,
    mut v_b_3521_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_3522_: usize = 0;
    let mut v_b_boxed_3523_: usize = 0;
    let mut v_res_3524_: usize = 0;
    let mut v_r_3525_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_3522_ = lean_unbox_usize(v_a_3520_);
    lean_dec(v_a_3520_);
    v_b_boxed_3523_ = lean_unbox_usize(v_b_3521_);
    lean_dec(v_b_3521_);
    v_res_3524_ = lean_isize_land(v_a_boxed_3522_, v_b_boxed_3523_);
    v_r_3525_ = lean_box_usize(v_res_3524_);
    return v_r_3525_;
}
pub unsafe fn l_ISize_lor___boxed(
    mut v_a_3528_: *mut LeanObject,
    mut v_b_3529_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_3530_: usize = 0;
    let mut v_b_boxed_3531_: usize = 0;
    let mut v_res_3532_: usize = 0;
    let mut v_r_3533_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_3530_ = lean_unbox_usize(v_a_3528_);
    lean_dec(v_a_3528_);
    v_b_boxed_3531_ = lean_unbox_usize(v_b_3529_);
    lean_dec(v_b_3529_);
    v_res_3532_ = lean_isize_lor(v_a_boxed_3530_, v_b_boxed_3531_);
    v_r_3533_ = lean_box_usize(v_res_3532_);
    return v_r_3533_;
}
pub unsafe fn l_ISize_xor___boxed(
    mut v_a_3536_: *mut LeanObject,
    mut v_b_3537_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_3538_: usize = 0;
    let mut v_b_boxed_3539_: usize = 0;
    let mut v_res_3540_: usize = 0;
    let mut v_r_3541_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_3538_ = lean_unbox_usize(v_a_3536_);
    lean_dec(v_a_3536_);
    v_b_boxed_3539_ = lean_unbox_usize(v_b_3537_);
    lean_dec(v_b_3537_);
    v_res_3540_ = lean_isize_xor(v_a_boxed_3538_, v_b_boxed_3539_);
    v_r_3541_ = lean_box_usize(v_res_3540_);
    return v_r_3541_;
}
pub unsafe fn l_ISize_shiftLeft___boxed(
    mut v_a_3544_: *mut LeanObject,
    mut v_b_3545_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_3546_: usize = 0;
    let mut v_b_boxed_3547_: usize = 0;
    let mut v_res_3548_: usize = 0;
    let mut v_r_3549_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_3546_ = lean_unbox_usize(v_a_3544_);
    lean_dec(v_a_3544_);
    v_b_boxed_3547_ = lean_unbox_usize(v_b_3545_);
    lean_dec(v_b_3545_);
    v_res_3548_ = lean_isize_shift_left(v_a_boxed_3546_, v_b_boxed_3547_);
    v_r_3549_ = lean_box_usize(v_res_3548_);
    return v_r_3549_;
}
pub unsafe fn l_ISize_shiftRight___boxed(
    mut v_a_3552_: *mut LeanObject,
    mut v_b_3553_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_3554_: usize = 0;
    let mut v_b_boxed_3555_: usize = 0;
    let mut v_res_3556_: usize = 0;
    let mut v_r_3557_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_3554_ = lean_unbox_usize(v_a_3552_);
    lean_dec(v_a_3552_);
    v_b_boxed_3555_ = lean_unbox_usize(v_b_3553_);
    lean_dec(v_b_3553_);
    v_res_3556_ = lean_isize_shift_right(v_a_boxed_3554_, v_b_boxed_3555_);
    v_r_3557_ = lean_box_usize(v_res_3556_);
    return v_r_3557_;
}
pub unsafe fn l_ISize_complement___boxed(mut v_a_3559_: *mut LeanObject) -> *mut LeanObject {
    let mut v_a_boxed_3560_: usize = 0;
    let mut v_res_3561_: usize = 0;
    let mut v_r_3562_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_3560_ = lean_unbox_usize(v_a_3559_);
    lean_dec(v_a_3559_);
    v_res_3561_ = lean_isize_complement(v_a_boxed_3560_);
    v_r_3562_ = lean_box_usize(v_res_3561_);
    return v_r_3562_;
}
pub unsafe fn l_ISize_abs___boxed(mut v_a_3564_: *mut LeanObject) -> *mut LeanObject {
    let mut v_a_boxed_3565_: usize = 0;
    let mut v_res_3566_: usize = 0;
    let mut v_r_3567_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_3565_ = lean_unbox_usize(v_a_3564_);
    lean_dec(v_a_3564_);
    v_res_3566_ = lean_isize_abs(v_a_boxed_3565_);
    v_r_3567_ = lean_box_usize(v_res_3566_);
    return v_r_3567_;
}
pub unsafe fn l_ISize_decEq___boxed(
    mut v_a_3570_: *mut LeanObject,
    mut v_b_3571_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_3572_: usize = 0;
    let mut v_b_boxed_3573_: usize = 0;
    let mut v_res_3574_: u8 = 0;
    let mut v_r_3575_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_3572_ = lean_unbox_usize(v_a_3570_);
    lean_dec(v_a_3570_);
    v_b_boxed_3573_ = lean_unbox_usize(v_b_3571_);
    lean_dec(v_b_3571_);
    v_res_3574_ = lean_isize_dec_eq(v_a_boxed_3572_, v_b_boxed_3573_);
    v_r_3575_ = lean_box((v_res_3574_) as usize);
    return v_r_3575_;
}
pub unsafe fn _init_l_instInhabitedISize___closed__0() -> usize {
    let mut v___x_3576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3577_: usize = 0;
    v___x_3576_ = lean_unsigned_to_nat(0);
    v___x_3577_ = lean_isize_of_nat(v___x_3576_);
    return v___x_3577_;
}
pub unsafe fn _init_l_instInhabitedISize() -> usize {
    let mut v___x_3578_: usize = 0;
    v___x_3578_ = lean_usize_once(
        core::ptr::addr_of_mut!(l_instInhabitedISize___closed__0),
        core::ptr::addr_of_mut!(l_instInhabitedISize___closed__0_once),
        _init_l_instInhabitedISize___closed__0,
    );
    return v___x_3578_;
}
pub unsafe fn _init_l_instLTISize() -> *mut LeanObject {
    let mut v___x_3591_: *mut LeanObject = core::ptr::null_mut();
    v___x_3591_ = lean_box(0);
    return v___x_3591_;
}
pub unsafe fn _init_l_instLEISize() -> *mut LeanObject {
    let mut v___x_3592_: *mut LeanObject = core::ptr::null_mut();
    v___x_3592_ = lean_box(0);
    return v___x_3592_;
}
pub unsafe fn l_instDecidableEqISize(mut v_a_3605_: usize, mut v_b_3606_: usize) -> u8 {
    let mut v___x_3607_: u8 = 0;
    v___x_3607_ = lean_isize_dec_eq(v_a_3605_, v_b_3606_);
    return v___x_3607_;
}
pub unsafe fn l_instDecidableEqISize___boxed(
    mut v_a_3608_: *mut LeanObject,
    mut v_b_3609_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_3610_: usize = 0;
    let mut v_b_boxed_3611_: usize = 0;
    let mut v_res_3612_: u8 = 0;
    let mut v_r_3613_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_3610_ = lean_unbox_usize(v_a_3608_);
    lean_dec(v_a_3608_);
    v_b_boxed_3611_ = lean_unbox_usize(v_b_3609_);
    lean_dec(v_b_3609_);
    v_res_3612_ = l_instDecidableEqISize(v_a_boxed_3610_, v_b_boxed_3611_);
    v_r_3613_ = lean_box((v_res_3612_) as usize);
    return v_r_3613_;
}
pub unsafe fn l_Bool_toISize___boxed(mut v_b_3615_: *mut LeanObject) -> *mut LeanObject {
    let mut v_b_boxed_3616_: u8 = 0;
    let mut v_res_3617_: usize = 0;
    let mut v_r_3618_: *mut LeanObject = core::ptr::null_mut();
    v_b_boxed_3616_ = (lean_unbox(v_b_3615_) as u8);
    v_res_3617_ = lean_bool_to_isize(v_b_boxed_3616_);
    v_r_3618_ = lean_box_usize(v_res_3617_);
    return v_r_3618_;
}
pub unsafe fn l_ISize_decLt___aux__1(mut v_a_3619_: usize, mut v_b_3620_: usize) -> u8 {
    let mut v___x_3621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3624_: u8 = 0;
    v___x_3621_ = l_System_Platform_numBits;
    v___x_3622_ = lean_usize_to_nat(v_a_3619_);
    v___x_3623_ = lean_usize_to_nat(v_b_3620_);
    v___x_3624_ = l_BitVec_slt(v___x_3621_, v___x_3622_, v___x_3623_);
    return v___x_3624_;
}
pub unsafe fn l_ISize_decLt___aux__1___boxed(
    mut v_a_3625_: *mut LeanObject,
    mut v_b_3626_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_3627_: usize = 0;
    let mut v_b_boxed_3628_: usize = 0;
    let mut v_res_3629_: u8 = 0;
    let mut v_r_3630_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_3627_ = lean_unbox_usize(v_a_3625_);
    lean_dec(v_a_3625_);
    v_b_boxed_3628_ = lean_unbox_usize(v_b_3626_);
    lean_dec(v_b_3626_);
    v_res_3629_ = l_ISize_decLt___aux__1(v_a_boxed_3627_, v_b_boxed_3628_);
    v_r_3630_ = lean_box((v_res_3629_) as usize);
    return v_r_3630_;
}
pub unsafe fn l_ISize_decLt___boxed(
    mut v_a_3633_: *mut LeanObject,
    mut v_b_3634_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_3635_: usize = 0;
    let mut v_b_boxed_3636_: usize = 0;
    let mut v_res_3637_: u8 = 0;
    let mut v_r_3638_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_3635_ = lean_unbox_usize(v_a_3633_);
    lean_dec(v_a_3633_);
    v_b_boxed_3636_ = lean_unbox_usize(v_b_3634_);
    lean_dec(v_b_3634_);
    v_res_3637_ = lean_isize_dec_lt(v_a_boxed_3635_, v_b_boxed_3636_);
    v_r_3638_ = lean_box((v_res_3637_) as usize);
    return v_r_3638_;
}
pub unsafe fn l_ISize_decLe___aux__1(mut v_a_3639_: usize, mut v_b_3640_: usize) -> u8 {
    let mut v___x_3641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3644_: u8 = 0;
    v___x_3641_ = l_System_Platform_numBits;
    v___x_3642_ = lean_usize_to_nat(v_a_3639_);
    v___x_3643_ = lean_usize_to_nat(v_b_3640_);
    v___x_3644_ = l_BitVec_sle(v___x_3641_, v___x_3642_, v___x_3643_);
    return v___x_3644_;
}
pub unsafe fn l_ISize_decLe___aux__1___boxed(
    mut v_a_3645_: *mut LeanObject,
    mut v_b_3646_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_3647_: usize = 0;
    let mut v_b_boxed_3648_: usize = 0;
    let mut v_res_3649_: u8 = 0;
    let mut v_r_3650_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_3647_ = lean_unbox_usize(v_a_3645_);
    lean_dec(v_a_3645_);
    v_b_boxed_3648_ = lean_unbox_usize(v_b_3646_);
    lean_dec(v_b_3646_);
    v_res_3649_ = l_ISize_decLe___aux__1(v_a_boxed_3647_, v_b_boxed_3648_);
    v_r_3650_ = lean_box((v_res_3649_) as usize);
    return v_r_3650_;
}
pub unsafe fn l_ISize_decLe___boxed(
    mut v_a_3653_: *mut LeanObject,
    mut v_b_3654_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_3655_: usize = 0;
    let mut v_b_boxed_3656_: usize = 0;
    let mut v_res_3657_: u8 = 0;
    let mut v_r_3658_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_3655_ = lean_unbox_usize(v_a_3653_);
    lean_dec(v_a_3653_);
    v_b_boxed_3656_ = lean_unbox_usize(v_b_3654_);
    lean_dec(v_b_3654_);
    v_res_3657_ = lean_isize_dec_le(v_a_boxed_3655_, v_b_boxed_3656_);
    v_r_3658_ = lean_box((v_res_3657_) as usize);
    return v_r_3658_;
}
pub unsafe fn l_instMaxISize___lam__0(mut v_x_3659_: usize, mut v_y_3660_: usize) -> usize {
    let mut v___x_3661_: u8 = 0;
    v___x_3661_ = lean_isize_dec_le(v_x_3659_, v_y_3660_);
    if v___x_3661_ == 0 {
        return v_x_3659_;
    } else {
        return v_y_3660_;
    }
}
pub unsafe fn l_instMaxISize___lam__0___boxed(
    mut v_x_3662_: *mut LeanObject,
    mut v_y_3663_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_boxed_3664_: usize = 0;
    let mut v_y_boxed_3665_: usize = 0;
    let mut v_res_3666_: usize = 0;
    let mut v_r_3667_: *mut LeanObject = core::ptr::null_mut();
    v_x_boxed_3664_ = lean_unbox_usize(v_x_3662_);
    lean_dec(v_x_3662_);
    v_y_boxed_3665_ = lean_unbox_usize(v_y_3663_);
    lean_dec(v_y_3663_);
    v_res_3666_ = l_instMaxISize___lam__0(v_x_boxed_3664_, v_y_boxed_3665_);
    v_r_3667_ = lean_box_usize(v_res_3666_);
    return v_r_3667_;
}
pub unsafe fn l_instMinISize___lam__0(mut v_x_3670_: usize, mut v_y_3671_: usize) -> usize {
    let mut v___x_3672_: u8 = 0;
    v___x_3672_ = lean_isize_dec_le(v_x_3670_, v_y_3671_);
    if v___x_3672_ == 0 {
        return v_y_3671_;
    } else {
        return v_x_3670_;
    }
}
pub unsafe fn l_instMinISize___lam__0___boxed(
    mut v_x_3673_: *mut LeanObject,
    mut v_y_3674_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_boxed_3675_: usize = 0;
    let mut v_y_boxed_3676_: usize = 0;
    let mut v_res_3677_: usize = 0;
    let mut v_r_3678_: *mut LeanObject = core::ptr::null_mut();
    v_x_boxed_3675_ = lean_unbox_usize(v_x_3673_);
    lean_dec(v_x_3673_);
    v_y_boxed_3676_ = lean_unbox_usize(v_y_3674_);
    lean_dec(v_y_3674_);
    v_res_3677_ = l_instMinISize___lam__0(v_x_boxed_3675_, v_y_boxed_3676_);
    v_r_3678_ = lean_box_usize(v_res_3677_);
    return v_r_3678_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_SInt_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_UInt_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_ToString_Extra(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Int8_size = _init_l_Int8_size();
    lean_mark_persistent(l_Int8_size);
    l_instReprAtomInt8 = _init_l_instReprAtomInt8();
    lean_mark_persistent(l_instReprAtomInt8);
    l_Int8_maxValue = _init_l_Int8_maxValue();
    l_Int8_minValue = _init_l_Int8_minValue();
    l_instInhabitedInt8 = _init_l_instInhabitedInt8();
    l_instLTInt8 = _init_l_instLTInt8();
    lean_mark_persistent(l_instLTInt8);
    l_instLEInt8 = _init_l_instLEInt8();
    lean_mark_persistent(l_instLEInt8);
    l_Int16_size = _init_l_Int16_size();
    lean_mark_persistent(l_Int16_size);
    l_instReprAtomInt16 = _init_l_instReprAtomInt16();
    lean_mark_persistent(l_instReprAtomInt16);
    l_Int16_maxValue = _init_l_Int16_maxValue();
    l_Int16_minValue = _init_l_Int16_minValue();
    l_instInhabitedInt16 = _init_l_instInhabitedInt16();
    l_instLTInt16 = _init_l_instLTInt16();
    lean_mark_persistent(l_instLTInt16);
    l_instLEInt16 = _init_l_instLEInt16();
    lean_mark_persistent(l_instLEInt16);
    l_Int32_size = _init_l_Int32_size();
    lean_mark_persistent(l_Int32_size);
    l_instReprAtomInt32 = _init_l_instReprAtomInt32();
    lean_mark_persistent(l_instReprAtomInt32);
    l_Int32_maxValue = _init_l_Int32_maxValue();
    l_Int32_minValue = _init_l_Int32_minValue();
    l_instInhabitedInt32 = _init_l_instInhabitedInt32();
    l_instLTInt32 = _init_l_instLTInt32();
    lean_mark_persistent(l_instLTInt32);
    l_instLEInt32 = _init_l_instLEInt32();
    lean_mark_persistent(l_instLEInt32);
    l_Int64_size = _init_l_Int64_size();
    lean_mark_persistent(l_Int64_size);
    l_instReprAtomInt64 = _init_l_instReprAtomInt64();
    lean_mark_persistent(l_instReprAtomInt64);
    l_Int64_maxValue = _init_l_Int64_maxValue();
    l_Int64_minValue = _init_l_Int64_minValue();
    l_instInhabitedInt64 = _init_l_instInhabitedInt64();
    l_instLTInt64 = _init_l_instLTInt64();
    lean_mark_persistent(l_instLTInt64);
    l_instLEInt64 = _init_l_instLEInt64();
    lean_mark_persistent(l_instLEInt64);
    l_ISize_size = _init_l_ISize_size();
    lean_mark_persistent(l_ISize_size);
    l_instReprAtomISize = _init_l_instReprAtomISize();
    lean_mark_persistent(l_instReprAtomISize);
    l_ISize_maxValue = _init_l_ISize_maxValue();
    l_ISize_minValue = _init_l_ISize_minValue();
    l_instInhabitedISize = _init_l_instInhabitedISize();
    l_instLTISize = _init_l_instLTISize();
    lean_mark_persistent(l_instLTISize);
    l_instLEISize = _init_l_instLEISize();
    lean_mark_persistent(l_instLEISize);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_SInt_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_SInt_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_UInt_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_ToString_Extra(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_SInt_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_SInt_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_SInt_Basic(builtin);
}
