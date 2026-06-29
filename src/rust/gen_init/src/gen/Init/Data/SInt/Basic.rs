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
use crate::ffi::{
    lean_int_dec_le, lean_int_dec_lt, lean_int_neg, lean_int_sub, lean_nat_to_int,
};
use crate::ffi::{
    lean_bool_to_int8, lean_bool_to_int16, lean_bool_to_int32, lean_bool_to_int64,
    lean_bool_to_isize, lean_int8_abs, lean_int8_add, lean_int8_complement, lean_int8_dec_eq,
    lean_int8_dec_le, lean_int8_dec_lt, lean_int8_div, lean_int8_land, lean_int8_lor,
    lean_int8_mod, lean_int8_mul, lean_int8_neg, lean_int8_of_int, lean_int8_of_nat,
    lean_int8_shift_left, lean_int8_shift_right, lean_int8_sub, lean_int8_to_int,
    lean_int8_to_int16, lean_int8_to_int32, lean_int8_to_int64, lean_int8_to_isize, lean_int8_xor,
    lean_int16_abs, lean_int16_add, lean_int16_complement, lean_int16_dec_eq, lean_int16_dec_le,
    lean_int16_dec_lt, lean_int16_div, lean_int16_land, lean_int16_lor, lean_int16_mod,
    lean_int16_mul, lean_int16_neg, lean_int16_of_int, lean_int16_of_nat, lean_int16_shift_left,
    lean_int16_shift_right, lean_int16_sub, lean_int16_to_int, lean_int16_to_int8,
    lean_int16_to_int32, lean_int16_to_int64, lean_int16_to_isize, lean_int16_xor, lean_int32_abs,
    lean_int32_add, lean_int32_complement, lean_int32_dec_eq, lean_int32_dec_le, lean_int32_dec_lt,
    lean_int32_div, lean_int32_land, lean_int32_lor, lean_int32_mod, lean_int32_mul,
    lean_int32_neg, lean_int32_of_int, lean_int32_of_nat, lean_int32_shift_left,
    lean_int32_shift_right, lean_int32_sub, lean_int32_to_int, lean_int32_to_int8,
    lean_int32_to_int16, lean_int32_to_int64, lean_int32_to_isize, lean_int32_xor, lean_int64_abs,
    lean_int64_add, lean_int64_complement, lean_int64_dec_eq, lean_int64_dec_le, lean_int64_dec_lt,
    lean_int64_div, lean_int64_land, lean_int64_lor, lean_int64_mod, lean_int64_mul,
    lean_int64_neg, lean_int64_of_int, lean_int64_of_nat, lean_int64_shift_left,
    lean_int64_shift_right, lean_int64_sub, lean_int64_to_int_sint, lean_int64_to_int8,
    lean_int64_to_int16, lean_int64_to_int32, lean_int64_to_isize, lean_int64_xor, lean_isize_abs,
    lean_isize_add, lean_isize_complement, lean_isize_dec_eq, lean_isize_dec_le, lean_isize_dec_lt,
    lean_isize_div, lean_isize_land, lean_isize_lor, lean_isize_mod, lean_isize_mul,
    lean_isize_neg, lean_isize_of_int, lean_isize_of_nat, lean_isize_shift_left,
    lean_isize_shift_right, lean_isize_sub, lean_isize_to_int, lean_isize_to_int8,
    lean_isize_to_int16, lean_isize_to_int32, lean_isize_to_int64, lean_isize_xor,
};
use crate::ffi::{
    lean_nat_dec_eq, lean_nat_pow, lean_nat_sub, lean_uint8_of_nat_mk, lean_uint8_to_nat,
    lean_uint16_of_nat_mk, lean_uint16_to_nat, lean_uint32_of_nat_mk, lean_uint32_to_nat,
    lean_uint64_of_nat_mk, lean_uint64_to_nat, lean_usize_of_nat_mk, lean_usize_to_nat,
};
pub static mut l_Int8_size: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_instToStringInt8___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_instToStringInt8___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instToStringInt8___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instToStringInt8___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instToStringInt8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instToStringInt8___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_instReprInt8___lam__0___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_instReprInt8___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_instReprInt8___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_instReprInt8___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instReprInt8___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instReprInt8___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instReprInt8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instReprInt8___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instReprAtomInt8: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_instHashableInt8___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_UInt8_toUInt64___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instHashableInt8___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instHashableInt8___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instHashableInt8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instHashableInt8___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Int8_instNeg___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Int8_neg___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Int8_instNeg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Int8_instNeg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Int8_instNeg: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Int8_instNeg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Int8_maxValue___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Int8_maxValue___closed__0: u8 = 0;
pub static mut l_Int8_maxValue: u8 = 0;
static mut l_Int8_minValue___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Int8_minValue___closed__0: u8 = 0;
static mut l_Int8_minValue___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Int8_minValue___closed__1: u8 = 0;
pub static mut l_Int8_minValue: u8 = 0;
static mut l_Int8_ofIntClamp___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Int8_ofIntClamp___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Int8_ofIntClamp___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Int8_ofIntClamp___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Int8_pow___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Int8_pow___closed__0: u8 = 0;
static mut l_instInhabitedInt8___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_instInhabitedInt8___closed__0: u8 = 0;
pub static mut l_instInhabitedInt8: u8 = 0;
pub static l_instAddInt8___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Int8_add___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instAddInt8___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instAddInt8___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instAddInt8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instAddInt8___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instSubInt8___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Int8_sub___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instSubInt8___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instSubInt8___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instSubInt8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instSubInt8___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instMulInt8___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Int8_mul___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instMulInt8___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instMulInt8___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instMulInt8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instMulInt8___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instPowInt8Nat___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Int8_pow___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instPowInt8Nat___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instPowInt8Nat___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instPowInt8Nat: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instPowInt8Nat___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instModInt8___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Int8_mod___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instModInt8___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instModInt8___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instModInt8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instModInt8___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instDivInt8___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Int8_div___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instDivInt8___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instDivInt8___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instDivInt8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instDivInt8___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instLTInt8: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_instLEInt8: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_instComplementInt8___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Int8_complement___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instComplementInt8___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instComplementInt8___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instComplementInt8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instComplementInt8___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instAndOpInt8___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Int8_land___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instAndOpInt8___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instAndOpInt8___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instAndOpInt8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instAndOpInt8___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instOrOpInt8___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Int8_lor___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instOrOpInt8___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instOrOpInt8___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instOrOpInt8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instOrOpInt8___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instXorOpInt8___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Int8_xor___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instXorOpInt8___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instXorOpInt8___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instXorOpInt8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instXorOpInt8___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instShiftLeftInt8___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Int8_shiftLeft___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instShiftLeftInt8___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instShiftLeftInt8___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instShiftLeftInt8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instShiftLeftInt8___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instShiftRightInt8___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Int8_shiftRight___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instShiftRightInt8___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instShiftRightInt8___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instShiftRightInt8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instShiftRightInt8___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instMaxInt8___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_instMaxInt8___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instMaxInt8___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instMaxInt8___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instMaxInt8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instMaxInt8___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instMinInt8___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_instMinInt8___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instMinInt8___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instMinInt8___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instMinInt8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instMinInt8___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Int16_size: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_instToStringInt16___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_instToStringInt16___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instToStringInt16___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instToStringInt16___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instToStringInt16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instToStringInt16___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instReprInt16___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_instReprInt16___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instReprInt16___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instReprInt16___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instReprInt16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instReprInt16___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instReprAtomInt16: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_instHashableInt16___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_UInt16_toUInt64___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instHashableInt16___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instHashableInt16___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instHashableInt16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instHashableInt16___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Int16_instNeg___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Int16_neg___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Int16_instNeg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Int16_instNeg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Int16_instNeg: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Int16_instNeg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Int16_maxValue___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Int16_maxValue___closed__0: u16 = 0;
pub static mut l_Int16_maxValue: u16 = 0;
static mut l_Int16_minValue___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Int16_minValue___closed__0: u16 = 0;
static mut l_Int16_minValue___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Int16_minValue___closed__1: u16 = 0;
pub static mut l_Int16_minValue: u16 = 0;
static mut l_Int16_ofIntClamp___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Int16_ofIntClamp___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Int16_ofIntClamp___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Int16_ofIntClamp___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Int16_pow___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Int16_pow___closed__0: u16 = 0;
static mut l_instInhabitedInt16___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_instInhabitedInt16___closed__0: u16 = 0;
pub static mut l_instInhabitedInt16: u16 = 0;
pub static l_instAddInt16___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Int16_add___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instAddInt16___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instAddInt16___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instAddInt16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instAddInt16___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instSubInt16___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Int16_sub___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instSubInt16___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instSubInt16___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instSubInt16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instSubInt16___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instMulInt16___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Int16_mul___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instMulInt16___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instMulInt16___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instMulInt16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instMulInt16___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instPowInt16Nat___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Int16_pow___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instPowInt16Nat___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instPowInt16Nat___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instPowInt16Nat: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instPowInt16Nat___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instModInt16___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Int16_mod___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instModInt16___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instModInt16___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instModInt16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instModInt16___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instDivInt16___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Int16_div___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instDivInt16___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instDivInt16___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instDivInt16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instDivInt16___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instLTInt16: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_instLEInt16: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_instComplementInt16___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Int16_complement___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instComplementInt16___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instComplementInt16___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instComplementInt16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instComplementInt16___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instAndOpInt16___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Int16_land___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instAndOpInt16___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instAndOpInt16___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instAndOpInt16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instAndOpInt16___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instOrOpInt16___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Int16_lor___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instOrOpInt16___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instOrOpInt16___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instOrOpInt16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instOrOpInt16___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instXorOpInt16___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Int16_xor___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instXorOpInt16___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instXorOpInt16___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instXorOpInt16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instXorOpInt16___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instShiftLeftInt16___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Int16_shiftLeft___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instShiftLeftInt16___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instShiftLeftInt16___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instShiftLeftInt16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instShiftLeftInt16___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instShiftRightInt16___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Int16_shiftRight___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instShiftRightInt16___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instShiftRightInt16___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instShiftRightInt16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instShiftRightInt16___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instMaxInt16___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_instMaxInt16___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instMaxInt16___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instMaxInt16___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instMaxInt16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instMaxInt16___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instMinInt16___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_instMinInt16___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instMinInt16___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instMinInt16___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instMinInt16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instMinInt16___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Int32_size: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_instToStringInt32___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_instToStringInt32___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instToStringInt32___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instToStringInt32___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instToStringInt32: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instToStringInt32___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instReprInt32___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_instReprInt32___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instReprInt32___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instReprInt32___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instReprInt32: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instReprInt32___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instReprAtomInt32: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_instHashableInt32___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_UInt32_toUInt64___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instHashableInt32___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instHashableInt32___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instHashableInt32: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instHashableInt32___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Int32_instNeg___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Int32_neg___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Int32_instNeg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Int32_instNeg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Int32_instNeg: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Int32_instNeg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Int32_maxValue___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Int32_maxValue___closed__0: u32 = 0;
pub static mut l_Int32_maxValue: u32 = 0;
static mut l_Int32_minValue___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Int32_minValue___closed__0: u32 = 0;
static mut l_Int32_minValue___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Int32_minValue___closed__1: u32 = 0;
pub static mut l_Int32_minValue: u32 = 0;
static mut l_Int32_ofIntClamp___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Int32_ofIntClamp___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Int32_ofIntClamp___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Int32_ofIntClamp___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Int32_pow___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Int32_pow___closed__0: u32 = 0;
static mut l_instInhabitedInt32___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_instInhabitedInt32___closed__0: u32 = 0;
pub static mut l_instInhabitedInt32: u32 = 0;
pub static l_instAddInt32___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Int32_add___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instAddInt32___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instAddInt32___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instAddInt32: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instAddInt32___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instSubInt32___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Int32_sub___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instSubInt32___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instSubInt32___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instSubInt32: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instSubInt32___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instMulInt32___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Int32_mul___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instMulInt32___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instMulInt32___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instMulInt32: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instMulInt32___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instPowInt32Nat___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Int32_pow___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instPowInt32Nat___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instPowInt32Nat___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instPowInt32Nat: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instPowInt32Nat___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instModInt32___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Int32_mod___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instModInt32___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instModInt32___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instModInt32: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instModInt32___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instDivInt32___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Int32_div___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instDivInt32___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instDivInt32___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instDivInt32: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instDivInt32___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instLTInt32: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_instLEInt32: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_instComplementInt32___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Int32_complement___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instComplementInt32___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instComplementInt32___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instComplementInt32: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instComplementInt32___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instAndOpInt32___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Int32_land___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instAndOpInt32___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instAndOpInt32___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instAndOpInt32: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instAndOpInt32___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instOrOpInt32___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Int32_lor___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instOrOpInt32___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instOrOpInt32___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instOrOpInt32: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instOrOpInt32___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instXorOpInt32___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Int32_xor___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instXorOpInt32___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instXorOpInt32___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instXorOpInt32: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instXorOpInt32___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instShiftLeftInt32___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Int32_shiftLeft___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instShiftLeftInt32___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instShiftLeftInt32___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instShiftLeftInt32: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instShiftLeftInt32___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instShiftRightInt32___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Int32_shiftRight___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instShiftRightInt32___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instShiftRightInt32___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instShiftRightInt32: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instShiftRightInt32___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instMaxInt32___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_instMaxInt32___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instMaxInt32___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instMaxInt32___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instMaxInt32: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instMaxInt32___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instMinInt32___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_instMinInt32___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instMinInt32___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instMinInt32___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instMinInt32: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instMinInt32___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Int64_size___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Int64_size___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Int64_size: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_instToStringInt64___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_instToStringInt64___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instToStringInt64___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instToStringInt64___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instToStringInt64: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instToStringInt64___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instReprInt64___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_instReprInt64___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instReprInt64___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instReprInt64___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instReprInt64: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instReprInt64___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instReprAtomInt64: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_instHashableInt64___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_instHashableInt64___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instHashableInt64___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instHashableInt64___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instHashableInt64: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instHashableInt64___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Int64_instNeg___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Int64_neg___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Int64_instNeg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Int64_instNeg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Int64_instNeg: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Int64_instNeg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Int64_maxValue___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Int64_maxValue___closed__0: u64 = 0;
pub static mut l_Int64_maxValue: u64 = 0;
static mut l_Int64_minValue___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Int64_minValue___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Int64_minValue___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Int64_minValue___closed__1: u64 = 0;
static mut l_Int64_minValue___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Int64_minValue___closed__2: u64 = 0;
pub static mut l_Int64_minValue: u64 = 0;
static mut l_Int64_ofIntClamp___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Int64_ofIntClamp___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Int64_ofIntClamp___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Int64_ofIntClamp___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Int64_pow___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Int64_pow___closed__0: u64 = 0;
static mut l_instInhabitedInt64___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_instInhabitedInt64___closed__0: u64 = 0;
pub static mut l_instInhabitedInt64: u64 = 0;
pub static l_instAddInt64___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Int64_add___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instAddInt64___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instAddInt64___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instAddInt64: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instAddInt64___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instSubInt64___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Int64_sub___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instSubInt64___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instSubInt64___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instSubInt64: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instSubInt64___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instMulInt64___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Int64_mul___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instMulInt64___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instMulInt64___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instMulInt64: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instMulInt64___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instPowInt64Nat___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Int64_pow___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instPowInt64Nat___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instPowInt64Nat___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instPowInt64Nat: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instPowInt64Nat___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instModInt64___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Int64_mod___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instModInt64___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instModInt64___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instModInt64: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instModInt64___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instDivInt64___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Int64_div___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instDivInt64___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instDivInt64___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instDivInt64: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instDivInt64___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instLTInt64: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_instLEInt64: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_instComplementInt64___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Int64_complement___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instComplementInt64___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instComplementInt64___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instComplementInt64: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instComplementInt64___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instAndOpInt64___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Int64_land___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instAndOpInt64___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instAndOpInt64___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instAndOpInt64: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instAndOpInt64___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instOrOpInt64___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Int64_lor___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instOrOpInt64___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instOrOpInt64___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instOrOpInt64: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instOrOpInt64___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instXorOpInt64___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Int64_xor___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instXorOpInt64___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instXorOpInt64___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instXorOpInt64: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instXorOpInt64___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instShiftLeftInt64___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Int64_shiftLeft___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instShiftLeftInt64___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instShiftLeftInt64___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instShiftLeftInt64: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instShiftLeftInt64___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instShiftRightInt64___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Int64_shiftRight___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instShiftRightInt64___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instShiftRightInt64___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instShiftRightInt64: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instShiftRightInt64___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instMaxInt64___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_instMaxInt64___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instMaxInt64___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instMaxInt64___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instMaxInt64: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instMaxInt64___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instMinInt64___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_instMinInt64___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instMinInt64___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instMinInt64___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instMinInt64: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instMinInt64___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_ISize_size___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_ISize_size___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_ISize_size: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_instToStringISize___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_instToStringISize___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instToStringISize___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instToStringISize___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instToStringISize: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instToStringISize___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instReprISize___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_instReprISize___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instReprISize___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instReprISize___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instReprISize: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instReprISize___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instReprAtomISize: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_instHashableISize___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_USize_toUInt64___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instHashableISize___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instHashableISize___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instHashableISize: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instHashableISize___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_ISize_instNeg___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_ISize_neg___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_ISize_instNeg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_ISize_instNeg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_ISize_instNeg: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_ISize_instNeg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_ISize_maxValue___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_ISize_maxValue___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_ISize_maxValue___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_ISize_maxValue___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_ISize_maxValue___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_ISize_maxValue___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_ISize_maxValue___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_ISize_maxValue___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_ISize_maxValue___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_ISize_maxValue___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_ISize_maxValue___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_ISize_maxValue___closed__5: usize = 0;
pub static mut l_ISize_maxValue: usize = 0;
static mut l_ISize_minValue___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_ISize_minValue___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_ISize_minValue___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_ISize_minValue___closed__1: usize = 0;
pub static mut l_ISize_minValue: usize = 0;
static mut l_ISize_ofIntClamp___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_ISize_ofIntClamp___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_ISize_ofIntClamp___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_ISize_ofIntClamp___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_ISize_pow___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_ISize_pow___closed__0: usize = 0;
static mut l_instInhabitedISize___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_instInhabitedISize___closed__0: usize = 0;
pub static mut l_instInhabitedISize: usize = 0;
pub static l_instAddISize___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_ISize_add___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instAddISize___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instAddISize___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instAddISize: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instAddISize___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instSubISize___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_ISize_sub___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instSubISize___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instSubISize___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instSubISize: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instSubISize___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instMulISize___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_ISize_mul___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instMulISize___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instMulISize___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instMulISize: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instMulISize___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instPowISizeNat___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_ISize_pow___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instPowISizeNat___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instPowISizeNat___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instPowISizeNat: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instPowISizeNat___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instModISize___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_ISize_mod___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instModISize___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instModISize___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instModISize: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instModISize___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instDivISize___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_ISize_div___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instDivISize___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instDivISize___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instDivISize: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instDivISize___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instLTISize: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_instLEISize: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_instComplementISize___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_ISize_complement___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instComplementISize___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instComplementISize___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instComplementISize: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instComplementISize___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instAndOpISize___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_ISize_land___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instAndOpISize___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instAndOpISize___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instAndOpISize: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instAndOpISize___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instOrOpISize___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_ISize_lor___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instOrOpISize___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instOrOpISize___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instOrOpISize: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instOrOpISize___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instXorOpISize___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_ISize_xor___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instXorOpISize___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instXorOpISize___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instXorOpISize: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instXorOpISize___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instShiftLeftISize___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_ISize_shiftLeft___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instShiftLeftISize___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instShiftLeftISize___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instShiftLeftISize: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instShiftLeftISize___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instShiftRightISize___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_ISize_shiftRight___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instShiftRightISize___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instShiftRightISize___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instShiftRightISize: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instShiftRightISize___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instMaxISize___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_instMaxISize___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instMaxISize___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instMaxISize___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instMaxISize: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instMaxISize___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instMinISize___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_instMinISize___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instMinISize___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instMinISize___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instMinISize: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instMinISize___closed__0_value) as *mut crate::leanh::LeanObject;
pub unsafe fn _init_l_Int8_size() -> *mut crate::leanh::LeanObject {
    let mut v___x_1841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1841_ = crate::leanh::lean_unsigned_to_nat(256);
    return v___x_1841_;
}
pub unsafe fn l_Int8_toBitVec(mut v_x_1842_: u8) -> *mut crate::leanh::LeanObject {
    let mut v___x_1843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1843_ = lean_uint8_to_nat(v_x_1842_);
    return v___x_1843_;
}
pub unsafe fn l_Int8_toBitVec___boxed(
    mut v_x_1844_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_1845_: u8 = 0;
    let mut v_res_1846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_1845_ = (crate::leanh::lean_unbox(v_x_1844_) as u8);
    v_res_1846_ = l_Int8_toBitVec(v_x_boxed_1845_);
    return v_res_1846_;
}
pub unsafe fn l_UInt8_toInt8(mut v_i_1847_: u8) -> u8 {
    return v_i_1847_;
}
pub unsafe fn l_UInt8_toInt8___boxed(
    mut v_i_1848_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_1849_: u8 = 0;
    let mut v_res_1850_: u8 = 0;
    let mut v_r_1851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1849_ = (crate::leanh::lean_unbox(v_i_1848_) as u8);
    v_res_1850_ = l_UInt8_toInt8(v_i_boxed_1849_);
    v_r_1851_ = crate::leanh::lean_box((v_res_1850_) as usize);
    return v_r_1851_;
}
pub unsafe fn l_Int8_ofInt___boxed(
    mut v_i_1853_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1854_: u8 = 0;
    let mut v_r_1855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1854_ = lean_int8_of_int(v_i_1853_);
    crate::leanh::lean_dec(v_i_1853_);
    v_r_1855_ = crate::leanh::lean_box((v_res_1854_) as usize);
    return v_r_1855_;
}
pub unsafe fn l_Int8_ofNat___boxed(
    mut v_n_1857_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1858_: u8 = 0;
    let mut v_r_1859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1858_ = lean_int8_of_nat(v_n_1857_);
    crate::leanh::lean_dec(v_n_1857_);
    v_r_1859_ = crate::leanh::lean_box((v_res_1858_) as usize);
    return v_r_1859_;
}
pub unsafe fn l_Int_toInt8(mut v_i_1860_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v___x_1861_: u8 = 0;
    v___x_1861_ = lean_int8_of_int(v_i_1860_);
    return v___x_1861_;
}
pub unsafe fn l_Int_toInt8___boxed(
    mut v_i_1862_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1863_: u8 = 0;
    let mut v_r_1864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1863_ = l_Int_toInt8(v_i_1862_);
    crate::leanh::lean_dec(v_i_1862_);
    v_r_1864_ = crate::leanh::lean_box((v_res_1863_) as usize);
    return v_r_1864_;
}
pub unsafe fn l_Nat_toInt8(mut v_n_1865_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v___x_1866_: u8 = 0;
    v___x_1866_ = lean_int8_of_nat(v_n_1865_);
    return v___x_1866_;
}
pub unsafe fn l_Nat_toInt8___boxed(
    mut v_n_1867_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1868_: u8 = 0;
    let mut v_r_1869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1868_ = l_Nat_toInt8(v_n_1867_);
    crate::leanh::lean_dec(v_n_1867_);
    v_r_1869_ = crate::leanh::lean_box((v_res_1868_) as usize);
    return v_r_1869_;
}
pub unsafe fn l_Int8_toInt___boxed(
    mut v_i_1871_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_1872_: u8 = 0;
    let mut v_res_1873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1872_ = (crate::leanh::lean_unbox(v_i_1871_) as u8);
    v_res_1873_ = lean_int8_to_int(v_i_boxed_1872_);
    return v_res_1873_;
}
pub unsafe fn l_Int8_toNatClampNeg(mut v_i_1874_: u8) -> *mut crate::leanh::LeanObject {
    let mut v___x_1875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1875_ = lean_int8_to_int(v_i_1874_);
    v___x_1876_ = l_Int_toNat(v___x_1875_);
    return v___x_1876_;
}
pub unsafe fn l_Int8_toNatClampNeg___boxed(
    mut v_i_1877_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_1878_: u8 = 0;
    let mut v_res_1879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1878_ = (crate::leanh::lean_unbox(v_i_1877_) as u8);
    v_res_1879_ = l_Int8_toNatClampNeg(v_i_boxed_1878_);
    return v_res_1879_;
}
pub unsafe fn l_Int8_ofBitVec(mut v_b_1880_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v___x_1881_: u8 = 0;
    v___x_1881_ = lean_uint8_of_nat_mk(v_b_1880_);
    return v___x_1881_;
}
pub unsafe fn l_Int8_ofBitVec___boxed(
    mut v_b_1882_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1883_: u8 = 0;
    let mut v_r_1884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1883_ = l_Int8_ofBitVec(v_b_1882_);
    v_r_1884_ = crate::leanh::lean_box((v_res_1883_) as usize);
    return v_r_1884_;
}
pub unsafe fn l_Int8_neg___boxed(
    mut v_i_1886_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_1887_: u8 = 0;
    let mut v_res_1888_: u8 = 0;
    let mut v_r_1889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1887_ = (crate::leanh::lean_unbox(v_i_1886_) as u8);
    v_res_1888_ = lean_int8_neg(v_i_boxed_1887_);
    v_r_1889_ = crate::leanh::lean_box((v_res_1888_) as usize);
    return v_r_1889_;
}
pub unsafe fn l_instToStringInt8___lam__0(mut v_i_1890_: u8) -> *mut crate::leanh::LeanObject {
    let mut v___x_1891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1891_ = lean_int8_to_int(v_i_1890_);
    v___x_1892_ = l_Int_repr(v___x_1891_);
    return v___x_1892_;
}
pub unsafe fn l_instToStringInt8___lam__0___boxed(
    mut v_i_1893_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_1894_: u8 = 0;
    let mut v_res_1895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1894_ = (crate::leanh::lean_unbox(v_i_1893_) as u8);
    v_res_1895_ = l_instToStringInt8___lam__0(v_i_boxed_1894_);
    return v_res_1895_;
}
pub unsafe fn _init_l_instReprInt8___lam__0___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_1898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1898_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1899_ = lean_nat_to_int(v___x_1898_);
    return v___x_1899_;
}
pub unsafe fn l_instReprInt8___lam__0(
    mut v_i_1900_: u8,
    mut v_prec_1901_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1904_: u8 = 0;
    v___x_1902_ = lean_int8_to_int(v_i_1900_);
    v___x_1903_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_instReprInt8___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_instReprInt8___lam__0___closed__0_once),
        _init_l_instReprInt8___lam__0___closed__0,
    );
    v___x_1904_ = lean_int_dec_lt(v___x_1902_, v___x_1903_);
    if v___x_1904_ == 0 {
        let mut v___x_1905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1905_ = l_Int_repr(v___x_1902_);
        v___x_1906_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1906_, 0, v___x_1905_);
        return v___x_1906_;
    } else {
        let mut v___x_1907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1907_ = l_Int_repr(v___x_1902_);
        v___x_1908_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1908_, 0, v___x_1907_);
        v___x_1909_ = l_Repr_addAppParen(v___x_1908_, v_prec_1901_);
        return v___x_1909_;
    }
}
pub unsafe fn l_instReprInt8___lam__0___boxed(
    mut v_i_1910_: *mut crate::leanh::LeanObject,
    mut v_prec_1911_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_1912_: u8 = 0;
    let mut v_res_1913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1912_ = (crate::leanh::lean_unbox(v_i_1910_) as u8);
    v_res_1913_ = l_instReprInt8___lam__0(v_i_boxed_1912_, v_prec_1911_);
    crate::leanh::lean_dec(v_prec_1911_);
    return v_res_1913_;
}
pub unsafe fn _init_l_instReprAtomInt8() -> *mut crate::leanh::LeanObject {
    let mut v___x_1916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1916_ = crate::leanh::lean_box(0);
    return v___x_1916_;
}
pub unsafe fn l_Int8_instOfNat(mut v_n_1919_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v___x_1920_: u8 = 0;
    v___x_1920_ = lean_int8_of_nat(v_n_1919_);
    return v___x_1920_;
}
pub unsafe fn l_Int8_instOfNat___boxed(
    mut v_n_1921_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1922_: u8 = 0;
    let mut v_r_1923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1922_ = l_Int8_instOfNat(v_n_1921_);
    crate::leanh::lean_dec(v_n_1921_);
    v_r_1923_ = crate::leanh::lean_box((v_res_1922_) as usize);
    return v_r_1923_;
}
pub unsafe fn _init_l_Int8_maxValue___closed__0() -> u8 {
    let mut v___x_1926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1927_: u8 = 0;
    v___x_1926_ = crate::leanh::lean_unsigned_to_nat(127);
    v___x_1927_ = lean_int8_of_nat(v___x_1926_);
    return v___x_1927_;
}
pub unsafe fn _init_l_Int8_maxValue() -> u8 {
    let mut v___x_1928_: u8 = 0;
    v___x_1928_ = crate::leanh::lean_uint8_once(
        core::ptr::addr_of_mut!(l_Int8_maxValue___closed__0),
        core::ptr::addr_of_mut!(l_Int8_maxValue___closed__0_once),
        _init_l_Int8_maxValue___closed__0,
    );
    return v___x_1928_;
}
pub unsafe fn _init_l_Int8_minValue___closed__0() -> u8 {
    let mut v___x_1929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1930_: u8 = 0;
    v___x_1929_ = crate::leanh::lean_unsigned_to_nat(128);
    v___x_1930_ = lean_int8_of_nat(v___x_1929_);
    return v___x_1930_;
}
pub unsafe fn _init_l_Int8_minValue___closed__1() -> u8 {
    let mut v___x_1931_: u8 = 0;
    let mut v___x_1932_: u8 = 0;
    v___x_1931_ = crate::leanh::lean_uint8_once(
        core::ptr::addr_of_mut!(l_Int8_minValue___closed__0),
        core::ptr::addr_of_mut!(l_Int8_minValue___closed__0_once),
        _init_l_Int8_minValue___closed__0,
    );
    v___x_1932_ = lean_int8_neg(v___x_1931_);
    return v___x_1932_;
}
pub unsafe fn _init_l_Int8_minValue() -> u8 {
    let mut v___x_1933_: u8 = 0;
    v___x_1933_ = crate::leanh::lean_uint8_once(
        core::ptr::addr_of_mut!(l_Int8_minValue___closed__1),
        core::ptr::addr_of_mut!(l_Int8_minValue___closed__1_once),
        _init_l_Int8_minValue___closed__1,
    );
    return v___x_1933_;
}
pub unsafe fn l_Int8_ofIntLE___redArg(mut v_i_1934_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v___x_1935_: u8 = 0;
    v___x_1935_ = lean_int8_of_int(v_i_1934_);
    return v___x_1935_;
}
pub unsafe fn l_Int8_ofIntLE___redArg___boxed(
    mut v_i_1936_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1937_: u8 = 0;
    let mut v_r_1938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1937_ = l_Int8_ofIntLE___redArg(v_i_1936_);
    crate::leanh::lean_dec(v_i_1936_);
    v_r_1938_ = crate::leanh::lean_box((v_res_1937_) as usize);
    return v_r_1938_;
}
pub unsafe fn l_Int8_ofIntLE(
    mut v_i_1939_: *mut crate::leanh::LeanObject,
    mut v___hl_1940_: *mut crate::leanh::LeanObject,
    mut v___hr_1941_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1942_: u8 = 0;
    v___x_1942_ = lean_int8_of_int(v_i_1939_);
    return v___x_1942_;
}
pub unsafe fn l_Int8_ofIntLE___boxed(
    mut v_i_1943_: *mut crate::leanh::LeanObject,
    mut v___hl_1944_: *mut crate::leanh::LeanObject,
    mut v___hr_1945_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1946_: u8 = 0;
    let mut v_r_1947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1946_ = l_Int8_ofIntLE(v_i_1943_, v___hl_1944_, v___hr_1945_);
    crate::leanh::lean_dec(v_i_1943_);
    v_r_1947_ = crate::leanh::lean_box((v_res_1946_) as usize);
    return v_r_1947_;
}
pub unsafe fn _init_l_Int8_ofIntClamp___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_1948_: u8 = 0;
    let mut v___x_1949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1948_ = crate::leanh::lean_uint8_once(
        core::ptr::addr_of_mut!(l_Int8_minValue___closed__1),
        core::ptr::addr_of_mut!(l_Int8_minValue___closed__1_once),
        _init_l_Int8_minValue___closed__1,
    );
    v___x_1949_ = lean_int8_to_int(v___x_1948_);
    return v___x_1949_;
}
pub unsafe fn _init_l_Int8_ofIntClamp___closed__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_1950_: u8 = 0;
    let mut v___x_1951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1950_ = crate::leanh::lean_uint8_once(
        core::ptr::addr_of_mut!(l_Int8_maxValue___closed__0),
        core::ptr::addr_of_mut!(l_Int8_maxValue___closed__0_once),
        _init_l_Int8_maxValue___closed__0,
    );
    v___x_1951_ = lean_int8_to_int(v___x_1950_);
    return v___x_1951_;
}
pub unsafe fn l_Int8_ofIntClamp(mut v_i_1952_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v___x_1953_: u8 = 0;
    let mut v___x_1954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1955_: u8 = 0;
    v___x_1953_ = crate::leanh::lean_uint8_once(
        core::ptr::addr_of_mut!(l_Int8_minValue___closed__1),
        core::ptr::addr_of_mut!(l_Int8_minValue___closed__1_once),
        _init_l_Int8_minValue___closed__1,
    );
    v___x_1954_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Int8_ofIntClamp___closed__0),
        core::ptr::addr_of_mut!(l_Int8_ofIntClamp___closed__0_once),
        _init_l_Int8_ofIntClamp___closed__0,
    );
    v___x_1955_ = lean_int_dec_le(v___x_1954_, v_i_1952_);
    if v___x_1955_ == 0 {
        return v___x_1953_;
    } else {
        let mut v___x_1956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1957_: u8 = 0;
        v___x_1956_ = crate::leanh::lean_obj_once(
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
pub unsafe fn l_Int8_ofIntClamp___boxed(
    mut v_i_1959_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1960_: u8 = 0;
    let mut v_r_1961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1960_ = l_Int8_ofIntClamp(v_i_1959_);
    crate::leanh::lean_dec(v_i_1959_);
    v_r_1961_ = crate::leanh::lean_box((v_res_1960_) as usize);
    return v_r_1961_;
}
pub unsafe fn l_Int8_ofIntTruncate(mut v_i_1962_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v___x_1963_: u8 = 0;
    v___x_1963_ = l_Int8_ofIntClamp(v_i_1962_);
    return v___x_1963_;
}
pub unsafe fn l_Int8_ofIntTruncate___boxed(
    mut v_i_1964_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1965_: u8 = 0;
    let mut v_r_1966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1965_ = l_Int8_ofIntTruncate(v_i_1964_);
    crate::leanh::lean_dec(v_i_1964_);
    v_r_1966_ = crate::leanh::lean_box((v_res_1965_) as usize);
    return v_r_1966_;
}
pub unsafe fn l_Int8_add___boxed(
    mut v_a_1969_: *mut crate::leanh::LeanObject,
    mut v_b_1970_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_1971_: u8 = 0;
    let mut v_b_boxed_1972_: u8 = 0;
    let mut v_res_1973_: u8 = 0;
    let mut v_r_1974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_1971_ = (crate::leanh::lean_unbox(v_a_1969_) as u8);
    v_b_boxed_1972_ = (crate::leanh::lean_unbox(v_b_1970_) as u8);
    v_res_1973_ = lean_int8_add(v_a_boxed_1971_, v_b_boxed_1972_);
    v_r_1974_ = crate::leanh::lean_box((v_res_1973_) as usize);
    return v_r_1974_;
}
pub unsafe fn l_Int8_sub___boxed(
    mut v_a_1977_: *mut crate::leanh::LeanObject,
    mut v_b_1978_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_1979_: u8 = 0;
    let mut v_b_boxed_1980_: u8 = 0;
    let mut v_res_1981_: u8 = 0;
    let mut v_r_1982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_1979_ = (crate::leanh::lean_unbox(v_a_1977_) as u8);
    v_b_boxed_1980_ = (crate::leanh::lean_unbox(v_b_1978_) as u8);
    v_res_1981_ = lean_int8_sub(v_a_boxed_1979_, v_b_boxed_1980_);
    v_r_1982_ = crate::leanh::lean_box((v_res_1981_) as usize);
    return v_r_1982_;
}
pub unsafe fn l_Int8_mul___boxed(
    mut v_a_1985_: *mut crate::leanh::LeanObject,
    mut v_b_1986_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_1987_: u8 = 0;
    let mut v_b_boxed_1988_: u8 = 0;
    let mut v_res_1989_: u8 = 0;
    let mut v_r_1990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_1987_ = (crate::leanh::lean_unbox(v_a_1985_) as u8);
    v_b_boxed_1988_ = (crate::leanh::lean_unbox(v_b_1986_) as u8);
    v_res_1989_ = lean_int8_mul(v_a_boxed_1987_, v_b_boxed_1988_);
    v_r_1990_ = crate::leanh::lean_box((v_res_1989_) as usize);
    return v_r_1990_;
}
pub unsafe fn l_Int8_div___boxed(
    mut v_a_1993_: *mut crate::leanh::LeanObject,
    mut v_b_1994_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_1995_: u8 = 0;
    let mut v_b_boxed_1996_: u8 = 0;
    let mut v_res_1997_: u8 = 0;
    let mut v_r_1998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_1995_ = (crate::leanh::lean_unbox(v_a_1993_) as u8);
    v_b_boxed_1996_ = (crate::leanh::lean_unbox(v_b_1994_) as u8);
    v_res_1997_ = lean_int8_div(v_a_boxed_1995_, v_b_boxed_1996_);
    v_r_1998_ = crate::leanh::lean_box((v_res_1997_) as usize);
    return v_r_1998_;
}
pub unsafe fn _init_l_Int8_pow___closed__0() -> u8 {
    let mut v___x_1999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2000_: u8 = 0;
    v___x_1999_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_2000_ = lean_int8_of_nat(v___x_1999_);
    return v___x_2000_;
}
pub unsafe fn l_Int8_pow(mut v_x_2001_: u8, mut v_n_2002_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v_zero_2003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_2004_: u8 = 0;
    v_zero_2003_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_2004_ = lean_nat_dec_eq(v_n_2002_, v_zero_2003_);
    if v_isZero_2004_ == 1 {
        let mut v___x_2005_: u8 = 0;
        v___x_2005_ = crate::leanh::lean_uint8_once(
            core::ptr::addr_of_mut!(l_Int8_pow___closed__0),
            core::ptr::addr_of_mut!(l_Int8_pow___closed__0_once),
            _init_l_Int8_pow___closed__0,
        );
        return v___x_2005_;
    } else {
        let mut v_one_2006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_2007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2008_: u8 = 0;
        let mut v___x_2009_: u8 = 0;
        v_one_2006_ = crate::leanh::lean_unsigned_to_nat(1);
        v_n_2007_ = lean_nat_sub(v_n_2002_, v_one_2006_);
        v___x_2008_ = l_Int8_pow(v_x_2001_, v_n_2007_);
        crate::leanh::lean_dec(v_n_2007_);
        v___x_2009_ = lean_int8_mul(v___x_2008_, v_x_2001_);
        return v___x_2009_;
    }
}
pub unsafe fn l_Int8_pow___boxed(
    mut v_x_2010_: *mut crate::leanh::LeanObject,
    mut v_n_2011_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_2012_: u8 = 0;
    let mut v_res_2013_: u8 = 0;
    let mut v_r_2014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_2012_ = (crate::leanh::lean_unbox(v_x_2010_) as u8);
    v_res_2013_ = l_Int8_pow(v_x_boxed_2012_, v_n_2011_);
    crate::leanh::lean_dec(v_n_2011_);
    v_r_2014_ = crate::leanh::lean_box((v_res_2013_) as usize);
    return v_r_2014_;
}
pub unsafe fn l_Int8_mod___boxed(
    mut v_a_2017_: *mut crate::leanh::LeanObject,
    mut v_b_2018_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_2019_: u8 = 0;
    let mut v_b_boxed_2020_: u8 = 0;
    let mut v_res_2021_: u8 = 0;
    let mut v_r_2022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_2019_ = (crate::leanh::lean_unbox(v_a_2017_) as u8);
    v_b_boxed_2020_ = (crate::leanh::lean_unbox(v_b_2018_) as u8);
    v_res_2021_ = lean_int8_mod(v_a_boxed_2019_, v_b_boxed_2020_);
    v_r_2022_ = crate::leanh::lean_box((v_res_2021_) as usize);
    return v_r_2022_;
}
pub unsafe fn l_Int8_land___boxed(
    mut v_a_2025_: *mut crate::leanh::LeanObject,
    mut v_b_2026_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_2027_: u8 = 0;
    let mut v_b_boxed_2028_: u8 = 0;
    let mut v_res_2029_: u8 = 0;
    let mut v_r_2030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_2027_ = (crate::leanh::lean_unbox(v_a_2025_) as u8);
    v_b_boxed_2028_ = (crate::leanh::lean_unbox(v_b_2026_) as u8);
    v_res_2029_ = lean_int8_land(v_a_boxed_2027_, v_b_boxed_2028_);
    v_r_2030_ = crate::leanh::lean_box((v_res_2029_) as usize);
    return v_r_2030_;
}
pub unsafe fn l_Int8_lor___boxed(
    mut v_a_2033_: *mut crate::leanh::LeanObject,
    mut v_b_2034_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_2035_: u8 = 0;
    let mut v_b_boxed_2036_: u8 = 0;
    let mut v_res_2037_: u8 = 0;
    let mut v_r_2038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_2035_ = (crate::leanh::lean_unbox(v_a_2033_) as u8);
    v_b_boxed_2036_ = (crate::leanh::lean_unbox(v_b_2034_) as u8);
    v_res_2037_ = lean_int8_lor(v_a_boxed_2035_, v_b_boxed_2036_);
    v_r_2038_ = crate::leanh::lean_box((v_res_2037_) as usize);
    return v_r_2038_;
}
pub unsafe fn l_Int8_xor___boxed(
    mut v_a_2041_: *mut crate::leanh::LeanObject,
    mut v_b_2042_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_2043_: u8 = 0;
    let mut v_b_boxed_2044_: u8 = 0;
    let mut v_res_2045_: u8 = 0;
    let mut v_r_2046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_2043_ = (crate::leanh::lean_unbox(v_a_2041_) as u8);
    v_b_boxed_2044_ = (crate::leanh::lean_unbox(v_b_2042_) as u8);
    v_res_2045_ = lean_int8_xor(v_a_boxed_2043_, v_b_boxed_2044_);
    v_r_2046_ = crate::leanh::lean_box((v_res_2045_) as usize);
    return v_r_2046_;
}
pub unsafe fn l_Int8_shiftLeft___boxed(
    mut v_a_2049_: *mut crate::leanh::LeanObject,
    mut v_b_2050_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_2051_: u8 = 0;
    let mut v_b_boxed_2052_: u8 = 0;
    let mut v_res_2053_: u8 = 0;
    let mut v_r_2054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_2051_ = (crate::leanh::lean_unbox(v_a_2049_) as u8);
    v_b_boxed_2052_ = (crate::leanh::lean_unbox(v_b_2050_) as u8);
    v_res_2053_ = lean_int8_shift_left(v_a_boxed_2051_, v_b_boxed_2052_);
    v_r_2054_ = crate::leanh::lean_box((v_res_2053_) as usize);
    return v_r_2054_;
}
pub unsafe fn l_Int8_shiftRight___boxed(
    mut v_a_2057_: *mut crate::leanh::LeanObject,
    mut v_b_2058_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_2059_: u8 = 0;
    let mut v_b_boxed_2060_: u8 = 0;
    let mut v_res_2061_: u8 = 0;
    let mut v_r_2062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_2059_ = (crate::leanh::lean_unbox(v_a_2057_) as u8);
    v_b_boxed_2060_ = (crate::leanh::lean_unbox(v_b_2058_) as u8);
    v_res_2061_ = lean_int8_shift_right(v_a_boxed_2059_, v_b_boxed_2060_);
    v_r_2062_ = crate::leanh::lean_box((v_res_2061_) as usize);
    return v_r_2062_;
}
pub unsafe fn l_Int8_complement___boxed(
    mut v_a_2064_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_2065_: u8 = 0;
    let mut v_res_2066_: u8 = 0;
    let mut v_r_2067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_2065_ = (crate::leanh::lean_unbox(v_a_2064_) as u8);
    v_res_2066_ = lean_int8_complement(v_a_boxed_2065_);
    v_r_2067_ = crate::leanh::lean_box((v_res_2066_) as usize);
    return v_r_2067_;
}
pub unsafe fn l_Int8_abs___boxed(
    mut v_a_2069_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_2070_: u8 = 0;
    let mut v_res_2071_: u8 = 0;
    let mut v_r_2072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_2070_ = (crate::leanh::lean_unbox(v_a_2069_) as u8);
    v_res_2071_ = lean_int8_abs(v_a_boxed_2070_);
    v_r_2072_ = crate::leanh::lean_box((v_res_2071_) as usize);
    return v_r_2072_;
}
pub unsafe fn l_Int8_decEq___boxed(
    mut v_a_2075_: *mut crate::leanh::LeanObject,
    mut v_b_2076_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_2077_: u8 = 0;
    let mut v_b_boxed_2078_: u8 = 0;
    let mut v_res_2079_: u8 = 0;
    let mut v_r_2080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_2077_ = (crate::leanh::lean_unbox(v_a_2075_) as u8);
    v_b_boxed_2078_ = (crate::leanh::lean_unbox(v_b_2076_) as u8);
    v_res_2079_ = lean_int8_dec_eq(v_a_boxed_2077_, v_b_boxed_2078_);
    v_r_2080_ = crate::leanh::lean_box((v_res_2079_) as usize);
    return v_r_2080_;
}
pub unsafe fn _init_l_instInhabitedInt8___closed__0() -> u8 {
    let mut v___x_2081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2082_: u8 = 0;
    v___x_2081_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2082_ = lean_int8_of_nat(v___x_2081_);
    return v___x_2082_;
}
pub unsafe fn _init_l_instInhabitedInt8() -> u8 {
    let mut v___x_2083_: u8 = 0;
    v___x_2083_ = crate::leanh::lean_uint8_once(
        core::ptr::addr_of_mut!(l_instInhabitedInt8___closed__0),
        core::ptr::addr_of_mut!(l_instInhabitedInt8___closed__0_once),
        _init_l_instInhabitedInt8___closed__0,
    );
    return v___x_2083_;
}
pub unsafe fn _init_l_instLTInt8() -> *mut crate::leanh::LeanObject {
    let mut v___x_2096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2096_ = crate::leanh::lean_box(0);
    return v___x_2096_;
}
pub unsafe fn _init_l_instLEInt8() -> *mut crate::leanh::LeanObject {
    let mut v___x_2097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2097_ = crate::leanh::lean_box(0);
    return v___x_2097_;
}
pub unsafe fn l_instDecidableEqInt8(mut v_a_2110_: u8, mut v_b_2111_: u8) -> u8 {
    let mut v___x_2112_: u8 = 0;
    v___x_2112_ = lean_int8_dec_eq(v_a_2110_, v_b_2111_);
    return v___x_2112_;
}
pub unsafe fn l_instDecidableEqInt8___boxed(
    mut v_a_2113_: *mut crate::leanh::LeanObject,
    mut v_b_2114_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_2115_: u8 = 0;
    let mut v_b_boxed_2116_: u8 = 0;
    let mut v_res_2117_: u8 = 0;
    let mut v_r_2118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_2115_ = (crate::leanh::lean_unbox(v_a_2113_) as u8);
    v_b_boxed_2116_ = (crate::leanh::lean_unbox(v_b_2114_) as u8);
    v_res_2117_ = l_instDecidableEqInt8(v_a_boxed_2115_, v_b_boxed_2116_);
    v_r_2118_ = crate::leanh::lean_box((v_res_2117_) as usize);
    return v_r_2118_;
}
pub unsafe fn l_Bool_toInt8___boxed(
    mut v_b_2120_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_b_boxed_2121_: u8 = 0;
    let mut v_res_2122_: u8 = 0;
    let mut v_r_2123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_b_boxed_2121_ = (crate::leanh::lean_unbox(v_b_2120_) as u8);
    v_res_2122_ = lean_bool_to_int8(v_b_boxed_2121_);
    v_r_2123_ = crate::leanh::lean_box((v_res_2122_) as usize);
    return v_r_2123_;
}
pub unsafe fn l_Int8_decLt___aux__1(mut v_a_2124_: u8, mut v_b_2125_: u8) -> u8 {
    let mut v___x_2126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2129_: u8 = 0;
    v___x_2126_ = crate::leanh::lean_unsigned_to_nat(8);
    v___x_2127_ = lean_uint8_to_nat(v_a_2124_);
    v___x_2128_ = lean_uint8_to_nat(v_b_2125_);
    v___x_2129_ = l_BitVec_slt(v___x_2126_, v___x_2127_, v___x_2128_);
    return v___x_2129_;
}
pub unsafe fn l_Int8_decLt___aux__1___boxed(
    mut v_a_2130_: *mut crate::leanh::LeanObject,
    mut v_b_2131_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_2132_: u8 = 0;
    let mut v_b_boxed_2133_: u8 = 0;
    let mut v_res_2134_: u8 = 0;
    let mut v_r_2135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_2132_ = (crate::leanh::lean_unbox(v_a_2130_) as u8);
    v_b_boxed_2133_ = (crate::leanh::lean_unbox(v_b_2131_) as u8);
    v_res_2134_ = l_Int8_decLt___aux__1(v_a_boxed_2132_, v_b_boxed_2133_);
    v_r_2135_ = crate::leanh::lean_box((v_res_2134_) as usize);
    return v_r_2135_;
}
pub unsafe fn l_Int8_decLt___boxed(
    mut v_a_2138_: *mut crate::leanh::LeanObject,
    mut v_b_2139_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_2140_: u8 = 0;
    let mut v_b_boxed_2141_: u8 = 0;
    let mut v_res_2142_: u8 = 0;
    let mut v_r_2143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_2140_ = (crate::leanh::lean_unbox(v_a_2138_) as u8);
    v_b_boxed_2141_ = (crate::leanh::lean_unbox(v_b_2139_) as u8);
    v_res_2142_ = lean_int8_dec_lt(v_a_boxed_2140_, v_b_boxed_2141_);
    v_r_2143_ = crate::leanh::lean_box((v_res_2142_) as usize);
    return v_r_2143_;
}
pub unsafe fn l_Int8_decLe___aux__1(mut v_a_2144_: u8, mut v_b_2145_: u8) -> u8 {
    let mut v___x_2146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2149_: u8 = 0;
    v___x_2146_ = crate::leanh::lean_unsigned_to_nat(8);
    v___x_2147_ = lean_uint8_to_nat(v_a_2144_);
    v___x_2148_ = lean_uint8_to_nat(v_b_2145_);
    v___x_2149_ = l_BitVec_sle(v___x_2146_, v___x_2147_, v___x_2148_);
    return v___x_2149_;
}
pub unsafe fn l_Int8_decLe___aux__1___boxed(
    mut v_a_2150_: *mut crate::leanh::LeanObject,
    mut v_b_2151_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_2152_: u8 = 0;
    let mut v_b_boxed_2153_: u8 = 0;
    let mut v_res_2154_: u8 = 0;
    let mut v_r_2155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_2152_ = (crate::leanh::lean_unbox(v_a_2150_) as u8);
    v_b_boxed_2153_ = (crate::leanh::lean_unbox(v_b_2151_) as u8);
    v_res_2154_ = l_Int8_decLe___aux__1(v_a_boxed_2152_, v_b_boxed_2153_);
    v_r_2155_ = crate::leanh::lean_box((v_res_2154_) as usize);
    return v_r_2155_;
}
pub unsafe fn l_Int8_decLe___boxed(
    mut v_a_2158_: *mut crate::leanh::LeanObject,
    mut v_b_2159_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_2160_: u8 = 0;
    let mut v_b_boxed_2161_: u8 = 0;
    let mut v_res_2162_: u8 = 0;
    let mut v_r_2163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_2160_ = (crate::leanh::lean_unbox(v_a_2158_) as u8);
    v_b_boxed_2161_ = (crate::leanh::lean_unbox(v_b_2159_) as u8);
    v_res_2162_ = lean_int8_dec_le(v_a_boxed_2160_, v_b_boxed_2161_);
    v_r_2163_ = crate::leanh::lean_box((v_res_2162_) as usize);
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
    mut v_x_2167_: *mut crate::leanh::LeanObject,
    mut v_y_2168_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_2169_: u8 = 0;
    let mut v_y_boxed_2170_: u8 = 0;
    let mut v_res_2171_: u8 = 0;
    let mut v_r_2172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_2169_ = (crate::leanh::lean_unbox(v_x_2167_) as u8);
    v_y_boxed_2170_ = (crate::leanh::lean_unbox(v_y_2168_) as u8);
    v_res_2171_ = l_instMaxInt8___lam__0(v_x_boxed_2169_, v_y_boxed_2170_);
    v_r_2172_ = crate::leanh::lean_box((v_res_2171_) as usize);
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
    mut v_x_2178_: *mut crate::leanh::LeanObject,
    mut v_y_2179_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_2180_: u8 = 0;
    let mut v_y_boxed_2181_: u8 = 0;
    let mut v_res_2182_: u8 = 0;
    let mut v_r_2183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_2180_ = (crate::leanh::lean_unbox(v_x_2178_) as u8);
    v_y_boxed_2181_ = (crate::leanh::lean_unbox(v_y_2179_) as u8);
    v_res_2182_ = l_instMinInt8___lam__0(v_x_boxed_2180_, v_y_boxed_2181_);
    v_r_2183_ = crate::leanh::lean_box((v_res_2182_) as usize);
    return v_r_2183_;
}
pub unsafe fn _init_l_Int16_size() -> *mut crate::leanh::LeanObject {
    let mut v___x_2186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2186_ = crate::leanh::lean_unsigned_to_nat(65536);
    return v___x_2186_;
}
pub unsafe fn l_Int16_toBitVec(mut v_x_2187_: u16) -> *mut crate::leanh::LeanObject {
    let mut v___x_2188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2188_ = lean_uint16_to_nat(v_x_2187_);
    return v___x_2188_;
}
pub unsafe fn l_Int16_toBitVec___boxed(
    mut v_x_2189_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_2190_: u16 = 0;
    let mut v_res_2191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_2190_ = (crate::leanh::lean_unbox(v_x_2189_) as u16);
    v_res_2191_ = l_Int16_toBitVec(v_x_boxed_2190_);
    return v_res_2191_;
}
pub unsafe fn l_UInt16_toInt16(mut v_i_2192_: u16) -> u16 {
    return v_i_2192_;
}
pub unsafe fn l_UInt16_toInt16___boxed(
    mut v_i_2193_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_2194_: u16 = 0;
    let mut v_res_2195_: u16 = 0;
    let mut v_r_2196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2194_ = (crate::leanh::lean_unbox(v_i_2193_) as u16);
    v_res_2195_ = l_UInt16_toInt16(v_i_boxed_2194_);
    v_r_2196_ = crate::leanh::lean_box((v_res_2195_) as usize);
    return v_r_2196_;
}
pub unsafe fn l_Int16_ofInt___boxed(
    mut v_i_2198_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2199_: u16 = 0;
    let mut v_r_2200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2199_ = lean_int16_of_int(v_i_2198_);
    crate::leanh::lean_dec(v_i_2198_);
    v_r_2200_ = crate::leanh::lean_box((v_res_2199_) as usize);
    return v_r_2200_;
}
pub unsafe fn l_Int16_ofNat___boxed(
    mut v_n_2202_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2203_: u16 = 0;
    let mut v_r_2204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2203_ = lean_int16_of_nat(v_n_2202_);
    crate::leanh::lean_dec(v_n_2202_);
    v_r_2204_ = crate::leanh::lean_box((v_res_2203_) as usize);
    return v_r_2204_;
}
pub unsafe fn l_Int_toInt16(mut v_i_2205_: *mut crate::leanh::LeanObject) -> u16 {
    let mut v___x_2206_: u16 = 0;
    v___x_2206_ = lean_int16_of_int(v_i_2205_);
    return v___x_2206_;
}
pub unsafe fn l_Int_toInt16___boxed(
    mut v_i_2207_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2208_: u16 = 0;
    let mut v_r_2209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2208_ = l_Int_toInt16(v_i_2207_);
    crate::leanh::lean_dec(v_i_2207_);
    v_r_2209_ = crate::leanh::lean_box((v_res_2208_) as usize);
    return v_r_2209_;
}
pub unsafe fn l_Nat_toInt16(mut v_n_2210_: *mut crate::leanh::LeanObject) -> u16 {
    let mut v___x_2211_: u16 = 0;
    v___x_2211_ = lean_int16_of_nat(v_n_2210_);
    return v___x_2211_;
}
pub unsafe fn l_Nat_toInt16___boxed(
    mut v_n_2212_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2213_: u16 = 0;
    let mut v_r_2214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2213_ = l_Nat_toInt16(v_n_2212_);
    crate::leanh::lean_dec(v_n_2212_);
    v_r_2214_ = crate::leanh::lean_box((v_res_2213_) as usize);
    return v_r_2214_;
}
pub unsafe fn l_Int16_toInt___boxed(
    mut v_i_2216_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_2217_: u16 = 0;
    let mut v_res_2218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2217_ = (crate::leanh::lean_unbox(v_i_2216_) as u16);
    v_res_2218_ = lean_int16_to_int(v_i_boxed_2217_);
    return v_res_2218_;
}
pub unsafe fn l_Int16_toNatClampNeg(mut v_i_2219_: u16) -> *mut crate::leanh::LeanObject {
    let mut v___x_2220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2220_ = lean_int16_to_int(v_i_2219_);
    v___x_2221_ = l_Int_toNat(v___x_2220_);
    return v___x_2221_;
}
pub unsafe fn l_Int16_toNatClampNeg___boxed(
    mut v_i_2222_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_2223_: u16 = 0;
    let mut v_res_2224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2223_ = (crate::leanh::lean_unbox(v_i_2222_) as u16);
    v_res_2224_ = l_Int16_toNatClampNeg(v_i_boxed_2223_);
    return v_res_2224_;
}
pub unsafe fn l_Int16_ofBitVec(mut v_b_2225_: *mut crate::leanh::LeanObject) -> u16 {
    let mut v___x_2226_: u16 = 0;
    v___x_2226_ = lean_uint16_of_nat_mk(v_b_2225_);
    return v___x_2226_;
}
pub unsafe fn l_Int16_ofBitVec___boxed(
    mut v_b_2227_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2228_: u16 = 0;
    let mut v_r_2229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2228_ = l_Int16_ofBitVec(v_b_2227_);
    v_r_2229_ = crate::leanh::lean_box((v_res_2228_) as usize);
    return v_r_2229_;
}
pub unsafe fn l_Int16_toInt8___boxed(
    mut v_a_2231_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_2232_: u16 = 0;
    let mut v_res_2233_: u8 = 0;
    let mut v_r_2234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_2232_ = (crate::leanh::lean_unbox(v_a_2231_) as u16);
    v_res_2233_ = lean_int16_to_int8(v_a_boxed_2232_);
    v_r_2234_ = crate::leanh::lean_box((v_res_2233_) as usize);
    return v_r_2234_;
}
pub unsafe fn l_Int8_toInt16___boxed(
    mut v_a_2236_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_2237_: u8 = 0;
    let mut v_res_2238_: u16 = 0;
    let mut v_r_2239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_2237_ = (crate::leanh::lean_unbox(v_a_2236_) as u8);
    v_res_2238_ = lean_int8_to_int16(v_a_boxed_2237_);
    v_r_2239_ = crate::leanh::lean_box((v_res_2238_) as usize);
    return v_r_2239_;
}
pub unsafe fn l_Int16_neg___boxed(
    mut v_i_2241_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_2242_: u16 = 0;
    let mut v_res_2243_: u16 = 0;
    let mut v_r_2244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2242_ = (crate::leanh::lean_unbox(v_i_2241_) as u16);
    v_res_2243_ = lean_int16_neg(v_i_boxed_2242_);
    v_r_2244_ = crate::leanh::lean_box((v_res_2243_) as usize);
    return v_r_2244_;
}
pub unsafe fn l_instToStringInt16___lam__0(mut v_i_2245_: u16) -> *mut crate::leanh::LeanObject {
    let mut v___x_2246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2246_ = lean_int16_to_int(v_i_2245_);
    v___x_2247_ = l_Int_repr(v___x_2246_);
    return v___x_2247_;
}
pub unsafe fn l_instToStringInt16___lam__0___boxed(
    mut v_i_2248_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_2249_: u16 = 0;
    let mut v_res_2250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2249_ = (crate::leanh::lean_unbox(v_i_2248_) as u16);
    v_res_2250_ = l_instToStringInt16___lam__0(v_i_boxed_2249_);
    return v_res_2250_;
}
pub unsafe fn l_instReprInt16___lam__0(
    mut v_i_2253_: u16,
    mut v_prec_2254_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2257_: u8 = 0;
    v___x_2255_ = lean_int16_to_int(v_i_2253_);
    v___x_2256_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_instReprInt8___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_instReprInt8___lam__0___closed__0_once),
        _init_l_instReprInt8___lam__0___closed__0,
    );
    v___x_2257_ = lean_int_dec_lt(v___x_2255_, v___x_2256_);
    if v___x_2257_ == 0 {
        let mut v___x_2258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2258_ = l_Int_repr(v___x_2255_);
        v___x_2259_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2259_, 0, v___x_2258_);
        return v___x_2259_;
    } else {
        let mut v___x_2260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2260_ = l_Int_repr(v___x_2255_);
        v___x_2261_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2261_, 0, v___x_2260_);
        v___x_2262_ = l_Repr_addAppParen(v___x_2261_, v_prec_2254_);
        return v___x_2262_;
    }
}
pub unsafe fn l_instReprInt16___lam__0___boxed(
    mut v_i_2263_: *mut crate::leanh::LeanObject,
    mut v_prec_2264_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_2265_: u16 = 0;
    let mut v_res_2266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2265_ = (crate::leanh::lean_unbox(v_i_2263_) as u16);
    v_res_2266_ = l_instReprInt16___lam__0(v_i_boxed_2265_, v_prec_2264_);
    crate::leanh::lean_dec(v_prec_2264_);
    return v_res_2266_;
}
pub unsafe fn _init_l_instReprAtomInt16() -> *mut crate::leanh::LeanObject {
    let mut v___x_2269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2269_ = crate::leanh::lean_box(0);
    return v___x_2269_;
}
pub unsafe fn l_Int16_instOfNat(mut v_n_2272_: *mut crate::leanh::LeanObject) -> u16 {
    let mut v___x_2273_: u16 = 0;
    v___x_2273_ = lean_int16_of_nat(v_n_2272_);
    return v___x_2273_;
}
pub unsafe fn l_Int16_instOfNat___boxed(
    mut v_n_2274_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2275_: u16 = 0;
    let mut v_r_2276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2275_ = l_Int16_instOfNat(v_n_2274_);
    crate::leanh::lean_dec(v_n_2274_);
    v_r_2276_ = crate::leanh::lean_box((v_res_2275_) as usize);
    return v_r_2276_;
}
pub unsafe fn _init_l_Int16_maxValue___closed__0() -> u16 {
    let mut v___x_2279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2280_: u16 = 0;
    v___x_2279_ = crate::leanh::lean_unsigned_to_nat(32767);
    v___x_2280_ = lean_int16_of_nat(v___x_2279_);
    return v___x_2280_;
}
pub unsafe fn _init_l_Int16_maxValue() -> u16 {
    let mut v___x_2281_: u16 = 0;
    v___x_2281_ = crate::leanh::lean_uint16_once(
        core::ptr::addr_of_mut!(l_Int16_maxValue___closed__0),
        core::ptr::addr_of_mut!(l_Int16_maxValue___closed__0_once),
        _init_l_Int16_maxValue___closed__0,
    );
    return v___x_2281_;
}
pub unsafe fn _init_l_Int16_minValue___closed__0() -> u16 {
    let mut v___x_2282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2283_: u16 = 0;
    v___x_2282_ = crate::leanh::lean_unsigned_to_nat(32768);
    v___x_2283_ = lean_int16_of_nat(v___x_2282_);
    return v___x_2283_;
}
pub unsafe fn _init_l_Int16_minValue___closed__1() -> u16 {
    let mut v___x_2284_: u16 = 0;
    let mut v___x_2285_: u16 = 0;
    v___x_2284_ = crate::leanh::lean_uint16_once(
        core::ptr::addr_of_mut!(l_Int16_minValue___closed__0),
        core::ptr::addr_of_mut!(l_Int16_minValue___closed__0_once),
        _init_l_Int16_minValue___closed__0,
    );
    v___x_2285_ = lean_int16_neg(v___x_2284_);
    return v___x_2285_;
}
pub unsafe fn _init_l_Int16_minValue() -> u16 {
    let mut v___x_2286_: u16 = 0;
    v___x_2286_ = crate::leanh::lean_uint16_once(
        core::ptr::addr_of_mut!(l_Int16_minValue___closed__1),
        core::ptr::addr_of_mut!(l_Int16_minValue___closed__1_once),
        _init_l_Int16_minValue___closed__1,
    );
    return v___x_2286_;
}
pub unsafe fn l_Int16_ofIntLE___redArg(mut v_i_2287_: *mut crate::leanh::LeanObject) -> u16 {
    let mut v___x_2288_: u16 = 0;
    v___x_2288_ = lean_int16_of_int(v_i_2287_);
    return v___x_2288_;
}
pub unsafe fn l_Int16_ofIntLE___redArg___boxed(
    mut v_i_2289_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2290_: u16 = 0;
    let mut v_r_2291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2290_ = l_Int16_ofIntLE___redArg(v_i_2289_);
    crate::leanh::lean_dec(v_i_2289_);
    v_r_2291_ = crate::leanh::lean_box((v_res_2290_) as usize);
    return v_r_2291_;
}
pub unsafe fn l_Int16_ofIntLE(
    mut v_i_2292_: *mut crate::leanh::LeanObject,
    mut v___hl_2293_: *mut crate::leanh::LeanObject,
    mut v___hr_2294_: *mut crate::leanh::LeanObject,
) -> u16 {
    let mut v___x_2295_: u16 = 0;
    v___x_2295_ = lean_int16_of_int(v_i_2292_);
    return v___x_2295_;
}
pub unsafe fn l_Int16_ofIntLE___boxed(
    mut v_i_2296_: *mut crate::leanh::LeanObject,
    mut v___hl_2297_: *mut crate::leanh::LeanObject,
    mut v___hr_2298_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2299_: u16 = 0;
    let mut v_r_2300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2299_ = l_Int16_ofIntLE(v_i_2296_, v___hl_2297_, v___hr_2298_);
    crate::leanh::lean_dec(v_i_2296_);
    v_r_2300_ = crate::leanh::lean_box((v_res_2299_) as usize);
    return v_r_2300_;
}
pub unsafe fn _init_l_Int16_ofIntClamp___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_2301_: u16 = 0;
    let mut v___x_2302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2301_ = crate::leanh::lean_uint16_once(
        core::ptr::addr_of_mut!(l_Int16_minValue___closed__1),
        core::ptr::addr_of_mut!(l_Int16_minValue___closed__1_once),
        _init_l_Int16_minValue___closed__1,
    );
    v___x_2302_ = lean_int16_to_int(v___x_2301_);
    return v___x_2302_;
}
pub unsafe fn _init_l_Int16_ofIntClamp___closed__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_2303_: u16 = 0;
    let mut v___x_2304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2303_ = crate::leanh::lean_uint16_once(
        core::ptr::addr_of_mut!(l_Int16_maxValue___closed__0),
        core::ptr::addr_of_mut!(l_Int16_maxValue___closed__0_once),
        _init_l_Int16_maxValue___closed__0,
    );
    v___x_2304_ = lean_int16_to_int(v___x_2303_);
    return v___x_2304_;
}
pub unsafe fn l_Int16_ofIntClamp(mut v_i_2305_: *mut crate::leanh::LeanObject) -> u16 {
    let mut v___x_2306_: u16 = 0;
    let mut v___x_2307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2308_: u8 = 0;
    v___x_2306_ = crate::leanh::lean_uint16_once(
        core::ptr::addr_of_mut!(l_Int16_minValue___closed__1),
        core::ptr::addr_of_mut!(l_Int16_minValue___closed__1_once),
        _init_l_Int16_minValue___closed__1,
    );
    v___x_2307_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Int16_ofIntClamp___closed__0),
        core::ptr::addr_of_mut!(l_Int16_ofIntClamp___closed__0_once),
        _init_l_Int16_ofIntClamp___closed__0,
    );
    v___x_2308_ = lean_int_dec_le(v___x_2307_, v_i_2305_);
    if v___x_2308_ == 0 {
        return v___x_2306_;
    } else {
        let mut v___x_2309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2310_: u8 = 0;
        v___x_2309_ = crate::leanh::lean_obj_once(
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
pub unsafe fn l_Int16_ofIntClamp___boxed(
    mut v_i_2312_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2313_: u16 = 0;
    let mut v_r_2314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2313_ = l_Int16_ofIntClamp(v_i_2312_);
    crate::leanh::lean_dec(v_i_2312_);
    v_r_2314_ = crate::leanh::lean_box((v_res_2313_) as usize);
    return v_r_2314_;
}
pub unsafe fn l_Int16_ofIntTruncate(mut v_i_2315_: *mut crate::leanh::LeanObject) -> u16 {
    let mut v___x_2316_: u16 = 0;
    v___x_2316_ = l_Int16_ofIntClamp(v_i_2315_);
    return v___x_2316_;
}
pub unsafe fn l_Int16_ofIntTruncate___boxed(
    mut v_i_2317_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2318_: u16 = 0;
    let mut v_r_2319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2318_ = l_Int16_ofIntTruncate(v_i_2317_);
    crate::leanh::lean_dec(v_i_2317_);
    v_r_2319_ = crate::leanh::lean_box((v_res_2318_) as usize);
    return v_r_2319_;
}
pub unsafe fn l_Int16_add___boxed(
    mut v_a_2322_: *mut crate::leanh::LeanObject,
    mut v_b_2323_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_2324_: u16 = 0;
    let mut v_b_boxed_2325_: u16 = 0;
    let mut v_res_2326_: u16 = 0;
    let mut v_r_2327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_2324_ = (crate::leanh::lean_unbox(v_a_2322_) as u16);
    v_b_boxed_2325_ = (crate::leanh::lean_unbox(v_b_2323_) as u16);
    v_res_2326_ = lean_int16_add(v_a_boxed_2324_, v_b_boxed_2325_);
    v_r_2327_ = crate::leanh::lean_box((v_res_2326_) as usize);
    return v_r_2327_;
}
pub unsafe fn l_Int16_sub___boxed(
    mut v_a_2330_: *mut crate::leanh::LeanObject,
    mut v_b_2331_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_2332_: u16 = 0;
    let mut v_b_boxed_2333_: u16 = 0;
    let mut v_res_2334_: u16 = 0;
    let mut v_r_2335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_2332_ = (crate::leanh::lean_unbox(v_a_2330_) as u16);
    v_b_boxed_2333_ = (crate::leanh::lean_unbox(v_b_2331_) as u16);
    v_res_2334_ = lean_int16_sub(v_a_boxed_2332_, v_b_boxed_2333_);
    v_r_2335_ = crate::leanh::lean_box((v_res_2334_) as usize);
    return v_r_2335_;
}
pub unsafe fn l_Int16_mul___boxed(
    mut v_a_2338_: *mut crate::leanh::LeanObject,
    mut v_b_2339_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_2340_: u16 = 0;
    let mut v_b_boxed_2341_: u16 = 0;
    let mut v_res_2342_: u16 = 0;
    let mut v_r_2343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_2340_ = (crate::leanh::lean_unbox(v_a_2338_) as u16);
    v_b_boxed_2341_ = (crate::leanh::lean_unbox(v_b_2339_) as u16);
    v_res_2342_ = lean_int16_mul(v_a_boxed_2340_, v_b_boxed_2341_);
    v_r_2343_ = crate::leanh::lean_box((v_res_2342_) as usize);
    return v_r_2343_;
}
pub unsafe fn l_Int16_div___boxed(
    mut v_a_2346_: *mut crate::leanh::LeanObject,
    mut v_b_2347_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_2348_: u16 = 0;
    let mut v_b_boxed_2349_: u16 = 0;
    let mut v_res_2350_: u16 = 0;
    let mut v_r_2351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_2348_ = (crate::leanh::lean_unbox(v_a_2346_) as u16);
    v_b_boxed_2349_ = (crate::leanh::lean_unbox(v_b_2347_) as u16);
    v_res_2350_ = lean_int16_div(v_a_boxed_2348_, v_b_boxed_2349_);
    v_r_2351_ = crate::leanh::lean_box((v_res_2350_) as usize);
    return v_r_2351_;
}
pub unsafe fn _init_l_Int16_pow___closed__0() -> u16 {
    let mut v___x_2352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2353_: u16 = 0;
    v___x_2352_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_2353_ = lean_int16_of_nat(v___x_2352_);
    return v___x_2353_;
}
pub unsafe fn l_Int16_pow(mut v_x_2354_: u16, mut v_n_2355_: *mut crate::leanh::LeanObject) -> u16 {
    let mut v_zero_2356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_2357_: u8 = 0;
    v_zero_2356_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_2357_ = lean_nat_dec_eq(v_n_2355_, v_zero_2356_);
    if v_isZero_2357_ == 1 {
        let mut v___x_2358_: u16 = 0;
        v___x_2358_ = crate::leanh::lean_uint16_once(
            core::ptr::addr_of_mut!(l_Int16_pow___closed__0),
            core::ptr::addr_of_mut!(l_Int16_pow___closed__0_once),
            _init_l_Int16_pow___closed__0,
        );
        return v___x_2358_;
    } else {
        let mut v_one_2359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_2360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2361_: u16 = 0;
        let mut v___x_2362_: u16 = 0;
        v_one_2359_ = crate::leanh::lean_unsigned_to_nat(1);
        v_n_2360_ = lean_nat_sub(v_n_2355_, v_one_2359_);
        v___x_2361_ = l_Int16_pow(v_x_2354_, v_n_2360_);
        crate::leanh::lean_dec(v_n_2360_);
        v___x_2362_ = lean_int16_mul(v___x_2361_, v_x_2354_);
        return v___x_2362_;
    }
}
pub unsafe fn l_Int16_pow___boxed(
    mut v_x_2363_: *mut crate::leanh::LeanObject,
    mut v_n_2364_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_2365_: u16 = 0;
    let mut v_res_2366_: u16 = 0;
    let mut v_r_2367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_2365_ = (crate::leanh::lean_unbox(v_x_2363_) as u16);
    v_res_2366_ = l_Int16_pow(v_x_boxed_2365_, v_n_2364_);
    crate::leanh::lean_dec(v_n_2364_);
    v_r_2367_ = crate::leanh::lean_box((v_res_2366_) as usize);
    return v_r_2367_;
}
pub unsafe fn l_Int16_mod___boxed(
    mut v_a_2370_: *mut crate::leanh::LeanObject,
    mut v_b_2371_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_2372_: u16 = 0;
    let mut v_b_boxed_2373_: u16 = 0;
    let mut v_res_2374_: u16 = 0;
    let mut v_r_2375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_2372_ = (crate::leanh::lean_unbox(v_a_2370_) as u16);
    v_b_boxed_2373_ = (crate::leanh::lean_unbox(v_b_2371_) as u16);
    v_res_2374_ = lean_int16_mod(v_a_boxed_2372_, v_b_boxed_2373_);
    v_r_2375_ = crate::leanh::lean_box((v_res_2374_) as usize);
    return v_r_2375_;
}
pub unsafe fn l_Int16_land___boxed(
    mut v_a_2378_: *mut crate::leanh::LeanObject,
    mut v_b_2379_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_2380_: u16 = 0;
    let mut v_b_boxed_2381_: u16 = 0;
    let mut v_res_2382_: u16 = 0;
    let mut v_r_2383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_2380_ = (crate::leanh::lean_unbox(v_a_2378_) as u16);
    v_b_boxed_2381_ = (crate::leanh::lean_unbox(v_b_2379_) as u16);
    v_res_2382_ = lean_int16_land(v_a_boxed_2380_, v_b_boxed_2381_);
    v_r_2383_ = crate::leanh::lean_box((v_res_2382_) as usize);
    return v_r_2383_;
}
pub unsafe fn l_Int16_lor___boxed(
    mut v_a_2386_: *mut crate::leanh::LeanObject,
    mut v_b_2387_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_2388_: u16 = 0;
    let mut v_b_boxed_2389_: u16 = 0;
    let mut v_res_2390_: u16 = 0;
    let mut v_r_2391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_2388_ = (crate::leanh::lean_unbox(v_a_2386_) as u16);
    v_b_boxed_2389_ = (crate::leanh::lean_unbox(v_b_2387_) as u16);
    v_res_2390_ = lean_int16_lor(v_a_boxed_2388_, v_b_boxed_2389_);
    v_r_2391_ = crate::leanh::lean_box((v_res_2390_) as usize);
    return v_r_2391_;
}
pub unsafe fn l_Int16_xor___boxed(
    mut v_a_2394_: *mut crate::leanh::LeanObject,
    mut v_b_2395_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_2396_: u16 = 0;
    let mut v_b_boxed_2397_: u16 = 0;
    let mut v_res_2398_: u16 = 0;
    let mut v_r_2399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_2396_ = (crate::leanh::lean_unbox(v_a_2394_) as u16);
    v_b_boxed_2397_ = (crate::leanh::lean_unbox(v_b_2395_) as u16);
    v_res_2398_ = lean_int16_xor(v_a_boxed_2396_, v_b_boxed_2397_);
    v_r_2399_ = crate::leanh::lean_box((v_res_2398_) as usize);
    return v_r_2399_;
}
pub unsafe fn l_Int16_shiftLeft___boxed(
    mut v_a_2402_: *mut crate::leanh::LeanObject,
    mut v_b_2403_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_2404_: u16 = 0;
    let mut v_b_boxed_2405_: u16 = 0;
    let mut v_res_2406_: u16 = 0;
    let mut v_r_2407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_2404_ = (crate::leanh::lean_unbox(v_a_2402_) as u16);
    v_b_boxed_2405_ = (crate::leanh::lean_unbox(v_b_2403_) as u16);
    v_res_2406_ = lean_int16_shift_left(v_a_boxed_2404_, v_b_boxed_2405_);
    v_r_2407_ = crate::leanh::lean_box((v_res_2406_) as usize);
    return v_r_2407_;
}
pub unsafe fn l_Int16_shiftRight___boxed(
    mut v_a_2410_: *mut crate::leanh::LeanObject,
    mut v_b_2411_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_2412_: u16 = 0;
    let mut v_b_boxed_2413_: u16 = 0;
    let mut v_res_2414_: u16 = 0;
    let mut v_r_2415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_2412_ = (crate::leanh::lean_unbox(v_a_2410_) as u16);
    v_b_boxed_2413_ = (crate::leanh::lean_unbox(v_b_2411_) as u16);
    v_res_2414_ = lean_int16_shift_right(v_a_boxed_2412_, v_b_boxed_2413_);
    v_r_2415_ = crate::leanh::lean_box((v_res_2414_) as usize);
    return v_r_2415_;
}
pub unsafe fn l_Int16_complement___boxed(
    mut v_a_2417_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_2418_: u16 = 0;
    let mut v_res_2419_: u16 = 0;
    let mut v_r_2420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_2418_ = (crate::leanh::lean_unbox(v_a_2417_) as u16);
    v_res_2419_ = lean_int16_complement(v_a_boxed_2418_);
    v_r_2420_ = crate::leanh::lean_box((v_res_2419_) as usize);
    return v_r_2420_;
}
pub unsafe fn l_Int16_abs___boxed(
    mut v_a_2422_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_2423_: u16 = 0;
    let mut v_res_2424_: u16 = 0;
    let mut v_r_2425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_2423_ = (crate::leanh::lean_unbox(v_a_2422_) as u16);
    v_res_2424_ = lean_int16_abs(v_a_boxed_2423_);
    v_r_2425_ = crate::leanh::lean_box((v_res_2424_) as usize);
    return v_r_2425_;
}
pub unsafe fn l_Int16_decEq___boxed(
    mut v_a_2428_: *mut crate::leanh::LeanObject,
    mut v_b_2429_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_2430_: u16 = 0;
    let mut v_b_boxed_2431_: u16 = 0;
    let mut v_res_2432_: u8 = 0;
    let mut v_r_2433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_2430_ = (crate::leanh::lean_unbox(v_a_2428_) as u16);
    v_b_boxed_2431_ = (crate::leanh::lean_unbox(v_b_2429_) as u16);
    v_res_2432_ = lean_int16_dec_eq(v_a_boxed_2430_, v_b_boxed_2431_);
    v_r_2433_ = crate::leanh::lean_box((v_res_2432_) as usize);
    return v_r_2433_;
}
pub unsafe fn _init_l_instInhabitedInt16___closed__0() -> u16 {
    let mut v___x_2434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2435_: u16 = 0;
    v___x_2434_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2435_ = lean_int16_of_nat(v___x_2434_);
    return v___x_2435_;
}
pub unsafe fn _init_l_instInhabitedInt16() -> u16 {
    let mut v___x_2436_: u16 = 0;
    v___x_2436_ = crate::leanh::lean_uint16_once(
        core::ptr::addr_of_mut!(l_instInhabitedInt16___closed__0),
        core::ptr::addr_of_mut!(l_instInhabitedInt16___closed__0_once),
        _init_l_instInhabitedInt16___closed__0,
    );
    return v___x_2436_;
}
pub unsafe fn _init_l_instLTInt16() -> *mut crate::leanh::LeanObject {
    let mut v___x_2449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2449_ = crate::leanh::lean_box(0);
    return v___x_2449_;
}
pub unsafe fn _init_l_instLEInt16() -> *mut crate::leanh::LeanObject {
    let mut v___x_2450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2450_ = crate::leanh::lean_box(0);
    return v___x_2450_;
}
pub unsafe fn l_instDecidableEqInt16(mut v_a_2463_: u16, mut v_b_2464_: u16) -> u8 {
    let mut v___x_2465_: u8 = 0;
    v___x_2465_ = lean_int16_dec_eq(v_a_2463_, v_b_2464_);
    return v___x_2465_;
}
pub unsafe fn l_instDecidableEqInt16___boxed(
    mut v_a_2466_: *mut crate::leanh::LeanObject,
    mut v_b_2467_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_2468_: u16 = 0;
    let mut v_b_boxed_2469_: u16 = 0;
    let mut v_res_2470_: u8 = 0;
    let mut v_r_2471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_2468_ = (crate::leanh::lean_unbox(v_a_2466_) as u16);
    v_b_boxed_2469_ = (crate::leanh::lean_unbox(v_b_2467_) as u16);
    v_res_2470_ = l_instDecidableEqInt16(v_a_boxed_2468_, v_b_boxed_2469_);
    v_r_2471_ = crate::leanh::lean_box((v_res_2470_) as usize);
    return v_r_2471_;
}
pub unsafe fn l_Bool_toInt16___boxed(
    mut v_b_2473_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_b_boxed_2474_: u8 = 0;
    let mut v_res_2475_: u16 = 0;
    let mut v_r_2476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_b_boxed_2474_ = (crate::leanh::lean_unbox(v_b_2473_) as u8);
    v_res_2475_ = lean_bool_to_int16(v_b_boxed_2474_);
    v_r_2476_ = crate::leanh::lean_box((v_res_2475_) as usize);
    return v_r_2476_;
}
pub unsafe fn l_Int16_decLt___aux__1(mut v_a_2477_: u16, mut v_b_2478_: u16) -> u8 {
    let mut v___x_2479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2482_: u8 = 0;
    v___x_2479_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_2480_ = lean_uint16_to_nat(v_a_2477_);
    v___x_2481_ = lean_uint16_to_nat(v_b_2478_);
    v___x_2482_ = l_BitVec_slt(v___x_2479_, v___x_2480_, v___x_2481_);
    return v___x_2482_;
}
pub unsafe fn l_Int16_decLt___aux__1___boxed(
    mut v_a_2483_: *mut crate::leanh::LeanObject,
    mut v_b_2484_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_2485_: u16 = 0;
    let mut v_b_boxed_2486_: u16 = 0;
    let mut v_res_2487_: u8 = 0;
    let mut v_r_2488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_2485_ = (crate::leanh::lean_unbox(v_a_2483_) as u16);
    v_b_boxed_2486_ = (crate::leanh::lean_unbox(v_b_2484_) as u16);
    v_res_2487_ = l_Int16_decLt___aux__1(v_a_boxed_2485_, v_b_boxed_2486_);
    v_r_2488_ = crate::leanh::lean_box((v_res_2487_) as usize);
    return v_r_2488_;
}
pub unsafe fn l_Int16_decLt___boxed(
    mut v_a_2491_: *mut crate::leanh::LeanObject,
    mut v_b_2492_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_2493_: u16 = 0;
    let mut v_b_boxed_2494_: u16 = 0;
    let mut v_res_2495_: u8 = 0;
    let mut v_r_2496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_2493_ = (crate::leanh::lean_unbox(v_a_2491_) as u16);
    v_b_boxed_2494_ = (crate::leanh::lean_unbox(v_b_2492_) as u16);
    v_res_2495_ = lean_int16_dec_lt(v_a_boxed_2493_, v_b_boxed_2494_);
    v_r_2496_ = crate::leanh::lean_box((v_res_2495_) as usize);
    return v_r_2496_;
}
pub unsafe fn l_Int16_decLe___aux__1(mut v_a_2497_: u16, mut v_b_2498_: u16) -> u8 {
    let mut v___x_2499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2502_: u8 = 0;
    v___x_2499_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_2500_ = lean_uint16_to_nat(v_a_2497_);
    v___x_2501_ = lean_uint16_to_nat(v_b_2498_);
    v___x_2502_ = l_BitVec_sle(v___x_2499_, v___x_2500_, v___x_2501_);
    return v___x_2502_;
}
pub unsafe fn l_Int16_decLe___aux__1___boxed(
    mut v_a_2503_: *mut crate::leanh::LeanObject,
    mut v_b_2504_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_2505_: u16 = 0;
    let mut v_b_boxed_2506_: u16 = 0;
    let mut v_res_2507_: u8 = 0;
    let mut v_r_2508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_2505_ = (crate::leanh::lean_unbox(v_a_2503_) as u16);
    v_b_boxed_2506_ = (crate::leanh::lean_unbox(v_b_2504_) as u16);
    v_res_2507_ = l_Int16_decLe___aux__1(v_a_boxed_2505_, v_b_boxed_2506_);
    v_r_2508_ = crate::leanh::lean_box((v_res_2507_) as usize);
    return v_r_2508_;
}
pub unsafe fn l_Int16_decLe___boxed(
    mut v_a_2511_: *mut crate::leanh::LeanObject,
    mut v_b_2512_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_2513_: u16 = 0;
    let mut v_b_boxed_2514_: u16 = 0;
    let mut v_res_2515_: u8 = 0;
    let mut v_r_2516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_2513_ = (crate::leanh::lean_unbox(v_a_2511_) as u16);
    v_b_boxed_2514_ = (crate::leanh::lean_unbox(v_b_2512_) as u16);
    v_res_2515_ = lean_int16_dec_le(v_a_boxed_2513_, v_b_boxed_2514_);
    v_r_2516_ = crate::leanh::lean_box((v_res_2515_) as usize);
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
    mut v_x_2520_: *mut crate::leanh::LeanObject,
    mut v_y_2521_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_2522_: u16 = 0;
    let mut v_y_boxed_2523_: u16 = 0;
    let mut v_res_2524_: u16 = 0;
    let mut v_r_2525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_2522_ = (crate::leanh::lean_unbox(v_x_2520_) as u16);
    v_y_boxed_2523_ = (crate::leanh::lean_unbox(v_y_2521_) as u16);
    v_res_2524_ = l_instMaxInt16___lam__0(v_x_boxed_2522_, v_y_boxed_2523_);
    v_r_2525_ = crate::leanh::lean_box((v_res_2524_) as usize);
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
    mut v_x_2531_: *mut crate::leanh::LeanObject,
    mut v_y_2532_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_2533_: u16 = 0;
    let mut v_y_boxed_2534_: u16 = 0;
    let mut v_res_2535_: u16 = 0;
    let mut v_r_2536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_2533_ = (crate::leanh::lean_unbox(v_x_2531_) as u16);
    v_y_boxed_2534_ = (crate::leanh::lean_unbox(v_y_2532_) as u16);
    v_res_2535_ = l_instMinInt16___lam__0(v_x_boxed_2533_, v_y_boxed_2534_);
    v_r_2536_ = crate::leanh::lean_box((v_res_2535_) as usize);
    return v_r_2536_;
}
pub unsafe fn _init_l_Int32_size() -> *mut crate::leanh::LeanObject {
    let mut v___x_2539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2539_ = crate::leanh::lean_cstr_to_nat(b"4294967296\0".as_ptr().cast());
    return v___x_2539_;
}
pub unsafe fn l_Int32_toBitVec(mut v_x_2540_: u32) -> *mut crate::leanh::LeanObject {
    let mut v___x_2541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2541_ = lean_uint32_to_nat(v_x_2540_);
    return v___x_2541_;
}
pub unsafe fn l_Int32_toBitVec___boxed(
    mut v_x_2542_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_2543_: u32 = 0;
    let mut v_res_2544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_2543_ = crate::leanh::lean_unbox_uint32(v_x_2542_);
    crate::leanh::lean_dec(v_x_2542_);
    v_res_2544_ = l_Int32_toBitVec(v_x_boxed_2543_);
    return v_res_2544_;
}
pub unsafe fn l_UInt32_toInt32(mut v_i_2545_: u32) -> u32 {
    return v_i_2545_;
}
pub unsafe fn l_UInt32_toInt32___boxed(
    mut v_i_2546_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_2547_: u32 = 0;
    let mut v_res_2548_: u32 = 0;
    let mut v_r_2549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2547_ = crate::leanh::lean_unbox_uint32(v_i_2546_);
    crate::leanh::lean_dec(v_i_2546_);
    v_res_2548_ = l_UInt32_toInt32(v_i_boxed_2547_);
    v_r_2549_ = crate::leanh::lean_box_uint32(v_res_2548_);
    return v_r_2549_;
}
pub unsafe fn l_Int32_ofInt___boxed(
    mut v_i_2551_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2552_: u32 = 0;
    let mut v_r_2553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2552_ = lean_int32_of_int(v_i_2551_);
    crate::leanh::lean_dec(v_i_2551_);
    v_r_2553_ = crate::leanh::lean_box_uint32(v_res_2552_);
    return v_r_2553_;
}
pub unsafe fn l_Int32_ofNat___boxed(
    mut v_n_2555_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2556_: u32 = 0;
    let mut v_r_2557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2556_ = lean_int32_of_nat(v_n_2555_);
    crate::leanh::lean_dec(v_n_2555_);
    v_r_2557_ = crate::leanh::lean_box_uint32(v_res_2556_);
    return v_r_2557_;
}
pub unsafe fn l_Int_toInt32(mut v_i_2558_: *mut crate::leanh::LeanObject) -> u32 {
    let mut v___x_2559_: u32 = 0;
    v___x_2559_ = lean_int32_of_int(v_i_2558_);
    return v___x_2559_;
}
pub unsafe fn l_Int_toInt32___boxed(
    mut v_i_2560_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2561_: u32 = 0;
    let mut v_r_2562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2561_ = l_Int_toInt32(v_i_2560_);
    crate::leanh::lean_dec(v_i_2560_);
    v_r_2562_ = crate::leanh::lean_box_uint32(v_res_2561_);
    return v_r_2562_;
}
pub unsafe fn l_Nat_toInt32(mut v_n_2563_: *mut crate::leanh::LeanObject) -> u32 {
    let mut v___x_2564_: u32 = 0;
    v___x_2564_ = lean_int32_of_nat(v_n_2563_);
    return v___x_2564_;
}
pub unsafe fn l_Nat_toInt32___boxed(
    mut v_n_2565_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2566_: u32 = 0;
    let mut v_r_2567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2566_ = l_Nat_toInt32(v_n_2565_);
    crate::leanh::lean_dec(v_n_2565_);
    v_r_2567_ = crate::leanh::lean_box_uint32(v_res_2566_);
    return v_r_2567_;
}
pub unsafe fn l_Int32_toInt___boxed(
    mut v_i_2569_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_2570_: u32 = 0;
    let mut v_res_2571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2570_ = crate::leanh::lean_unbox_uint32(v_i_2569_);
    crate::leanh::lean_dec(v_i_2569_);
    v_res_2571_ = lean_int32_to_int(v_i_boxed_2570_);
    return v_res_2571_;
}
pub unsafe fn l_Int32_toNatClampNeg(mut v_i_2572_: u32) -> *mut crate::leanh::LeanObject {
    let mut v___x_2573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2573_ = lean_int32_to_int(v_i_2572_);
    v___x_2574_ = l_Int_toNat(v___x_2573_);
    crate::leanh::lean_dec(v___x_2573_);
    return v___x_2574_;
}
pub unsafe fn l_Int32_toNatClampNeg___boxed(
    mut v_i_2575_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_2576_: u32 = 0;
    let mut v_res_2577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2576_ = crate::leanh::lean_unbox_uint32(v_i_2575_);
    crate::leanh::lean_dec(v_i_2575_);
    v_res_2577_ = l_Int32_toNatClampNeg(v_i_boxed_2576_);
    return v_res_2577_;
}
pub unsafe fn l_Int32_ofBitVec(mut v_b_2578_: *mut crate::leanh::LeanObject) -> u32 {
    let mut v___x_2579_: u32 = 0;
    v___x_2579_ = lean_uint32_of_nat_mk(v_b_2578_);
    return v___x_2579_;
}
pub unsafe fn l_Int32_ofBitVec___boxed(
    mut v_b_2580_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2581_: u32 = 0;
    let mut v_r_2582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2581_ = l_Int32_ofBitVec(v_b_2580_);
    v_r_2582_ = crate::leanh::lean_box_uint32(v_res_2581_);
    return v_r_2582_;
}
pub unsafe fn l_Int32_toInt8___boxed(
    mut v_a_2584_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_2585_: u32 = 0;
    let mut v_res_2586_: u8 = 0;
    let mut v_r_2587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_2585_ = crate::leanh::lean_unbox_uint32(v_a_2584_);
    crate::leanh::lean_dec(v_a_2584_);
    v_res_2586_ = lean_int32_to_int8(v_a_boxed_2585_);
    v_r_2587_ = crate::leanh::lean_box((v_res_2586_) as usize);
    return v_r_2587_;
}
pub unsafe fn l_Int32_toInt16___boxed(
    mut v_a_2589_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_2590_: u32 = 0;
    let mut v_res_2591_: u16 = 0;
    let mut v_r_2592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_2590_ = crate::leanh::lean_unbox_uint32(v_a_2589_);
    crate::leanh::lean_dec(v_a_2589_);
    v_res_2591_ = lean_int32_to_int16(v_a_boxed_2590_);
    v_r_2592_ = crate::leanh::lean_box((v_res_2591_) as usize);
    return v_r_2592_;
}
pub unsafe fn l_Int8_toInt32___boxed(
    mut v_a_2594_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_2595_: u8 = 0;
    let mut v_res_2596_: u32 = 0;
    let mut v_r_2597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_2595_ = (crate::leanh::lean_unbox(v_a_2594_) as u8);
    v_res_2596_ = lean_int8_to_int32(v_a_boxed_2595_);
    v_r_2597_ = crate::leanh::lean_box_uint32(v_res_2596_);
    return v_r_2597_;
}
pub unsafe fn l_Int16_toInt32___boxed(
    mut v_a_2599_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_2600_: u16 = 0;
    let mut v_res_2601_: u32 = 0;
    let mut v_r_2602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_2600_ = (crate::leanh::lean_unbox(v_a_2599_) as u16);
    v_res_2601_ = lean_int16_to_int32(v_a_boxed_2600_);
    v_r_2602_ = crate::leanh::lean_box_uint32(v_res_2601_);
    return v_r_2602_;
}
pub unsafe fn l_Int32_neg___boxed(
    mut v_i_2604_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_2605_: u32 = 0;
    let mut v_res_2606_: u32 = 0;
    let mut v_r_2607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2605_ = crate::leanh::lean_unbox_uint32(v_i_2604_);
    crate::leanh::lean_dec(v_i_2604_);
    v_res_2606_ = lean_int32_neg(v_i_boxed_2605_);
    v_r_2607_ = crate::leanh::lean_box_uint32(v_res_2606_);
    return v_r_2607_;
}
pub unsafe fn l_instToStringInt32___lam__0(mut v_i_2608_: u32) -> *mut crate::leanh::LeanObject {
    let mut v___x_2609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2609_ = lean_int32_to_int(v_i_2608_);
    v___x_2610_ = l_Int_repr(v___x_2609_);
    crate::leanh::lean_dec(v___x_2609_);
    return v___x_2610_;
}
pub unsafe fn l_instToStringInt32___lam__0___boxed(
    mut v_i_2611_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_2612_: u32 = 0;
    let mut v_res_2613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2612_ = crate::leanh::lean_unbox_uint32(v_i_2611_);
    crate::leanh::lean_dec(v_i_2611_);
    v_res_2613_ = l_instToStringInt32___lam__0(v_i_boxed_2612_);
    return v_res_2613_;
}
pub unsafe fn l_instReprInt32___lam__0(
    mut v_i_2616_: u32,
    mut v_prec_2617_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2620_: u8 = 0;
    v___x_2618_ = lean_int32_to_int(v_i_2616_);
    v___x_2619_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_instReprInt8___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_instReprInt8___lam__0___closed__0_once),
        _init_l_instReprInt8___lam__0___closed__0,
    );
    v___x_2620_ = lean_int_dec_lt(v___x_2618_, v___x_2619_);
    if v___x_2620_ == 0 {
        let mut v___x_2621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2621_ = l_Int_repr(v___x_2618_);
        crate::leanh::lean_dec(v___x_2618_);
        v___x_2622_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2622_, 0, v___x_2621_);
        return v___x_2622_;
    } else {
        let mut v___x_2623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2623_ = l_Int_repr(v___x_2618_);
        crate::leanh::lean_dec(v___x_2618_);
        v___x_2624_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2624_, 0, v___x_2623_);
        v___x_2625_ = l_Repr_addAppParen(v___x_2624_, v_prec_2617_);
        return v___x_2625_;
    }
}
pub unsafe fn l_instReprInt32___lam__0___boxed(
    mut v_i_2626_: *mut crate::leanh::LeanObject,
    mut v_prec_2627_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_2628_: u32 = 0;
    let mut v_res_2629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2628_ = crate::leanh::lean_unbox_uint32(v_i_2626_);
    crate::leanh::lean_dec(v_i_2626_);
    v_res_2629_ = l_instReprInt32___lam__0(v_i_boxed_2628_, v_prec_2627_);
    crate::leanh::lean_dec(v_prec_2627_);
    return v_res_2629_;
}
pub unsafe fn _init_l_instReprAtomInt32() -> *mut crate::leanh::LeanObject {
    let mut v___x_2632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2632_ = crate::leanh::lean_box(0);
    return v___x_2632_;
}
pub unsafe fn l_Int32_instOfNat(mut v_n_2635_: *mut crate::leanh::LeanObject) -> u32 {
    let mut v___x_2636_: u32 = 0;
    v___x_2636_ = lean_int32_of_nat(v_n_2635_);
    return v___x_2636_;
}
pub unsafe fn l_Int32_instOfNat___boxed(
    mut v_n_2637_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2638_: u32 = 0;
    let mut v_r_2639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2638_ = l_Int32_instOfNat(v_n_2637_);
    crate::leanh::lean_dec(v_n_2637_);
    v_r_2639_ = crate::leanh::lean_box_uint32(v_res_2638_);
    return v_r_2639_;
}
pub unsafe fn _init_l_Int32_maxValue___closed__0() -> u32 {
    let mut v___x_2642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2643_: u32 = 0;
    v___x_2642_ = crate::leanh::lean_unsigned_to_nat(2147483647);
    v___x_2643_ = lean_int32_of_nat(v___x_2642_);
    return v___x_2643_;
}
pub unsafe fn _init_l_Int32_maxValue() -> u32 {
    let mut v___x_2644_: u32 = 0;
    v___x_2644_ = crate::leanh::lean_uint32_once(
        core::ptr::addr_of_mut!(l_Int32_maxValue___closed__0),
        core::ptr::addr_of_mut!(l_Int32_maxValue___closed__0_once),
        _init_l_Int32_maxValue___closed__0,
    );
    return v___x_2644_;
}
pub unsafe fn _init_l_Int32_minValue___closed__0() -> u32 {
    let mut v___x_2645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2646_: u32 = 0;
    v___x_2645_ = crate::leanh::lean_unsigned_to_nat(2147483648);
    v___x_2646_ = lean_int32_of_nat(v___x_2645_);
    return v___x_2646_;
}
pub unsafe fn _init_l_Int32_minValue___closed__1() -> u32 {
    let mut v___x_2647_: u32 = 0;
    let mut v___x_2648_: u32 = 0;
    v___x_2647_ = crate::leanh::lean_uint32_once(
        core::ptr::addr_of_mut!(l_Int32_minValue___closed__0),
        core::ptr::addr_of_mut!(l_Int32_minValue___closed__0_once),
        _init_l_Int32_minValue___closed__0,
    );
    v___x_2648_ = lean_int32_neg(v___x_2647_);
    return v___x_2648_;
}
pub unsafe fn _init_l_Int32_minValue() -> u32 {
    let mut v___x_2649_: u32 = 0;
    v___x_2649_ = crate::leanh::lean_uint32_once(
        core::ptr::addr_of_mut!(l_Int32_minValue___closed__1),
        core::ptr::addr_of_mut!(l_Int32_minValue___closed__1_once),
        _init_l_Int32_minValue___closed__1,
    );
    return v___x_2649_;
}
pub unsafe fn l_Int32_ofIntLE___redArg(mut v_i_2650_: *mut crate::leanh::LeanObject) -> u32 {
    let mut v___x_2651_: u32 = 0;
    v___x_2651_ = lean_int32_of_int(v_i_2650_);
    return v___x_2651_;
}
pub unsafe fn l_Int32_ofIntLE___redArg___boxed(
    mut v_i_2652_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2653_: u32 = 0;
    let mut v_r_2654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2653_ = l_Int32_ofIntLE___redArg(v_i_2652_);
    crate::leanh::lean_dec(v_i_2652_);
    v_r_2654_ = crate::leanh::lean_box_uint32(v_res_2653_);
    return v_r_2654_;
}
pub unsafe fn l_Int32_ofIntLE(
    mut v_i_2655_: *mut crate::leanh::LeanObject,
    mut v___hl_2656_: *mut crate::leanh::LeanObject,
    mut v___hr_2657_: *mut crate::leanh::LeanObject,
) -> u32 {
    let mut v___x_2658_: u32 = 0;
    v___x_2658_ = lean_int32_of_int(v_i_2655_);
    return v___x_2658_;
}
pub unsafe fn l_Int32_ofIntLE___boxed(
    mut v_i_2659_: *mut crate::leanh::LeanObject,
    mut v___hl_2660_: *mut crate::leanh::LeanObject,
    mut v___hr_2661_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2662_: u32 = 0;
    let mut v_r_2663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2662_ = l_Int32_ofIntLE(v_i_2659_, v___hl_2660_, v___hr_2661_);
    crate::leanh::lean_dec(v_i_2659_);
    v_r_2663_ = crate::leanh::lean_box_uint32(v_res_2662_);
    return v_r_2663_;
}
pub unsafe fn _init_l_Int32_ofIntClamp___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_2664_: u32 = 0;
    let mut v___x_2665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2664_ = crate::leanh::lean_uint32_once(
        core::ptr::addr_of_mut!(l_Int32_minValue___closed__1),
        core::ptr::addr_of_mut!(l_Int32_minValue___closed__1_once),
        _init_l_Int32_minValue___closed__1,
    );
    v___x_2665_ = lean_int32_to_int(v___x_2664_);
    return v___x_2665_;
}
pub unsafe fn _init_l_Int32_ofIntClamp___closed__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_2666_: u32 = 0;
    let mut v___x_2667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2666_ = crate::leanh::lean_uint32_once(
        core::ptr::addr_of_mut!(l_Int32_maxValue___closed__0),
        core::ptr::addr_of_mut!(l_Int32_maxValue___closed__0_once),
        _init_l_Int32_maxValue___closed__0,
    );
    v___x_2667_ = lean_int32_to_int(v___x_2666_);
    return v___x_2667_;
}
pub unsafe fn l_Int32_ofIntClamp(mut v_i_2668_: *mut crate::leanh::LeanObject) -> u32 {
    let mut v___x_2669_: u32 = 0;
    let mut v___x_2670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2671_: u8 = 0;
    v___x_2669_ = crate::leanh::lean_uint32_once(
        core::ptr::addr_of_mut!(l_Int32_minValue___closed__1),
        core::ptr::addr_of_mut!(l_Int32_minValue___closed__1_once),
        _init_l_Int32_minValue___closed__1,
    );
    v___x_2670_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Int32_ofIntClamp___closed__0),
        core::ptr::addr_of_mut!(l_Int32_ofIntClamp___closed__0_once),
        _init_l_Int32_ofIntClamp___closed__0,
    );
    v___x_2671_ = lean_int_dec_le(v___x_2670_, v_i_2668_);
    if v___x_2671_ == 0 {
        return v___x_2669_;
    } else {
        let mut v___x_2672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2673_: u8 = 0;
        v___x_2672_ = crate::leanh::lean_obj_once(
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
pub unsafe fn l_Int32_ofIntClamp___boxed(
    mut v_i_2675_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2676_: u32 = 0;
    let mut v_r_2677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2676_ = l_Int32_ofIntClamp(v_i_2675_);
    crate::leanh::lean_dec(v_i_2675_);
    v_r_2677_ = crate::leanh::lean_box_uint32(v_res_2676_);
    return v_r_2677_;
}
pub unsafe fn l_Int32_ofIntTruncate(mut v_i_2678_: *mut crate::leanh::LeanObject) -> u32 {
    let mut v___x_2679_: u32 = 0;
    v___x_2679_ = l_Int32_ofIntClamp(v_i_2678_);
    return v___x_2679_;
}
pub unsafe fn l_Int32_ofIntTruncate___boxed(
    mut v_i_2680_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2681_: u32 = 0;
    let mut v_r_2682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2681_ = l_Int32_ofIntTruncate(v_i_2680_);
    crate::leanh::lean_dec(v_i_2680_);
    v_r_2682_ = crate::leanh::lean_box_uint32(v_res_2681_);
    return v_r_2682_;
}
pub unsafe fn l_Int32_add___boxed(
    mut v_a_2685_: *mut crate::leanh::LeanObject,
    mut v_b_2686_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_2687_: u32 = 0;
    let mut v_b_boxed_2688_: u32 = 0;
    let mut v_res_2689_: u32 = 0;
    let mut v_r_2690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_2687_ = crate::leanh::lean_unbox_uint32(v_a_2685_);
    crate::leanh::lean_dec(v_a_2685_);
    v_b_boxed_2688_ = crate::leanh::lean_unbox_uint32(v_b_2686_);
    crate::leanh::lean_dec(v_b_2686_);
    v_res_2689_ = lean_int32_add(v_a_boxed_2687_, v_b_boxed_2688_);
    v_r_2690_ = crate::leanh::lean_box_uint32(v_res_2689_);
    return v_r_2690_;
}
pub unsafe fn l_Int32_sub___boxed(
    mut v_a_2693_: *mut crate::leanh::LeanObject,
    mut v_b_2694_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_2695_: u32 = 0;
    let mut v_b_boxed_2696_: u32 = 0;
    let mut v_res_2697_: u32 = 0;
    let mut v_r_2698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_2695_ = crate::leanh::lean_unbox_uint32(v_a_2693_);
    crate::leanh::lean_dec(v_a_2693_);
    v_b_boxed_2696_ = crate::leanh::lean_unbox_uint32(v_b_2694_);
    crate::leanh::lean_dec(v_b_2694_);
    v_res_2697_ = lean_int32_sub(v_a_boxed_2695_, v_b_boxed_2696_);
    v_r_2698_ = crate::leanh::lean_box_uint32(v_res_2697_);
    return v_r_2698_;
}
pub unsafe fn l_Int32_mul___boxed(
    mut v_a_2701_: *mut crate::leanh::LeanObject,
    mut v_b_2702_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_2703_: u32 = 0;
    let mut v_b_boxed_2704_: u32 = 0;
    let mut v_res_2705_: u32 = 0;
    let mut v_r_2706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_2703_ = crate::leanh::lean_unbox_uint32(v_a_2701_);
    crate::leanh::lean_dec(v_a_2701_);
    v_b_boxed_2704_ = crate::leanh::lean_unbox_uint32(v_b_2702_);
    crate::leanh::lean_dec(v_b_2702_);
    v_res_2705_ = lean_int32_mul(v_a_boxed_2703_, v_b_boxed_2704_);
    v_r_2706_ = crate::leanh::lean_box_uint32(v_res_2705_);
    return v_r_2706_;
}
pub unsafe fn l_Int32_div___boxed(
    mut v_a_2709_: *mut crate::leanh::LeanObject,
    mut v_b_2710_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_2711_: u32 = 0;
    let mut v_b_boxed_2712_: u32 = 0;
    let mut v_res_2713_: u32 = 0;
    let mut v_r_2714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_2711_ = crate::leanh::lean_unbox_uint32(v_a_2709_);
    crate::leanh::lean_dec(v_a_2709_);
    v_b_boxed_2712_ = crate::leanh::lean_unbox_uint32(v_b_2710_);
    crate::leanh::lean_dec(v_b_2710_);
    v_res_2713_ = lean_int32_div(v_a_boxed_2711_, v_b_boxed_2712_);
    v_r_2714_ = crate::leanh::lean_box_uint32(v_res_2713_);
    return v_r_2714_;
}
pub unsafe fn _init_l_Int32_pow___closed__0() -> u32 {
    let mut v___x_2715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2716_: u32 = 0;
    v___x_2715_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_2716_ = lean_int32_of_nat(v___x_2715_);
    return v___x_2716_;
}
pub unsafe fn l_Int32_pow(mut v_x_2717_: u32, mut v_n_2718_: *mut crate::leanh::LeanObject) -> u32 {
    let mut v_zero_2719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_2720_: u8 = 0;
    v_zero_2719_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_2720_ = lean_nat_dec_eq(v_n_2718_, v_zero_2719_);
    if v_isZero_2720_ == 1 {
        let mut v___x_2721_: u32 = 0;
        v___x_2721_ = crate::leanh::lean_uint32_once(
            core::ptr::addr_of_mut!(l_Int32_pow___closed__0),
            core::ptr::addr_of_mut!(l_Int32_pow___closed__0_once),
            _init_l_Int32_pow___closed__0,
        );
        return v___x_2721_;
    } else {
        let mut v_one_2722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_2723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2724_: u32 = 0;
        let mut v___x_2725_: u32 = 0;
        v_one_2722_ = crate::leanh::lean_unsigned_to_nat(1);
        v_n_2723_ = lean_nat_sub(v_n_2718_, v_one_2722_);
        v___x_2724_ = l_Int32_pow(v_x_2717_, v_n_2723_);
        crate::leanh::lean_dec(v_n_2723_);
        v___x_2725_ = lean_int32_mul(v___x_2724_, v_x_2717_);
        return v___x_2725_;
    }
}
pub unsafe fn l_Int32_pow___boxed(
    mut v_x_2726_: *mut crate::leanh::LeanObject,
    mut v_n_2727_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_2728_: u32 = 0;
    let mut v_res_2729_: u32 = 0;
    let mut v_r_2730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_2728_ = crate::leanh::lean_unbox_uint32(v_x_2726_);
    crate::leanh::lean_dec(v_x_2726_);
    v_res_2729_ = l_Int32_pow(v_x_boxed_2728_, v_n_2727_);
    crate::leanh::lean_dec(v_n_2727_);
    v_r_2730_ = crate::leanh::lean_box_uint32(v_res_2729_);
    return v_r_2730_;
}
pub unsafe fn l_Int32_mod___boxed(
    mut v_a_2733_: *mut crate::leanh::LeanObject,
    mut v_b_2734_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_2735_: u32 = 0;
    let mut v_b_boxed_2736_: u32 = 0;
    let mut v_res_2737_: u32 = 0;
    let mut v_r_2738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_2735_ = crate::leanh::lean_unbox_uint32(v_a_2733_);
    crate::leanh::lean_dec(v_a_2733_);
    v_b_boxed_2736_ = crate::leanh::lean_unbox_uint32(v_b_2734_);
    crate::leanh::lean_dec(v_b_2734_);
    v_res_2737_ = lean_int32_mod(v_a_boxed_2735_, v_b_boxed_2736_);
    v_r_2738_ = crate::leanh::lean_box_uint32(v_res_2737_);
    return v_r_2738_;
}
pub unsafe fn l_Int32_land___boxed(
    mut v_a_2741_: *mut crate::leanh::LeanObject,
    mut v_b_2742_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_2743_: u32 = 0;
    let mut v_b_boxed_2744_: u32 = 0;
    let mut v_res_2745_: u32 = 0;
    let mut v_r_2746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_2743_ = crate::leanh::lean_unbox_uint32(v_a_2741_);
    crate::leanh::lean_dec(v_a_2741_);
    v_b_boxed_2744_ = crate::leanh::lean_unbox_uint32(v_b_2742_);
    crate::leanh::lean_dec(v_b_2742_);
    v_res_2745_ = lean_int32_land(v_a_boxed_2743_, v_b_boxed_2744_);
    v_r_2746_ = crate::leanh::lean_box_uint32(v_res_2745_);
    return v_r_2746_;
}
pub unsafe fn l_Int32_lor___boxed(
    mut v_a_2749_: *mut crate::leanh::LeanObject,
    mut v_b_2750_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_2751_: u32 = 0;
    let mut v_b_boxed_2752_: u32 = 0;
    let mut v_res_2753_: u32 = 0;
    let mut v_r_2754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_2751_ = crate::leanh::lean_unbox_uint32(v_a_2749_);
    crate::leanh::lean_dec(v_a_2749_);
    v_b_boxed_2752_ = crate::leanh::lean_unbox_uint32(v_b_2750_);
    crate::leanh::lean_dec(v_b_2750_);
    v_res_2753_ = lean_int32_lor(v_a_boxed_2751_, v_b_boxed_2752_);
    v_r_2754_ = crate::leanh::lean_box_uint32(v_res_2753_);
    return v_r_2754_;
}
pub unsafe fn l_Int32_xor___boxed(
    mut v_a_2757_: *mut crate::leanh::LeanObject,
    mut v_b_2758_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_2759_: u32 = 0;
    let mut v_b_boxed_2760_: u32 = 0;
    let mut v_res_2761_: u32 = 0;
    let mut v_r_2762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_2759_ = crate::leanh::lean_unbox_uint32(v_a_2757_);
    crate::leanh::lean_dec(v_a_2757_);
    v_b_boxed_2760_ = crate::leanh::lean_unbox_uint32(v_b_2758_);
    crate::leanh::lean_dec(v_b_2758_);
    v_res_2761_ = lean_int32_xor(v_a_boxed_2759_, v_b_boxed_2760_);
    v_r_2762_ = crate::leanh::lean_box_uint32(v_res_2761_);
    return v_r_2762_;
}
pub unsafe fn l_Int32_shiftLeft___boxed(
    mut v_a_2765_: *mut crate::leanh::LeanObject,
    mut v_b_2766_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_2767_: u32 = 0;
    let mut v_b_boxed_2768_: u32 = 0;
    let mut v_res_2769_: u32 = 0;
    let mut v_r_2770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_2767_ = crate::leanh::lean_unbox_uint32(v_a_2765_);
    crate::leanh::lean_dec(v_a_2765_);
    v_b_boxed_2768_ = crate::leanh::lean_unbox_uint32(v_b_2766_);
    crate::leanh::lean_dec(v_b_2766_);
    v_res_2769_ = lean_int32_shift_left(v_a_boxed_2767_, v_b_boxed_2768_);
    v_r_2770_ = crate::leanh::lean_box_uint32(v_res_2769_);
    return v_r_2770_;
}
pub unsafe fn l_Int32_shiftRight___boxed(
    mut v_a_2773_: *mut crate::leanh::LeanObject,
    mut v_b_2774_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_2775_: u32 = 0;
    let mut v_b_boxed_2776_: u32 = 0;
    let mut v_res_2777_: u32 = 0;
    let mut v_r_2778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_2775_ = crate::leanh::lean_unbox_uint32(v_a_2773_);
    crate::leanh::lean_dec(v_a_2773_);
    v_b_boxed_2776_ = crate::leanh::lean_unbox_uint32(v_b_2774_);
    crate::leanh::lean_dec(v_b_2774_);
    v_res_2777_ = lean_int32_shift_right(v_a_boxed_2775_, v_b_boxed_2776_);
    v_r_2778_ = crate::leanh::lean_box_uint32(v_res_2777_);
    return v_r_2778_;
}
pub unsafe fn l_Int32_complement___boxed(
    mut v_a_2780_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_2781_: u32 = 0;
    let mut v_res_2782_: u32 = 0;
    let mut v_r_2783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_2781_ = crate::leanh::lean_unbox_uint32(v_a_2780_);
    crate::leanh::lean_dec(v_a_2780_);
    v_res_2782_ = lean_int32_complement(v_a_boxed_2781_);
    v_r_2783_ = crate::leanh::lean_box_uint32(v_res_2782_);
    return v_r_2783_;
}
pub unsafe fn l_Int32_abs___boxed(
    mut v_a_2785_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_2786_: u32 = 0;
    let mut v_res_2787_: u32 = 0;
    let mut v_r_2788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_2786_ = crate::leanh::lean_unbox_uint32(v_a_2785_);
    crate::leanh::lean_dec(v_a_2785_);
    v_res_2787_ = lean_int32_abs(v_a_boxed_2786_);
    v_r_2788_ = crate::leanh::lean_box_uint32(v_res_2787_);
    return v_r_2788_;
}
pub unsafe fn l_Int32_decEq___boxed(
    mut v_a_2791_: *mut crate::leanh::LeanObject,
    mut v_b_2792_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_2793_: u32 = 0;
    let mut v_b_boxed_2794_: u32 = 0;
    let mut v_res_2795_: u8 = 0;
    let mut v_r_2796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_2793_ = crate::leanh::lean_unbox_uint32(v_a_2791_);
    crate::leanh::lean_dec(v_a_2791_);
    v_b_boxed_2794_ = crate::leanh::lean_unbox_uint32(v_b_2792_);
    crate::leanh::lean_dec(v_b_2792_);
    v_res_2795_ = lean_int32_dec_eq(v_a_boxed_2793_, v_b_boxed_2794_);
    v_r_2796_ = crate::leanh::lean_box((v_res_2795_) as usize);
    return v_r_2796_;
}
pub unsafe fn _init_l_instInhabitedInt32___closed__0() -> u32 {
    let mut v___x_2797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2798_: u32 = 0;
    v___x_2797_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2798_ = lean_int32_of_nat(v___x_2797_);
    return v___x_2798_;
}
pub unsafe fn _init_l_instInhabitedInt32() -> u32 {
    let mut v___x_2799_: u32 = 0;
    v___x_2799_ = crate::leanh::lean_uint32_once(
        core::ptr::addr_of_mut!(l_instInhabitedInt32___closed__0),
        core::ptr::addr_of_mut!(l_instInhabitedInt32___closed__0_once),
        _init_l_instInhabitedInt32___closed__0,
    );
    return v___x_2799_;
}
pub unsafe fn _init_l_instLTInt32() -> *mut crate::leanh::LeanObject {
    let mut v___x_2812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2812_ = crate::leanh::lean_box(0);
    return v___x_2812_;
}
pub unsafe fn _init_l_instLEInt32() -> *mut crate::leanh::LeanObject {
    let mut v___x_2813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2813_ = crate::leanh::lean_box(0);
    return v___x_2813_;
}
pub unsafe fn l_instDecidableEqInt32(mut v_a_2826_: u32, mut v_b_2827_: u32) -> u8 {
    let mut v___x_2828_: u8 = 0;
    v___x_2828_ = lean_int32_dec_eq(v_a_2826_, v_b_2827_);
    return v___x_2828_;
}
pub unsafe fn l_instDecidableEqInt32___boxed(
    mut v_a_2829_: *mut crate::leanh::LeanObject,
    mut v_b_2830_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_2831_: u32 = 0;
    let mut v_b_boxed_2832_: u32 = 0;
    let mut v_res_2833_: u8 = 0;
    let mut v_r_2834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_2831_ = crate::leanh::lean_unbox_uint32(v_a_2829_);
    crate::leanh::lean_dec(v_a_2829_);
    v_b_boxed_2832_ = crate::leanh::lean_unbox_uint32(v_b_2830_);
    crate::leanh::lean_dec(v_b_2830_);
    v_res_2833_ = l_instDecidableEqInt32(v_a_boxed_2831_, v_b_boxed_2832_);
    v_r_2834_ = crate::leanh::lean_box((v_res_2833_) as usize);
    return v_r_2834_;
}
pub unsafe fn l_Bool_toInt32___boxed(
    mut v_b_2836_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_b_boxed_2837_: u8 = 0;
    let mut v_res_2838_: u32 = 0;
    let mut v_r_2839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_b_boxed_2837_ = (crate::leanh::lean_unbox(v_b_2836_) as u8);
    v_res_2838_ = lean_bool_to_int32(v_b_boxed_2837_);
    v_r_2839_ = crate::leanh::lean_box_uint32(v_res_2838_);
    return v_r_2839_;
}
pub unsafe fn l_Int32_decLt___aux__1(mut v_a_2840_: u32, mut v_b_2841_: u32) -> u8 {
    let mut v___x_2842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2845_: u8 = 0;
    v___x_2842_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_2843_ = lean_uint32_to_nat(v_a_2840_);
    v___x_2844_ = lean_uint32_to_nat(v_b_2841_);
    v___x_2845_ = l_BitVec_slt(v___x_2842_, v___x_2843_, v___x_2844_);
    return v___x_2845_;
}
pub unsafe fn l_Int32_decLt___aux__1___boxed(
    mut v_a_2846_: *mut crate::leanh::LeanObject,
    mut v_b_2847_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_2848_: u32 = 0;
    let mut v_b_boxed_2849_: u32 = 0;
    let mut v_res_2850_: u8 = 0;
    let mut v_r_2851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_2848_ = crate::leanh::lean_unbox_uint32(v_a_2846_);
    crate::leanh::lean_dec(v_a_2846_);
    v_b_boxed_2849_ = crate::leanh::lean_unbox_uint32(v_b_2847_);
    crate::leanh::lean_dec(v_b_2847_);
    v_res_2850_ = l_Int32_decLt___aux__1(v_a_boxed_2848_, v_b_boxed_2849_);
    v_r_2851_ = crate::leanh::lean_box((v_res_2850_) as usize);
    return v_r_2851_;
}
pub unsafe fn l_Int32_decLt___boxed(
    mut v_a_2854_: *mut crate::leanh::LeanObject,
    mut v_b_2855_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_2856_: u32 = 0;
    let mut v_b_boxed_2857_: u32 = 0;
    let mut v_res_2858_: u8 = 0;
    let mut v_r_2859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_2856_ = crate::leanh::lean_unbox_uint32(v_a_2854_);
    crate::leanh::lean_dec(v_a_2854_);
    v_b_boxed_2857_ = crate::leanh::lean_unbox_uint32(v_b_2855_);
    crate::leanh::lean_dec(v_b_2855_);
    v_res_2858_ = lean_int32_dec_lt(v_a_boxed_2856_, v_b_boxed_2857_);
    v_r_2859_ = crate::leanh::lean_box((v_res_2858_) as usize);
    return v_r_2859_;
}
pub unsafe fn l_Int32_decLe___aux__1(mut v_a_2860_: u32, mut v_b_2861_: u32) -> u8 {
    let mut v___x_2862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2865_: u8 = 0;
    v___x_2862_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_2863_ = lean_uint32_to_nat(v_a_2860_);
    v___x_2864_ = lean_uint32_to_nat(v_b_2861_);
    v___x_2865_ = l_BitVec_sle(v___x_2862_, v___x_2863_, v___x_2864_);
    return v___x_2865_;
}
pub unsafe fn l_Int32_decLe___aux__1___boxed(
    mut v_a_2866_: *mut crate::leanh::LeanObject,
    mut v_b_2867_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_2868_: u32 = 0;
    let mut v_b_boxed_2869_: u32 = 0;
    let mut v_res_2870_: u8 = 0;
    let mut v_r_2871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_2868_ = crate::leanh::lean_unbox_uint32(v_a_2866_);
    crate::leanh::lean_dec(v_a_2866_);
    v_b_boxed_2869_ = crate::leanh::lean_unbox_uint32(v_b_2867_);
    crate::leanh::lean_dec(v_b_2867_);
    v_res_2870_ = l_Int32_decLe___aux__1(v_a_boxed_2868_, v_b_boxed_2869_);
    v_r_2871_ = crate::leanh::lean_box((v_res_2870_) as usize);
    return v_r_2871_;
}
pub unsafe fn l_Int32_decLe___boxed(
    mut v_a_2874_: *mut crate::leanh::LeanObject,
    mut v_b_2875_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_2876_: u32 = 0;
    let mut v_b_boxed_2877_: u32 = 0;
    let mut v_res_2878_: u8 = 0;
    let mut v_r_2879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_2876_ = crate::leanh::lean_unbox_uint32(v_a_2874_);
    crate::leanh::lean_dec(v_a_2874_);
    v_b_boxed_2877_ = crate::leanh::lean_unbox_uint32(v_b_2875_);
    crate::leanh::lean_dec(v_b_2875_);
    v_res_2878_ = lean_int32_dec_le(v_a_boxed_2876_, v_b_boxed_2877_);
    v_r_2879_ = crate::leanh::lean_box((v_res_2878_) as usize);
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
    mut v_x_2883_: *mut crate::leanh::LeanObject,
    mut v_y_2884_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_2885_: u32 = 0;
    let mut v_y_boxed_2886_: u32 = 0;
    let mut v_res_2887_: u32 = 0;
    let mut v_r_2888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_2885_ = crate::leanh::lean_unbox_uint32(v_x_2883_);
    crate::leanh::lean_dec(v_x_2883_);
    v_y_boxed_2886_ = crate::leanh::lean_unbox_uint32(v_y_2884_);
    crate::leanh::lean_dec(v_y_2884_);
    v_res_2887_ = l_instMaxInt32___lam__0(v_x_boxed_2885_, v_y_boxed_2886_);
    v_r_2888_ = crate::leanh::lean_box_uint32(v_res_2887_);
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
    mut v_x_2894_: *mut crate::leanh::LeanObject,
    mut v_y_2895_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_2896_: u32 = 0;
    let mut v_y_boxed_2897_: u32 = 0;
    let mut v_res_2898_: u32 = 0;
    let mut v_r_2899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_2896_ = crate::leanh::lean_unbox_uint32(v_x_2894_);
    crate::leanh::lean_dec(v_x_2894_);
    v_y_boxed_2897_ = crate::leanh::lean_unbox_uint32(v_y_2895_);
    crate::leanh::lean_dec(v_y_2895_);
    v_res_2898_ = l_instMinInt32___lam__0(v_x_boxed_2896_, v_y_boxed_2897_);
    v_r_2899_ = crate::leanh::lean_box_uint32(v_res_2898_);
    return v_r_2899_;
}
pub unsafe fn _init_l_Int64_size___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_2902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2902_ = crate::leanh::lean_cstr_to_nat(b"18446744073709551616\0".as_ptr().cast());
    return v___x_2902_;
}
pub unsafe fn _init_l_Int64_size() -> *mut crate::leanh::LeanObject {
    let mut v___x_2903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2903_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Int64_size___closed__0),
        core::ptr::addr_of_mut!(l_Int64_size___closed__0_once),
        _init_l_Int64_size___closed__0,
    );
    return v___x_2903_;
}
pub unsafe fn l_Int64_toBitVec(mut v_x_2904_: u64) -> *mut crate::leanh::LeanObject {
    let mut v___x_2905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2905_ = lean_uint64_to_nat(v_x_2904_);
    return v___x_2905_;
}
pub unsafe fn l_Int64_toBitVec___boxed(
    mut v_x_2906_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_2907_: u64 = 0;
    let mut v_res_2908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_2907_ = crate::leanh::lean_unbox_uint64(v_x_2906_);
    crate::leanh::lean_dec_ref(v_x_2906_);
    v_res_2908_ = l_Int64_toBitVec(v_x_boxed_2907_);
    return v_res_2908_;
}
pub unsafe fn l_UInt64_toInt64(mut v_i_2909_: u64) -> u64 {
    return v_i_2909_;
}
pub unsafe fn l_UInt64_toInt64___boxed(
    mut v_i_2910_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_2911_: u64 = 0;
    let mut v_res_2912_: u64 = 0;
    let mut v_r_2913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2911_ = crate::leanh::lean_unbox_uint64(v_i_2910_);
    crate::leanh::lean_dec_ref(v_i_2910_);
    v_res_2912_ = l_UInt64_toInt64(v_i_boxed_2911_);
    v_r_2913_ = crate::leanh::lean_box_uint64(v_res_2912_);
    return v_r_2913_;
}
pub unsafe fn l_Int64_ofInt___boxed(
    mut v_i_2915_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2916_: u64 = 0;
    let mut v_r_2917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2916_ = lean_int64_of_int(v_i_2915_);
    crate::leanh::lean_dec(v_i_2915_);
    v_r_2917_ = crate::leanh::lean_box_uint64(v_res_2916_);
    return v_r_2917_;
}
pub unsafe fn l_Int64_ofNat___boxed(
    mut v_n_2919_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2920_: u64 = 0;
    let mut v_r_2921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2920_ = lean_int64_of_nat(v_n_2919_);
    crate::leanh::lean_dec(v_n_2919_);
    v_r_2921_ = crate::leanh::lean_box_uint64(v_res_2920_);
    return v_r_2921_;
}
pub unsafe fn l_Int_toInt64(mut v_i_2922_: *mut crate::leanh::LeanObject) -> u64 {
    let mut v___x_2923_: u64 = 0;
    v___x_2923_ = lean_int64_of_int(v_i_2922_);
    return v___x_2923_;
}
pub unsafe fn l_Int_toInt64___boxed(
    mut v_i_2924_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2925_: u64 = 0;
    let mut v_r_2926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2925_ = l_Int_toInt64(v_i_2924_);
    crate::leanh::lean_dec(v_i_2924_);
    v_r_2926_ = crate::leanh::lean_box_uint64(v_res_2925_);
    return v_r_2926_;
}
pub unsafe fn l_Nat_toInt64(mut v_n_2927_: *mut crate::leanh::LeanObject) -> u64 {
    let mut v___x_2928_: u64 = 0;
    v___x_2928_ = lean_int64_of_nat(v_n_2927_);
    return v___x_2928_;
}
pub unsafe fn l_Nat_toInt64___boxed(
    mut v_n_2929_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2930_: u64 = 0;
    let mut v_r_2931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2930_ = l_Nat_toInt64(v_n_2929_);
    crate::leanh::lean_dec(v_n_2929_);
    v_r_2931_ = crate::leanh::lean_box_uint64(v_res_2930_);
    return v_r_2931_;
}
pub unsafe fn l_Int64_toInt___boxed(
    mut v_i_2933_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_2934_: u64 = 0;
    let mut v_res_2935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2934_ = crate::leanh::lean_unbox_uint64(v_i_2933_);
    crate::leanh::lean_dec_ref(v_i_2933_);
    v_res_2935_ = lean_int64_to_int_sint(v_i_boxed_2934_);
    return v_res_2935_;
}
pub unsafe fn l_Int64_toNatClampNeg(mut v_i_2936_: u64) -> *mut crate::leanh::LeanObject {
    let mut v___x_2937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2937_ = lean_int64_to_int_sint(v_i_2936_);
    v___x_2938_ = l_Int_toNat(v___x_2937_);
    crate::leanh::lean_dec(v___x_2937_);
    return v___x_2938_;
}
pub unsafe fn l_Int64_toNatClampNeg___boxed(
    mut v_i_2939_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_2940_: u64 = 0;
    let mut v_res_2941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2940_ = crate::leanh::lean_unbox_uint64(v_i_2939_);
    crate::leanh::lean_dec_ref(v_i_2939_);
    v_res_2941_ = l_Int64_toNatClampNeg(v_i_boxed_2940_);
    return v_res_2941_;
}
pub unsafe fn l_Int64_ofBitVec(mut v_b_2942_: *mut crate::leanh::LeanObject) -> u64 {
    let mut v___x_2943_: u64 = 0;
    v___x_2943_ = lean_uint64_of_nat_mk(v_b_2942_);
    return v___x_2943_;
}
pub unsafe fn l_Int64_ofBitVec___boxed(
    mut v_b_2944_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2945_: u64 = 0;
    let mut v_r_2946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2945_ = l_Int64_ofBitVec(v_b_2944_);
    v_r_2946_ = crate::leanh::lean_box_uint64(v_res_2945_);
    return v_r_2946_;
}
pub unsafe fn l_Int64_toInt8___boxed(
    mut v_a_2948_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_2949_: u64 = 0;
    let mut v_res_2950_: u8 = 0;
    let mut v_r_2951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_2949_ = crate::leanh::lean_unbox_uint64(v_a_2948_);
    crate::leanh::lean_dec_ref(v_a_2948_);
    v_res_2950_ = lean_int64_to_int8(v_a_boxed_2949_);
    v_r_2951_ = crate::leanh::lean_box((v_res_2950_) as usize);
    return v_r_2951_;
}
pub unsafe fn l_Int64_toInt16___boxed(
    mut v_a_2953_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_2954_: u64 = 0;
    let mut v_res_2955_: u16 = 0;
    let mut v_r_2956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_2954_ = crate::leanh::lean_unbox_uint64(v_a_2953_);
    crate::leanh::lean_dec_ref(v_a_2953_);
    v_res_2955_ = lean_int64_to_int16(v_a_boxed_2954_);
    v_r_2956_ = crate::leanh::lean_box((v_res_2955_) as usize);
    return v_r_2956_;
}
pub unsafe fn l_Int64_toInt32___boxed(
    mut v_a_2958_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_2959_: u64 = 0;
    let mut v_res_2960_: u32 = 0;
    let mut v_r_2961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_2959_ = crate::leanh::lean_unbox_uint64(v_a_2958_);
    crate::leanh::lean_dec_ref(v_a_2958_);
    v_res_2960_ = lean_int64_to_int32(v_a_boxed_2959_);
    v_r_2961_ = crate::leanh::lean_box_uint32(v_res_2960_);
    return v_r_2961_;
}
pub unsafe fn l_Int8_toInt64___boxed(
    mut v_a_2963_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_2964_: u8 = 0;
    let mut v_res_2965_: u64 = 0;
    let mut v_r_2966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_2964_ = (crate::leanh::lean_unbox(v_a_2963_) as u8);
    v_res_2965_ = lean_int8_to_int64(v_a_boxed_2964_);
    v_r_2966_ = crate::leanh::lean_box_uint64(v_res_2965_);
    return v_r_2966_;
}
pub unsafe fn l_Int16_toInt64___boxed(
    mut v_a_2968_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_2969_: u16 = 0;
    let mut v_res_2970_: u64 = 0;
    let mut v_r_2971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_2969_ = (crate::leanh::lean_unbox(v_a_2968_) as u16);
    v_res_2970_ = lean_int16_to_int64(v_a_boxed_2969_);
    v_r_2971_ = crate::leanh::lean_box_uint64(v_res_2970_);
    return v_r_2971_;
}
pub unsafe fn l_Int32_toInt64___boxed(
    mut v_a_2973_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_2974_: u32 = 0;
    let mut v_res_2975_: u64 = 0;
    let mut v_r_2976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_2974_ = crate::leanh::lean_unbox_uint32(v_a_2973_);
    crate::leanh::lean_dec(v_a_2973_);
    v_res_2975_ = lean_int32_to_int64(v_a_boxed_2974_);
    v_r_2976_ = crate::leanh::lean_box_uint64(v_res_2975_);
    return v_r_2976_;
}
pub unsafe fn l_Int64_neg___boxed(
    mut v_i_2978_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_2979_: u64 = 0;
    let mut v_res_2980_: u64 = 0;
    let mut v_r_2981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2979_ = crate::leanh::lean_unbox_uint64(v_i_2978_);
    crate::leanh::lean_dec_ref(v_i_2978_);
    v_res_2980_ = lean_int64_neg(v_i_boxed_2979_);
    v_r_2981_ = crate::leanh::lean_box_uint64(v_res_2980_);
    return v_r_2981_;
}
pub unsafe fn l_instToStringInt64___lam__0(mut v_i_2982_: u64) -> *mut crate::leanh::LeanObject {
    let mut v___x_2983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2983_ = lean_int64_to_int_sint(v_i_2982_);
    v___x_2984_ = l_Int_repr(v___x_2983_);
    crate::leanh::lean_dec(v___x_2983_);
    return v___x_2984_;
}
pub unsafe fn l_instToStringInt64___lam__0___boxed(
    mut v_i_2985_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_2986_: u64 = 0;
    let mut v_res_2987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2986_ = crate::leanh::lean_unbox_uint64(v_i_2985_);
    crate::leanh::lean_dec_ref(v_i_2985_);
    v_res_2987_ = l_instToStringInt64___lam__0(v_i_boxed_2986_);
    return v_res_2987_;
}
pub unsafe fn l_instReprInt64___lam__0(
    mut v_i_2990_: u64,
    mut v_prec_2991_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2994_: u8 = 0;
    v___x_2992_ = lean_int64_to_int_sint(v_i_2990_);
    v___x_2993_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_instReprInt8___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_instReprInt8___lam__0___closed__0_once),
        _init_l_instReprInt8___lam__0___closed__0,
    );
    v___x_2994_ = lean_int_dec_lt(v___x_2992_, v___x_2993_);
    if v___x_2994_ == 0 {
        let mut v___x_2995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2995_ = l_Int_repr(v___x_2992_);
        crate::leanh::lean_dec(v___x_2992_);
        v___x_2996_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2996_, 0, v___x_2995_);
        return v___x_2996_;
    } else {
        let mut v___x_2997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2997_ = l_Int_repr(v___x_2992_);
        crate::leanh::lean_dec(v___x_2992_);
        v___x_2998_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2998_, 0, v___x_2997_);
        v___x_2999_ = l_Repr_addAppParen(v___x_2998_, v_prec_2991_);
        return v___x_2999_;
    }
}
pub unsafe fn l_instReprInt64___lam__0___boxed(
    mut v_i_3000_: *mut crate::leanh::LeanObject,
    mut v_prec_3001_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_3002_: u64 = 0;
    let mut v_res_3003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3002_ = crate::leanh::lean_unbox_uint64(v_i_3000_);
    crate::leanh::lean_dec_ref(v_i_3000_);
    v_res_3003_ = l_instReprInt64___lam__0(v_i_boxed_3002_, v_prec_3001_);
    crate::leanh::lean_dec(v_prec_3001_);
    return v_res_3003_;
}
pub unsafe fn _init_l_instReprAtomInt64() -> *mut crate::leanh::LeanObject {
    let mut v___x_3006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3006_ = crate::leanh::lean_box(0);
    return v___x_3006_;
}
pub unsafe fn l_instHashableInt64___lam__0(mut v_i_3007_: u64) -> u64 {
    return v_i_3007_;
}
pub unsafe fn l_instHashableInt64___lam__0___boxed(
    mut v_i_3008_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_3009_: u64 = 0;
    let mut v_res_3010_: u64 = 0;
    let mut v_r_3011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3009_ = crate::leanh::lean_unbox_uint64(v_i_3008_);
    crate::leanh::lean_dec_ref(v_i_3008_);
    v_res_3010_ = l_instHashableInt64___lam__0(v_i_boxed_3009_);
    v_r_3011_ = crate::leanh::lean_box_uint64(v_res_3010_);
    return v_r_3011_;
}
pub unsafe fn l_Int64_instOfNat(mut v_n_3014_: *mut crate::leanh::LeanObject) -> u64 {
    let mut v___x_3015_: u64 = 0;
    v___x_3015_ = lean_int64_of_nat(v_n_3014_);
    return v___x_3015_;
}
pub unsafe fn l_Int64_instOfNat___boxed(
    mut v_n_3016_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3017_: u64 = 0;
    let mut v_r_3018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3017_ = l_Int64_instOfNat(v_n_3016_);
    crate::leanh::lean_dec(v_n_3016_);
    v_r_3018_ = crate::leanh::lean_box_uint64(v_res_3017_);
    return v_r_3018_;
}
pub unsafe fn _init_l_Int64_maxValue___closed__0() -> u64 {
    let mut v___x_3021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3022_: u64 = 0;
    v___x_3021_ = crate::leanh::lean_cstr_to_nat(b"9223372036854775807\0".as_ptr().cast());
    v___x_3022_ = lean_int64_of_nat(v___x_3021_);
    return v___x_3022_;
}
pub unsafe fn _init_l_Int64_maxValue() -> u64 {
    let mut v___x_3023_: u64 = 0;
    v___x_3023_ = crate::leanh::lean_uint64_once(
        core::ptr::addr_of_mut!(l_Int64_maxValue___closed__0),
        core::ptr::addr_of_mut!(l_Int64_maxValue___closed__0_once),
        _init_l_Int64_maxValue___closed__0,
    );
    return v___x_3023_;
}
pub unsafe fn _init_l_Int64_minValue___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_3024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3024_ = crate::leanh::lean_cstr_to_nat(b"9223372036854775808\0".as_ptr().cast());
    return v___x_3024_;
}
pub unsafe fn _init_l_Int64_minValue___closed__1() -> u64 {
    let mut v___x_3025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3026_: u64 = 0;
    v___x_3025_ = crate::leanh::lean_obj_once(
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
    v___x_3027_ = crate::leanh::lean_uint64_once(
        core::ptr::addr_of_mut!(l_Int64_minValue___closed__1),
        core::ptr::addr_of_mut!(l_Int64_minValue___closed__1_once),
        _init_l_Int64_minValue___closed__1,
    );
    v___x_3028_ = lean_int64_neg(v___x_3027_);
    return v___x_3028_;
}
pub unsafe fn _init_l_Int64_minValue() -> u64 {
    let mut v___x_3029_: u64 = 0;
    v___x_3029_ = crate::leanh::lean_uint64_once(
        core::ptr::addr_of_mut!(l_Int64_minValue___closed__2),
        core::ptr::addr_of_mut!(l_Int64_minValue___closed__2_once),
        _init_l_Int64_minValue___closed__2,
    );
    return v___x_3029_;
}
pub unsafe fn l_Int64_ofIntLE___redArg(mut v_i_3030_: *mut crate::leanh::LeanObject) -> u64 {
    let mut v___x_3031_: u64 = 0;
    v___x_3031_ = lean_int64_of_int(v_i_3030_);
    return v___x_3031_;
}
pub unsafe fn l_Int64_ofIntLE___redArg___boxed(
    mut v_i_3032_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3033_: u64 = 0;
    let mut v_r_3034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3033_ = l_Int64_ofIntLE___redArg(v_i_3032_);
    crate::leanh::lean_dec(v_i_3032_);
    v_r_3034_ = crate::leanh::lean_box_uint64(v_res_3033_);
    return v_r_3034_;
}
pub unsafe fn l_Int64_ofIntLE(
    mut v_i_3035_: *mut crate::leanh::LeanObject,
    mut v___hl_3036_: *mut crate::leanh::LeanObject,
    mut v___hr_3037_: *mut crate::leanh::LeanObject,
) -> u64 {
    let mut v___x_3038_: u64 = 0;
    v___x_3038_ = lean_int64_of_int(v_i_3035_);
    return v___x_3038_;
}
pub unsafe fn l_Int64_ofIntLE___boxed(
    mut v_i_3039_: *mut crate::leanh::LeanObject,
    mut v___hl_3040_: *mut crate::leanh::LeanObject,
    mut v___hr_3041_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3042_: u64 = 0;
    let mut v_r_3043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3042_ = l_Int64_ofIntLE(v_i_3039_, v___hl_3040_, v___hr_3041_);
    crate::leanh::lean_dec(v_i_3039_);
    v_r_3043_ = crate::leanh::lean_box_uint64(v_res_3042_);
    return v_r_3043_;
}
pub unsafe fn _init_l_Int64_ofIntClamp___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_3044_: u64 = 0;
    let mut v___x_3045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3044_ = crate::leanh::lean_uint64_once(
        core::ptr::addr_of_mut!(l_Int64_minValue___closed__2),
        core::ptr::addr_of_mut!(l_Int64_minValue___closed__2_once),
        _init_l_Int64_minValue___closed__2,
    );
    v___x_3045_ = lean_int64_to_int_sint(v___x_3044_);
    return v___x_3045_;
}
pub unsafe fn _init_l_Int64_ofIntClamp___closed__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_3046_: u64 = 0;
    let mut v___x_3047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3046_ = crate::leanh::lean_uint64_once(
        core::ptr::addr_of_mut!(l_Int64_maxValue___closed__0),
        core::ptr::addr_of_mut!(l_Int64_maxValue___closed__0_once),
        _init_l_Int64_maxValue___closed__0,
    );
    v___x_3047_ = lean_int64_to_int_sint(v___x_3046_);
    return v___x_3047_;
}
pub unsafe fn l_Int64_ofIntClamp(mut v_i_3048_: *mut crate::leanh::LeanObject) -> u64 {
    let mut v___x_3049_: u64 = 0;
    let mut v___x_3050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3051_: u8 = 0;
    v___x_3049_ = crate::leanh::lean_uint64_once(
        core::ptr::addr_of_mut!(l_Int64_minValue___closed__2),
        core::ptr::addr_of_mut!(l_Int64_minValue___closed__2_once),
        _init_l_Int64_minValue___closed__2,
    );
    v___x_3050_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Int64_ofIntClamp___closed__0),
        core::ptr::addr_of_mut!(l_Int64_ofIntClamp___closed__0_once),
        _init_l_Int64_ofIntClamp___closed__0,
    );
    v___x_3051_ = lean_int_dec_le(v___x_3050_, v_i_3048_);
    if v___x_3051_ == 0 {
        return v___x_3049_;
    } else {
        let mut v___x_3052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3053_: u8 = 0;
        v___x_3052_ = crate::leanh::lean_obj_once(
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
pub unsafe fn l_Int64_ofIntClamp___boxed(
    mut v_i_3055_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3056_: u64 = 0;
    let mut v_r_3057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3056_ = l_Int64_ofIntClamp(v_i_3055_);
    crate::leanh::lean_dec(v_i_3055_);
    v_r_3057_ = crate::leanh::lean_box_uint64(v_res_3056_);
    return v_r_3057_;
}
pub unsafe fn l_Int64_ofIntTruncate(mut v_i_3058_: *mut crate::leanh::LeanObject) -> u64 {
    let mut v___x_3059_: u64 = 0;
    v___x_3059_ = l_Int64_ofIntClamp(v_i_3058_);
    return v___x_3059_;
}
pub unsafe fn l_Int64_ofIntTruncate___boxed(
    mut v_i_3060_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3061_: u64 = 0;
    let mut v_r_3062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3061_ = l_Int64_ofIntTruncate(v_i_3060_);
    crate::leanh::lean_dec(v_i_3060_);
    v_r_3062_ = crate::leanh::lean_box_uint64(v_res_3061_);
    return v_r_3062_;
}
pub unsafe fn l_Int64_add___boxed(
    mut v_a_3065_: *mut crate::leanh::LeanObject,
    mut v_b_3066_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_3067_: u64 = 0;
    let mut v_b_boxed_3068_: u64 = 0;
    let mut v_res_3069_: u64 = 0;
    let mut v_r_3070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_3067_ = crate::leanh::lean_unbox_uint64(v_a_3065_);
    crate::leanh::lean_dec_ref(v_a_3065_);
    v_b_boxed_3068_ = crate::leanh::lean_unbox_uint64(v_b_3066_);
    crate::leanh::lean_dec_ref(v_b_3066_);
    v_res_3069_ = lean_int64_add(v_a_boxed_3067_, v_b_boxed_3068_);
    v_r_3070_ = crate::leanh::lean_box_uint64(v_res_3069_);
    return v_r_3070_;
}
pub unsafe fn l_Int64_sub___boxed(
    mut v_a_3073_: *mut crate::leanh::LeanObject,
    mut v_b_3074_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_3075_: u64 = 0;
    let mut v_b_boxed_3076_: u64 = 0;
    let mut v_res_3077_: u64 = 0;
    let mut v_r_3078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_3075_ = crate::leanh::lean_unbox_uint64(v_a_3073_);
    crate::leanh::lean_dec_ref(v_a_3073_);
    v_b_boxed_3076_ = crate::leanh::lean_unbox_uint64(v_b_3074_);
    crate::leanh::lean_dec_ref(v_b_3074_);
    v_res_3077_ = lean_int64_sub(v_a_boxed_3075_, v_b_boxed_3076_);
    v_r_3078_ = crate::leanh::lean_box_uint64(v_res_3077_);
    return v_r_3078_;
}
pub unsafe fn l_Int64_mul___boxed(
    mut v_a_3081_: *mut crate::leanh::LeanObject,
    mut v_b_3082_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_3083_: u64 = 0;
    let mut v_b_boxed_3084_: u64 = 0;
    let mut v_res_3085_: u64 = 0;
    let mut v_r_3086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_3083_ = crate::leanh::lean_unbox_uint64(v_a_3081_);
    crate::leanh::lean_dec_ref(v_a_3081_);
    v_b_boxed_3084_ = crate::leanh::lean_unbox_uint64(v_b_3082_);
    crate::leanh::lean_dec_ref(v_b_3082_);
    v_res_3085_ = lean_int64_mul(v_a_boxed_3083_, v_b_boxed_3084_);
    v_r_3086_ = crate::leanh::lean_box_uint64(v_res_3085_);
    return v_r_3086_;
}
pub unsafe fn l_Int64_div___boxed(
    mut v_a_3089_: *mut crate::leanh::LeanObject,
    mut v_b_3090_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_3091_: u64 = 0;
    let mut v_b_boxed_3092_: u64 = 0;
    let mut v_res_3093_: u64 = 0;
    let mut v_r_3094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_3091_ = crate::leanh::lean_unbox_uint64(v_a_3089_);
    crate::leanh::lean_dec_ref(v_a_3089_);
    v_b_boxed_3092_ = crate::leanh::lean_unbox_uint64(v_b_3090_);
    crate::leanh::lean_dec_ref(v_b_3090_);
    v_res_3093_ = lean_int64_div(v_a_boxed_3091_, v_b_boxed_3092_);
    v_r_3094_ = crate::leanh::lean_box_uint64(v_res_3093_);
    return v_r_3094_;
}
pub unsafe fn _init_l_Int64_pow___closed__0() -> u64 {
    let mut v___x_3095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3096_: u64 = 0;
    v___x_3095_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_3096_ = lean_int64_of_nat(v___x_3095_);
    return v___x_3096_;
}
pub unsafe fn l_Int64_pow(mut v_x_3097_: u64, mut v_n_3098_: *mut crate::leanh::LeanObject) -> u64 {
    let mut v_zero_3099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_3100_: u8 = 0;
    v_zero_3099_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_3100_ = lean_nat_dec_eq(v_n_3098_, v_zero_3099_);
    if v_isZero_3100_ == 1 {
        let mut v___x_3101_: u64 = 0;
        v___x_3101_ = crate::leanh::lean_uint64_once(
            core::ptr::addr_of_mut!(l_Int64_pow___closed__0),
            core::ptr::addr_of_mut!(l_Int64_pow___closed__0_once),
            _init_l_Int64_pow___closed__0,
        );
        return v___x_3101_;
    } else {
        let mut v_one_3102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_3103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3104_: u64 = 0;
        let mut v___x_3105_: u64 = 0;
        v_one_3102_ = crate::leanh::lean_unsigned_to_nat(1);
        v_n_3103_ = lean_nat_sub(v_n_3098_, v_one_3102_);
        v___x_3104_ = l_Int64_pow(v_x_3097_, v_n_3103_);
        crate::leanh::lean_dec(v_n_3103_);
        v___x_3105_ = lean_int64_mul(v___x_3104_, v_x_3097_);
        return v___x_3105_;
    }
}
pub unsafe fn l_Int64_pow___boxed(
    mut v_x_3106_: *mut crate::leanh::LeanObject,
    mut v_n_3107_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_3108_: u64 = 0;
    let mut v_res_3109_: u64 = 0;
    let mut v_r_3110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_3108_ = crate::leanh::lean_unbox_uint64(v_x_3106_);
    crate::leanh::lean_dec_ref(v_x_3106_);
    v_res_3109_ = l_Int64_pow(v_x_boxed_3108_, v_n_3107_);
    crate::leanh::lean_dec(v_n_3107_);
    v_r_3110_ = crate::leanh::lean_box_uint64(v_res_3109_);
    return v_r_3110_;
}
pub unsafe fn l_Int64_mod___boxed(
    mut v_a_3113_: *mut crate::leanh::LeanObject,
    mut v_b_3114_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_3115_: u64 = 0;
    let mut v_b_boxed_3116_: u64 = 0;
    let mut v_res_3117_: u64 = 0;
    let mut v_r_3118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_3115_ = crate::leanh::lean_unbox_uint64(v_a_3113_);
    crate::leanh::lean_dec_ref(v_a_3113_);
    v_b_boxed_3116_ = crate::leanh::lean_unbox_uint64(v_b_3114_);
    crate::leanh::lean_dec_ref(v_b_3114_);
    v_res_3117_ = lean_int64_mod(v_a_boxed_3115_, v_b_boxed_3116_);
    v_r_3118_ = crate::leanh::lean_box_uint64(v_res_3117_);
    return v_r_3118_;
}
pub unsafe fn l_Int64_land___boxed(
    mut v_a_3121_: *mut crate::leanh::LeanObject,
    mut v_b_3122_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_3123_: u64 = 0;
    let mut v_b_boxed_3124_: u64 = 0;
    let mut v_res_3125_: u64 = 0;
    let mut v_r_3126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_3123_ = crate::leanh::lean_unbox_uint64(v_a_3121_);
    crate::leanh::lean_dec_ref(v_a_3121_);
    v_b_boxed_3124_ = crate::leanh::lean_unbox_uint64(v_b_3122_);
    crate::leanh::lean_dec_ref(v_b_3122_);
    v_res_3125_ = lean_int64_land(v_a_boxed_3123_, v_b_boxed_3124_);
    v_r_3126_ = crate::leanh::lean_box_uint64(v_res_3125_);
    return v_r_3126_;
}
pub unsafe fn l_Int64_lor___boxed(
    mut v_a_3129_: *mut crate::leanh::LeanObject,
    mut v_b_3130_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_3131_: u64 = 0;
    let mut v_b_boxed_3132_: u64 = 0;
    let mut v_res_3133_: u64 = 0;
    let mut v_r_3134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_3131_ = crate::leanh::lean_unbox_uint64(v_a_3129_);
    crate::leanh::lean_dec_ref(v_a_3129_);
    v_b_boxed_3132_ = crate::leanh::lean_unbox_uint64(v_b_3130_);
    crate::leanh::lean_dec_ref(v_b_3130_);
    v_res_3133_ = lean_int64_lor(v_a_boxed_3131_, v_b_boxed_3132_);
    v_r_3134_ = crate::leanh::lean_box_uint64(v_res_3133_);
    return v_r_3134_;
}
pub unsafe fn l_Int64_xor___boxed(
    mut v_a_3137_: *mut crate::leanh::LeanObject,
    mut v_b_3138_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_3139_: u64 = 0;
    let mut v_b_boxed_3140_: u64 = 0;
    let mut v_res_3141_: u64 = 0;
    let mut v_r_3142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_3139_ = crate::leanh::lean_unbox_uint64(v_a_3137_);
    crate::leanh::lean_dec_ref(v_a_3137_);
    v_b_boxed_3140_ = crate::leanh::lean_unbox_uint64(v_b_3138_);
    crate::leanh::lean_dec_ref(v_b_3138_);
    v_res_3141_ = lean_int64_xor(v_a_boxed_3139_, v_b_boxed_3140_);
    v_r_3142_ = crate::leanh::lean_box_uint64(v_res_3141_);
    return v_r_3142_;
}
pub unsafe fn l_Int64_shiftLeft___boxed(
    mut v_a_3145_: *mut crate::leanh::LeanObject,
    mut v_b_3146_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_3147_: u64 = 0;
    let mut v_b_boxed_3148_: u64 = 0;
    let mut v_res_3149_: u64 = 0;
    let mut v_r_3150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_3147_ = crate::leanh::lean_unbox_uint64(v_a_3145_);
    crate::leanh::lean_dec_ref(v_a_3145_);
    v_b_boxed_3148_ = crate::leanh::lean_unbox_uint64(v_b_3146_);
    crate::leanh::lean_dec_ref(v_b_3146_);
    v_res_3149_ = lean_int64_shift_left(v_a_boxed_3147_, v_b_boxed_3148_);
    v_r_3150_ = crate::leanh::lean_box_uint64(v_res_3149_);
    return v_r_3150_;
}
pub unsafe fn l_Int64_shiftRight___boxed(
    mut v_a_3153_: *mut crate::leanh::LeanObject,
    mut v_b_3154_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_3155_: u64 = 0;
    let mut v_b_boxed_3156_: u64 = 0;
    let mut v_res_3157_: u64 = 0;
    let mut v_r_3158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_3155_ = crate::leanh::lean_unbox_uint64(v_a_3153_);
    crate::leanh::lean_dec_ref(v_a_3153_);
    v_b_boxed_3156_ = crate::leanh::lean_unbox_uint64(v_b_3154_);
    crate::leanh::lean_dec_ref(v_b_3154_);
    v_res_3157_ = lean_int64_shift_right(v_a_boxed_3155_, v_b_boxed_3156_);
    v_r_3158_ = crate::leanh::lean_box_uint64(v_res_3157_);
    return v_r_3158_;
}
pub unsafe fn l_Int64_complement___boxed(
    mut v_a_3160_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_3161_: u64 = 0;
    let mut v_res_3162_: u64 = 0;
    let mut v_r_3163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_3161_ = crate::leanh::lean_unbox_uint64(v_a_3160_);
    crate::leanh::lean_dec_ref(v_a_3160_);
    v_res_3162_ = lean_int64_complement(v_a_boxed_3161_);
    v_r_3163_ = crate::leanh::lean_box_uint64(v_res_3162_);
    return v_r_3163_;
}
pub unsafe fn l_Int64_abs___boxed(
    mut v_a_3165_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_3166_: u64 = 0;
    let mut v_res_3167_: u64 = 0;
    let mut v_r_3168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_3166_ = crate::leanh::lean_unbox_uint64(v_a_3165_);
    crate::leanh::lean_dec_ref(v_a_3165_);
    v_res_3167_ = lean_int64_abs(v_a_boxed_3166_);
    v_r_3168_ = crate::leanh::lean_box_uint64(v_res_3167_);
    return v_r_3168_;
}
pub unsafe fn l_Int64_decEq___boxed(
    mut v_a_3171_: *mut crate::leanh::LeanObject,
    mut v_b_3172_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_3173_: u64 = 0;
    let mut v_b_boxed_3174_: u64 = 0;
    let mut v_res_3175_: u8 = 0;
    let mut v_r_3176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_3173_ = crate::leanh::lean_unbox_uint64(v_a_3171_);
    crate::leanh::lean_dec_ref(v_a_3171_);
    v_b_boxed_3174_ = crate::leanh::lean_unbox_uint64(v_b_3172_);
    crate::leanh::lean_dec_ref(v_b_3172_);
    v_res_3175_ = lean_int64_dec_eq(v_a_boxed_3173_, v_b_boxed_3174_);
    v_r_3176_ = crate::leanh::lean_box((v_res_3175_) as usize);
    return v_r_3176_;
}
pub unsafe fn _init_l_instInhabitedInt64___closed__0() -> u64 {
    let mut v___x_3177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3178_: u64 = 0;
    v___x_3177_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3178_ = lean_int64_of_nat(v___x_3177_);
    return v___x_3178_;
}
pub unsafe fn _init_l_instInhabitedInt64() -> u64 {
    let mut v___x_3179_: u64 = 0;
    v___x_3179_ = crate::leanh::lean_uint64_once(
        core::ptr::addr_of_mut!(l_instInhabitedInt64___closed__0),
        core::ptr::addr_of_mut!(l_instInhabitedInt64___closed__0_once),
        _init_l_instInhabitedInt64___closed__0,
    );
    return v___x_3179_;
}
pub unsafe fn _init_l_instLTInt64() -> *mut crate::leanh::LeanObject {
    let mut v___x_3192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3192_ = crate::leanh::lean_box(0);
    return v___x_3192_;
}
pub unsafe fn _init_l_instLEInt64() -> *mut crate::leanh::LeanObject {
    let mut v___x_3193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3193_ = crate::leanh::lean_box(0);
    return v___x_3193_;
}
pub unsafe fn l_instDecidableEqInt64(mut v_a_3206_: u64, mut v_b_3207_: u64) -> u8 {
    let mut v___x_3208_: u8 = 0;
    v___x_3208_ = lean_int64_dec_eq(v_a_3206_, v_b_3207_);
    return v___x_3208_;
}
pub unsafe fn l_instDecidableEqInt64___boxed(
    mut v_a_3209_: *mut crate::leanh::LeanObject,
    mut v_b_3210_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_3211_: u64 = 0;
    let mut v_b_boxed_3212_: u64 = 0;
    let mut v_res_3213_: u8 = 0;
    let mut v_r_3214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_3211_ = crate::leanh::lean_unbox_uint64(v_a_3209_);
    crate::leanh::lean_dec_ref(v_a_3209_);
    v_b_boxed_3212_ = crate::leanh::lean_unbox_uint64(v_b_3210_);
    crate::leanh::lean_dec_ref(v_b_3210_);
    v_res_3213_ = l_instDecidableEqInt64(v_a_boxed_3211_, v_b_boxed_3212_);
    v_r_3214_ = crate::leanh::lean_box((v_res_3213_) as usize);
    return v_r_3214_;
}
pub unsafe fn l_Bool_toInt64___boxed(
    mut v_b_3216_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_b_boxed_3217_: u8 = 0;
    let mut v_res_3218_: u64 = 0;
    let mut v_r_3219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_b_boxed_3217_ = (crate::leanh::lean_unbox(v_b_3216_) as u8);
    v_res_3218_ = lean_bool_to_int64(v_b_boxed_3217_);
    v_r_3219_ = crate::leanh::lean_box_uint64(v_res_3218_);
    return v_r_3219_;
}
pub unsafe fn l_Int64_decLt___aux__1(mut v_a_3220_: u64, mut v_b_3221_: u64) -> u8 {
    let mut v___x_3222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3225_: u8 = 0;
    v___x_3222_ = crate::leanh::lean_unsigned_to_nat(64);
    v___x_3223_ = lean_uint64_to_nat(v_a_3220_);
    v___x_3224_ = lean_uint64_to_nat(v_b_3221_);
    v___x_3225_ = l_BitVec_slt(v___x_3222_, v___x_3223_, v___x_3224_);
    return v___x_3225_;
}
pub unsafe fn l_Int64_decLt___aux__1___boxed(
    mut v_a_3226_: *mut crate::leanh::LeanObject,
    mut v_b_3227_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_3228_: u64 = 0;
    let mut v_b_boxed_3229_: u64 = 0;
    let mut v_res_3230_: u8 = 0;
    let mut v_r_3231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_3228_ = crate::leanh::lean_unbox_uint64(v_a_3226_);
    crate::leanh::lean_dec_ref(v_a_3226_);
    v_b_boxed_3229_ = crate::leanh::lean_unbox_uint64(v_b_3227_);
    crate::leanh::lean_dec_ref(v_b_3227_);
    v_res_3230_ = l_Int64_decLt___aux__1(v_a_boxed_3228_, v_b_boxed_3229_);
    v_r_3231_ = crate::leanh::lean_box((v_res_3230_) as usize);
    return v_r_3231_;
}
pub unsafe fn l_Int64_decLt___boxed(
    mut v_a_3234_: *mut crate::leanh::LeanObject,
    mut v_b_3235_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_3236_: u64 = 0;
    let mut v_b_boxed_3237_: u64 = 0;
    let mut v_res_3238_: u8 = 0;
    let mut v_r_3239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_3236_ = crate::leanh::lean_unbox_uint64(v_a_3234_);
    crate::leanh::lean_dec_ref(v_a_3234_);
    v_b_boxed_3237_ = crate::leanh::lean_unbox_uint64(v_b_3235_);
    crate::leanh::lean_dec_ref(v_b_3235_);
    v_res_3238_ = lean_int64_dec_lt(v_a_boxed_3236_, v_b_boxed_3237_);
    v_r_3239_ = crate::leanh::lean_box((v_res_3238_) as usize);
    return v_r_3239_;
}
pub unsafe fn l_Int64_decLe___aux__1(mut v_a_3240_: u64, mut v_b_3241_: u64) -> u8 {
    let mut v___x_3242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3245_: u8 = 0;
    v___x_3242_ = crate::leanh::lean_unsigned_to_nat(64);
    v___x_3243_ = lean_uint64_to_nat(v_a_3240_);
    v___x_3244_ = lean_uint64_to_nat(v_b_3241_);
    v___x_3245_ = l_BitVec_sle(v___x_3242_, v___x_3243_, v___x_3244_);
    return v___x_3245_;
}
pub unsafe fn l_Int64_decLe___aux__1___boxed(
    mut v_a_3246_: *mut crate::leanh::LeanObject,
    mut v_b_3247_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_3248_: u64 = 0;
    let mut v_b_boxed_3249_: u64 = 0;
    let mut v_res_3250_: u8 = 0;
    let mut v_r_3251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_3248_ = crate::leanh::lean_unbox_uint64(v_a_3246_);
    crate::leanh::lean_dec_ref(v_a_3246_);
    v_b_boxed_3249_ = crate::leanh::lean_unbox_uint64(v_b_3247_);
    crate::leanh::lean_dec_ref(v_b_3247_);
    v_res_3250_ = l_Int64_decLe___aux__1(v_a_boxed_3248_, v_b_boxed_3249_);
    v_r_3251_ = crate::leanh::lean_box((v_res_3250_) as usize);
    return v_r_3251_;
}
pub unsafe fn l_Int64_decLe___boxed(
    mut v_a_3254_: *mut crate::leanh::LeanObject,
    mut v_b_3255_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_3256_: u64 = 0;
    let mut v_b_boxed_3257_: u64 = 0;
    let mut v_res_3258_: u8 = 0;
    let mut v_r_3259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_3256_ = crate::leanh::lean_unbox_uint64(v_a_3254_);
    crate::leanh::lean_dec_ref(v_a_3254_);
    v_b_boxed_3257_ = crate::leanh::lean_unbox_uint64(v_b_3255_);
    crate::leanh::lean_dec_ref(v_b_3255_);
    v_res_3258_ = lean_int64_dec_le(v_a_boxed_3256_, v_b_boxed_3257_);
    v_r_3259_ = crate::leanh::lean_box((v_res_3258_) as usize);
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
    mut v_x_3263_: *mut crate::leanh::LeanObject,
    mut v_y_3264_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_3265_: u64 = 0;
    let mut v_y_boxed_3266_: u64 = 0;
    let mut v_res_3267_: u64 = 0;
    let mut v_r_3268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_3265_ = crate::leanh::lean_unbox_uint64(v_x_3263_);
    crate::leanh::lean_dec_ref(v_x_3263_);
    v_y_boxed_3266_ = crate::leanh::lean_unbox_uint64(v_y_3264_);
    crate::leanh::lean_dec_ref(v_y_3264_);
    v_res_3267_ = l_instMaxInt64___lam__0(v_x_boxed_3265_, v_y_boxed_3266_);
    v_r_3268_ = crate::leanh::lean_box_uint64(v_res_3267_);
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
    mut v_x_3274_: *mut crate::leanh::LeanObject,
    mut v_y_3275_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_3276_: u64 = 0;
    let mut v_y_boxed_3277_: u64 = 0;
    let mut v_res_3278_: u64 = 0;
    let mut v_r_3279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_3276_ = crate::leanh::lean_unbox_uint64(v_x_3274_);
    crate::leanh::lean_dec_ref(v_x_3274_);
    v_y_boxed_3277_ = crate::leanh::lean_unbox_uint64(v_y_3275_);
    crate::leanh::lean_dec_ref(v_y_3275_);
    v_res_3278_ = l_instMinInt64___lam__0(v_x_boxed_3276_, v_y_boxed_3277_);
    v_r_3279_ = crate::leanh::lean_box_uint64(v_res_3278_);
    return v_r_3279_;
}
pub unsafe fn _init_l_ISize_size___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_3282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3282_ = l_System_Platform_numBits;
    v___x_3283_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_3284_ = lean_nat_pow(v___x_3283_, v___x_3282_);
    return v___x_3284_;
}
pub unsafe fn _init_l_ISize_size() -> *mut crate::leanh::LeanObject {
    let mut v___x_3285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3285_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_ISize_size___closed__0),
        core::ptr::addr_of_mut!(l_ISize_size___closed__0_once),
        _init_l_ISize_size___closed__0,
    );
    return v___x_3285_;
}
pub unsafe fn l_ISize_toBitVec(mut v_x_3286_: usize) -> *mut crate::leanh::LeanObject {
    let mut v___x_3287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3287_ = lean_usize_to_nat(v_x_3286_);
    return v___x_3287_;
}
pub unsafe fn l_ISize_toBitVec___boxed(
    mut v_x_3288_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_3289_: usize = 0;
    let mut v_res_3290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_3289_ = crate::leanh::lean_unbox_usize(v_x_3288_);
    crate::leanh::lean_dec(v_x_3288_);
    v_res_3290_ = l_ISize_toBitVec(v_x_boxed_3289_);
    return v_res_3290_;
}
pub unsafe fn l_USize_toISize(mut v_i_3291_: usize) -> usize {
    return v_i_3291_;
}
pub unsafe fn l_USize_toISize___boxed(
    mut v_i_3292_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_3293_: usize = 0;
    let mut v_res_3294_: usize = 0;
    let mut v_r_3295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3293_ = crate::leanh::lean_unbox_usize(v_i_3292_);
    crate::leanh::lean_dec(v_i_3292_);
    v_res_3294_ = l_USize_toISize(v_i_boxed_3293_);
    v_r_3295_ = crate::leanh::lean_box_usize(v_res_3294_);
    return v_r_3295_;
}
pub unsafe fn l_ISize_ofInt___boxed(
    mut v_i_3297_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3298_: usize = 0;
    let mut v_r_3299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3298_ = lean_isize_of_int(v_i_3297_);
    crate::leanh::lean_dec(v_i_3297_);
    v_r_3299_ = crate::leanh::lean_box_usize(v_res_3298_);
    return v_r_3299_;
}
pub unsafe fn l_ISize_ofNat___boxed(
    mut v_n_3301_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3302_: usize = 0;
    let mut v_r_3303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3302_ = lean_isize_of_nat(v_n_3301_);
    crate::leanh::lean_dec(v_n_3301_);
    v_r_3303_ = crate::leanh::lean_box_usize(v_res_3302_);
    return v_r_3303_;
}
pub unsafe fn l_Int_toISize(mut v_i_3304_: *mut crate::leanh::LeanObject) -> usize {
    let mut v___x_3305_: usize = 0;
    v___x_3305_ = lean_isize_of_int(v_i_3304_);
    return v___x_3305_;
}
pub unsafe fn l_Int_toISize___boxed(
    mut v_i_3306_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3307_: usize = 0;
    let mut v_r_3308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3307_ = l_Int_toISize(v_i_3306_);
    crate::leanh::lean_dec(v_i_3306_);
    v_r_3308_ = crate::leanh::lean_box_usize(v_res_3307_);
    return v_r_3308_;
}
pub unsafe fn l_Nat_toISize(mut v_n_3309_: *mut crate::leanh::LeanObject) -> usize {
    let mut v___x_3310_: usize = 0;
    v___x_3310_ = lean_isize_of_nat(v_n_3309_);
    return v___x_3310_;
}
pub unsafe fn l_Nat_toISize___boxed(
    mut v_n_3311_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3312_: usize = 0;
    let mut v_r_3313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3312_ = l_Nat_toISize(v_n_3311_);
    crate::leanh::lean_dec(v_n_3311_);
    v_r_3313_ = crate::leanh::lean_box_usize(v_res_3312_);
    return v_r_3313_;
}
pub unsafe fn l_ISize_toInt___boxed(
    mut v_i_3315_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_3316_: usize = 0;
    let mut v_res_3317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3316_ = crate::leanh::lean_unbox_usize(v_i_3315_);
    crate::leanh::lean_dec(v_i_3315_);
    v_res_3317_ = lean_isize_to_int(v_i_boxed_3316_);
    return v_res_3317_;
}
pub unsafe fn l_ISize_toNatClampNeg(mut v_i_3318_: usize) -> *mut crate::leanh::LeanObject {
    let mut v___x_3319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3319_ = lean_isize_to_int(v_i_3318_);
    v___x_3320_ = l_Int_toNat(v___x_3319_);
    crate::leanh::lean_dec(v___x_3319_);
    return v___x_3320_;
}
pub unsafe fn l_ISize_toNatClampNeg___boxed(
    mut v_i_3321_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_3322_: usize = 0;
    let mut v_res_3323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3322_ = crate::leanh::lean_unbox_usize(v_i_3321_);
    crate::leanh::lean_dec(v_i_3321_);
    v_res_3323_ = l_ISize_toNatClampNeg(v_i_boxed_3322_);
    return v_res_3323_;
}
pub unsafe fn l_ISize_ofBitVec(mut v_b_3324_: *mut crate::leanh::LeanObject) -> usize {
    let mut v___x_3325_: usize = 0;
    v___x_3325_ = lean_usize_of_nat_mk(v_b_3324_);
    return v___x_3325_;
}
pub unsafe fn l_ISize_ofBitVec___boxed(
    mut v_b_3326_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3327_: usize = 0;
    let mut v_r_3328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3327_ = l_ISize_ofBitVec(v_b_3326_);
    v_r_3328_ = crate::leanh::lean_box_usize(v_res_3327_);
    return v_r_3328_;
}
pub unsafe fn l_ISize_toInt8___boxed(
    mut v_a_3330_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_3331_: usize = 0;
    let mut v_res_3332_: u8 = 0;
    let mut v_r_3333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_3331_ = crate::leanh::lean_unbox_usize(v_a_3330_);
    crate::leanh::lean_dec(v_a_3330_);
    v_res_3332_ = lean_isize_to_int8(v_a_boxed_3331_);
    v_r_3333_ = crate::leanh::lean_box((v_res_3332_) as usize);
    return v_r_3333_;
}
pub unsafe fn l_ISize_toInt16___boxed(
    mut v_a_3335_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_3336_: usize = 0;
    let mut v_res_3337_: u16 = 0;
    let mut v_r_3338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_3336_ = crate::leanh::lean_unbox_usize(v_a_3335_);
    crate::leanh::lean_dec(v_a_3335_);
    v_res_3337_ = lean_isize_to_int16(v_a_boxed_3336_);
    v_r_3338_ = crate::leanh::lean_box((v_res_3337_) as usize);
    return v_r_3338_;
}
pub unsafe fn l_ISize_toInt32___boxed(
    mut v_a_3340_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_3341_: usize = 0;
    let mut v_res_3342_: u32 = 0;
    let mut v_r_3343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_3341_ = crate::leanh::lean_unbox_usize(v_a_3340_);
    crate::leanh::lean_dec(v_a_3340_);
    v_res_3342_ = lean_isize_to_int32(v_a_boxed_3341_);
    v_r_3343_ = crate::leanh::lean_box_uint32(v_res_3342_);
    return v_r_3343_;
}
pub unsafe fn l_ISize_toInt64___boxed(
    mut v_a_3345_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_3346_: usize = 0;
    let mut v_res_3347_: u64 = 0;
    let mut v_r_3348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_3346_ = crate::leanh::lean_unbox_usize(v_a_3345_);
    crate::leanh::lean_dec(v_a_3345_);
    v_res_3347_ = lean_isize_to_int64(v_a_boxed_3346_);
    v_r_3348_ = crate::leanh::lean_box_uint64(v_res_3347_);
    return v_r_3348_;
}
pub unsafe fn l_Int8_toISize___boxed(
    mut v_a_3350_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_3351_: u8 = 0;
    let mut v_res_3352_: usize = 0;
    let mut v_r_3353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_3351_ = (crate::leanh::lean_unbox(v_a_3350_) as u8);
    v_res_3352_ = lean_int8_to_isize(v_a_boxed_3351_);
    v_r_3353_ = crate::leanh::lean_box_usize(v_res_3352_);
    return v_r_3353_;
}
pub unsafe fn l_Int16_toISize___boxed(
    mut v_a_3355_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_3356_: u16 = 0;
    let mut v_res_3357_: usize = 0;
    let mut v_r_3358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_3356_ = (crate::leanh::lean_unbox(v_a_3355_) as u16);
    v_res_3357_ = lean_int16_to_isize(v_a_boxed_3356_);
    v_r_3358_ = crate::leanh::lean_box_usize(v_res_3357_);
    return v_r_3358_;
}
pub unsafe fn l_Int32_toISize___boxed(
    mut v_a_3360_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_3361_: u32 = 0;
    let mut v_res_3362_: usize = 0;
    let mut v_r_3363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_3361_ = crate::leanh::lean_unbox_uint32(v_a_3360_);
    crate::leanh::lean_dec(v_a_3360_);
    v_res_3362_ = lean_int32_to_isize(v_a_boxed_3361_);
    v_r_3363_ = crate::leanh::lean_box_usize(v_res_3362_);
    return v_r_3363_;
}
pub unsafe fn l_Int64_toISize___boxed(
    mut v_a_3365_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_3366_: u64 = 0;
    let mut v_res_3367_: usize = 0;
    let mut v_r_3368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_3366_ = crate::leanh::lean_unbox_uint64(v_a_3365_);
    crate::leanh::lean_dec_ref(v_a_3365_);
    v_res_3367_ = lean_int64_to_isize(v_a_boxed_3366_);
    v_r_3368_ = crate::leanh::lean_box_usize(v_res_3367_);
    return v_r_3368_;
}
pub unsafe fn l_ISize_neg___boxed(
    mut v_i_3370_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_3371_: usize = 0;
    let mut v_res_3372_: usize = 0;
    let mut v_r_3373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3371_ = crate::leanh::lean_unbox_usize(v_i_3370_);
    crate::leanh::lean_dec(v_i_3370_);
    v_res_3372_ = lean_isize_neg(v_i_boxed_3371_);
    v_r_3373_ = crate::leanh::lean_box_usize(v_res_3372_);
    return v_r_3373_;
}
pub unsafe fn l_instToStringISize___lam__0(mut v_i_3374_: usize) -> *mut crate::leanh::LeanObject {
    let mut v___x_3375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3375_ = lean_isize_to_int(v_i_3374_);
    v___x_3376_ = l_Int_repr(v___x_3375_);
    crate::leanh::lean_dec(v___x_3375_);
    return v___x_3376_;
}
pub unsafe fn l_instToStringISize___lam__0___boxed(
    mut v_i_3377_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_3378_: usize = 0;
    let mut v_res_3379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3378_ = crate::leanh::lean_unbox_usize(v_i_3377_);
    crate::leanh::lean_dec(v_i_3377_);
    v_res_3379_ = l_instToStringISize___lam__0(v_i_boxed_3378_);
    return v_res_3379_;
}
pub unsafe fn l_instReprISize___lam__0(
    mut v_i_3382_: usize,
    mut v_prec_3383_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3386_: u8 = 0;
    v___x_3384_ = lean_isize_to_int(v_i_3382_);
    v___x_3385_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_instReprInt8___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_instReprInt8___lam__0___closed__0_once),
        _init_l_instReprInt8___lam__0___closed__0,
    );
    v___x_3386_ = lean_int_dec_lt(v___x_3384_, v___x_3385_);
    if v___x_3386_ == 0 {
        let mut v___x_3387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3387_ = l_Int_repr(v___x_3384_);
        crate::leanh::lean_dec(v___x_3384_);
        v___x_3388_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3388_, 0, v___x_3387_);
        return v___x_3388_;
    } else {
        let mut v___x_3389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3389_ = l_Int_repr(v___x_3384_);
        crate::leanh::lean_dec(v___x_3384_);
        v___x_3390_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3390_, 0, v___x_3389_);
        v___x_3391_ = l_Repr_addAppParen(v___x_3390_, v_prec_3383_);
        return v___x_3391_;
    }
}
pub unsafe fn l_instReprISize___lam__0___boxed(
    mut v_i_3392_: *mut crate::leanh::LeanObject,
    mut v_prec_3393_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_3394_: usize = 0;
    let mut v_res_3395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3394_ = crate::leanh::lean_unbox_usize(v_i_3392_);
    crate::leanh::lean_dec(v_i_3392_);
    v_res_3395_ = l_instReprISize___lam__0(v_i_boxed_3394_, v_prec_3393_);
    crate::leanh::lean_dec(v_prec_3393_);
    return v_res_3395_;
}
pub unsafe fn _init_l_instReprAtomISize() -> *mut crate::leanh::LeanObject {
    let mut v___x_3398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3398_ = crate::leanh::lean_box(0);
    return v___x_3398_;
}
pub unsafe fn l_ISize_instOfNat(mut v_n_3401_: *mut crate::leanh::LeanObject) -> usize {
    let mut v___x_3402_: usize = 0;
    v___x_3402_ = lean_isize_of_nat(v_n_3401_);
    return v___x_3402_;
}
pub unsafe fn l_ISize_instOfNat___boxed(
    mut v_n_3403_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3404_: usize = 0;
    let mut v_r_3405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3404_ = l_ISize_instOfNat(v_n_3403_);
    crate::leanh::lean_dec(v_n_3403_);
    v_r_3405_ = crate::leanh::lean_box_usize(v_res_3404_);
    return v_r_3405_;
}
pub unsafe fn _init_l_ISize_maxValue___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_3408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3408_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_3409_ = lean_nat_to_int(v___x_3408_);
    return v___x_3409_;
}
pub unsafe fn _init_l_ISize_maxValue___closed__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_3410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3410_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_3411_ = l_System_Platform_numBits;
    v___x_3412_ = lean_nat_sub(v___x_3411_, v___x_3410_);
    return v___x_3412_;
}
pub unsafe fn _init_l_ISize_maxValue___closed__2() -> *mut crate::leanh::LeanObject {
    let mut v___x_3413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3413_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_ISize_maxValue___closed__1),
        core::ptr::addr_of_mut!(l_ISize_maxValue___closed__1_once),
        _init_l_ISize_maxValue___closed__1,
    );
    v___x_3414_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_ISize_maxValue___closed__0),
        core::ptr::addr_of_mut!(l_ISize_maxValue___closed__0_once),
        _init_l_ISize_maxValue___closed__0,
    );
    v___x_3415_ = l_Int_pow(v___x_3414_, v___x_3413_);
    return v___x_3415_;
}
pub unsafe fn _init_l_ISize_maxValue___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_3416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3416_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_3417_ = lean_nat_to_int(v___x_3416_);
    return v___x_3417_;
}
pub unsafe fn _init_l_ISize_maxValue___closed__4() -> *mut crate::leanh::LeanObject {
    let mut v___x_3418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3418_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_ISize_maxValue___closed__3),
        core::ptr::addr_of_mut!(l_ISize_maxValue___closed__3_once),
        _init_l_ISize_maxValue___closed__3,
    );
    v___x_3419_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_ISize_maxValue___closed__2),
        core::ptr::addr_of_mut!(l_ISize_maxValue___closed__2_once),
        _init_l_ISize_maxValue___closed__2,
    );
    v___x_3420_ = lean_int_sub(v___x_3419_, v___x_3418_);
    return v___x_3420_;
}
pub unsafe fn _init_l_ISize_maxValue___closed__5() -> usize {
    let mut v___x_3421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3422_: usize = 0;
    v___x_3421_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_ISize_maxValue___closed__4),
        core::ptr::addr_of_mut!(l_ISize_maxValue___closed__4_once),
        _init_l_ISize_maxValue___closed__4,
    );
    v___x_3422_ = lean_isize_of_int(v___x_3421_);
    return v___x_3422_;
}
pub unsafe fn _init_l_ISize_maxValue() -> usize {
    let mut v___x_3423_: usize = 0;
    v___x_3423_ = crate::leanh::lean_usize_once(
        core::ptr::addr_of_mut!(l_ISize_maxValue___closed__5),
        core::ptr::addr_of_mut!(l_ISize_maxValue___closed__5_once),
        _init_l_ISize_maxValue___closed__5,
    );
    return v___x_3423_;
}
pub unsafe fn _init_l_ISize_minValue___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_3424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3424_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_ISize_maxValue___closed__2),
        core::ptr::addr_of_mut!(l_ISize_maxValue___closed__2_once),
        _init_l_ISize_maxValue___closed__2,
    );
    v___x_3425_ = lean_int_neg(v___x_3424_);
    return v___x_3425_;
}
pub unsafe fn _init_l_ISize_minValue___closed__1() -> usize {
    let mut v___x_3426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3427_: usize = 0;
    v___x_3426_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_ISize_minValue___closed__0),
        core::ptr::addr_of_mut!(l_ISize_minValue___closed__0_once),
        _init_l_ISize_minValue___closed__0,
    );
    v___x_3427_ = lean_isize_of_int(v___x_3426_);
    return v___x_3427_;
}
pub unsafe fn _init_l_ISize_minValue() -> usize {
    let mut v___x_3428_: usize = 0;
    v___x_3428_ = crate::leanh::lean_usize_once(
        core::ptr::addr_of_mut!(l_ISize_minValue___closed__1),
        core::ptr::addr_of_mut!(l_ISize_minValue___closed__1_once),
        _init_l_ISize_minValue___closed__1,
    );
    return v___x_3428_;
}
pub unsafe fn l_ISize_ofIntLE___redArg(mut v_i_3429_: *mut crate::leanh::LeanObject) -> usize {
    let mut v___x_3430_: usize = 0;
    v___x_3430_ = lean_isize_of_int(v_i_3429_);
    return v___x_3430_;
}
pub unsafe fn l_ISize_ofIntLE___redArg___boxed(
    mut v_i_3431_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3432_: usize = 0;
    let mut v_r_3433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3432_ = l_ISize_ofIntLE___redArg(v_i_3431_);
    crate::leanh::lean_dec(v_i_3431_);
    v_r_3433_ = crate::leanh::lean_box_usize(v_res_3432_);
    return v_r_3433_;
}
pub unsafe fn l_ISize_ofIntLE(
    mut v_i_3434_: *mut crate::leanh::LeanObject,
    mut v___hl_3435_: *mut crate::leanh::LeanObject,
    mut v___hr_3436_: *mut crate::leanh::LeanObject,
) -> usize {
    let mut v___x_3437_: usize = 0;
    v___x_3437_ = lean_isize_of_int(v_i_3434_);
    return v___x_3437_;
}
pub unsafe fn l_ISize_ofIntLE___boxed(
    mut v_i_3438_: *mut crate::leanh::LeanObject,
    mut v___hl_3439_: *mut crate::leanh::LeanObject,
    mut v___hr_3440_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3441_: usize = 0;
    let mut v_r_3442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3441_ = l_ISize_ofIntLE(v_i_3438_, v___hl_3439_, v___hr_3440_);
    crate::leanh::lean_dec(v_i_3438_);
    v_r_3442_ = crate::leanh::lean_box_usize(v_res_3441_);
    return v_r_3442_;
}
pub unsafe fn _init_l_ISize_ofIntClamp___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_3443_: usize = 0;
    let mut v___x_3444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3443_ = crate::leanh::lean_usize_once(
        core::ptr::addr_of_mut!(l_ISize_minValue___closed__1),
        core::ptr::addr_of_mut!(l_ISize_minValue___closed__1_once),
        _init_l_ISize_minValue___closed__1,
    );
    v___x_3444_ = lean_isize_to_int(v___x_3443_);
    return v___x_3444_;
}
pub unsafe fn _init_l_ISize_ofIntClamp___closed__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_3445_: usize = 0;
    let mut v___x_3446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3445_ = crate::leanh::lean_usize_once(
        core::ptr::addr_of_mut!(l_ISize_maxValue___closed__5),
        core::ptr::addr_of_mut!(l_ISize_maxValue___closed__5_once),
        _init_l_ISize_maxValue___closed__5,
    );
    v___x_3446_ = lean_isize_to_int(v___x_3445_);
    return v___x_3446_;
}
pub unsafe fn l_ISize_ofIntClamp(mut v_i_3447_: *mut crate::leanh::LeanObject) -> usize {
    let mut v___x_3448_: usize = 0;
    let mut v___x_3449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3450_: u8 = 0;
    v___x_3448_ = crate::leanh::lean_usize_once(
        core::ptr::addr_of_mut!(l_ISize_minValue___closed__1),
        core::ptr::addr_of_mut!(l_ISize_minValue___closed__1_once),
        _init_l_ISize_minValue___closed__1,
    );
    v___x_3449_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_ISize_ofIntClamp___closed__0),
        core::ptr::addr_of_mut!(l_ISize_ofIntClamp___closed__0_once),
        _init_l_ISize_ofIntClamp___closed__0,
    );
    v___x_3450_ = lean_int_dec_le(v___x_3449_, v_i_3447_);
    if v___x_3450_ == 0 {
        return v___x_3448_;
    } else {
        let mut v___x_3451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3452_: u8 = 0;
        v___x_3451_ = crate::leanh::lean_obj_once(
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
pub unsafe fn l_ISize_ofIntClamp___boxed(
    mut v_i_3454_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3455_: usize = 0;
    let mut v_r_3456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3455_ = l_ISize_ofIntClamp(v_i_3454_);
    crate::leanh::lean_dec(v_i_3454_);
    v_r_3456_ = crate::leanh::lean_box_usize(v_res_3455_);
    return v_r_3456_;
}
pub unsafe fn l_ISize_ofIntTruncate(mut v_i_3457_: *mut crate::leanh::LeanObject) -> usize {
    let mut v___x_3458_: usize = 0;
    v___x_3458_ = l_ISize_ofIntClamp(v_i_3457_);
    return v___x_3458_;
}
pub unsafe fn l_ISize_ofIntTruncate___boxed(
    mut v_i_3459_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3460_: usize = 0;
    let mut v_r_3461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3460_ = l_ISize_ofIntTruncate(v_i_3459_);
    crate::leanh::lean_dec(v_i_3459_);
    v_r_3461_ = crate::leanh::lean_box_usize(v_res_3460_);
    return v_r_3461_;
}
pub unsafe fn l_ISize_add___boxed(
    mut v_a_3464_: *mut crate::leanh::LeanObject,
    mut v_b_3465_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_3466_: usize = 0;
    let mut v_b_boxed_3467_: usize = 0;
    let mut v_res_3468_: usize = 0;
    let mut v_r_3469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_3466_ = crate::leanh::lean_unbox_usize(v_a_3464_);
    crate::leanh::lean_dec(v_a_3464_);
    v_b_boxed_3467_ = crate::leanh::lean_unbox_usize(v_b_3465_);
    crate::leanh::lean_dec(v_b_3465_);
    v_res_3468_ = lean_isize_add(v_a_boxed_3466_, v_b_boxed_3467_);
    v_r_3469_ = crate::leanh::lean_box_usize(v_res_3468_);
    return v_r_3469_;
}
pub unsafe fn l_ISize_sub___boxed(
    mut v_a_3472_: *mut crate::leanh::LeanObject,
    mut v_b_3473_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_3474_: usize = 0;
    let mut v_b_boxed_3475_: usize = 0;
    let mut v_res_3476_: usize = 0;
    let mut v_r_3477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_3474_ = crate::leanh::lean_unbox_usize(v_a_3472_);
    crate::leanh::lean_dec(v_a_3472_);
    v_b_boxed_3475_ = crate::leanh::lean_unbox_usize(v_b_3473_);
    crate::leanh::lean_dec(v_b_3473_);
    v_res_3476_ = lean_isize_sub(v_a_boxed_3474_, v_b_boxed_3475_);
    v_r_3477_ = crate::leanh::lean_box_usize(v_res_3476_);
    return v_r_3477_;
}
pub unsafe fn l_ISize_mul___boxed(
    mut v_a_3480_: *mut crate::leanh::LeanObject,
    mut v_b_3481_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_3482_: usize = 0;
    let mut v_b_boxed_3483_: usize = 0;
    let mut v_res_3484_: usize = 0;
    let mut v_r_3485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_3482_ = crate::leanh::lean_unbox_usize(v_a_3480_);
    crate::leanh::lean_dec(v_a_3480_);
    v_b_boxed_3483_ = crate::leanh::lean_unbox_usize(v_b_3481_);
    crate::leanh::lean_dec(v_b_3481_);
    v_res_3484_ = lean_isize_mul(v_a_boxed_3482_, v_b_boxed_3483_);
    v_r_3485_ = crate::leanh::lean_box_usize(v_res_3484_);
    return v_r_3485_;
}
pub unsafe fn l_ISize_div___boxed(
    mut v_a_3488_: *mut crate::leanh::LeanObject,
    mut v_b_3489_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_3490_: usize = 0;
    let mut v_b_boxed_3491_: usize = 0;
    let mut v_res_3492_: usize = 0;
    let mut v_r_3493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_3490_ = crate::leanh::lean_unbox_usize(v_a_3488_);
    crate::leanh::lean_dec(v_a_3488_);
    v_b_boxed_3491_ = crate::leanh::lean_unbox_usize(v_b_3489_);
    crate::leanh::lean_dec(v_b_3489_);
    v_res_3492_ = lean_isize_div(v_a_boxed_3490_, v_b_boxed_3491_);
    v_r_3493_ = crate::leanh::lean_box_usize(v_res_3492_);
    return v_r_3493_;
}
pub unsafe fn _init_l_ISize_pow___closed__0() -> usize {
    let mut v___x_3494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3495_: usize = 0;
    v___x_3494_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_3495_ = lean_isize_of_nat(v___x_3494_);
    return v___x_3495_;
}
pub unsafe fn l_ISize_pow(
    mut v_x_3496_: usize,
    mut v_n_3497_: *mut crate::leanh::LeanObject,
) -> usize {
    let mut v_zero_3498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_3499_: u8 = 0;
    v_zero_3498_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_3499_ = lean_nat_dec_eq(v_n_3497_, v_zero_3498_);
    if v_isZero_3499_ == 1 {
        let mut v___x_3500_: usize = 0;
        v___x_3500_ = crate::leanh::lean_usize_once(
            core::ptr::addr_of_mut!(l_ISize_pow___closed__0),
            core::ptr::addr_of_mut!(l_ISize_pow___closed__0_once),
            _init_l_ISize_pow___closed__0,
        );
        return v___x_3500_;
    } else {
        let mut v_one_3501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_3502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3503_: usize = 0;
        let mut v___x_3504_: usize = 0;
        v_one_3501_ = crate::leanh::lean_unsigned_to_nat(1);
        v_n_3502_ = lean_nat_sub(v_n_3497_, v_one_3501_);
        v___x_3503_ = l_ISize_pow(v_x_3496_, v_n_3502_);
        crate::leanh::lean_dec(v_n_3502_);
        v___x_3504_ = lean_isize_mul(v___x_3503_, v_x_3496_);
        return v___x_3504_;
    }
}
pub unsafe fn l_ISize_pow___boxed(
    mut v_x_3505_: *mut crate::leanh::LeanObject,
    mut v_n_3506_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_3507_: usize = 0;
    let mut v_res_3508_: usize = 0;
    let mut v_r_3509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_3507_ = crate::leanh::lean_unbox_usize(v_x_3505_);
    crate::leanh::lean_dec(v_x_3505_);
    v_res_3508_ = l_ISize_pow(v_x_boxed_3507_, v_n_3506_);
    crate::leanh::lean_dec(v_n_3506_);
    v_r_3509_ = crate::leanh::lean_box_usize(v_res_3508_);
    return v_r_3509_;
}
pub unsafe fn l_ISize_mod___boxed(
    mut v_a_3512_: *mut crate::leanh::LeanObject,
    mut v_b_3513_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_3514_: usize = 0;
    let mut v_b_boxed_3515_: usize = 0;
    let mut v_res_3516_: usize = 0;
    let mut v_r_3517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_3514_ = crate::leanh::lean_unbox_usize(v_a_3512_);
    crate::leanh::lean_dec(v_a_3512_);
    v_b_boxed_3515_ = crate::leanh::lean_unbox_usize(v_b_3513_);
    crate::leanh::lean_dec(v_b_3513_);
    v_res_3516_ = lean_isize_mod(v_a_boxed_3514_, v_b_boxed_3515_);
    v_r_3517_ = crate::leanh::lean_box_usize(v_res_3516_);
    return v_r_3517_;
}
pub unsafe fn l_ISize_land___boxed(
    mut v_a_3520_: *mut crate::leanh::LeanObject,
    mut v_b_3521_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_3522_: usize = 0;
    let mut v_b_boxed_3523_: usize = 0;
    let mut v_res_3524_: usize = 0;
    let mut v_r_3525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_3522_ = crate::leanh::lean_unbox_usize(v_a_3520_);
    crate::leanh::lean_dec(v_a_3520_);
    v_b_boxed_3523_ = crate::leanh::lean_unbox_usize(v_b_3521_);
    crate::leanh::lean_dec(v_b_3521_);
    v_res_3524_ = lean_isize_land(v_a_boxed_3522_, v_b_boxed_3523_);
    v_r_3525_ = crate::leanh::lean_box_usize(v_res_3524_);
    return v_r_3525_;
}
pub unsafe fn l_ISize_lor___boxed(
    mut v_a_3528_: *mut crate::leanh::LeanObject,
    mut v_b_3529_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_3530_: usize = 0;
    let mut v_b_boxed_3531_: usize = 0;
    let mut v_res_3532_: usize = 0;
    let mut v_r_3533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_3530_ = crate::leanh::lean_unbox_usize(v_a_3528_);
    crate::leanh::lean_dec(v_a_3528_);
    v_b_boxed_3531_ = crate::leanh::lean_unbox_usize(v_b_3529_);
    crate::leanh::lean_dec(v_b_3529_);
    v_res_3532_ = lean_isize_lor(v_a_boxed_3530_, v_b_boxed_3531_);
    v_r_3533_ = crate::leanh::lean_box_usize(v_res_3532_);
    return v_r_3533_;
}
pub unsafe fn l_ISize_xor___boxed(
    mut v_a_3536_: *mut crate::leanh::LeanObject,
    mut v_b_3537_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_3538_: usize = 0;
    let mut v_b_boxed_3539_: usize = 0;
    let mut v_res_3540_: usize = 0;
    let mut v_r_3541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_3538_ = crate::leanh::lean_unbox_usize(v_a_3536_);
    crate::leanh::lean_dec(v_a_3536_);
    v_b_boxed_3539_ = crate::leanh::lean_unbox_usize(v_b_3537_);
    crate::leanh::lean_dec(v_b_3537_);
    v_res_3540_ = lean_isize_xor(v_a_boxed_3538_, v_b_boxed_3539_);
    v_r_3541_ = crate::leanh::lean_box_usize(v_res_3540_);
    return v_r_3541_;
}
pub unsafe fn l_ISize_shiftLeft___boxed(
    mut v_a_3544_: *mut crate::leanh::LeanObject,
    mut v_b_3545_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_3546_: usize = 0;
    let mut v_b_boxed_3547_: usize = 0;
    let mut v_res_3548_: usize = 0;
    let mut v_r_3549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_3546_ = crate::leanh::lean_unbox_usize(v_a_3544_);
    crate::leanh::lean_dec(v_a_3544_);
    v_b_boxed_3547_ = crate::leanh::lean_unbox_usize(v_b_3545_);
    crate::leanh::lean_dec(v_b_3545_);
    v_res_3548_ = lean_isize_shift_left(v_a_boxed_3546_, v_b_boxed_3547_);
    v_r_3549_ = crate::leanh::lean_box_usize(v_res_3548_);
    return v_r_3549_;
}
pub unsafe fn l_ISize_shiftRight___boxed(
    mut v_a_3552_: *mut crate::leanh::LeanObject,
    mut v_b_3553_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_3554_: usize = 0;
    let mut v_b_boxed_3555_: usize = 0;
    let mut v_res_3556_: usize = 0;
    let mut v_r_3557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_3554_ = crate::leanh::lean_unbox_usize(v_a_3552_);
    crate::leanh::lean_dec(v_a_3552_);
    v_b_boxed_3555_ = crate::leanh::lean_unbox_usize(v_b_3553_);
    crate::leanh::lean_dec(v_b_3553_);
    v_res_3556_ = lean_isize_shift_right(v_a_boxed_3554_, v_b_boxed_3555_);
    v_r_3557_ = crate::leanh::lean_box_usize(v_res_3556_);
    return v_r_3557_;
}
pub unsafe fn l_ISize_complement___boxed(
    mut v_a_3559_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_3560_: usize = 0;
    let mut v_res_3561_: usize = 0;
    let mut v_r_3562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_3560_ = crate::leanh::lean_unbox_usize(v_a_3559_);
    crate::leanh::lean_dec(v_a_3559_);
    v_res_3561_ = lean_isize_complement(v_a_boxed_3560_);
    v_r_3562_ = crate::leanh::lean_box_usize(v_res_3561_);
    return v_r_3562_;
}
pub unsafe fn l_ISize_abs___boxed(
    mut v_a_3564_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_3565_: usize = 0;
    let mut v_res_3566_: usize = 0;
    let mut v_r_3567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_3565_ = crate::leanh::lean_unbox_usize(v_a_3564_);
    crate::leanh::lean_dec(v_a_3564_);
    v_res_3566_ = lean_isize_abs(v_a_boxed_3565_);
    v_r_3567_ = crate::leanh::lean_box_usize(v_res_3566_);
    return v_r_3567_;
}
pub unsafe fn l_ISize_decEq___boxed(
    mut v_a_3570_: *mut crate::leanh::LeanObject,
    mut v_b_3571_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_3572_: usize = 0;
    let mut v_b_boxed_3573_: usize = 0;
    let mut v_res_3574_: u8 = 0;
    let mut v_r_3575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_3572_ = crate::leanh::lean_unbox_usize(v_a_3570_);
    crate::leanh::lean_dec(v_a_3570_);
    v_b_boxed_3573_ = crate::leanh::lean_unbox_usize(v_b_3571_);
    crate::leanh::lean_dec(v_b_3571_);
    v_res_3574_ = lean_isize_dec_eq(v_a_boxed_3572_, v_b_boxed_3573_);
    v_r_3575_ = crate::leanh::lean_box((v_res_3574_) as usize);
    return v_r_3575_;
}
pub unsafe fn _init_l_instInhabitedISize___closed__0() -> usize {
    let mut v___x_3576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3577_: usize = 0;
    v___x_3576_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3577_ = lean_isize_of_nat(v___x_3576_);
    return v___x_3577_;
}
pub unsafe fn _init_l_instInhabitedISize() -> usize {
    let mut v___x_3578_: usize = 0;
    v___x_3578_ = crate::leanh::lean_usize_once(
        core::ptr::addr_of_mut!(l_instInhabitedISize___closed__0),
        core::ptr::addr_of_mut!(l_instInhabitedISize___closed__0_once),
        _init_l_instInhabitedISize___closed__0,
    );
    return v___x_3578_;
}
pub unsafe fn _init_l_instLTISize() -> *mut crate::leanh::LeanObject {
    let mut v___x_3591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3591_ = crate::leanh::lean_box(0);
    return v___x_3591_;
}
pub unsafe fn _init_l_instLEISize() -> *mut crate::leanh::LeanObject {
    let mut v___x_3592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3592_ = crate::leanh::lean_box(0);
    return v___x_3592_;
}
pub unsafe fn l_instDecidableEqISize(mut v_a_3605_: usize, mut v_b_3606_: usize) -> u8 {
    let mut v___x_3607_: u8 = 0;
    v___x_3607_ = lean_isize_dec_eq(v_a_3605_, v_b_3606_);
    return v___x_3607_;
}
pub unsafe fn l_instDecidableEqISize___boxed(
    mut v_a_3608_: *mut crate::leanh::LeanObject,
    mut v_b_3609_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_3610_: usize = 0;
    let mut v_b_boxed_3611_: usize = 0;
    let mut v_res_3612_: u8 = 0;
    let mut v_r_3613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_3610_ = crate::leanh::lean_unbox_usize(v_a_3608_);
    crate::leanh::lean_dec(v_a_3608_);
    v_b_boxed_3611_ = crate::leanh::lean_unbox_usize(v_b_3609_);
    crate::leanh::lean_dec(v_b_3609_);
    v_res_3612_ = l_instDecidableEqISize(v_a_boxed_3610_, v_b_boxed_3611_);
    v_r_3613_ = crate::leanh::lean_box((v_res_3612_) as usize);
    return v_r_3613_;
}
pub unsafe fn l_Bool_toISize___boxed(
    mut v_b_3615_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_b_boxed_3616_: u8 = 0;
    let mut v_res_3617_: usize = 0;
    let mut v_r_3618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_b_boxed_3616_ = (crate::leanh::lean_unbox(v_b_3615_) as u8);
    v_res_3617_ = lean_bool_to_isize(v_b_boxed_3616_);
    v_r_3618_ = crate::leanh::lean_box_usize(v_res_3617_);
    return v_r_3618_;
}
pub unsafe fn l_ISize_decLt___aux__1(mut v_a_3619_: usize, mut v_b_3620_: usize) -> u8 {
    let mut v___x_3621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3624_: u8 = 0;
    v___x_3621_ = l_System_Platform_numBits;
    v___x_3622_ = lean_usize_to_nat(v_a_3619_);
    v___x_3623_ = lean_usize_to_nat(v_b_3620_);
    v___x_3624_ = l_BitVec_slt(v___x_3621_, v___x_3622_, v___x_3623_);
    return v___x_3624_;
}
pub unsafe fn l_ISize_decLt___aux__1___boxed(
    mut v_a_3625_: *mut crate::leanh::LeanObject,
    mut v_b_3626_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_3627_: usize = 0;
    let mut v_b_boxed_3628_: usize = 0;
    let mut v_res_3629_: u8 = 0;
    let mut v_r_3630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_3627_ = crate::leanh::lean_unbox_usize(v_a_3625_);
    crate::leanh::lean_dec(v_a_3625_);
    v_b_boxed_3628_ = crate::leanh::lean_unbox_usize(v_b_3626_);
    crate::leanh::lean_dec(v_b_3626_);
    v_res_3629_ = l_ISize_decLt___aux__1(v_a_boxed_3627_, v_b_boxed_3628_);
    v_r_3630_ = crate::leanh::lean_box((v_res_3629_) as usize);
    return v_r_3630_;
}
pub unsafe fn l_ISize_decLt___boxed(
    mut v_a_3633_: *mut crate::leanh::LeanObject,
    mut v_b_3634_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_3635_: usize = 0;
    let mut v_b_boxed_3636_: usize = 0;
    let mut v_res_3637_: u8 = 0;
    let mut v_r_3638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_3635_ = crate::leanh::lean_unbox_usize(v_a_3633_);
    crate::leanh::lean_dec(v_a_3633_);
    v_b_boxed_3636_ = crate::leanh::lean_unbox_usize(v_b_3634_);
    crate::leanh::lean_dec(v_b_3634_);
    v_res_3637_ = lean_isize_dec_lt(v_a_boxed_3635_, v_b_boxed_3636_);
    v_r_3638_ = crate::leanh::lean_box((v_res_3637_) as usize);
    return v_r_3638_;
}
pub unsafe fn l_ISize_decLe___aux__1(mut v_a_3639_: usize, mut v_b_3640_: usize) -> u8 {
    let mut v___x_3641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3644_: u8 = 0;
    v___x_3641_ = l_System_Platform_numBits;
    v___x_3642_ = lean_usize_to_nat(v_a_3639_);
    v___x_3643_ = lean_usize_to_nat(v_b_3640_);
    v___x_3644_ = l_BitVec_sle(v___x_3641_, v___x_3642_, v___x_3643_);
    return v___x_3644_;
}
pub unsafe fn l_ISize_decLe___aux__1___boxed(
    mut v_a_3645_: *mut crate::leanh::LeanObject,
    mut v_b_3646_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_3647_: usize = 0;
    let mut v_b_boxed_3648_: usize = 0;
    let mut v_res_3649_: u8 = 0;
    let mut v_r_3650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_3647_ = crate::leanh::lean_unbox_usize(v_a_3645_);
    crate::leanh::lean_dec(v_a_3645_);
    v_b_boxed_3648_ = crate::leanh::lean_unbox_usize(v_b_3646_);
    crate::leanh::lean_dec(v_b_3646_);
    v_res_3649_ = l_ISize_decLe___aux__1(v_a_boxed_3647_, v_b_boxed_3648_);
    v_r_3650_ = crate::leanh::lean_box((v_res_3649_) as usize);
    return v_r_3650_;
}
pub unsafe fn l_ISize_decLe___boxed(
    mut v_a_3653_: *mut crate::leanh::LeanObject,
    mut v_b_3654_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_3655_: usize = 0;
    let mut v_b_boxed_3656_: usize = 0;
    let mut v_res_3657_: u8 = 0;
    let mut v_r_3658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_3655_ = crate::leanh::lean_unbox_usize(v_a_3653_);
    crate::leanh::lean_dec(v_a_3653_);
    v_b_boxed_3656_ = crate::leanh::lean_unbox_usize(v_b_3654_);
    crate::leanh::lean_dec(v_b_3654_);
    v_res_3657_ = lean_isize_dec_le(v_a_boxed_3655_, v_b_boxed_3656_);
    v_r_3658_ = crate::leanh::lean_box((v_res_3657_) as usize);
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
    mut v_x_3662_: *mut crate::leanh::LeanObject,
    mut v_y_3663_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_3664_: usize = 0;
    let mut v_y_boxed_3665_: usize = 0;
    let mut v_res_3666_: usize = 0;
    let mut v_r_3667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_3664_ = crate::leanh::lean_unbox_usize(v_x_3662_);
    crate::leanh::lean_dec(v_x_3662_);
    v_y_boxed_3665_ = crate::leanh::lean_unbox_usize(v_y_3663_);
    crate::leanh::lean_dec(v_y_3663_);
    v_res_3666_ = l_instMaxISize___lam__0(v_x_boxed_3664_, v_y_boxed_3665_);
    v_r_3667_ = crate::leanh::lean_box_usize(v_res_3666_);
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
    mut v_x_3673_: *mut crate::leanh::LeanObject,
    mut v_y_3674_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_3675_: usize = 0;
    let mut v_y_boxed_3676_: usize = 0;
    let mut v_res_3677_: usize = 0;
    let mut v_r_3678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_3675_ = crate::leanh::lean_unbox_usize(v_x_3673_);
    crate::leanh::lean_dec(v_x_3673_);
    v_y_boxed_3676_ = crate::leanh::lean_unbox_usize(v_y_3674_);
    crate::leanh::lean_dec(v_y_3674_);
    v_res_3677_ = l_instMinISize___lam__0(v_x_boxed_3675_, v_y_boxed_3676_);
    v_r_3678_ = crate::leanh::lean_box_usize(v_res_3677_);
    return v_r_3678_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_SInt_Basic(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_UInt_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_ToString_Extra(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Int8_size = _init_l_Int8_size();
    crate::leanh::lean_mark_persistent(l_Int8_size);
    l_instReprAtomInt8 = _init_l_instReprAtomInt8();
    crate::leanh::lean_mark_persistent(l_instReprAtomInt8);
    l_Int8_maxValue = _init_l_Int8_maxValue();
    l_Int8_minValue = _init_l_Int8_minValue();
    l_instInhabitedInt8 = _init_l_instInhabitedInt8();
    l_instLTInt8 = _init_l_instLTInt8();
    crate::leanh::lean_mark_persistent(l_instLTInt8);
    l_instLEInt8 = _init_l_instLEInt8();
    crate::leanh::lean_mark_persistent(l_instLEInt8);
    l_Int16_size = _init_l_Int16_size();
    crate::leanh::lean_mark_persistent(l_Int16_size);
    l_instReprAtomInt16 = _init_l_instReprAtomInt16();
    crate::leanh::lean_mark_persistent(l_instReprAtomInt16);
    l_Int16_maxValue = _init_l_Int16_maxValue();
    l_Int16_minValue = _init_l_Int16_minValue();
    l_instInhabitedInt16 = _init_l_instInhabitedInt16();
    l_instLTInt16 = _init_l_instLTInt16();
    crate::leanh::lean_mark_persistent(l_instLTInt16);
    l_instLEInt16 = _init_l_instLEInt16();
    crate::leanh::lean_mark_persistent(l_instLEInt16);
    l_Int32_size = _init_l_Int32_size();
    crate::leanh::lean_mark_persistent(l_Int32_size);
    l_instReprAtomInt32 = _init_l_instReprAtomInt32();
    crate::leanh::lean_mark_persistent(l_instReprAtomInt32);
    l_Int32_maxValue = _init_l_Int32_maxValue();
    l_Int32_minValue = _init_l_Int32_minValue();
    l_instInhabitedInt32 = _init_l_instInhabitedInt32();
    l_instLTInt32 = _init_l_instLTInt32();
    crate::leanh::lean_mark_persistent(l_instLTInt32);
    l_instLEInt32 = _init_l_instLEInt32();
    crate::leanh::lean_mark_persistent(l_instLEInt32);
    l_Int64_size = _init_l_Int64_size();
    crate::leanh::lean_mark_persistent(l_Int64_size);
    l_instReprAtomInt64 = _init_l_instReprAtomInt64();
    crate::leanh::lean_mark_persistent(l_instReprAtomInt64);
    l_Int64_maxValue = _init_l_Int64_maxValue();
    l_Int64_minValue = _init_l_Int64_minValue();
    l_instInhabitedInt64 = _init_l_instInhabitedInt64();
    l_instLTInt64 = _init_l_instLTInt64();
    crate::leanh::lean_mark_persistent(l_instLTInt64);
    l_instLEInt64 = _init_l_instLEInt64();
    crate::leanh::lean_mark_persistent(l_instLEInt64);
    l_ISize_size = _init_l_ISize_size();
    crate::leanh::lean_mark_persistent(l_ISize_size);
    l_instReprAtomISize = _init_l_instReprAtomISize();
    crate::leanh::lean_mark_persistent(l_instReprAtomISize);
    l_ISize_maxValue = _init_l_ISize_maxValue();
    l_ISize_minValue = _init_l_ISize_minValue();
    l_instInhabitedISize = _init_l_instInhabitedISize();
    l_instLTISize = _init_l_instLTISize();
    crate::leanh::lean_mark_persistent(l_instLTISize);
    l_instLEISize = _init_l_instLEISize();
    crate::leanh::lean_mark_persistent(l_instLEISize);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_SInt_Basic(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_SInt_Basic(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_UInt_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_ToString_Extra(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_SInt_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_SInt_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_SInt_Basic(builtin);
}
