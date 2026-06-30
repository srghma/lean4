// Lean compiler output
// Module: Init.Data.UInt.Basic
// Imports: Init.Data.BitVec.Basic
use crate::ffi::{
    lean_bool_to_uint8, lean_bool_to_uint16, lean_bool_to_uint32, lean_bool_to_uint64,
    lean_bool_to_usize, lean_int_emod, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt,
    lean_nat_mod, lean_nat_sub, lean_nat_to_int, lean_uint8_add, lean_uint8_complement,
    lean_uint8_dec_le, lean_uint8_div, lean_uint8_land, lean_uint8_lor, lean_uint8_mod,
    lean_uint8_mul, lean_uint8_neg, lean_uint8_of_nat, lean_uint8_of_nat_mk, lean_uint8_shift_left,
    lean_uint8_shift_right, lean_uint8_sub, lean_uint8_to_nat, lean_uint8_to_usize, lean_uint8_xor,
    lean_uint16_add, lean_uint16_complement, lean_uint16_dec_le, lean_uint16_dec_lt,
    lean_uint16_div, lean_uint16_land, lean_uint16_lor, lean_uint16_mod, lean_uint16_mul,
    lean_uint16_neg, lean_uint16_of_nat, lean_uint16_of_nat_mk, lean_uint16_shift_left,
    lean_uint16_shift_right, lean_uint16_sub, lean_uint16_to_nat, lean_uint16_to_usize,
    lean_uint16_xor, lean_uint32_complement, lean_uint32_div, lean_uint32_land, lean_uint32_lor,
    lean_uint32_mod, lean_uint32_mul, lean_uint32_neg, lean_uint32_of_nat, lean_uint32_of_nat_mk,
    lean_uint32_shift_left, lean_uint32_shift_right, lean_uint32_to_nat, lean_uint32_to_usize,
    lean_uint32_xor, lean_uint64_add, lean_uint64_complement, lean_uint64_dec_le,
    lean_uint64_dec_lt, lean_uint64_div, lean_uint64_land, lean_uint64_lor, lean_uint64_mod,
    lean_uint64_mul, lean_uint64_neg, lean_uint64_of_nat, lean_uint64_of_nat_mk,
    lean_uint64_shift_left, lean_uint64_shift_right, lean_uint64_sub, lean_uint64_to_nat,
    lean_uint64_to_usize, lean_uint64_xor, lean_usize_complement, lean_usize_dec_le,
    lean_usize_div, lean_usize_land, lean_usize_lor, lean_usize_mod, lean_usize_mul,
    lean_usize_neg, lean_usize_of_nat, lean_usize_of_nat_mk, lean_usize_shift_left,
    lean_usize_shift_right, lean_usize_to_nat, lean_usize_to_uint8, lean_usize_to_uint16,
    lean_usize_to_uint32, lean_usize_to_uint64, lean_usize_xor,
};
use crate::r#gen::Init::Data::BitVec::Basic::{
    initialize_Init_Data_BitVec_Basic, runtime_initialize_Init_Data_BitVec_Basic,
};
use crate::r#gen::Init::Data::Int::Basic::{l_Int_pow, l_Int_toNat};
use crate::r#gen::Init::Prelude::{l_BitVec_ofNat, l_System_Platform_numBits};
static mut l_UInt8_ofInt___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_UInt8_ofInt___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_UInt8_ofInt___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_UInt8_ofInt___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_instAddUInt8___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_UInt8_add___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instAddUInt8___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instAddUInt8___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_instAddUInt8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instAddUInt8___closed__0_value) as *mut leanh::LeanObject;
pub static l_instSubUInt8___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_UInt8_sub___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instSubUInt8___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instSubUInt8___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_instSubUInt8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instSubUInt8___closed__0_value) as *mut leanh::LeanObject;
pub static l_instMulUInt8___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_UInt8_mul___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instMulUInt8___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instMulUInt8___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_instMulUInt8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instMulUInt8___closed__0_value) as *mut leanh::LeanObject;
pub static l_instPowUInt8Nat___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_UInt8_pow___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instPowUInt8Nat___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instPowUInt8Nat___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_instPowUInt8Nat: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instPowUInt8Nat___closed__0_value) as *mut leanh::LeanObject;
pub static l_instModUInt8___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_UInt8_mod___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instModUInt8___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instModUInt8___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_instModUInt8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instModUInt8___closed__0_value) as *mut leanh::LeanObject;
pub static l_instHModUInt8Nat___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_UInt8_modn___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instHModUInt8Nat___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instHModUInt8Nat___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_instHModUInt8Nat: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instHModUInt8Nat___closed__0_value) as *mut leanh::LeanObject;
pub static l_instDivUInt8___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_UInt8_div___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instDivUInt8___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instDivUInt8___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_instDivUInt8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instDivUInt8___closed__0_value) as *mut leanh::LeanObject;
pub static l_instComplementUInt8___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_UInt8_complement___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instComplementUInt8___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instComplementUInt8___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_instComplementUInt8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instComplementUInt8___closed__0_value) as *mut leanh::LeanObject;
pub static l_instNegUInt8___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_UInt8_neg___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instNegUInt8___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instNegUInt8___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_instNegUInt8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instNegUInt8___closed__0_value) as *mut leanh::LeanObject;
pub static l_instAndOpUInt8___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_UInt8_land___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instAndOpUInt8___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instAndOpUInt8___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_instAndOpUInt8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instAndOpUInt8___closed__0_value) as *mut leanh::LeanObject;
pub static l_instOrOpUInt8___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_UInt8_lor___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instOrOpUInt8___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instOrOpUInt8___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_instOrOpUInt8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instOrOpUInt8___closed__0_value) as *mut leanh::LeanObject;
pub static l_instXorOpUInt8___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_UInt8_xor___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instXorOpUInt8___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instXorOpUInt8___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_instXorOpUInt8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instXorOpUInt8___closed__0_value) as *mut leanh::LeanObject;
pub static l_instShiftLeftUInt8___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_UInt8_shiftLeft___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instShiftLeftUInt8___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instShiftLeftUInt8___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_instShiftLeftUInt8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instShiftLeftUInt8___closed__0_value) as *mut leanh::LeanObject;
pub static l_instShiftRightUInt8___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_UInt8_shiftRight___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instShiftRightUInt8___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instShiftRightUInt8___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_instShiftRightUInt8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instShiftRightUInt8___closed__0_value) as *mut leanh::LeanObject;
pub static l_instMaxUInt8___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_instMaxUInt8___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instMaxUInt8___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instMaxUInt8___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_instMaxUInt8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instMaxUInt8___closed__0_value) as *mut leanh::LeanObject;
pub static l_instMinUInt8___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_instMinUInt8___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instMinUInt8___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instMinUInt8___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_instMinUInt8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instMinUInt8___closed__0_value) as *mut leanh::LeanObject;
static mut l_UInt16_ofInt___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_UInt16_ofInt___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_instAddUInt16___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_UInt16_add___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instAddUInt16___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instAddUInt16___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_instAddUInt16: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instAddUInt16___closed__0_value) as *mut leanh::LeanObject;
pub static l_instSubUInt16___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_UInt16_sub___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instSubUInt16___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instSubUInt16___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_instSubUInt16: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instSubUInt16___closed__0_value) as *mut leanh::LeanObject;
pub static l_instMulUInt16___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_UInt16_mul___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instMulUInt16___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instMulUInt16___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_instMulUInt16: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instMulUInt16___closed__0_value) as *mut leanh::LeanObject;
pub static l_instPowUInt16Nat___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_UInt16_pow___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instPowUInt16Nat___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instPowUInt16Nat___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_instPowUInt16Nat: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instPowUInt16Nat___closed__0_value) as *mut leanh::LeanObject;
pub static l_instModUInt16___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_UInt16_mod___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instModUInt16___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instModUInt16___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_instModUInt16: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instModUInt16___closed__0_value) as *mut leanh::LeanObject;
pub static l_instHModUInt16Nat___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_UInt16_modn___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instHModUInt16Nat___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instHModUInt16Nat___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_instHModUInt16Nat: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instHModUInt16Nat___closed__0_value) as *mut leanh::LeanObject;
pub static l_instDivUInt16___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_UInt16_div___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instDivUInt16___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instDivUInt16___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_instDivUInt16: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instDivUInt16___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_instLTUInt16: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_instLEUInt16: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_instComplementUInt16___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_UInt16_complement___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instComplementUInt16___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instComplementUInt16___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_instComplementUInt16: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instComplementUInt16___closed__0_value) as *mut leanh::LeanObject;
pub static l_instNegUInt16___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_UInt16_neg___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instNegUInt16___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instNegUInt16___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_instNegUInt16: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instNegUInt16___closed__0_value) as *mut leanh::LeanObject;
pub static l_instAndOpUInt16___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_UInt16_land___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instAndOpUInt16___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instAndOpUInt16___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_instAndOpUInt16: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instAndOpUInt16___closed__0_value) as *mut leanh::LeanObject;
pub static l_instOrOpUInt16___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_UInt16_lor___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instOrOpUInt16___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instOrOpUInt16___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_instOrOpUInt16: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instOrOpUInt16___closed__0_value) as *mut leanh::LeanObject;
pub static l_instXorOpUInt16___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_UInt16_xor___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instXorOpUInt16___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instXorOpUInt16___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_instXorOpUInt16: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instXorOpUInt16___closed__0_value) as *mut leanh::LeanObject;
pub static l_instShiftLeftUInt16___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_UInt16_shiftLeft___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instShiftLeftUInt16___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instShiftLeftUInt16___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_instShiftLeftUInt16: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instShiftLeftUInt16___closed__0_value) as *mut leanh::LeanObject;
pub static l_instShiftRightUInt16___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_UInt16_shiftRight___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instShiftRightUInt16___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instShiftRightUInt16___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_instShiftRightUInt16: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instShiftRightUInt16___closed__0_value) as *mut leanh::LeanObject;
pub static l_instMaxUInt16___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_instMaxUInt16___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instMaxUInt16___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instMaxUInt16___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_instMaxUInt16: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instMaxUInt16___closed__0_value) as *mut leanh::LeanObject;
pub static l_instMinUInt16___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_instMinUInt16___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instMinUInt16___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instMinUInt16___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_instMinUInt16: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instMinUInt16___closed__0_value) as *mut leanh::LeanObject;
static mut l_UInt32_ofInt___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_UInt32_ofInt___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_instMulUInt32___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_UInt32_mul___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instMulUInt32___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instMulUInt32___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_instMulUInt32: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instMulUInt32___closed__0_value) as *mut leanh::LeanObject;
pub static l_instPowUInt32Nat___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_UInt32_pow___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instPowUInt32Nat___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instPowUInt32Nat___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_instPowUInt32Nat: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instPowUInt32Nat___closed__0_value) as *mut leanh::LeanObject;
pub static l_instModUInt32___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_UInt32_mod___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instModUInt32___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instModUInt32___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_instModUInt32: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instModUInt32___closed__0_value) as *mut leanh::LeanObject;
pub static l_instHModUInt32Nat___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_UInt32_modn___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instHModUInt32Nat___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instHModUInt32Nat___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_instHModUInt32Nat: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instHModUInt32Nat___closed__0_value) as *mut leanh::LeanObject;
pub static l_instDivUInt32___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_UInt32_div___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instDivUInt32___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instDivUInt32___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_instDivUInt32: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instDivUInt32___closed__0_value) as *mut leanh::LeanObject;
pub static l_instComplementUInt32___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_UInt32_complement___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instComplementUInt32___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instComplementUInt32___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_instComplementUInt32: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instComplementUInt32___closed__0_value) as *mut leanh::LeanObject;
pub static l_instNegUInt32___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_UInt32_neg___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instNegUInt32___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instNegUInt32___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_instNegUInt32: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instNegUInt32___closed__0_value) as *mut leanh::LeanObject;
pub static l_instAndOpUInt32___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_UInt32_land___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instAndOpUInt32___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instAndOpUInt32___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_instAndOpUInt32: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instAndOpUInt32___closed__0_value) as *mut leanh::LeanObject;
pub static l_instOrOpUInt32___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_UInt32_lor___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instOrOpUInt32___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instOrOpUInt32___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_instOrOpUInt32: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instOrOpUInt32___closed__0_value) as *mut leanh::LeanObject;
pub static l_instXorOpUInt32___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_UInt32_xor___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instXorOpUInt32___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instXorOpUInt32___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_instXorOpUInt32: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instXorOpUInt32___closed__0_value) as *mut leanh::LeanObject;
pub static l_instShiftLeftUInt32___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_UInt32_shiftLeft___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instShiftLeftUInt32___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instShiftLeftUInt32___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_instShiftLeftUInt32: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instShiftLeftUInt32___closed__0_value) as *mut leanh::LeanObject;
pub static l_instShiftRightUInt32___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_UInt32_shiftRight___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instShiftRightUInt32___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instShiftRightUInt32___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_instShiftRightUInt32: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instShiftRightUInt32___closed__0_value) as *mut leanh::LeanObject;
static mut l_UInt64_ofInt___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_UInt64_ofInt___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_instAddUInt64___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_UInt64_add___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instAddUInt64___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instAddUInt64___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_instAddUInt64: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instAddUInt64___closed__0_value) as *mut leanh::LeanObject;
pub static l_instSubUInt64___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_UInt64_sub___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instSubUInt64___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instSubUInt64___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_instSubUInt64: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instSubUInt64___closed__0_value) as *mut leanh::LeanObject;
pub static l_instMulUInt64___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_UInt64_mul___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instMulUInt64___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instMulUInt64___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_instMulUInt64: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instMulUInt64___closed__0_value) as *mut leanh::LeanObject;
pub static l_instPowUInt64Nat___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_UInt64_pow___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instPowUInt64Nat___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instPowUInt64Nat___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_instPowUInt64Nat: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instPowUInt64Nat___closed__0_value) as *mut leanh::LeanObject;
pub static l_instModUInt64___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_UInt64_mod___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instModUInt64___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instModUInt64___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_instModUInt64: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instModUInt64___closed__0_value) as *mut leanh::LeanObject;
pub static l_instHModUInt64Nat___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_UInt64_modn___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instHModUInt64Nat___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instHModUInt64Nat___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_instHModUInt64Nat: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instHModUInt64Nat___closed__0_value) as *mut leanh::LeanObject;
pub static l_instDivUInt64___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_UInt64_div___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instDivUInt64___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instDivUInt64___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_instDivUInt64: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instDivUInt64___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_instLTUInt64: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_instLEUInt64: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_instComplementUInt64___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_UInt64_complement___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instComplementUInt64___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instComplementUInt64___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_instComplementUInt64: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instComplementUInt64___closed__0_value) as *mut leanh::LeanObject;
pub static l_instNegUInt64___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_UInt64_neg___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instNegUInt64___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instNegUInt64___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_instNegUInt64: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instNegUInt64___closed__0_value) as *mut leanh::LeanObject;
pub static l_instAndOpUInt64___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_UInt64_land___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instAndOpUInt64___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instAndOpUInt64___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_instAndOpUInt64: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instAndOpUInt64___closed__0_value) as *mut leanh::LeanObject;
pub static l_instOrOpUInt64___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_UInt64_lor___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instOrOpUInt64___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instOrOpUInt64___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_instOrOpUInt64: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instOrOpUInt64___closed__0_value) as *mut leanh::LeanObject;
pub static l_instXorOpUInt64___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_UInt64_xor___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instXorOpUInt64___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instXorOpUInt64___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_instXorOpUInt64: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instXorOpUInt64___closed__0_value) as *mut leanh::LeanObject;
pub static l_instShiftLeftUInt64___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_UInt64_shiftLeft___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instShiftLeftUInt64___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instShiftLeftUInt64___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_instShiftLeftUInt64: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instShiftLeftUInt64___closed__0_value) as *mut leanh::LeanObject;
pub static l_instShiftRightUInt64___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_UInt64_shiftRight___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instShiftRightUInt64___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instShiftRightUInt64___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_instShiftRightUInt64: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instShiftRightUInt64___closed__0_value) as *mut leanh::LeanObject;
pub static l_instMaxUInt64___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_instMaxUInt64___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instMaxUInt64___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instMaxUInt64___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_instMaxUInt64: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instMaxUInt64___closed__0_value) as *mut leanh::LeanObject;
pub static l_instMinUInt64___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_instMinUInt64___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instMinUInt64___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instMinUInt64___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_instMinUInt64: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instMinUInt64___closed__0_value) as *mut leanh::LeanObject;
static mut l_USize_ofInt___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_USize_ofInt___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_instMulUSize___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_USize_mul___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instMulUSize___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instMulUSize___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_instMulUSize: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instMulUSize___closed__0_value) as *mut leanh::LeanObject;
pub static l_instPowUSizeNat___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_USize_pow___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instPowUSizeNat___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instPowUSizeNat___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_instPowUSizeNat: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instPowUSizeNat___closed__0_value) as *mut leanh::LeanObject;
pub static l_instModUSize___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_USize_mod___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instModUSize___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instModUSize___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_instModUSize: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instModUSize___closed__0_value) as *mut leanh::LeanObject;
pub static l_instHModUSizeNat___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_USize_modn___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instHModUSizeNat___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instHModUSizeNat___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_instHModUSizeNat: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instHModUSizeNat___closed__0_value) as *mut leanh::LeanObject;
pub static l_instDivUSize___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_USize_div___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instDivUSize___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instDivUSize___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_instDivUSize: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instDivUSize___closed__0_value) as *mut leanh::LeanObject;
pub static l_instComplementUSize___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_USize_complement___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instComplementUSize___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instComplementUSize___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_instComplementUSize: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instComplementUSize___closed__0_value) as *mut leanh::LeanObject;
pub static l_instNegUSize___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_USize_neg___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instNegUSize___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instNegUSize___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_instNegUSize: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instNegUSize___closed__0_value) as *mut leanh::LeanObject;
pub static l_instAndOpUSize___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_USize_land___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instAndOpUSize___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instAndOpUSize___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_instAndOpUSize: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instAndOpUSize___closed__0_value) as *mut leanh::LeanObject;
pub static l_instOrOpUSize___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_USize_lor___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instOrOpUSize___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instOrOpUSize___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_instOrOpUSize: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instOrOpUSize___closed__0_value) as *mut leanh::LeanObject;
pub static l_instXorOpUSize___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_USize_xor___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instXorOpUSize___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instXorOpUSize___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_instXorOpUSize: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instXorOpUSize___closed__0_value) as *mut leanh::LeanObject;
pub static l_instShiftLeftUSize___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_USize_shiftLeft___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instShiftLeftUSize___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instShiftLeftUSize___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_instShiftLeftUSize: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instShiftLeftUSize___closed__0_value) as *mut leanh::LeanObject;
pub static l_instShiftRightUSize___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_USize_shiftRight___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instShiftRightUSize___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instShiftRightUSize___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_instShiftRightUSize: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instShiftRightUSize___closed__0_value) as *mut leanh::LeanObject;
pub static l_instMaxUSize___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_instMaxUSize___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instMaxUSize___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instMaxUSize___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_instMaxUSize: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instMaxUSize___closed__0_value) as *mut leanh::LeanObject;
pub static l_instMinUSize___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_instMinUSize___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instMinUSize___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instMinUSize___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_instMinUSize: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instMinUSize___closed__0_value) as *mut leanh::LeanObject;
pub unsafe fn l_UInt8_ofFin(mut v_a_1035_: *mut leanh::LeanObject) -> u8 {
    let mut v___x_1036_: u8 = 0;
    v___x_1036_ = lean_uint8_of_nat_mk(v_a_1035_);
    return v___x_1036_;
}
pub unsafe fn l_UInt8_ofFin___boxed(
    mut v_a_1037_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1038_: u8 = 0;
    let mut v_r_1039_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1038_ = l_UInt8_ofFin(v_a_1037_);
    v_r_1039_ = leanh::lean_box((v_res_1038_) as usize);
    return v_r_1039_;
}
pub unsafe fn _init_l_UInt8_ofInt___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_1040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1041_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1040_ = leanh::lean_unsigned_to_nat(2);
    v___x_1041_ = lean_nat_to_int(v___x_1040_);
    return v___x_1041_;
}
pub unsafe fn _init_l_UInt8_ofInt___closed__1() -> *mut leanh::LeanObject {
    let mut v___x_1042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1044_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1042_ = leanh::lean_unsigned_to_nat(8);
    v___x_1043_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_UInt8_ofInt___closed__0),
        core::ptr::addr_of_mut!(l_UInt8_ofInt___closed__0_once),
        _init_l_UInt8_ofInt___closed__0,
    );
    v___x_1044_ = l_Int_pow(v___x_1043_, v___x_1042_);
    return v___x_1044_;
}
pub unsafe fn l_UInt8_ofInt(mut v_x_1045_: *mut leanh::LeanObject) -> u8 {
    let mut v___x_1046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1049_: u8 = 0;
    v___x_1046_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_UInt8_ofInt___closed__1),
        core::ptr::addr_of_mut!(l_UInt8_ofInt___closed__1_once),
        _init_l_UInt8_ofInt___closed__1,
    );
    v___x_1047_ = lean_int_emod(v_x_1045_, v___x_1046_);
    v___x_1048_ = l_Int_toNat(v___x_1047_);
    leanh::lean_dec(v___x_1047_);
    v___x_1049_ = lean_uint8_of_nat(v___x_1048_);
    leanh::lean_dec(v___x_1048_);
    return v___x_1049_;
}
pub unsafe fn l_UInt8_ofInt___boxed(
    mut v_x_1050_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1051_: u8 = 0;
    let mut v_r_1052_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1051_ = l_UInt8_ofInt(v_x_1050_);
    leanh::lean_dec(v_x_1050_);
    v_r_1052_ = leanh::lean_box((v_res_1051_) as usize);
    return v_r_1052_;
}
pub unsafe fn l_UInt8_add___boxed(
    mut v_a_1055_: *mut leanh::LeanObject,
    mut v_b_1056_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_1057_: u8 = 0;
    let mut v_b_boxed_1058_: u8 = 0;
    let mut v_res_1059_: u8 = 0;
    let mut v_r_1060_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_1057_ = (leanh::lean_unbox(v_a_1055_) as u8);
    v_b_boxed_1058_ = (leanh::lean_unbox(v_b_1056_) as u8);
    v_res_1059_ = lean_uint8_add(v_a_boxed_1057_, v_b_boxed_1058_);
    v_r_1060_ = leanh::lean_box((v_res_1059_) as usize);
    return v_r_1060_;
}
pub unsafe fn l_UInt8_sub___boxed(
    mut v_a_1063_: *mut leanh::LeanObject,
    mut v_b_1064_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_1065_: u8 = 0;
    let mut v_b_boxed_1066_: u8 = 0;
    let mut v_res_1067_: u8 = 0;
    let mut v_r_1068_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_1065_ = (leanh::lean_unbox(v_a_1063_) as u8);
    v_b_boxed_1066_ = (leanh::lean_unbox(v_b_1064_) as u8);
    v_res_1067_ = lean_uint8_sub(v_a_boxed_1065_, v_b_boxed_1066_);
    v_r_1068_ = leanh::lean_box((v_res_1067_) as usize);
    return v_r_1068_;
}
pub unsafe fn l_UInt8_mul___boxed(
    mut v_a_1071_: *mut leanh::LeanObject,
    mut v_b_1072_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_1073_: u8 = 0;
    let mut v_b_boxed_1074_: u8 = 0;
    let mut v_res_1075_: u8 = 0;
    let mut v_r_1076_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_1073_ = (leanh::lean_unbox(v_a_1071_) as u8);
    v_b_boxed_1074_ = (leanh::lean_unbox(v_b_1072_) as u8);
    v_res_1075_ = lean_uint8_mul(v_a_boxed_1073_, v_b_boxed_1074_);
    v_r_1076_ = leanh::lean_box((v_res_1075_) as usize);
    return v_r_1076_;
}
pub unsafe fn l_UInt8_div___boxed(
    mut v_a_1079_: *mut leanh::LeanObject,
    mut v_b_1080_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_1081_: u8 = 0;
    let mut v_b_boxed_1082_: u8 = 0;
    let mut v_res_1083_: u8 = 0;
    let mut v_r_1084_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_1081_ = (leanh::lean_unbox(v_a_1079_) as u8);
    v_b_boxed_1082_ = (leanh::lean_unbox(v_b_1080_) as u8);
    v_res_1083_ = lean_uint8_div(v_a_boxed_1081_, v_b_boxed_1082_);
    v_r_1084_ = leanh::lean_box((v_res_1083_) as usize);
    return v_r_1084_;
}
pub unsafe fn l_UInt8_pow(mut v_x_1085_: u8, mut v_n_1086_: *mut leanh::LeanObject) -> u8 {
    let mut v_zero_1087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_1088_: u8 = 0;
    v_zero_1087_ = leanh::lean_unsigned_to_nat(0);
    v_isZero_1088_ = lean_nat_dec_eq(v_n_1086_, v_zero_1087_);
    if v_isZero_1088_ == 1 {
        let mut v___x_1089_: u8 = 0;
        v___x_1089_ = 1;
        return v___x_1089_;
    } else {
        let mut v_one_1090_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_1091_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1092_: u8 = 0;
        let mut v___x_1093_: u8 = 0;
        v_one_1090_ = leanh::lean_unsigned_to_nat(1);
        v_n_1091_ = lean_nat_sub(v_n_1086_, v_one_1090_);
        v___x_1092_ = l_UInt8_pow(v_x_1085_, v_n_1091_);
        leanh::lean_dec(v_n_1091_);
        v___x_1093_ = lean_uint8_mul(v___x_1092_, v_x_1085_);
        return v___x_1093_;
    }
}
pub unsafe fn l_UInt8_pow___boxed(
    mut v_x_1094_: *mut leanh::LeanObject,
    mut v_n_1095_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_boxed_1096_: u8 = 0;
    let mut v_res_1097_: u8 = 0;
    let mut v_r_1098_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_1096_ = (leanh::lean_unbox(v_x_1094_) as u8);
    v_res_1097_ = l_UInt8_pow(v_x_boxed_1096_, v_n_1095_);
    leanh::lean_dec(v_n_1095_);
    v_r_1098_ = leanh::lean_box((v_res_1097_) as usize);
    return v_r_1098_;
}
pub unsafe fn l_UInt8_mod___boxed(
    mut v_a_1101_: *mut leanh::LeanObject,
    mut v_b_1102_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_1103_: u8 = 0;
    let mut v_b_boxed_1104_: u8 = 0;
    let mut v_res_1105_: u8 = 0;
    let mut v_r_1106_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_1103_ = (leanh::lean_unbox(v_a_1101_) as u8);
    v_b_boxed_1104_ = (leanh::lean_unbox(v_b_1102_) as u8);
    v_res_1105_ = lean_uint8_mod(v_a_boxed_1103_, v_b_boxed_1104_);
    v_r_1106_ = leanh::lean_box((v_res_1105_) as usize);
    return v_r_1106_;
}
pub unsafe fn l_Nat_cast___at___00UInt8_modn_spec__0(
    mut v_a_1107_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1109_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1108_ = leanh::lean_unsigned_to_nat(8);
    v___x_1109_ = l_BitVec_ofNat(v___x_1108_, v_a_1107_);
    return v___x_1109_;
}
pub unsafe fn l_Nat_cast___at___00UInt8_modn_spec__0___boxed(
    mut v_a_1110_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1111_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1111_ = l_Nat_cast___at___00UInt8_modn_spec__0(v_a_1110_);
    leanh::lean_dec(v_a_1110_);
    return v_res_1111_;
}
pub unsafe fn l_UInt8_modn(mut v_a_1112_: u8, mut v_n_1113_: *mut leanh::LeanObject) -> u8 {
    let mut v___x_1114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1117_: u8 = 0;
    v___x_1114_ = lean_uint8_to_nat(v_a_1112_);
    v___x_1115_ = lean_nat_mod(v___x_1114_, v_n_1113_);
    leanh::lean_dec(v___x_1114_);
    v___x_1116_ = l_Nat_cast___at___00UInt8_modn_spec__0(v___x_1115_);
    leanh::lean_dec(v___x_1115_);
    v___x_1117_ = lean_uint8_of_nat_mk(v___x_1116_);
    return v___x_1117_;
}
pub unsafe fn l_UInt8_modn___boxed(
    mut v_a_1118_: *mut leanh::LeanObject,
    mut v_n_1119_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_1120_: u8 = 0;
    let mut v_res_1121_: u8 = 0;
    let mut v_r_1122_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_1120_ = (leanh::lean_unbox(v_a_1118_) as u8);
    v_res_1121_ = l_UInt8_modn(v_a_boxed_1120_, v_n_1119_);
    leanh::lean_dec(v_n_1119_);
    v_r_1122_ = leanh::lean_box((v_res_1121_) as usize);
    return v_r_1122_;
}
pub unsafe fn l_UInt8_land___boxed(
    mut v_a_1125_: *mut leanh::LeanObject,
    mut v_b_1126_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_1127_: u8 = 0;
    let mut v_b_boxed_1128_: u8 = 0;
    let mut v_res_1129_: u8 = 0;
    let mut v_r_1130_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_1127_ = (leanh::lean_unbox(v_a_1125_) as u8);
    v_b_boxed_1128_ = (leanh::lean_unbox(v_b_1126_) as u8);
    v_res_1129_ = lean_uint8_land(v_a_boxed_1127_, v_b_boxed_1128_);
    v_r_1130_ = leanh::lean_box((v_res_1129_) as usize);
    return v_r_1130_;
}
pub unsafe fn l_UInt8_lor___boxed(
    mut v_a_1133_: *mut leanh::LeanObject,
    mut v_b_1134_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_1135_: u8 = 0;
    let mut v_b_boxed_1136_: u8 = 0;
    let mut v_res_1137_: u8 = 0;
    let mut v_r_1138_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_1135_ = (leanh::lean_unbox(v_a_1133_) as u8);
    v_b_boxed_1136_ = (leanh::lean_unbox(v_b_1134_) as u8);
    v_res_1137_ = lean_uint8_lor(v_a_boxed_1135_, v_b_boxed_1136_);
    v_r_1138_ = leanh::lean_box((v_res_1137_) as usize);
    return v_r_1138_;
}
pub unsafe fn l_UInt8_xor___boxed(
    mut v_a_1141_: *mut leanh::LeanObject,
    mut v_b_1142_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_1143_: u8 = 0;
    let mut v_b_boxed_1144_: u8 = 0;
    let mut v_res_1145_: u8 = 0;
    let mut v_r_1146_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_1143_ = (leanh::lean_unbox(v_a_1141_) as u8);
    v_b_boxed_1144_ = (leanh::lean_unbox(v_b_1142_) as u8);
    v_res_1145_ = lean_uint8_xor(v_a_boxed_1143_, v_b_boxed_1144_);
    v_r_1146_ = leanh::lean_box((v_res_1145_) as usize);
    return v_r_1146_;
}
pub unsafe fn l_UInt8_shiftLeft___boxed(
    mut v_a_1149_: *mut leanh::LeanObject,
    mut v_b_1150_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_1151_: u8 = 0;
    let mut v_b_boxed_1152_: u8 = 0;
    let mut v_res_1153_: u8 = 0;
    let mut v_r_1154_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_1151_ = (leanh::lean_unbox(v_a_1149_) as u8);
    v_b_boxed_1152_ = (leanh::lean_unbox(v_b_1150_) as u8);
    v_res_1153_ = lean_uint8_shift_left(v_a_boxed_1151_, v_b_boxed_1152_);
    v_r_1154_ = leanh::lean_box((v_res_1153_) as usize);
    return v_r_1154_;
}
pub unsafe fn l_UInt8_shiftRight___boxed(
    mut v_a_1157_: *mut leanh::LeanObject,
    mut v_b_1158_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_1159_: u8 = 0;
    let mut v_b_boxed_1160_: u8 = 0;
    let mut v_res_1161_: u8 = 0;
    let mut v_r_1162_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_1159_ = (leanh::lean_unbox(v_a_1157_) as u8);
    v_b_boxed_1160_ = (leanh::lean_unbox(v_b_1158_) as u8);
    v_res_1161_ = lean_uint8_shift_right(v_a_boxed_1159_, v_b_boxed_1160_);
    v_r_1162_ = leanh::lean_box((v_res_1161_) as usize);
    return v_r_1162_;
}
pub unsafe fn l_UInt8_complement___boxed(
    mut v_a_1178_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_1179_: u8 = 0;
    let mut v_res_1180_: u8 = 0;
    let mut v_r_1181_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_1179_ = (leanh::lean_unbox(v_a_1178_) as u8);
    v_res_1180_ = lean_uint8_complement(v_a_boxed_1179_);
    v_r_1181_ = leanh::lean_box((v_res_1180_) as usize);
    return v_r_1181_;
}
pub unsafe fn l_UInt8_neg___boxed(
    mut v_a_1183_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_1184_: u8 = 0;
    let mut v_res_1185_: u8 = 0;
    let mut v_r_1186_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_1184_ = (leanh::lean_unbox(v_a_1183_) as u8);
    v_res_1185_ = lean_uint8_neg(v_a_boxed_1184_);
    v_r_1186_ = leanh::lean_box((v_res_1185_) as usize);
    return v_r_1186_;
}
pub unsafe fn l_Bool_toUInt8___boxed(
    mut v_b_1202_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_b_boxed_1203_: u8 = 0;
    let mut v_res_1204_: u8 = 0;
    let mut v_r_1205_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_b_boxed_1203_ = (leanh::lean_unbox(v_b_1202_) as u8);
    v_res_1204_ = lean_bool_to_uint8(v_b_boxed_1203_);
    v_r_1205_ = leanh::lean_box((v_res_1204_) as usize);
    return v_r_1205_;
}
pub unsafe fn l_instMaxUInt8___lam__0(mut v_x_1206_: u8, mut v_y_1207_: u8) -> u8 {
    let mut v___x_1208_: u8 = 0;
    v___x_1208_ = lean_uint8_dec_le(v_x_1206_, v_y_1207_);
    if v___x_1208_ == 0 {
        return v_x_1206_;
    } else {
        return v_y_1207_;
    }
}
pub unsafe fn l_instMaxUInt8___lam__0___boxed(
    mut v_x_1209_: *mut leanh::LeanObject,
    mut v_y_1210_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_boxed_1211_: u8 = 0;
    let mut v_y_boxed_1212_: u8 = 0;
    let mut v_res_1213_: u8 = 0;
    let mut v_r_1214_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_1211_ = (leanh::lean_unbox(v_x_1209_) as u8);
    v_y_boxed_1212_ = (leanh::lean_unbox(v_y_1210_) as u8);
    v_res_1213_ = l_instMaxUInt8___lam__0(v_x_boxed_1211_, v_y_boxed_1212_);
    v_r_1214_ = leanh::lean_box((v_res_1213_) as usize);
    return v_r_1214_;
}
pub unsafe fn l_instMinUInt8___lam__0(mut v_x_1217_: u8, mut v_y_1218_: u8) -> u8 {
    let mut v___x_1219_: u8 = 0;
    v___x_1219_ = lean_uint8_dec_le(v_x_1217_, v_y_1218_);
    if v___x_1219_ == 0 {
        return v_y_1218_;
    } else {
        return v_x_1217_;
    }
}
pub unsafe fn l_instMinUInt8___lam__0___boxed(
    mut v_x_1220_: *mut leanh::LeanObject,
    mut v_y_1221_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_boxed_1222_: u8 = 0;
    let mut v_y_boxed_1223_: u8 = 0;
    let mut v_res_1224_: u8 = 0;
    let mut v_r_1225_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_1222_ = (leanh::lean_unbox(v_x_1220_) as u8);
    v_y_boxed_1223_ = (leanh::lean_unbox(v_y_1221_) as u8);
    v_res_1224_ = l_instMinUInt8___lam__0(v_x_boxed_1222_, v_y_boxed_1223_);
    v_r_1225_ = leanh::lean_box((v_res_1224_) as usize);
    return v_r_1225_;
}
pub unsafe fn l_UInt8_toAsciiLower(mut v_b_1228_: u8) -> u8 {
    let mut v___y_1230_: u8 = 0;
    let mut v___x_1231_: u8 = 0;
    let mut v___x_1232_: u8 = 0;
    let mut v___x_1233_: u8 = 0;
    let mut v___x_1234_: u8 = 0;
    let mut v___x_1235_: u8 = 0;
    let mut v___x_1236_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1233_ = 65;
                v___x_1234_ = lean_uint8_dec_le(v___x_1233_, v_b_1228_);
                if v___x_1234_ == 0 {
                    v___y_1230_ = v___x_1234_;
                    state = 1;
                    continue;
                } else {
                    v___x_1235_ = 90;
                    v___x_1236_ = lean_uint8_dec_le(v_b_1228_, v___x_1235_);
                    v___y_1230_ = v___x_1236_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_1230_ == 0 {
                    return v_b_1228_;
                } else {
                    v___x_1231_ = 32;
                    v___x_1232_ = lean_uint8_add(v_b_1228_, v___x_1231_);
                    return v___x_1232_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_UInt8_toAsciiLower___boxed(
    mut v_b_1237_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_b_boxed_1238_: u8 = 0;
    let mut v_res_1239_: u8 = 0;
    let mut v_r_1240_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_b_boxed_1238_ = (leanh::lean_unbox(v_b_1237_) as u8);
    v_res_1239_ = l_UInt8_toAsciiLower(v_b_boxed_1238_);
    v_r_1240_ = leanh::lean_box((v_res_1239_) as usize);
    return v_r_1240_;
}
pub unsafe fn l_UInt16_ofFin(mut v_a_1241_: *mut leanh::LeanObject) -> u16 {
    let mut v___x_1242_: u16 = 0;
    v___x_1242_ = lean_uint16_of_nat_mk(v_a_1241_);
    return v___x_1242_;
}
pub unsafe fn l_UInt16_ofFin___boxed(
    mut v_a_1243_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1244_: u16 = 0;
    let mut v_r_1245_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1244_ = l_UInt16_ofFin(v_a_1243_);
    v_r_1245_ = leanh::lean_box((v_res_1244_) as usize);
    return v_r_1245_;
}
pub unsafe fn _init_l_UInt16_ofInt___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_1246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1248_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1246_ = leanh::lean_unsigned_to_nat(16);
    v___x_1247_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_UInt8_ofInt___closed__0),
        core::ptr::addr_of_mut!(l_UInt8_ofInt___closed__0_once),
        _init_l_UInt8_ofInt___closed__0,
    );
    v___x_1248_ = l_Int_pow(v___x_1247_, v___x_1246_);
    return v___x_1248_;
}
pub unsafe fn l_UInt16_ofInt(mut v_x_1249_: *mut leanh::LeanObject) -> u16 {
    let mut v___x_1250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1253_: u16 = 0;
    v___x_1250_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_UInt16_ofInt___closed__0),
        core::ptr::addr_of_mut!(l_UInt16_ofInt___closed__0_once),
        _init_l_UInt16_ofInt___closed__0,
    );
    v___x_1251_ = lean_int_emod(v_x_1249_, v___x_1250_);
    v___x_1252_ = l_Int_toNat(v___x_1251_);
    leanh::lean_dec(v___x_1251_);
    v___x_1253_ = lean_uint16_of_nat(v___x_1252_);
    leanh::lean_dec(v___x_1252_);
    return v___x_1253_;
}
pub unsafe fn l_UInt16_ofInt___boxed(
    mut v_x_1254_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1255_: u16 = 0;
    let mut v_r_1256_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1255_ = l_UInt16_ofInt(v_x_1254_);
    leanh::lean_dec(v_x_1254_);
    v_r_1256_ = leanh::lean_box((v_res_1255_) as usize);
    return v_r_1256_;
}
pub unsafe fn l_UInt16_add___boxed(
    mut v_a_1259_: *mut leanh::LeanObject,
    mut v_b_1260_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_1261_: u16 = 0;
    let mut v_b_boxed_1262_: u16 = 0;
    let mut v_res_1263_: u16 = 0;
    let mut v_r_1264_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_1261_ = (leanh::lean_unbox(v_a_1259_) as u16);
    v_b_boxed_1262_ = (leanh::lean_unbox(v_b_1260_) as u16);
    v_res_1263_ = lean_uint16_add(v_a_boxed_1261_, v_b_boxed_1262_);
    v_r_1264_ = leanh::lean_box((v_res_1263_) as usize);
    return v_r_1264_;
}
pub unsafe fn l_UInt16_sub___boxed(
    mut v_a_1267_: *mut leanh::LeanObject,
    mut v_b_1268_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_1269_: u16 = 0;
    let mut v_b_boxed_1270_: u16 = 0;
    let mut v_res_1271_: u16 = 0;
    let mut v_r_1272_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_1269_ = (leanh::lean_unbox(v_a_1267_) as u16);
    v_b_boxed_1270_ = (leanh::lean_unbox(v_b_1268_) as u16);
    v_res_1271_ = lean_uint16_sub(v_a_boxed_1269_, v_b_boxed_1270_);
    v_r_1272_ = leanh::lean_box((v_res_1271_) as usize);
    return v_r_1272_;
}
pub unsafe fn l_UInt16_mul___boxed(
    mut v_a_1275_: *mut leanh::LeanObject,
    mut v_b_1276_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_1277_: u16 = 0;
    let mut v_b_boxed_1278_: u16 = 0;
    let mut v_res_1279_: u16 = 0;
    let mut v_r_1280_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_1277_ = (leanh::lean_unbox(v_a_1275_) as u16);
    v_b_boxed_1278_ = (leanh::lean_unbox(v_b_1276_) as u16);
    v_res_1279_ = lean_uint16_mul(v_a_boxed_1277_, v_b_boxed_1278_);
    v_r_1280_ = leanh::lean_box((v_res_1279_) as usize);
    return v_r_1280_;
}
pub unsafe fn l_UInt16_div___boxed(
    mut v_a_1283_: *mut leanh::LeanObject,
    mut v_b_1284_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_1285_: u16 = 0;
    let mut v_b_boxed_1286_: u16 = 0;
    let mut v_res_1287_: u16 = 0;
    let mut v_r_1288_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_1285_ = (leanh::lean_unbox(v_a_1283_) as u16);
    v_b_boxed_1286_ = (leanh::lean_unbox(v_b_1284_) as u16);
    v_res_1287_ = lean_uint16_div(v_a_boxed_1285_, v_b_boxed_1286_);
    v_r_1288_ = leanh::lean_box((v_res_1287_) as usize);
    return v_r_1288_;
}
pub unsafe fn l_UInt16_pow(
    mut v_x_1289_: u16,
    mut v_n_1290_: *mut leanh::LeanObject,
) -> u16 {
    let mut v_zero_1291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_1292_: u8 = 0;
    v_zero_1291_ = leanh::lean_unsigned_to_nat(0);
    v_isZero_1292_ = lean_nat_dec_eq(v_n_1290_, v_zero_1291_);
    if v_isZero_1292_ == 1 {
        let mut v___x_1293_: u16 = 0;
        v___x_1293_ = 1;
        return v___x_1293_;
    } else {
        let mut v_one_1294_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_1295_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1296_: u16 = 0;
        let mut v___x_1297_: u16 = 0;
        v_one_1294_ = leanh::lean_unsigned_to_nat(1);
        v_n_1295_ = lean_nat_sub(v_n_1290_, v_one_1294_);
        v___x_1296_ = l_UInt16_pow(v_x_1289_, v_n_1295_);
        leanh::lean_dec(v_n_1295_);
        v___x_1297_ = lean_uint16_mul(v___x_1296_, v_x_1289_);
        return v___x_1297_;
    }
}
pub unsafe fn l_UInt16_pow___boxed(
    mut v_x_1298_: *mut leanh::LeanObject,
    mut v_n_1299_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_boxed_1300_: u16 = 0;
    let mut v_res_1301_: u16 = 0;
    let mut v_r_1302_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_1300_ = (leanh::lean_unbox(v_x_1298_) as u16);
    v_res_1301_ = l_UInt16_pow(v_x_boxed_1300_, v_n_1299_);
    leanh::lean_dec(v_n_1299_);
    v_r_1302_ = leanh::lean_box((v_res_1301_) as usize);
    return v_r_1302_;
}
pub unsafe fn l_UInt16_mod___boxed(
    mut v_a_1305_: *mut leanh::LeanObject,
    mut v_b_1306_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_1307_: u16 = 0;
    let mut v_b_boxed_1308_: u16 = 0;
    let mut v_res_1309_: u16 = 0;
    let mut v_r_1310_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_1307_ = (leanh::lean_unbox(v_a_1305_) as u16);
    v_b_boxed_1308_ = (leanh::lean_unbox(v_b_1306_) as u16);
    v_res_1309_ = lean_uint16_mod(v_a_boxed_1307_, v_b_boxed_1308_);
    v_r_1310_ = leanh::lean_box((v_res_1309_) as usize);
    return v_r_1310_;
}
pub unsafe fn l_Nat_cast___at___00UInt16_modn_spec__0(
    mut v_a_1311_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1313_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1312_ = leanh::lean_unsigned_to_nat(16);
    v___x_1313_ = l_BitVec_ofNat(v___x_1312_, v_a_1311_);
    return v___x_1313_;
}
pub unsafe fn l_Nat_cast___at___00UInt16_modn_spec__0___boxed(
    mut v_a_1314_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1315_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1315_ = l_Nat_cast___at___00UInt16_modn_spec__0(v_a_1314_);
    leanh::lean_dec(v_a_1314_);
    return v_res_1315_;
}
pub unsafe fn l_UInt16_modn(
    mut v_a_1316_: u16,
    mut v_n_1317_: *mut leanh::LeanObject,
) -> u16 {
    let mut v___x_1318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1321_: u16 = 0;
    v___x_1318_ = lean_uint16_to_nat(v_a_1316_);
    v___x_1319_ = lean_nat_mod(v___x_1318_, v_n_1317_);
    leanh::lean_dec(v___x_1318_);
    v___x_1320_ = l_Nat_cast___at___00UInt16_modn_spec__0(v___x_1319_);
    leanh::lean_dec(v___x_1319_);
    v___x_1321_ = lean_uint16_of_nat_mk(v___x_1320_);
    return v___x_1321_;
}
pub unsafe fn l_UInt16_modn___boxed(
    mut v_a_1322_: *mut leanh::LeanObject,
    mut v_n_1323_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_1324_: u16 = 0;
    let mut v_res_1325_: u16 = 0;
    let mut v_r_1326_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_1324_ = (leanh::lean_unbox(v_a_1322_) as u16);
    v_res_1325_ = l_UInt16_modn(v_a_boxed_1324_, v_n_1323_);
    leanh::lean_dec(v_n_1323_);
    v_r_1326_ = leanh::lean_box((v_res_1325_) as usize);
    return v_r_1326_;
}
pub unsafe fn l_UInt16_land___boxed(
    mut v_a_1329_: *mut leanh::LeanObject,
    mut v_b_1330_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_1331_: u16 = 0;
    let mut v_b_boxed_1332_: u16 = 0;
    let mut v_res_1333_: u16 = 0;
    let mut v_r_1334_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_1331_ = (leanh::lean_unbox(v_a_1329_) as u16);
    v_b_boxed_1332_ = (leanh::lean_unbox(v_b_1330_) as u16);
    v_res_1333_ = lean_uint16_land(v_a_boxed_1331_, v_b_boxed_1332_);
    v_r_1334_ = leanh::lean_box((v_res_1333_) as usize);
    return v_r_1334_;
}
pub unsafe fn l_UInt16_lor___boxed(
    mut v_a_1337_: *mut leanh::LeanObject,
    mut v_b_1338_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_1339_: u16 = 0;
    let mut v_b_boxed_1340_: u16 = 0;
    let mut v_res_1341_: u16 = 0;
    let mut v_r_1342_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_1339_ = (leanh::lean_unbox(v_a_1337_) as u16);
    v_b_boxed_1340_ = (leanh::lean_unbox(v_b_1338_) as u16);
    v_res_1341_ = lean_uint16_lor(v_a_boxed_1339_, v_b_boxed_1340_);
    v_r_1342_ = leanh::lean_box((v_res_1341_) as usize);
    return v_r_1342_;
}
pub unsafe fn l_UInt16_xor___boxed(
    mut v_a_1345_: *mut leanh::LeanObject,
    mut v_b_1346_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_1347_: u16 = 0;
    let mut v_b_boxed_1348_: u16 = 0;
    let mut v_res_1349_: u16 = 0;
    let mut v_r_1350_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_1347_ = (leanh::lean_unbox(v_a_1345_) as u16);
    v_b_boxed_1348_ = (leanh::lean_unbox(v_b_1346_) as u16);
    v_res_1349_ = lean_uint16_xor(v_a_boxed_1347_, v_b_boxed_1348_);
    v_r_1350_ = leanh::lean_box((v_res_1349_) as usize);
    return v_r_1350_;
}
pub unsafe fn l_UInt16_shiftLeft___boxed(
    mut v_a_1353_: *mut leanh::LeanObject,
    mut v_b_1354_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_1355_: u16 = 0;
    let mut v_b_boxed_1356_: u16 = 0;
    let mut v_res_1357_: u16 = 0;
    let mut v_r_1358_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_1355_ = (leanh::lean_unbox(v_a_1353_) as u16);
    v_b_boxed_1356_ = (leanh::lean_unbox(v_b_1354_) as u16);
    v_res_1357_ = lean_uint16_shift_left(v_a_boxed_1355_, v_b_boxed_1356_);
    v_r_1358_ = leanh::lean_box((v_res_1357_) as usize);
    return v_r_1358_;
}
pub unsafe fn l_UInt16_shiftRight___boxed(
    mut v_a_1361_: *mut leanh::LeanObject,
    mut v_b_1362_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_1363_: u16 = 0;
    let mut v_b_boxed_1364_: u16 = 0;
    let mut v_res_1365_: u16 = 0;
    let mut v_r_1366_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_1363_ = (leanh::lean_unbox(v_a_1361_) as u16);
    v_b_boxed_1364_ = (leanh::lean_unbox(v_b_1362_) as u16);
    v_res_1365_ = lean_uint16_shift_right(v_a_boxed_1363_, v_b_boxed_1364_);
    v_r_1366_ = leanh::lean_box((v_res_1365_) as usize);
    return v_r_1366_;
}
pub unsafe fn _init_l_instLTUInt16() -> *mut leanh::LeanObject {
    let mut v___x_1381_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1381_ = leanh::lean_box(0);
    return v___x_1381_;
}
pub unsafe fn _init_l_instLEUInt16() -> *mut leanh::LeanObject {
    let mut v___x_1382_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1382_ = leanh::lean_box(0);
    return v___x_1382_;
}
pub unsafe fn l_UInt16_complement___boxed(
    mut v_a_1384_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_1385_: u16 = 0;
    let mut v_res_1386_: u16 = 0;
    let mut v_r_1387_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_1385_ = (leanh::lean_unbox(v_a_1384_) as u16);
    v_res_1386_ = lean_uint16_complement(v_a_boxed_1385_);
    v_r_1387_ = leanh::lean_box((v_res_1386_) as usize);
    return v_r_1387_;
}
pub unsafe fn l_UInt16_neg___boxed(
    mut v_a_1389_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_1390_: u16 = 0;
    let mut v_res_1391_: u16 = 0;
    let mut v_r_1392_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_1390_ = (leanh::lean_unbox(v_a_1389_) as u16);
    v_res_1391_ = lean_uint16_neg(v_a_boxed_1390_);
    v_r_1392_ = leanh::lean_box((v_res_1391_) as usize);
    return v_r_1392_;
}
pub unsafe fn l_Bool_toUInt16___boxed(
    mut v_b_1408_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_b_boxed_1409_: u8 = 0;
    let mut v_res_1410_: u16 = 0;
    let mut v_r_1411_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_b_boxed_1409_ = (leanh::lean_unbox(v_b_1408_) as u8);
    v_res_1410_ = lean_bool_to_uint16(v_b_boxed_1409_);
    v_r_1411_ = leanh::lean_box((v_res_1410_) as usize);
    return v_r_1411_;
}
pub unsafe fn l_UInt16_decLt___aux__1(mut v_a_1412_: u16, mut v_b_1413_: u16) -> u8 {
    let mut v___x_1414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1416_: u8 = 0;
    v___x_1414_ = lean_uint16_to_nat(v_a_1412_);
    v___x_1415_ = lean_uint16_to_nat(v_b_1413_);
    v___x_1416_ = lean_nat_dec_lt(v___x_1414_, v___x_1415_);
    leanh::lean_dec(v___x_1415_);
    leanh::lean_dec(v___x_1414_);
    return v___x_1416_;
}
pub unsafe fn l_UInt16_decLt___aux__1___boxed(
    mut v_a_1417_: *mut leanh::LeanObject,
    mut v_b_1418_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_1419_: u16 = 0;
    let mut v_b_boxed_1420_: u16 = 0;
    let mut v_res_1421_: u8 = 0;
    let mut v_r_1422_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_1419_ = (leanh::lean_unbox(v_a_1417_) as u16);
    v_b_boxed_1420_ = (leanh::lean_unbox(v_b_1418_) as u16);
    v_res_1421_ = l_UInt16_decLt___aux__1(v_a_boxed_1419_, v_b_boxed_1420_);
    v_r_1422_ = leanh::lean_box((v_res_1421_) as usize);
    return v_r_1422_;
}
pub unsafe fn l_UInt16_decLt___boxed(
    mut v_a_1425_: *mut leanh::LeanObject,
    mut v_b_1426_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_1427_: u16 = 0;
    let mut v_b_boxed_1428_: u16 = 0;
    let mut v_res_1429_: u8 = 0;
    let mut v_r_1430_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_1427_ = (leanh::lean_unbox(v_a_1425_) as u16);
    v_b_boxed_1428_ = (leanh::lean_unbox(v_b_1426_) as u16);
    v_res_1429_ = lean_uint16_dec_lt(v_a_boxed_1427_, v_b_boxed_1428_);
    v_r_1430_ = leanh::lean_box((v_res_1429_) as usize);
    return v_r_1430_;
}
pub unsafe fn l_UInt16_decLe___aux__1(mut v_a_1431_: u16, mut v_b_1432_: u16) -> u8 {
    let mut v___x_1433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1435_: u8 = 0;
    v___x_1433_ = lean_uint16_to_nat(v_a_1431_);
    v___x_1434_ = lean_uint16_to_nat(v_b_1432_);
    v___x_1435_ = lean_nat_dec_le(v___x_1433_, v___x_1434_);
    leanh::lean_dec(v___x_1434_);
    leanh::lean_dec(v___x_1433_);
    return v___x_1435_;
}
pub unsafe fn l_UInt16_decLe___aux__1___boxed(
    mut v_a_1436_: *mut leanh::LeanObject,
    mut v_b_1437_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_1438_: u16 = 0;
    let mut v_b_boxed_1439_: u16 = 0;
    let mut v_res_1440_: u8 = 0;
    let mut v_r_1441_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_1438_ = (leanh::lean_unbox(v_a_1436_) as u16);
    v_b_boxed_1439_ = (leanh::lean_unbox(v_b_1437_) as u16);
    v_res_1440_ = l_UInt16_decLe___aux__1(v_a_boxed_1438_, v_b_boxed_1439_);
    v_r_1441_ = leanh::lean_box((v_res_1440_) as usize);
    return v_r_1441_;
}
pub unsafe fn l_UInt16_decLe___boxed(
    mut v_a_1444_: *mut leanh::LeanObject,
    mut v_b_1445_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_1446_: u16 = 0;
    let mut v_b_boxed_1447_: u16 = 0;
    let mut v_res_1448_: u8 = 0;
    let mut v_r_1449_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_1446_ = (leanh::lean_unbox(v_a_1444_) as u16);
    v_b_boxed_1447_ = (leanh::lean_unbox(v_b_1445_) as u16);
    v_res_1448_ = lean_uint16_dec_le(v_a_boxed_1446_, v_b_boxed_1447_);
    v_r_1449_ = leanh::lean_box((v_res_1448_) as usize);
    return v_r_1449_;
}
pub unsafe fn l_instMaxUInt16___lam__0(mut v_x_1450_: u16, mut v_y_1451_: u16) -> u16 {
    let mut v___x_1452_: u8 = 0;
    v___x_1452_ = lean_uint16_dec_le(v_x_1450_, v_y_1451_);
    if v___x_1452_ == 0 {
        return v_x_1450_;
    } else {
        return v_y_1451_;
    }
}
pub unsafe fn l_instMaxUInt16___lam__0___boxed(
    mut v_x_1453_: *mut leanh::LeanObject,
    mut v_y_1454_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_boxed_1455_: u16 = 0;
    let mut v_y_boxed_1456_: u16 = 0;
    let mut v_res_1457_: u16 = 0;
    let mut v_r_1458_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_1455_ = (leanh::lean_unbox(v_x_1453_) as u16);
    v_y_boxed_1456_ = (leanh::lean_unbox(v_y_1454_) as u16);
    v_res_1457_ = l_instMaxUInt16___lam__0(v_x_boxed_1455_, v_y_boxed_1456_);
    v_r_1458_ = leanh::lean_box((v_res_1457_) as usize);
    return v_r_1458_;
}
pub unsafe fn l_instMinUInt16___lam__0(mut v_x_1461_: u16, mut v_y_1462_: u16) -> u16 {
    let mut v___x_1463_: u8 = 0;
    v___x_1463_ = lean_uint16_dec_le(v_x_1461_, v_y_1462_);
    if v___x_1463_ == 0 {
        return v_y_1462_;
    } else {
        return v_x_1461_;
    }
}
pub unsafe fn l_instMinUInt16___lam__0___boxed(
    mut v_x_1464_: *mut leanh::LeanObject,
    mut v_y_1465_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_boxed_1466_: u16 = 0;
    let mut v_y_boxed_1467_: u16 = 0;
    let mut v_res_1468_: u16 = 0;
    let mut v_r_1469_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_1466_ = (leanh::lean_unbox(v_x_1464_) as u16);
    v_y_boxed_1467_ = (leanh::lean_unbox(v_y_1465_) as u16);
    v_res_1468_ = l_instMinUInt16___lam__0(v_x_boxed_1466_, v_y_boxed_1467_);
    v_r_1469_ = leanh::lean_box((v_res_1468_) as usize);
    return v_r_1469_;
}
pub unsafe fn l_UInt32_ofFin(mut v_a_1472_: *mut leanh::LeanObject) -> u32 {
    let mut v___x_1473_: u32 = 0;
    v___x_1473_ = lean_uint32_of_nat_mk(v_a_1472_);
    return v___x_1473_;
}
pub unsafe fn l_UInt32_ofFin___boxed(
    mut v_a_1474_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1475_: u32 = 0;
    let mut v_r_1476_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1475_ = l_UInt32_ofFin(v_a_1474_);
    v_r_1476_ = leanh::lean_box_uint32(v_res_1475_);
    return v_r_1476_;
}
pub unsafe fn _init_l_UInt32_ofInt___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_1477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1479_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1477_ = leanh::lean_unsigned_to_nat(32);
    v___x_1478_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_UInt8_ofInt___closed__0),
        core::ptr::addr_of_mut!(l_UInt8_ofInt___closed__0_once),
        _init_l_UInt8_ofInt___closed__0,
    );
    v___x_1479_ = l_Int_pow(v___x_1478_, v___x_1477_);
    return v___x_1479_;
}
pub unsafe fn l_UInt32_ofInt(mut v_x_1480_: *mut leanh::LeanObject) -> u32 {
    let mut v___x_1481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1484_: u32 = 0;
    v___x_1481_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_UInt32_ofInt___closed__0),
        core::ptr::addr_of_mut!(l_UInt32_ofInt___closed__0_once),
        _init_l_UInt32_ofInt___closed__0,
    );
    v___x_1482_ = lean_int_emod(v_x_1480_, v___x_1481_);
    v___x_1483_ = l_Int_toNat(v___x_1482_);
    leanh::lean_dec(v___x_1482_);
    v___x_1484_ = lean_uint32_of_nat(v___x_1483_);
    leanh::lean_dec(v___x_1483_);
    return v___x_1484_;
}
pub unsafe fn l_UInt32_ofInt___boxed(
    mut v_x_1485_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1486_: u32 = 0;
    let mut v_r_1487_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1486_ = l_UInt32_ofInt(v_x_1485_);
    leanh::lean_dec(v_x_1485_);
    v_r_1487_ = leanh::lean_box_uint32(v_res_1486_);
    return v_r_1487_;
}
pub unsafe fn l_UInt32_mul___boxed(
    mut v_a_1490_: *mut leanh::LeanObject,
    mut v_b_1491_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_1492_: u32 = 0;
    let mut v_b_boxed_1493_: u32 = 0;
    let mut v_res_1494_: u32 = 0;
    let mut v_r_1495_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_1492_ = leanh::lean_unbox_uint32(v_a_1490_);
    leanh::lean_dec(v_a_1490_);
    v_b_boxed_1493_ = leanh::lean_unbox_uint32(v_b_1491_);
    leanh::lean_dec(v_b_1491_);
    v_res_1494_ = lean_uint32_mul(v_a_boxed_1492_, v_b_boxed_1493_);
    v_r_1495_ = leanh::lean_box_uint32(v_res_1494_);
    return v_r_1495_;
}
pub unsafe fn l_UInt32_div___boxed(
    mut v_a_1498_: *mut leanh::LeanObject,
    mut v_b_1499_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_1500_: u32 = 0;
    let mut v_b_boxed_1501_: u32 = 0;
    let mut v_res_1502_: u32 = 0;
    let mut v_r_1503_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_1500_ = leanh::lean_unbox_uint32(v_a_1498_);
    leanh::lean_dec(v_a_1498_);
    v_b_boxed_1501_ = leanh::lean_unbox_uint32(v_b_1499_);
    leanh::lean_dec(v_b_1499_);
    v_res_1502_ = lean_uint32_div(v_a_boxed_1500_, v_b_boxed_1501_);
    v_r_1503_ = leanh::lean_box_uint32(v_res_1502_);
    return v_r_1503_;
}
pub unsafe fn l_UInt32_pow(
    mut v_x_1504_: u32,
    mut v_n_1505_: *mut leanh::LeanObject,
) -> u32 {
    let mut v_zero_1506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_1507_: u8 = 0;
    v_zero_1506_ = leanh::lean_unsigned_to_nat(0);
    v_isZero_1507_ = lean_nat_dec_eq(v_n_1505_, v_zero_1506_);
    if v_isZero_1507_ == 1 {
        let mut v___x_1508_: u32 = 0;
        v___x_1508_ = 1;
        return v___x_1508_;
    } else {
        let mut v_one_1509_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_1510_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1511_: u32 = 0;
        let mut v___x_1512_: u32 = 0;
        v_one_1509_ = leanh::lean_unsigned_to_nat(1);
        v_n_1510_ = lean_nat_sub(v_n_1505_, v_one_1509_);
        v___x_1511_ = l_UInt32_pow(v_x_1504_, v_n_1510_);
        leanh::lean_dec(v_n_1510_);
        v___x_1512_ = lean_uint32_mul(v___x_1511_, v_x_1504_);
        return v___x_1512_;
    }
}
pub unsafe fn l_UInt32_pow___boxed(
    mut v_x_1513_: *mut leanh::LeanObject,
    mut v_n_1514_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_boxed_1515_: u32 = 0;
    let mut v_res_1516_: u32 = 0;
    let mut v_r_1517_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_1515_ = leanh::lean_unbox_uint32(v_x_1513_);
    leanh::lean_dec(v_x_1513_);
    v_res_1516_ = l_UInt32_pow(v_x_boxed_1515_, v_n_1514_);
    leanh::lean_dec(v_n_1514_);
    v_r_1517_ = leanh::lean_box_uint32(v_res_1516_);
    return v_r_1517_;
}
pub unsafe fn l_UInt32_mod___boxed(
    mut v_a_1520_: *mut leanh::LeanObject,
    mut v_b_1521_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_1522_: u32 = 0;
    let mut v_b_boxed_1523_: u32 = 0;
    let mut v_res_1524_: u32 = 0;
    let mut v_r_1525_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_1522_ = leanh::lean_unbox_uint32(v_a_1520_);
    leanh::lean_dec(v_a_1520_);
    v_b_boxed_1523_ = leanh::lean_unbox_uint32(v_b_1521_);
    leanh::lean_dec(v_b_1521_);
    v_res_1524_ = lean_uint32_mod(v_a_boxed_1522_, v_b_boxed_1523_);
    v_r_1525_ = leanh::lean_box_uint32(v_res_1524_);
    return v_r_1525_;
}
pub unsafe fn l_Nat_cast___at___00UInt32_modn_spec__0(
    mut v_a_1526_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1528_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1527_ = leanh::lean_unsigned_to_nat(32);
    v___x_1528_ = l_BitVec_ofNat(v___x_1527_, v_a_1526_);
    return v___x_1528_;
}
pub unsafe fn l_Nat_cast___at___00UInt32_modn_spec__0___boxed(
    mut v_a_1529_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1530_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1530_ = l_Nat_cast___at___00UInt32_modn_spec__0(v_a_1529_);
    leanh::lean_dec(v_a_1529_);
    return v_res_1530_;
}
pub unsafe fn l_UInt32_modn(
    mut v_a_1531_: u32,
    mut v_n_1532_: *mut leanh::LeanObject,
) -> u32 {
    let mut v___x_1533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1536_: u32 = 0;
    v___x_1533_ = lean_uint32_to_nat(v_a_1531_);
    v___x_1534_ = lean_nat_mod(v___x_1533_, v_n_1532_);
    leanh::lean_dec(v___x_1533_);
    v___x_1535_ = l_Nat_cast___at___00UInt32_modn_spec__0(v___x_1534_);
    leanh::lean_dec(v___x_1534_);
    v___x_1536_ = lean_uint32_of_nat_mk(v___x_1535_);
    return v___x_1536_;
}
pub unsafe fn l_UInt32_modn___boxed(
    mut v_a_1537_: *mut leanh::LeanObject,
    mut v_n_1538_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_1539_: u32 = 0;
    let mut v_res_1540_: u32 = 0;
    let mut v_r_1541_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_1539_ = leanh::lean_unbox_uint32(v_a_1537_);
    leanh::lean_dec(v_a_1537_);
    v_res_1540_ = l_UInt32_modn(v_a_boxed_1539_, v_n_1538_);
    leanh::lean_dec(v_n_1538_);
    v_r_1541_ = leanh::lean_box_uint32(v_res_1540_);
    return v_r_1541_;
}
pub unsafe fn l_UInt32_land___boxed(
    mut v_a_1544_: *mut leanh::LeanObject,
    mut v_b_1545_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_1546_: u32 = 0;
    let mut v_b_boxed_1547_: u32 = 0;
    let mut v_res_1548_: u32 = 0;
    let mut v_r_1549_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_1546_ = leanh::lean_unbox_uint32(v_a_1544_);
    leanh::lean_dec(v_a_1544_);
    v_b_boxed_1547_ = leanh::lean_unbox_uint32(v_b_1545_);
    leanh::lean_dec(v_b_1545_);
    v_res_1548_ = lean_uint32_land(v_a_boxed_1546_, v_b_boxed_1547_);
    v_r_1549_ = leanh::lean_box_uint32(v_res_1548_);
    return v_r_1549_;
}
pub unsafe fn l_UInt32_lor___boxed(
    mut v_a_1552_: *mut leanh::LeanObject,
    mut v_b_1553_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_1554_: u32 = 0;
    let mut v_b_boxed_1555_: u32 = 0;
    let mut v_res_1556_: u32 = 0;
    let mut v_r_1557_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_1554_ = leanh::lean_unbox_uint32(v_a_1552_);
    leanh::lean_dec(v_a_1552_);
    v_b_boxed_1555_ = leanh::lean_unbox_uint32(v_b_1553_);
    leanh::lean_dec(v_b_1553_);
    v_res_1556_ = lean_uint32_lor(v_a_boxed_1554_, v_b_boxed_1555_);
    v_r_1557_ = leanh::lean_box_uint32(v_res_1556_);
    return v_r_1557_;
}
pub unsafe fn l_UInt32_xor___boxed(
    mut v_a_1560_: *mut leanh::LeanObject,
    mut v_b_1561_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_1562_: u32 = 0;
    let mut v_b_boxed_1563_: u32 = 0;
    let mut v_res_1564_: u32 = 0;
    let mut v_r_1565_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_1562_ = leanh::lean_unbox_uint32(v_a_1560_);
    leanh::lean_dec(v_a_1560_);
    v_b_boxed_1563_ = leanh::lean_unbox_uint32(v_b_1561_);
    leanh::lean_dec(v_b_1561_);
    v_res_1564_ = lean_uint32_xor(v_a_boxed_1562_, v_b_boxed_1563_);
    v_r_1565_ = leanh::lean_box_uint32(v_res_1564_);
    return v_r_1565_;
}
pub unsafe fn l_UInt32_shiftLeft___boxed(
    mut v_a_1568_: *mut leanh::LeanObject,
    mut v_b_1569_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_1570_: u32 = 0;
    let mut v_b_boxed_1571_: u32 = 0;
    let mut v_res_1572_: u32 = 0;
    let mut v_r_1573_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_1570_ = leanh::lean_unbox_uint32(v_a_1568_);
    leanh::lean_dec(v_a_1568_);
    v_b_boxed_1571_ = leanh::lean_unbox_uint32(v_b_1569_);
    leanh::lean_dec(v_b_1569_);
    v_res_1572_ = lean_uint32_shift_left(v_a_boxed_1570_, v_b_boxed_1571_);
    v_r_1573_ = leanh::lean_box_uint32(v_res_1572_);
    return v_r_1573_;
}
pub unsafe fn l_UInt32_shiftRight___boxed(
    mut v_a_1576_: *mut leanh::LeanObject,
    mut v_b_1577_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_1578_: u32 = 0;
    let mut v_b_boxed_1579_: u32 = 0;
    let mut v_res_1580_: u32 = 0;
    let mut v_r_1581_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_1578_ = leanh::lean_unbox_uint32(v_a_1576_);
    leanh::lean_dec(v_a_1576_);
    v_b_boxed_1579_ = leanh::lean_unbox_uint32(v_b_1577_);
    leanh::lean_dec(v_b_1577_);
    v_res_1580_ = lean_uint32_shift_right(v_a_boxed_1578_, v_b_boxed_1579_);
    v_r_1581_ = leanh::lean_box_uint32(v_res_1580_);
    return v_r_1581_;
}
pub unsafe fn l_UInt32_complement___boxed(
    mut v_a_1593_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_1594_: u32 = 0;
    let mut v_res_1595_: u32 = 0;
    let mut v_r_1596_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_1594_ = leanh::lean_unbox_uint32(v_a_1593_);
    leanh::lean_dec(v_a_1593_);
    v_res_1595_ = lean_uint32_complement(v_a_boxed_1594_);
    v_r_1596_ = leanh::lean_box_uint32(v_res_1595_);
    return v_r_1596_;
}
pub unsafe fn l_UInt32_neg___boxed(
    mut v_a_1598_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_1599_: u32 = 0;
    let mut v_res_1600_: u32 = 0;
    let mut v_r_1601_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_1599_ = leanh::lean_unbox_uint32(v_a_1598_);
    leanh::lean_dec(v_a_1598_);
    v_res_1600_ = lean_uint32_neg(v_a_boxed_1599_);
    v_r_1601_ = leanh::lean_box_uint32(v_res_1600_);
    return v_r_1601_;
}
pub unsafe fn l_Bool_toUInt32___boxed(
    mut v_b_1617_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_b_boxed_1618_: u8 = 0;
    let mut v_res_1619_: u32 = 0;
    let mut v_r_1620_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_b_boxed_1618_ = (leanh::lean_unbox(v_b_1617_) as u8);
    v_res_1619_ = lean_bool_to_uint32(v_b_boxed_1618_);
    v_r_1620_ = leanh::lean_box_uint32(v_res_1619_);
    return v_r_1620_;
}
pub unsafe fn l_UInt64_ofFin(mut v_a_1621_: *mut leanh::LeanObject) -> u64 {
    let mut v___x_1622_: u64 = 0;
    v___x_1622_ = lean_uint64_of_nat_mk(v_a_1621_);
    return v___x_1622_;
}
pub unsafe fn l_UInt64_ofFin___boxed(
    mut v_a_1623_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1624_: u64 = 0;
    let mut v_r_1625_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1624_ = l_UInt64_ofFin(v_a_1623_);
    v_r_1625_ = leanh::lean_box_uint64(v_res_1624_);
    return v_r_1625_;
}
pub unsafe fn _init_l_UInt64_ofInt___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_1626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1628_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1626_ = leanh::lean_unsigned_to_nat(64);
    v___x_1627_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_UInt8_ofInt___closed__0),
        core::ptr::addr_of_mut!(l_UInt8_ofInt___closed__0_once),
        _init_l_UInt8_ofInt___closed__0,
    );
    v___x_1628_ = l_Int_pow(v___x_1627_, v___x_1626_);
    return v___x_1628_;
}
pub unsafe fn l_UInt64_ofInt(mut v_x_1629_: *mut leanh::LeanObject) -> u64 {
    let mut v___x_1630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1633_: u64 = 0;
    v___x_1630_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_UInt64_ofInt___closed__0),
        core::ptr::addr_of_mut!(l_UInt64_ofInt___closed__0_once),
        _init_l_UInt64_ofInt___closed__0,
    );
    v___x_1631_ = lean_int_emod(v_x_1629_, v___x_1630_);
    v___x_1632_ = l_Int_toNat(v___x_1631_);
    leanh::lean_dec(v___x_1631_);
    v___x_1633_ = lean_uint64_of_nat(v___x_1632_);
    leanh::lean_dec(v___x_1632_);
    return v___x_1633_;
}
pub unsafe fn l_UInt64_ofInt___boxed(
    mut v_x_1634_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1635_: u64 = 0;
    let mut v_r_1636_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1635_ = l_UInt64_ofInt(v_x_1634_);
    leanh::lean_dec(v_x_1634_);
    v_r_1636_ = leanh::lean_box_uint64(v_res_1635_);
    return v_r_1636_;
}
pub unsafe fn l_UInt64_add___boxed(
    mut v_a_1639_: *mut leanh::LeanObject,
    mut v_b_1640_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_1641_: u64 = 0;
    let mut v_b_boxed_1642_: u64 = 0;
    let mut v_res_1643_: u64 = 0;
    let mut v_r_1644_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_1641_ = leanh::lean_unbox_uint64(v_a_1639_);
    leanh::lean_dec_ref(v_a_1639_);
    v_b_boxed_1642_ = leanh::lean_unbox_uint64(v_b_1640_);
    leanh::lean_dec_ref(v_b_1640_);
    v_res_1643_ = lean_uint64_add(v_a_boxed_1641_, v_b_boxed_1642_);
    v_r_1644_ = leanh::lean_box_uint64(v_res_1643_);
    return v_r_1644_;
}
pub unsafe fn l_UInt64_sub___boxed(
    mut v_a_1647_: *mut leanh::LeanObject,
    mut v_b_1648_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_1649_: u64 = 0;
    let mut v_b_boxed_1650_: u64 = 0;
    let mut v_res_1651_: u64 = 0;
    let mut v_r_1652_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_1649_ = leanh::lean_unbox_uint64(v_a_1647_);
    leanh::lean_dec_ref(v_a_1647_);
    v_b_boxed_1650_ = leanh::lean_unbox_uint64(v_b_1648_);
    leanh::lean_dec_ref(v_b_1648_);
    v_res_1651_ = lean_uint64_sub(v_a_boxed_1649_, v_b_boxed_1650_);
    v_r_1652_ = leanh::lean_box_uint64(v_res_1651_);
    return v_r_1652_;
}
pub unsafe fn l_UInt64_mul___boxed(
    mut v_a_1655_: *mut leanh::LeanObject,
    mut v_b_1656_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_1657_: u64 = 0;
    let mut v_b_boxed_1658_: u64 = 0;
    let mut v_res_1659_: u64 = 0;
    let mut v_r_1660_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_1657_ = leanh::lean_unbox_uint64(v_a_1655_);
    leanh::lean_dec_ref(v_a_1655_);
    v_b_boxed_1658_ = leanh::lean_unbox_uint64(v_b_1656_);
    leanh::lean_dec_ref(v_b_1656_);
    v_res_1659_ = lean_uint64_mul(v_a_boxed_1657_, v_b_boxed_1658_);
    v_r_1660_ = leanh::lean_box_uint64(v_res_1659_);
    return v_r_1660_;
}
pub unsafe fn l_UInt64_div___boxed(
    mut v_a_1663_: *mut leanh::LeanObject,
    mut v_b_1664_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_1665_: u64 = 0;
    let mut v_b_boxed_1666_: u64 = 0;
    let mut v_res_1667_: u64 = 0;
    let mut v_r_1668_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_1665_ = leanh::lean_unbox_uint64(v_a_1663_);
    leanh::lean_dec_ref(v_a_1663_);
    v_b_boxed_1666_ = leanh::lean_unbox_uint64(v_b_1664_);
    leanh::lean_dec_ref(v_b_1664_);
    v_res_1667_ = lean_uint64_div(v_a_boxed_1665_, v_b_boxed_1666_);
    v_r_1668_ = leanh::lean_box_uint64(v_res_1667_);
    return v_r_1668_;
}
pub unsafe fn l_UInt64_pow(
    mut v_x_1669_: u64,
    mut v_n_1670_: *mut leanh::LeanObject,
) -> u64 {
    let mut v_zero_1671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_1672_: u8 = 0;
    v_zero_1671_ = leanh::lean_unsigned_to_nat(0);
    v_isZero_1672_ = lean_nat_dec_eq(v_n_1670_, v_zero_1671_);
    if v_isZero_1672_ == 1 {
        let mut v___x_1673_: u64 = 0;
        v___x_1673_ = 1u64;
        return v___x_1673_;
    } else {
        let mut v_one_1674_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_1675_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1676_: u64 = 0;
        let mut v___x_1677_: u64 = 0;
        v_one_1674_ = leanh::lean_unsigned_to_nat(1);
        v_n_1675_ = lean_nat_sub(v_n_1670_, v_one_1674_);
        v___x_1676_ = l_UInt64_pow(v_x_1669_, v_n_1675_);
        leanh::lean_dec(v_n_1675_);
        v___x_1677_ = lean_uint64_mul(v___x_1676_, v_x_1669_);
        return v___x_1677_;
    }
}
pub unsafe fn l_UInt64_pow___boxed(
    mut v_x_1678_: *mut leanh::LeanObject,
    mut v_n_1679_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_boxed_1680_: u64 = 0;
    let mut v_res_1681_: u64 = 0;
    let mut v_r_1682_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_1680_ = leanh::lean_unbox_uint64(v_x_1678_);
    leanh::lean_dec_ref(v_x_1678_);
    v_res_1681_ = l_UInt64_pow(v_x_boxed_1680_, v_n_1679_);
    leanh::lean_dec(v_n_1679_);
    v_r_1682_ = leanh::lean_box_uint64(v_res_1681_);
    return v_r_1682_;
}
pub unsafe fn l_UInt64_mod___boxed(
    mut v_a_1685_: *mut leanh::LeanObject,
    mut v_b_1686_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_1687_: u64 = 0;
    let mut v_b_boxed_1688_: u64 = 0;
    let mut v_res_1689_: u64 = 0;
    let mut v_r_1690_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_1687_ = leanh::lean_unbox_uint64(v_a_1685_);
    leanh::lean_dec_ref(v_a_1685_);
    v_b_boxed_1688_ = leanh::lean_unbox_uint64(v_b_1686_);
    leanh::lean_dec_ref(v_b_1686_);
    v_res_1689_ = lean_uint64_mod(v_a_boxed_1687_, v_b_boxed_1688_);
    v_r_1690_ = leanh::lean_box_uint64(v_res_1689_);
    return v_r_1690_;
}
pub unsafe fn l_Nat_cast___at___00UInt64_modn_spec__0(
    mut v_a_1691_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1693_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1692_ = leanh::lean_unsigned_to_nat(64);
    v___x_1693_ = l_BitVec_ofNat(v___x_1692_, v_a_1691_);
    return v___x_1693_;
}
pub unsafe fn l_Nat_cast___at___00UInt64_modn_spec__0___boxed(
    mut v_a_1694_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1695_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1695_ = l_Nat_cast___at___00UInt64_modn_spec__0(v_a_1694_);
    leanh::lean_dec(v_a_1694_);
    return v_res_1695_;
}
pub unsafe fn l_UInt64_modn(
    mut v_a_1696_: u64,
    mut v_n_1697_: *mut leanh::LeanObject,
) -> u64 {
    let mut v___x_1698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1701_: u64 = 0;
    v___x_1698_ = lean_uint64_to_nat(v_a_1696_);
    v___x_1699_ = lean_nat_mod(v___x_1698_, v_n_1697_);
    leanh::lean_dec(v___x_1698_);
    v___x_1700_ = l_Nat_cast___at___00UInt64_modn_spec__0(v___x_1699_);
    leanh::lean_dec(v___x_1699_);
    v___x_1701_ = lean_uint64_of_nat_mk(v___x_1700_);
    return v___x_1701_;
}
pub unsafe fn l_UInt64_modn___boxed(
    mut v_a_1702_: *mut leanh::LeanObject,
    mut v_n_1703_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_1704_: u64 = 0;
    let mut v_res_1705_: u64 = 0;
    let mut v_r_1706_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_1704_ = leanh::lean_unbox_uint64(v_a_1702_);
    leanh::lean_dec_ref(v_a_1702_);
    v_res_1705_ = l_UInt64_modn(v_a_boxed_1704_, v_n_1703_);
    leanh::lean_dec(v_n_1703_);
    v_r_1706_ = leanh::lean_box_uint64(v_res_1705_);
    return v_r_1706_;
}
pub unsafe fn l_UInt64_land___boxed(
    mut v_a_1709_: *mut leanh::LeanObject,
    mut v_b_1710_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_1711_: u64 = 0;
    let mut v_b_boxed_1712_: u64 = 0;
    let mut v_res_1713_: u64 = 0;
    let mut v_r_1714_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_1711_ = leanh::lean_unbox_uint64(v_a_1709_);
    leanh::lean_dec_ref(v_a_1709_);
    v_b_boxed_1712_ = leanh::lean_unbox_uint64(v_b_1710_);
    leanh::lean_dec_ref(v_b_1710_);
    v_res_1713_ = lean_uint64_land(v_a_boxed_1711_, v_b_boxed_1712_);
    v_r_1714_ = leanh::lean_box_uint64(v_res_1713_);
    return v_r_1714_;
}
pub unsafe fn l_UInt64_lor___boxed(
    mut v_a_1717_: *mut leanh::LeanObject,
    mut v_b_1718_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_1719_: u64 = 0;
    let mut v_b_boxed_1720_: u64 = 0;
    let mut v_res_1721_: u64 = 0;
    let mut v_r_1722_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_1719_ = leanh::lean_unbox_uint64(v_a_1717_);
    leanh::lean_dec_ref(v_a_1717_);
    v_b_boxed_1720_ = leanh::lean_unbox_uint64(v_b_1718_);
    leanh::lean_dec_ref(v_b_1718_);
    v_res_1721_ = lean_uint64_lor(v_a_boxed_1719_, v_b_boxed_1720_);
    v_r_1722_ = leanh::lean_box_uint64(v_res_1721_);
    return v_r_1722_;
}
pub unsafe fn l_UInt64_xor___boxed(
    mut v_a_1725_: *mut leanh::LeanObject,
    mut v_b_1726_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_1727_: u64 = 0;
    let mut v_b_boxed_1728_: u64 = 0;
    let mut v_res_1729_: u64 = 0;
    let mut v_r_1730_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_1727_ = leanh::lean_unbox_uint64(v_a_1725_);
    leanh::lean_dec_ref(v_a_1725_);
    v_b_boxed_1728_ = leanh::lean_unbox_uint64(v_b_1726_);
    leanh::lean_dec_ref(v_b_1726_);
    v_res_1729_ = lean_uint64_xor(v_a_boxed_1727_, v_b_boxed_1728_);
    v_r_1730_ = leanh::lean_box_uint64(v_res_1729_);
    return v_r_1730_;
}
pub unsafe fn l_UInt64_shiftLeft___boxed(
    mut v_a_1733_: *mut leanh::LeanObject,
    mut v_b_1734_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_1735_: u64 = 0;
    let mut v_b_boxed_1736_: u64 = 0;
    let mut v_res_1737_: u64 = 0;
    let mut v_r_1738_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_1735_ = leanh::lean_unbox_uint64(v_a_1733_);
    leanh::lean_dec_ref(v_a_1733_);
    v_b_boxed_1736_ = leanh::lean_unbox_uint64(v_b_1734_);
    leanh::lean_dec_ref(v_b_1734_);
    v_res_1737_ = lean_uint64_shift_left(v_a_boxed_1735_, v_b_boxed_1736_);
    v_r_1738_ = leanh::lean_box_uint64(v_res_1737_);
    return v_r_1738_;
}
pub unsafe fn l_UInt64_shiftRight___boxed(
    mut v_a_1741_: *mut leanh::LeanObject,
    mut v_b_1742_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_1743_: u64 = 0;
    let mut v_b_boxed_1744_: u64 = 0;
    let mut v_res_1745_: u64 = 0;
    let mut v_r_1746_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_1743_ = leanh::lean_unbox_uint64(v_a_1741_);
    leanh::lean_dec_ref(v_a_1741_);
    v_b_boxed_1744_ = leanh::lean_unbox_uint64(v_b_1742_);
    leanh::lean_dec_ref(v_b_1742_);
    v_res_1745_ = lean_uint64_shift_right(v_a_boxed_1743_, v_b_boxed_1744_);
    v_r_1746_ = leanh::lean_box_uint64(v_res_1745_);
    return v_r_1746_;
}
pub unsafe fn _init_l_instLTUInt64() -> *mut leanh::LeanObject {
    let mut v___x_1761_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1761_ = leanh::lean_box(0);
    return v___x_1761_;
}
pub unsafe fn _init_l_instLEUInt64() -> *mut leanh::LeanObject {
    let mut v___x_1762_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1762_ = leanh::lean_box(0);
    return v___x_1762_;
}
pub unsafe fn l_UInt64_complement___boxed(
    mut v_a_1764_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_1765_: u64 = 0;
    let mut v_res_1766_: u64 = 0;
    let mut v_r_1767_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_1765_ = leanh::lean_unbox_uint64(v_a_1764_);
    leanh::lean_dec_ref(v_a_1764_);
    v_res_1766_ = lean_uint64_complement(v_a_boxed_1765_);
    v_r_1767_ = leanh::lean_box_uint64(v_res_1766_);
    return v_r_1767_;
}
pub unsafe fn l_UInt64_neg___boxed(
    mut v_a_1769_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_1770_: u64 = 0;
    let mut v_res_1771_: u64 = 0;
    let mut v_r_1772_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_1770_ = leanh::lean_unbox_uint64(v_a_1769_);
    leanh::lean_dec_ref(v_a_1769_);
    v_res_1771_ = lean_uint64_neg(v_a_boxed_1770_);
    v_r_1772_ = leanh::lean_box_uint64(v_res_1771_);
    return v_r_1772_;
}
pub unsafe fn l_Bool_toUInt64___boxed(
    mut v_b_1788_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_b_boxed_1789_: u8 = 0;
    let mut v_res_1790_: u64 = 0;
    let mut v_r_1791_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_b_boxed_1789_ = (leanh::lean_unbox(v_b_1788_) as u8);
    v_res_1790_ = lean_bool_to_uint64(v_b_boxed_1789_);
    v_r_1791_ = leanh::lean_box_uint64(v_res_1790_);
    return v_r_1791_;
}
pub unsafe fn l_UInt64_decLt___aux__1(mut v_a_1792_: u64, mut v_b_1793_: u64) -> u8 {
    let mut v___x_1794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1796_: u8 = 0;
    v___x_1794_ = lean_uint64_to_nat(v_a_1792_);
    v___x_1795_ = lean_uint64_to_nat(v_b_1793_);
    v___x_1796_ = lean_nat_dec_lt(v___x_1794_, v___x_1795_);
    leanh::lean_dec(v___x_1795_);
    leanh::lean_dec(v___x_1794_);
    return v___x_1796_;
}
pub unsafe fn l_UInt64_decLt___aux__1___boxed(
    mut v_a_1797_: *mut leanh::LeanObject,
    mut v_b_1798_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_1799_: u64 = 0;
    let mut v_b_boxed_1800_: u64 = 0;
    let mut v_res_1801_: u8 = 0;
    let mut v_r_1802_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_1799_ = leanh::lean_unbox_uint64(v_a_1797_);
    leanh::lean_dec_ref(v_a_1797_);
    v_b_boxed_1800_ = leanh::lean_unbox_uint64(v_b_1798_);
    leanh::lean_dec_ref(v_b_1798_);
    v_res_1801_ = l_UInt64_decLt___aux__1(v_a_boxed_1799_, v_b_boxed_1800_);
    v_r_1802_ = leanh::lean_box((v_res_1801_) as usize);
    return v_r_1802_;
}
pub unsafe fn l_UInt64_decLt___boxed(
    mut v_a_1805_: *mut leanh::LeanObject,
    mut v_b_1806_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_1807_: u64 = 0;
    let mut v_b_boxed_1808_: u64 = 0;
    let mut v_res_1809_: u8 = 0;
    let mut v_r_1810_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_1807_ = leanh::lean_unbox_uint64(v_a_1805_);
    leanh::lean_dec_ref(v_a_1805_);
    v_b_boxed_1808_ = leanh::lean_unbox_uint64(v_b_1806_);
    leanh::lean_dec_ref(v_b_1806_);
    v_res_1809_ = lean_uint64_dec_lt(v_a_boxed_1807_, v_b_boxed_1808_);
    v_r_1810_ = leanh::lean_box((v_res_1809_) as usize);
    return v_r_1810_;
}
pub unsafe fn l_UInt64_decLe___aux__1(mut v_a_1811_: u64, mut v_b_1812_: u64) -> u8 {
    let mut v___x_1813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: u8 = 0;
    v___x_1813_ = lean_uint64_to_nat(v_a_1811_);
    v___x_1814_ = lean_uint64_to_nat(v_b_1812_);
    v___x_1815_ = lean_nat_dec_le(v___x_1813_, v___x_1814_);
    leanh::lean_dec(v___x_1814_);
    leanh::lean_dec(v___x_1813_);
    return v___x_1815_;
}
pub unsafe fn l_UInt64_decLe___aux__1___boxed(
    mut v_a_1816_: *mut leanh::LeanObject,
    mut v_b_1817_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_1818_: u64 = 0;
    let mut v_b_boxed_1819_: u64 = 0;
    let mut v_res_1820_: u8 = 0;
    let mut v_r_1821_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_1818_ = leanh::lean_unbox_uint64(v_a_1816_);
    leanh::lean_dec_ref(v_a_1816_);
    v_b_boxed_1819_ = leanh::lean_unbox_uint64(v_b_1817_);
    leanh::lean_dec_ref(v_b_1817_);
    v_res_1820_ = l_UInt64_decLe___aux__1(v_a_boxed_1818_, v_b_boxed_1819_);
    v_r_1821_ = leanh::lean_box((v_res_1820_) as usize);
    return v_r_1821_;
}
pub unsafe fn l_UInt64_decLe___boxed(
    mut v_a_1824_: *mut leanh::LeanObject,
    mut v_b_1825_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_1826_: u64 = 0;
    let mut v_b_boxed_1827_: u64 = 0;
    let mut v_res_1828_: u8 = 0;
    let mut v_r_1829_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_1826_ = leanh::lean_unbox_uint64(v_a_1824_);
    leanh::lean_dec_ref(v_a_1824_);
    v_b_boxed_1827_ = leanh::lean_unbox_uint64(v_b_1825_);
    leanh::lean_dec_ref(v_b_1825_);
    v_res_1828_ = lean_uint64_dec_le(v_a_boxed_1826_, v_b_boxed_1827_);
    v_r_1829_ = leanh::lean_box((v_res_1828_) as usize);
    return v_r_1829_;
}
pub unsafe fn l_instMaxUInt64___lam__0(mut v_x_1830_: u64, mut v_y_1831_: u64) -> u64 {
    let mut v___x_1832_: u8 = 0;
    v___x_1832_ = lean_uint64_dec_le(v_x_1830_, v_y_1831_);
    if v___x_1832_ == 0 {
        return v_x_1830_;
    } else {
        return v_y_1831_;
    }
}
pub unsafe fn l_instMaxUInt64___lam__0___boxed(
    mut v_x_1833_: *mut leanh::LeanObject,
    mut v_y_1834_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_boxed_1835_: u64 = 0;
    let mut v_y_boxed_1836_: u64 = 0;
    let mut v_res_1837_: u64 = 0;
    let mut v_r_1838_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_1835_ = leanh::lean_unbox_uint64(v_x_1833_);
    leanh::lean_dec_ref(v_x_1833_);
    v_y_boxed_1836_ = leanh::lean_unbox_uint64(v_y_1834_);
    leanh::lean_dec_ref(v_y_1834_);
    v_res_1837_ = l_instMaxUInt64___lam__0(v_x_boxed_1835_, v_y_boxed_1836_);
    v_r_1838_ = leanh::lean_box_uint64(v_res_1837_);
    return v_r_1838_;
}
pub unsafe fn l_instMinUInt64___lam__0(mut v_x_1841_: u64, mut v_y_1842_: u64) -> u64 {
    let mut v___x_1843_: u8 = 0;
    v___x_1843_ = lean_uint64_dec_le(v_x_1841_, v_y_1842_);
    if v___x_1843_ == 0 {
        return v_y_1842_;
    } else {
        return v_x_1841_;
    }
}
pub unsafe fn l_instMinUInt64___lam__0___boxed(
    mut v_x_1844_: *mut leanh::LeanObject,
    mut v_y_1845_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_boxed_1846_: u64 = 0;
    let mut v_y_boxed_1847_: u64 = 0;
    let mut v_res_1848_: u64 = 0;
    let mut v_r_1849_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_1846_ = leanh::lean_unbox_uint64(v_x_1844_);
    leanh::lean_dec_ref(v_x_1844_);
    v_y_boxed_1847_ = leanh::lean_unbox_uint64(v_y_1845_);
    leanh::lean_dec_ref(v_y_1845_);
    v_res_1848_ = l_instMinUInt64___lam__0(v_x_boxed_1846_, v_y_boxed_1847_);
    v_r_1849_ = leanh::lean_box_uint64(v_res_1848_);
    return v_r_1849_;
}
pub unsafe fn l_USize_ofFin(mut v_a_1852_: *mut leanh::LeanObject) -> usize {
    let mut v___x_1853_: usize = 0;
    v___x_1853_ = lean_usize_of_nat_mk(v_a_1852_);
    return v___x_1853_;
}
pub unsafe fn l_USize_ofFin___boxed(
    mut v_a_1854_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1855_: usize = 0;
    let mut v_r_1856_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1855_ = l_USize_ofFin(v_a_1854_);
    v_r_1856_ = leanh::lean_box_usize(v_res_1855_);
    return v_r_1856_;
}
pub unsafe fn _init_l_USize_ofInt___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_1857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1859_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1857_ = l_System_Platform_numBits;
    v___x_1858_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_UInt8_ofInt___closed__0),
        core::ptr::addr_of_mut!(l_UInt8_ofInt___closed__0_once),
        _init_l_UInt8_ofInt___closed__0,
    );
    v___x_1859_ = l_Int_pow(v___x_1858_, v___x_1857_);
    return v___x_1859_;
}
pub unsafe fn l_USize_ofInt(mut v_x_1860_: *mut leanh::LeanObject) -> usize {
    let mut v___x_1861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1864_: usize = 0;
    v___x_1861_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_USize_ofInt___closed__0),
        core::ptr::addr_of_mut!(l_USize_ofInt___closed__0_once),
        _init_l_USize_ofInt___closed__0,
    );
    v___x_1862_ = lean_int_emod(v_x_1860_, v___x_1861_);
    v___x_1863_ = l_Int_toNat(v___x_1862_);
    leanh::lean_dec(v___x_1862_);
    v___x_1864_ = lean_usize_of_nat(v___x_1863_);
    leanh::lean_dec(v___x_1863_);
    return v___x_1864_;
}
pub unsafe fn l_USize_ofInt___boxed(
    mut v_x_1865_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1866_: usize = 0;
    let mut v_r_1867_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1866_ = l_USize_ofInt(v_x_1865_);
    leanh::lean_dec(v_x_1865_);
    v_r_1867_ = leanh::lean_box_usize(v_res_1866_);
    return v_r_1867_;
}
pub unsafe fn l_USize_mul___boxed(
    mut v_a_1870_: *mut leanh::LeanObject,
    mut v_b_1871_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_1872_: usize = 0;
    let mut v_b_boxed_1873_: usize = 0;
    let mut v_res_1874_: usize = 0;
    let mut v_r_1875_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_1872_ = leanh::lean_unbox_usize(v_a_1870_);
    leanh::lean_dec(v_a_1870_);
    v_b_boxed_1873_ = leanh::lean_unbox_usize(v_b_1871_);
    leanh::lean_dec(v_b_1871_);
    v_res_1874_ = lean_usize_mul(v_a_boxed_1872_, v_b_boxed_1873_);
    v_r_1875_ = leanh::lean_box_usize(v_res_1874_);
    return v_r_1875_;
}
pub unsafe fn l_USize_div___boxed(
    mut v_a_1878_: *mut leanh::LeanObject,
    mut v_b_1879_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_1880_: usize = 0;
    let mut v_b_boxed_1881_: usize = 0;
    let mut v_res_1882_: usize = 0;
    let mut v_r_1883_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_1880_ = leanh::lean_unbox_usize(v_a_1878_);
    leanh::lean_dec(v_a_1878_);
    v_b_boxed_1881_ = leanh::lean_unbox_usize(v_b_1879_);
    leanh::lean_dec(v_b_1879_);
    v_res_1882_ = lean_usize_div(v_a_boxed_1880_, v_b_boxed_1881_);
    v_r_1883_ = leanh::lean_box_usize(v_res_1882_);
    return v_r_1883_;
}
pub unsafe fn l_USize_pow(
    mut v_x_1884_: usize,
    mut v_n_1885_: *mut leanh::LeanObject,
) -> usize {
    let mut v_zero_1886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_1887_: u8 = 0;
    v_zero_1886_ = leanh::lean_unsigned_to_nat(0);
    v_isZero_1887_ = lean_nat_dec_eq(v_n_1885_, v_zero_1886_);
    if v_isZero_1887_ == 1 {
        let mut v___x_1888_: usize = 0;
        v___x_1888_ = 1usize;
        return v___x_1888_;
    } else {
        let mut v_one_1889_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_1890_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1891_: usize = 0;
        let mut v___x_1892_: usize = 0;
        v_one_1889_ = leanh::lean_unsigned_to_nat(1);
        v_n_1890_ = lean_nat_sub(v_n_1885_, v_one_1889_);
        v___x_1891_ = l_USize_pow(v_x_1884_, v_n_1890_);
        leanh::lean_dec(v_n_1890_);
        v___x_1892_ = lean_usize_mul(v___x_1891_, v_x_1884_);
        return v___x_1892_;
    }
}
pub unsafe fn l_USize_pow___boxed(
    mut v_x_1893_: *mut leanh::LeanObject,
    mut v_n_1894_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_boxed_1895_: usize = 0;
    let mut v_res_1896_: usize = 0;
    let mut v_r_1897_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_1895_ = leanh::lean_unbox_usize(v_x_1893_);
    leanh::lean_dec(v_x_1893_);
    v_res_1896_ = l_USize_pow(v_x_boxed_1895_, v_n_1894_);
    leanh::lean_dec(v_n_1894_);
    v_r_1897_ = leanh::lean_box_usize(v_res_1896_);
    return v_r_1897_;
}
pub unsafe fn l_USize_mod___boxed(
    mut v_a_1900_: *mut leanh::LeanObject,
    mut v_b_1901_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_1902_: usize = 0;
    let mut v_b_boxed_1903_: usize = 0;
    let mut v_res_1904_: usize = 0;
    let mut v_r_1905_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_1902_ = leanh::lean_unbox_usize(v_a_1900_);
    leanh::lean_dec(v_a_1900_);
    v_b_boxed_1903_ = leanh::lean_unbox_usize(v_b_1901_);
    leanh::lean_dec(v_b_1901_);
    v_res_1904_ = lean_usize_mod(v_a_boxed_1902_, v_b_boxed_1903_);
    v_r_1905_ = leanh::lean_box_usize(v_res_1904_);
    return v_r_1905_;
}
pub unsafe fn l_Nat_cast___at___00USize_modn_spec__0(
    mut v_a_1906_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1908_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1907_ = l_System_Platform_numBits;
    v___x_1908_ = l_BitVec_ofNat(v___x_1907_, v_a_1906_);
    return v___x_1908_;
}
pub unsafe fn l_Nat_cast___at___00USize_modn_spec__0___boxed(
    mut v_a_1909_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1910_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1910_ = l_Nat_cast___at___00USize_modn_spec__0(v_a_1909_);
    leanh::lean_dec(v_a_1909_);
    return v_res_1910_;
}
pub unsafe fn l_USize_modn(
    mut v_a_1911_: usize,
    mut v_n_1912_: *mut leanh::LeanObject,
) -> usize {
    let mut v___x_1913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1916_: usize = 0;
    v___x_1913_ = lean_usize_to_nat(v_a_1911_);
    v___x_1914_ = lean_nat_mod(v___x_1913_, v_n_1912_);
    leanh::lean_dec(v___x_1913_);
    v___x_1915_ = l_Nat_cast___at___00USize_modn_spec__0(v___x_1914_);
    leanh::lean_dec(v___x_1914_);
    v___x_1916_ = lean_usize_of_nat_mk(v___x_1915_);
    return v___x_1916_;
}
pub unsafe fn l_USize_modn___boxed(
    mut v_a_1917_: *mut leanh::LeanObject,
    mut v_n_1918_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_1919_: usize = 0;
    let mut v_res_1920_: usize = 0;
    let mut v_r_1921_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_1919_ = leanh::lean_unbox_usize(v_a_1917_);
    leanh::lean_dec(v_a_1917_);
    v_res_1920_ = l_USize_modn(v_a_boxed_1919_, v_n_1918_);
    leanh::lean_dec(v_n_1918_);
    v_r_1921_ = leanh::lean_box_usize(v_res_1920_);
    return v_r_1921_;
}
pub unsafe fn l_USize_land___boxed(
    mut v_a_1924_: *mut leanh::LeanObject,
    mut v_b_1925_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_1926_: usize = 0;
    let mut v_b_boxed_1927_: usize = 0;
    let mut v_res_1928_: usize = 0;
    let mut v_r_1929_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_1926_ = leanh::lean_unbox_usize(v_a_1924_);
    leanh::lean_dec(v_a_1924_);
    v_b_boxed_1927_ = leanh::lean_unbox_usize(v_b_1925_);
    leanh::lean_dec(v_b_1925_);
    v_res_1928_ = lean_usize_land(v_a_boxed_1926_, v_b_boxed_1927_);
    v_r_1929_ = leanh::lean_box_usize(v_res_1928_);
    return v_r_1929_;
}
pub unsafe fn l_USize_lor___boxed(
    mut v_a_1932_: *mut leanh::LeanObject,
    mut v_b_1933_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_1934_: usize = 0;
    let mut v_b_boxed_1935_: usize = 0;
    let mut v_res_1936_: usize = 0;
    let mut v_r_1937_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_1934_ = leanh::lean_unbox_usize(v_a_1932_);
    leanh::lean_dec(v_a_1932_);
    v_b_boxed_1935_ = leanh::lean_unbox_usize(v_b_1933_);
    leanh::lean_dec(v_b_1933_);
    v_res_1936_ = lean_usize_lor(v_a_boxed_1934_, v_b_boxed_1935_);
    v_r_1937_ = leanh::lean_box_usize(v_res_1936_);
    return v_r_1937_;
}
pub unsafe fn l_USize_xor___boxed(
    mut v_a_1940_: *mut leanh::LeanObject,
    mut v_b_1941_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_1942_: usize = 0;
    let mut v_b_boxed_1943_: usize = 0;
    let mut v_res_1944_: usize = 0;
    let mut v_r_1945_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_1942_ = leanh::lean_unbox_usize(v_a_1940_);
    leanh::lean_dec(v_a_1940_);
    v_b_boxed_1943_ = leanh::lean_unbox_usize(v_b_1941_);
    leanh::lean_dec(v_b_1941_);
    v_res_1944_ = lean_usize_xor(v_a_boxed_1942_, v_b_boxed_1943_);
    v_r_1945_ = leanh::lean_box_usize(v_res_1944_);
    return v_r_1945_;
}
pub unsafe fn l_USize_shiftLeft___boxed(
    mut v_a_1948_: *mut leanh::LeanObject,
    mut v_b_1949_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_1950_: usize = 0;
    let mut v_b_boxed_1951_: usize = 0;
    let mut v_res_1952_: usize = 0;
    let mut v_r_1953_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_1950_ = leanh::lean_unbox_usize(v_a_1948_);
    leanh::lean_dec(v_a_1948_);
    v_b_boxed_1951_ = leanh::lean_unbox_usize(v_b_1949_);
    leanh::lean_dec(v_b_1949_);
    v_res_1952_ = lean_usize_shift_left(v_a_boxed_1950_, v_b_boxed_1951_);
    v_r_1953_ = leanh::lean_box_usize(v_res_1952_);
    return v_r_1953_;
}
pub unsafe fn l_USize_shiftRight___boxed(
    mut v_a_1956_: *mut leanh::LeanObject,
    mut v_b_1957_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_1958_: usize = 0;
    let mut v_b_boxed_1959_: usize = 0;
    let mut v_res_1960_: usize = 0;
    let mut v_r_1961_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_1958_ = leanh::lean_unbox_usize(v_a_1956_);
    leanh::lean_dec(v_a_1956_);
    v_b_boxed_1959_ = leanh::lean_unbox_usize(v_b_1957_);
    leanh::lean_dec(v_b_1957_);
    v_res_1960_ = lean_usize_shift_right(v_a_boxed_1958_, v_b_boxed_1959_);
    v_r_1961_ = leanh::lean_box_usize(v_res_1960_);
    return v_r_1961_;
}
pub unsafe fn l_USize_ofNat32___boxed(
    mut v_n_1964_: *mut leanh::LeanObject,
    mut v_h_1965_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1966_: usize = 0;
    let mut v_r_1967_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1966_ = lean_usize_of_nat(v_n_1964_);
    leanh::lean_dec(v_n_1964_);
    v_r_1967_ = leanh::lean_box_usize(v_res_1966_);
    return v_r_1967_;
}
pub unsafe fn l_UInt8_toUSize___boxed(
    mut v_a_1969_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_1970_: u8 = 0;
    let mut v_res_1971_: usize = 0;
    let mut v_r_1972_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_1970_ = (leanh::lean_unbox(v_a_1969_) as u8);
    v_res_1971_ = lean_uint8_to_usize(v_a_boxed_1970_);
    v_r_1972_ = leanh::lean_box_usize(v_res_1971_);
    return v_r_1972_;
}
pub unsafe fn l_USize_toUInt8___boxed(
    mut v_a_1974_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_1975_: usize = 0;
    let mut v_res_1976_: u8 = 0;
    let mut v_r_1977_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_1975_ = leanh::lean_unbox_usize(v_a_1974_);
    leanh::lean_dec(v_a_1974_);
    v_res_1976_ = lean_usize_to_uint8(v_a_boxed_1975_);
    v_r_1977_ = leanh::lean_box((v_res_1976_) as usize);
    return v_r_1977_;
}
pub unsafe fn l_UInt16_toUSize___boxed(
    mut v_a_1979_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_1980_: u16 = 0;
    let mut v_res_1981_: usize = 0;
    let mut v_r_1982_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_1980_ = (leanh::lean_unbox(v_a_1979_) as u16);
    v_res_1981_ = lean_uint16_to_usize(v_a_boxed_1980_);
    v_r_1982_ = leanh::lean_box_usize(v_res_1981_);
    return v_r_1982_;
}
pub unsafe fn l_USize_toUInt16___boxed(
    mut v_a_1984_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_1985_: usize = 0;
    let mut v_res_1986_: u16 = 0;
    let mut v_r_1987_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_1985_ = leanh::lean_unbox_usize(v_a_1984_);
    leanh::lean_dec(v_a_1984_);
    v_res_1986_ = lean_usize_to_uint16(v_a_boxed_1985_);
    v_r_1987_ = leanh::lean_box((v_res_1986_) as usize);
    return v_r_1987_;
}
pub unsafe fn l_UInt32_toUSize___boxed(
    mut v_a_1989_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_1990_: u32 = 0;
    let mut v_res_1991_: usize = 0;
    let mut v_r_1992_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_1990_ = leanh::lean_unbox_uint32(v_a_1989_);
    leanh::lean_dec(v_a_1989_);
    v_res_1991_ = lean_uint32_to_usize(v_a_boxed_1990_);
    v_r_1992_ = leanh::lean_box_usize(v_res_1991_);
    return v_r_1992_;
}
pub unsafe fn l_USize_toUInt32___boxed(
    mut v_a_1994_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_1995_: usize = 0;
    let mut v_res_1996_: u32 = 0;
    let mut v_r_1997_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_1995_ = leanh::lean_unbox_usize(v_a_1994_);
    leanh::lean_dec(v_a_1994_);
    v_res_1996_ = lean_usize_to_uint32(v_a_boxed_1995_);
    v_r_1997_ = leanh::lean_box_uint32(v_res_1996_);
    return v_r_1997_;
}
pub unsafe fn l_UInt64_toUSize___boxed(
    mut v_a_1999_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_2000_: u64 = 0;
    let mut v_res_2001_: usize = 0;
    let mut v_r_2002_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_2000_ = leanh::lean_unbox_uint64(v_a_1999_);
    leanh::lean_dec_ref(v_a_1999_);
    v_res_2001_ = lean_uint64_to_usize(v_a_boxed_2000_);
    v_r_2002_ = leanh::lean_box_usize(v_res_2001_);
    return v_r_2002_;
}
pub unsafe fn l_USize_toUInt64___boxed(
    mut v_a_2004_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_2005_: usize = 0;
    let mut v_res_2006_: u64 = 0;
    let mut v_r_2007_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_2005_ = leanh::lean_unbox_usize(v_a_2004_);
    leanh::lean_dec(v_a_2004_);
    v_res_2006_ = lean_usize_to_uint64(v_a_boxed_2005_);
    v_r_2007_ = leanh::lean_box_uint64(v_res_2006_);
    return v_r_2007_;
}
pub unsafe fn l_USize_complement___boxed(
    mut v_a_2019_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_2020_: usize = 0;
    let mut v_res_2021_: usize = 0;
    let mut v_r_2022_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_2020_ = leanh::lean_unbox_usize(v_a_2019_);
    leanh::lean_dec(v_a_2019_);
    v_res_2021_ = lean_usize_complement(v_a_boxed_2020_);
    v_r_2022_ = leanh::lean_box_usize(v_res_2021_);
    return v_r_2022_;
}
pub unsafe fn l_USize_neg___boxed(
    mut v_a_2024_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_2025_: usize = 0;
    let mut v_res_2026_: usize = 0;
    let mut v_r_2027_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_2025_ = leanh::lean_unbox_usize(v_a_2024_);
    leanh::lean_dec(v_a_2024_);
    v_res_2026_ = lean_usize_neg(v_a_boxed_2025_);
    v_r_2027_ = leanh::lean_box_usize(v_res_2026_);
    return v_r_2027_;
}
pub unsafe fn l_Bool_toUSize___boxed(
    mut v_b_2043_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_b_boxed_2044_: u8 = 0;
    let mut v_res_2045_: usize = 0;
    let mut v_r_2046_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_b_boxed_2044_ = (leanh::lean_unbox(v_b_2043_) as u8);
    v_res_2045_ = lean_bool_to_usize(v_b_boxed_2044_);
    v_r_2046_ = leanh::lean_box_usize(v_res_2045_);
    return v_r_2046_;
}
pub unsafe fn l_instMaxUSize___lam__0(mut v_x_2047_: usize, mut v_y_2048_: usize) -> usize {
    let mut v___x_2049_: u8 = 0;
    v___x_2049_ = lean_usize_dec_le(v_x_2047_, v_y_2048_);
    if v___x_2049_ == 0 {
        return v_x_2047_;
    } else {
        return v_y_2048_;
    }
}
pub unsafe fn l_instMaxUSize___lam__0___boxed(
    mut v_x_2050_: *mut leanh::LeanObject,
    mut v_y_2051_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_boxed_2052_: usize = 0;
    let mut v_y_boxed_2053_: usize = 0;
    let mut v_res_2054_: usize = 0;
    let mut v_r_2055_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_2052_ = leanh::lean_unbox_usize(v_x_2050_);
    leanh::lean_dec(v_x_2050_);
    v_y_boxed_2053_ = leanh::lean_unbox_usize(v_y_2051_);
    leanh::lean_dec(v_y_2051_);
    v_res_2054_ = l_instMaxUSize___lam__0(v_x_boxed_2052_, v_y_boxed_2053_);
    v_r_2055_ = leanh::lean_box_usize(v_res_2054_);
    return v_r_2055_;
}
pub unsafe fn l_instMinUSize___lam__0(mut v_x_2058_: usize, mut v_y_2059_: usize) -> usize {
    let mut v___x_2060_: u8 = 0;
    v___x_2060_ = lean_usize_dec_le(v_x_2058_, v_y_2059_);
    if v___x_2060_ == 0 {
        return v_y_2059_;
    } else {
        return v_x_2058_;
    }
}
pub unsafe fn l_instMinUSize___lam__0___boxed(
    mut v_x_2061_: *mut leanh::LeanObject,
    mut v_y_2062_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_boxed_2063_: usize = 0;
    let mut v_y_boxed_2064_: usize = 0;
    let mut v_res_2065_: usize = 0;
    let mut v_r_2066_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_2063_ = leanh::lean_unbox_usize(v_x_2061_);
    leanh::lean_dec(v_x_2061_);
    v_y_boxed_2064_ = leanh::lean_unbox_usize(v_y_2062_);
    leanh::lean_dec(v_y_2062_);
    v_res_2065_ = l_instMinUSize___lam__0(v_x_boxed_2063_, v_y_boxed_2064_);
    v_r_2066_ = leanh::lean_box_usize(v_res_2065_);
    return v_r_2066_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_UInt_Basic(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_BitVec_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_instLTUInt16 = _init_l_instLTUInt16();
    leanh::lean_mark_persistent(l_instLTUInt16);
    l_instLEUInt16 = _init_l_instLEUInt16();
    leanh::lean_mark_persistent(l_instLEUInt16);
    l_instLTUInt64 = _init_l_instLTUInt64();
    leanh::lean_mark_persistent(l_instLTUInt64);
    l_instLEUInt64 = _init_l_instLEUInt64();
    leanh::lean_mark_persistent(l_instLEUInt64);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_UInt_Basic(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_UInt_Basic(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_BitVec_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_UInt_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_UInt_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_UInt_Basic(builtin);
}