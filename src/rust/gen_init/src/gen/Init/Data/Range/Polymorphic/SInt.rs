// Lean compiler output
// Module: Init.Data.Range.Polymorphic.SInt
// Imports: Init.Data.Range.Polymorphic.Instances Init.Data.SInt Init.Data.SInt.Basic Init.Data.Range.Polymorphic.Internal.SignedBitVec Init.ByCases Init.Data.Int.LemmasAux Init.System.Platform
use crate::ffi::{
    lean_int_add, lean_int_dec_le, lean_int_neg, lean_int_sub, lean_int8_add, lean_int8_dec_eq,
    lean_int8_neg, lean_int8_of_int, lean_int8_of_nat, lean_int8_to_int, lean_int16_add,
    lean_int16_dec_eq, lean_int16_neg, lean_int16_of_int, lean_int16_of_nat, lean_int16_to_int,
    lean_int32_add, lean_int32_dec_eq, lean_int32_neg, lean_int32_of_int, lean_int32_of_nat,
    lean_int32_to_int, lean_int64_add, lean_int64_dec_eq, lean_int64_neg, lean_int64_of_int,
    lean_int64_of_nat, lean_int64_to_int_sint, lean_isize_add, lean_isize_dec_eq,
    lean_isize_of_int, lean_isize_of_nat, lean_isize_to_int, lean_nat_sub, lean_nat_to_int,
};
use crate::r#gen::Init::ByCases::{initialize_Init_ByCases, runtime_initialize_Init_ByCases};
use crate::r#gen::Init::Data::Int::Basic::{l_Int_pow, l_Int_toNat};
use crate::r#gen::Init::Data::Int::LemmasAux::{
    initialize_Init_Data_Int_LemmasAux, runtime_initialize_Init_Data_Int_LemmasAux,
};
use crate::r#gen::Init::Data::Range::Polymorphic::Instances::{
    initialize_Init_Data_Range_Polymorphic_Instances,
    runtime_initialize_Init_Data_Range_Polymorphic_Instances,
};
use crate::r#gen::Init::Data::Range::Polymorphic::Internal::SignedBitVec::{
    initialize_Init_Data_Range_Polymorphic_Internal_SignedBitVec,
    runtime_initialize_Init_Data_Range_Polymorphic_Internal_SignedBitVec,
};
use crate::r#gen::Init::Data::SInt::Basic::{
    initialize_Init_Data_SInt_Basic, runtime_initialize_Init_Data_SInt_Basic,
};
use crate::r#gen::Init::Data::SInt::{
    initialize_Init_Data_SInt, runtime_initialize_Init_Data_SInt,
};
use crate::r#gen::Init::Prelude::{
    l_System_Platform_numBits, l_UInt8_ofBitVec___boxed, l_UInt8_toBitVec___boxed,
    l_UInt16_ofBitVec___boxed, l_UInt16_toBitVec___boxed, l_UInt32_ofBitVec___boxed,
    l_UInt32_toBitVec___boxed, l_UInt64_ofBitVec___boxed, l_UInt64_toBitVec___boxed,
    l_USize_ofBitVec___boxed, l_USize_toBitVec___boxed,
};
use crate::r#gen::Init::System::Platform::{
    initialize_Init_System_Platform, runtime_initialize_Init_System_Platform,
};
static mut l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___lam__0___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___lam__0___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___lam__0___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___closed__0_value
) as *mut leanh::LeanObject;
pub static mut l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___closed__0_value
) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_minValueSealed___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_minValueSealed___closed__0: u8 = 0;
static mut l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_minValueSealed___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_minValueSealed___closed__1: u8 = 0;
pub static mut l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_minValueSealed: u8 = 0;
static mut l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_maxValueSealed___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_maxValueSealed___closed__0: u8 = 0;
pub static mut l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_maxValueSealed: u8 = 0;
static mut l_Int8_instUpwardEnumerable___lam__0___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Int8_instUpwardEnumerable___lam__0___closed__0: u8 = 0;
static mut l_Int8_instUpwardEnumerable___lam__1___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Int8_instUpwardEnumerable___lam__1___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Int8_instUpwardEnumerable___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Int8_instUpwardEnumerable___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Int8_instUpwardEnumerable___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Int8_instUpwardEnumerable___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Int8_instUpwardEnumerable___closed__1_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Int8_instUpwardEnumerable___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Int8_instUpwardEnumerable___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Int8_instUpwardEnumerable___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Int8_instUpwardEnumerable___closed__2_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Int8_instUpwardEnumerable___closed__0_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Int8_instUpwardEnumerable___closed__1_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Int8_instUpwardEnumerable___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Int8_instUpwardEnumerable___closed__2_value)
        as *mut leanh::LeanObject;
pub static mut l_Int8_instUpwardEnumerable: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Int8_instUpwardEnumerable___closed__2_value)
        as *mut leanh::LeanObject;
static mut l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_instLeast_x3f___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_instLeast_x3f___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_instLeast_x3f:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_instHasModelBitVecOfNatNat___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_UInt8_toBitVec___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_instHasModelBitVecOfNatNat___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_instHasModelBitVecOfNatNat___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_instHasModelBitVecOfNatNat___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_instHasModelBitVecOfNatNat___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_instHasModelBitVecOfNatNat:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Int8_instRxcHasSize: *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___closed__0_value
)
    as *mut leanh::LeanObject;
pub static l_Int8_instRxoHasSize___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Int8_instRxoHasSize___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Int8_instRxoHasSize___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Int8_instRxoHasSize___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_Int8_instRxoHasSize: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Int8_instRxoHasSize___closed__0_value) as *mut leanh::LeanObject;
static mut l_Int8_instRxiHasSize___lam__0___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Int8_instRxiHasSize___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Int8_instRxiHasSize___lam__0___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Int8_instRxiHasSize___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Int8_instRxiHasSize___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Int8_instRxiHasSize___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Int8_instRxiHasSize___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Int8_instRxiHasSize___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_Int8_instRxiHasSize: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Int8_instRxiHasSize___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_minValueSealed___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_minValueSealed___closed__0: u16 =
    0;
static mut l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_minValueSealed___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_minValueSealed___closed__1: u16 =
    0;
pub static mut l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_minValueSealed: u16 = 0;
static mut l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_maxValueSealed___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_maxValueSealed___closed__0: u16 =
    0;
pub static mut l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_maxValueSealed: u16 = 0;
static mut l_Int16_instUpwardEnumerable___lam__0___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Int16_instUpwardEnumerable___lam__0___closed__0: u16 = 0;
static mut l_Int16_instUpwardEnumerable___lam__1___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Int16_instUpwardEnumerable___lam__1___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Int16_instUpwardEnumerable___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Int16_instUpwardEnumerable___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Int16_instUpwardEnumerable___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Int16_instUpwardEnumerable___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Int16_instUpwardEnumerable___closed__1_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Int16_instUpwardEnumerable___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Int16_instUpwardEnumerable___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Int16_instUpwardEnumerable___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Int16_instUpwardEnumerable___closed__2_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Int16_instUpwardEnumerable___closed__0_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Int16_instUpwardEnumerable___closed__1_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Int16_instUpwardEnumerable___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Int16_instUpwardEnumerable___closed__2_value)
        as *mut leanh::LeanObject;
pub static mut l_Int16_instUpwardEnumerable: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Int16_instUpwardEnumerable___closed__2_value)
        as *mut leanh::LeanObject;
static mut l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_instLeast_x3f___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_instLeast_x3f___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_instLeast_x3f:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_instHasModelBitVecOfNatNat___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_UInt16_toBitVec___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_instHasModelBitVecOfNatNat___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_instHasModelBitVecOfNatNat___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_instHasModelBitVecOfNatNat___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_instHasModelBitVecOfNatNat___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_instHasModelBitVecOfNatNat:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Int16_instRxcHasSize___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Int16_instRxcHasSize___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Int16_instRxcHasSize___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Int16_instRxcHasSize___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_Int16_instRxcHasSize: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Int16_instRxcHasSize___closed__0_value) as *mut leanh::LeanObject;
pub static l_Int16_instRxoHasSize___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Int16_instRxoHasSize___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Int16_instRxoHasSize___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Int16_instRxoHasSize___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_Int16_instRxoHasSize: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Int16_instRxoHasSize___closed__0_value) as *mut leanh::LeanObject;
static mut l_Int16_instRxiHasSize___lam__0___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Int16_instRxiHasSize___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Int16_instRxiHasSize___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Int16_instRxiHasSize___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Int16_instRxiHasSize___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Int16_instRxiHasSize___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_Int16_instRxiHasSize: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Int16_instRxiHasSize___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_minValueSealed___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_minValueSealed___closed__0: u32 =
    0;
static mut l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_minValueSealed___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_minValueSealed___closed__1: u32 =
    0;
pub static mut l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_minValueSealed: u32 = 0;
static mut l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_maxValueSealed___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_maxValueSealed___closed__0: u32 =
    0;
pub static mut l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_maxValueSealed: u32 = 0;
static mut l_Int32_instUpwardEnumerable___lam__0___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Int32_instUpwardEnumerable___lam__0___closed__0: u32 = 0;
static mut l_Int32_instUpwardEnumerable___lam__1___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Int32_instUpwardEnumerable___lam__1___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Int32_instUpwardEnumerable___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Int32_instUpwardEnumerable___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Int32_instUpwardEnumerable___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Int32_instUpwardEnumerable___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Int32_instUpwardEnumerable___closed__1_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Int32_instUpwardEnumerable___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Int32_instUpwardEnumerable___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Int32_instUpwardEnumerable___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Int32_instUpwardEnumerable___closed__2_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Int32_instUpwardEnumerable___closed__0_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Int32_instUpwardEnumerable___closed__1_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Int32_instUpwardEnumerable___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Int32_instUpwardEnumerable___closed__2_value)
        as *mut leanh::LeanObject;
pub static mut l_Int32_instUpwardEnumerable: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Int32_instUpwardEnumerable___closed__2_value)
        as *mut leanh::LeanObject;
pub static mut l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_instLeast_x3f___closed__0___boxed__const__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_instLeast_x3f___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_instLeast_x3f___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_instLeast_x3f:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_instHasModelBitVecOfNatNat___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_UInt32_toBitVec___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_instHasModelBitVecOfNatNat___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_instHasModelBitVecOfNatNat___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_instHasModelBitVecOfNatNat___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_instHasModelBitVecOfNatNat___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_instHasModelBitVecOfNatNat:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Int32_instRxcHasSize___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Int32_instRxcHasSize___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Int32_instRxcHasSize___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Int32_instRxcHasSize___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_Int32_instRxcHasSize: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Int32_instRxcHasSize___closed__0_value) as *mut leanh::LeanObject;
pub static l_Int32_instRxoHasSize___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Int32_instRxoHasSize___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Int32_instRxoHasSize___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Int32_instRxoHasSize___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_Int32_instRxoHasSize: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Int32_instRxoHasSize___closed__0_value) as *mut leanh::LeanObject;
static mut l_Int32_instRxiHasSize___lam__0___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Int32_instRxiHasSize___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Int32_instRxiHasSize___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Int32_instRxiHasSize___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Int32_instRxiHasSize___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Int32_instRxiHasSize___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_Int32_instRxiHasSize: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Int32_instRxiHasSize___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_minValueSealed___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_minValueSealed___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_minValueSealed___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_minValueSealed___closed__1: u64 =
    0;
static mut l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_minValueSealed___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_minValueSealed___closed__2: u64 =
    0;
pub static mut l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_minValueSealed: u64 = 0;
static mut l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_maxValueSealed___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_maxValueSealed___closed__0: u64 =
    0;
pub static mut l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_maxValueSealed: u64 = 0;
static mut l_Int64_instUpwardEnumerable___lam__0___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Int64_instUpwardEnumerable___lam__0___closed__0: u64 = 0;
static mut l_Int64_instUpwardEnumerable___lam__1___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Int64_instUpwardEnumerable___lam__1___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Int64_instUpwardEnumerable___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Int64_instUpwardEnumerable___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Int64_instUpwardEnumerable___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Int64_instUpwardEnumerable___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Int64_instUpwardEnumerable___closed__1_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Int64_instUpwardEnumerable___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Int64_instUpwardEnumerable___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Int64_instUpwardEnumerable___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Int64_instUpwardEnumerable___closed__2_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Int64_instUpwardEnumerable___closed__0_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Int64_instUpwardEnumerable___closed__1_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Int64_instUpwardEnumerable___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Int64_instUpwardEnumerable___closed__2_value)
        as *mut leanh::LeanObject;
pub static mut l_Int64_instUpwardEnumerable: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Int64_instUpwardEnumerable___closed__2_value)
        as *mut leanh::LeanObject;
pub static mut l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_instLeast_x3f___closed__0___boxed__const__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_instLeast_x3f___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_instLeast_x3f___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_instLeast_x3f:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_instHasModelBitVecOfNatNat___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_UInt64_toBitVec___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_instHasModelBitVecOfNatNat___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_instHasModelBitVecOfNatNat___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_instHasModelBitVecOfNatNat___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_instHasModelBitVecOfNatNat___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_instHasModelBitVecOfNatNat:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Int64_instRxcHasSize___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Int64_instRxcHasSize___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Int64_instRxcHasSize___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Int64_instRxcHasSize___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_Int64_instRxcHasSize: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Int64_instRxcHasSize___closed__0_value) as *mut leanh::LeanObject;
pub static l_Int64_instRxoHasSize___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Int64_instRxoHasSize___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Int64_instRxoHasSize___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Int64_instRxoHasSize___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_Int64_instRxoHasSize: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Int64_instRxoHasSize___closed__0_value) as *mut leanh::LeanObject;
static mut l_Int64_instRxiHasSize___lam__0___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Int64_instRxiHasSize___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Int64_instRxiHasSize___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Int64_instRxiHasSize___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Int64_instRxiHasSize___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Int64_instRxiHasSize___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_Int64_instRxiHasSize: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Int64_instRxiHasSize___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_minValueSealed___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_minValueSealed___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_minValueSealed___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_minValueSealed___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_minValueSealed___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_minValueSealed___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_minValueSealed___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_minValueSealed___closed__3: usize =
    0;
pub static mut l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_minValueSealed: usize = 0;
static mut l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_maxValueSealed___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_maxValueSealed___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_maxValueSealed___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_maxValueSealed___closed__1: usize =
    0;
pub static mut l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_maxValueSealed: usize = 0;
static mut l_ISize_instUpwardEnumerable___lam__0___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_ISize_instUpwardEnumerable___lam__0___closed__0: usize = 0;
static mut l_ISize_instUpwardEnumerable___lam__1___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_ISize_instUpwardEnumerable___lam__1___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_ISize_instUpwardEnumerable___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_ISize_instUpwardEnumerable___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_ISize_instUpwardEnumerable___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_ISize_instUpwardEnumerable___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_ISize_instUpwardEnumerable___closed__1_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_ISize_instUpwardEnumerable___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_ISize_instUpwardEnumerable___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_ISize_instUpwardEnumerable___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_ISize_instUpwardEnumerable___closed__2_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_ISize_instUpwardEnumerable___closed__0_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_ISize_instUpwardEnumerable___closed__1_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_ISize_instUpwardEnumerable___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_ISize_instUpwardEnumerable___closed__2_value)
        as *mut leanh::LeanObject;
pub static mut l_ISize_instUpwardEnumerable: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_ISize_instUpwardEnumerable___closed__2_value)
        as *mut leanh::LeanObject;
pub static mut l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_instLeast_x3f___closed__0___boxed__const__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_instLeast_x3f___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_instLeast_x3f___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_instLeast_x3f:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_instHasModelBitVecNumBits___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_USize_toBitVec___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_instHasModelBitVecNumBits___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_instHasModelBitVecNumBits___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_instHasModelBitVecNumBits___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_instHasModelBitVecNumBits___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_instHasModelBitVecNumBits:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_ISize_instRxcHasSize___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_ISize_instRxcHasSize___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_ISize_instRxcHasSize___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_ISize_instRxcHasSize___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_ISize_instRxcHasSize: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_ISize_instRxcHasSize___closed__0_value) as *mut leanh::LeanObject;
pub static l_ISize_instRxoHasSize___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_ISize_instRxoHasSize___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_ISize_instRxoHasSize___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_ISize_instRxoHasSize___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_ISize_instRxoHasSize: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_ISize_instRxoHasSize___closed__0_value) as *mut leanh::LeanObject;
pub static l_ISize_instRxiHasSize___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_ISize_instRxiHasSize___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_ISize_instRxiHasSize___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_ISize_instRxiHasSize___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_ISize_instRxiHasSize: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_ISize_instRxiHasSize___closed__0_value) as *mut leanh::LeanObject;
pub unsafe fn l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instUpwardEnumerable___redArg___lam__0(
    mut v_m_632_: *mut leanh::LeanObject,
    mut v_inst_633_: *mut leanh::LeanObject,
    mut v_a_634_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_encode_635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_decode_636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_succ_x3f_637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_644_: u8 = 0;
    let mut v___x_645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_649_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_encode_635_ = leanh::lean_ctor_get(v_m_632_, 0);
                leanh::lean_inc(v_encode_635_);
                v_decode_636_ = leanh::lean_ctor_get(v_m_632_, 1);
                leanh::lean_inc(v_decode_636_);
                leanh::lean_dec_ref(v_m_632_);
                v_succ_x3f_637_ = leanh::lean_ctor_get(v_inst_633_, 0);
                leanh::lean_inc_ref(v_succ_x3f_637_);
                leanh::lean_dec_ref(v_inst_633_);
                v___x_638_ = leanh::lean_apply_1(v_encode_635_, v_a_634_);
                v___x_639_ = leanh::lean_apply_1(v_succ_x3f_637_, v___x_638_);
                if leanh::lean_obj_tag(v___x_639_) == 0 {
                    leanh::lean_dec(v_decode_636_);
                    v___x_640_ = leanh::lean_box(0);
                    return v___x_640_;
                } else {
                    v_val_641_ = leanh::lean_ctor_get(v___x_639_, 0);
                    v_isSharedCheck_649_ = (!leanh::lean_is_exclusive(v___x_639_)) as u8;
                    if v_isSharedCheck_649_ == 0 {
                        v___x_643_ = v___x_639_;
                        v_isShared_644_ = v_isSharedCheck_649_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_641_);
                        leanh::lean_dec(v___x_639_);
                        v___x_643_ = leanh::lean_box(0);
                        v_isShared_644_ = v_isSharedCheck_649_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_645_ = leanh::lean_apply_1(v_decode_636_, v_val_641_);
                if v_isShared_644_ == 0 {
                    leanh::lean_ctor_set(v___x_643_, 0, v___x_645_);
                    v___x_647_ = v___x_643_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_648_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_648_, 0, v___x_645_);
                    v___x_647_ = v_reuseFailAlloc_648_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_647_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instUpwardEnumerable___redArg___lam__1(
    mut v_m_650_: *mut leanh::LeanObject,
    mut v_inst_651_: *mut leanh::LeanObject,
    mut v_n_652_: *mut leanh::LeanObject,
    mut v_a_653_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_encode_654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_decode_655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_succMany_x3f_656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_663_: u8 = 0;
    let mut v___x_664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_668_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_encode_654_ = leanh::lean_ctor_get(v_m_650_, 0);
                leanh::lean_inc(v_encode_654_);
                v_decode_655_ = leanh::lean_ctor_get(v_m_650_, 1);
                leanh::lean_inc(v_decode_655_);
                leanh::lean_dec_ref(v_m_650_);
                v_succMany_x3f_656_ = leanh::lean_ctor_get(v_inst_651_, 1);
                leanh::lean_inc_ref(v_succMany_x3f_656_);
                leanh::lean_dec_ref(v_inst_651_);
                v___x_657_ = leanh::lean_apply_1(v_encode_654_, v_a_653_);
                v___x_658_ = leanh::lean_apply_2(v_succMany_x3f_656_, v_n_652_, v___x_657_);
                if leanh::lean_obj_tag(v___x_658_) == 0 {
                    leanh::lean_dec(v_decode_655_);
                    v___x_659_ = leanh::lean_box(0);
                    return v___x_659_;
                } else {
                    v_val_660_ = leanh::lean_ctor_get(v___x_658_, 0);
                    v_isSharedCheck_668_ = (!leanh::lean_is_exclusive(v___x_658_)) as u8;
                    if v_isSharedCheck_668_ == 0 {
                        v___x_662_ = v___x_658_;
                        v_isShared_663_ = v_isSharedCheck_668_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_660_);
                        leanh::lean_dec(v___x_658_);
                        v___x_662_ = leanh::lean_box(0);
                        v_isShared_663_ = v_isSharedCheck_668_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_664_ = leanh::lean_apply_1(v_decode_655_, v_val_660_);
                if v_isShared_663_ == 0 {
                    leanh::lean_ctor_set(v___x_662_, 0, v___x_664_);
                    v___x_666_ = v___x_662_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_667_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_667_, 0, v___x_664_);
                    v___x_666_ = v_reuseFailAlloc_667_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_666_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instUpwardEnumerable___redArg(
    mut v_inst_669_: *mut leanh::LeanObject,
    mut v_m_670_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_673_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_inst_669_);
    leanh::lean_inc_ref(v_m_670_);
    v___f_671_ = leanh::lean_alloc_closure(l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instUpwardEnumerable___redArg___lam__0 as *mut core::ffi::c_void, 3, 2);
    leanh::lean_closure_set(v___f_671_, 0, v_m_670_);
    leanh::lean_closure_set(v___f_671_, 1, v_inst_669_);
    v___f_672_ = leanh::lean_alloc_closure(l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instUpwardEnumerable___redArg___lam__1 as *mut core::ffi::c_void, 4, 2);
    leanh::lean_closure_set(v___f_672_, 0, v_m_670_);
    leanh::lean_closure_set(v___f_672_, 1, v_inst_669_);
    v___x_673_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_673_, 0, v___f_671_);
    leanh::lean_ctor_set(v___x_673_, 1, v___f_672_);
    return v___x_673_;
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instUpwardEnumerable(
    mut v_00_u03b1_674_: *mut leanh::LeanObject,
    mut v_inst_675_: *mut leanh::LeanObject,
    mut v_inst_676_: *mut leanh::LeanObject,
    mut v_00_u03b2_677_: *mut leanh::LeanObject,
    mut v_inst_678_: *mut leanh::LeanObject,
    mut v_inst_679_: *mut leanh::LeanObject,
    mut v_inst_680_: *mut leanh::LeanObject,
    mut v_inst_681_: *mut leanh::LeanObject,
    mut v_inst_682_: *mut leanh::LeanObject,
    mut v_inst_683_: *mut leanh::LeanObject,
    mut v_m_684_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_685_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_685_ =
        l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instUpwardEnumerable___redArg(
            v_inst_680_,
            v_m_684_,
        );
    return v___x_685_;
}
pub unsafe fn _init_l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___lam__0___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_687_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_686_ = leanh::lean_unsigned_to_nat(1);
    v___x_687_ = lean_nat_to_int(v___x_686_);
    return v___x_687_;
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___lam__0(
    mut v_lo_688_: u8,
    mut v_hi_689_: u8,
) -> *mut leanh::LeanObject {
    let mut v___x_690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_695_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_690_ = lean_int8_to_int(v_hi_689_);
    v___x_691_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___lam__0___closed__0), core::ptr::addr_of_mut!(l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___lam__0___closed__0_once), _init_l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___lam__0___closed__0);
    v___x_692_ = lean_int_add(v___x_690_, v___x_691_);
    v___x_693_ = lean_int8_to_int(v_lo_688_);
    v___x_694_ = lean_int_sub(v___x_692_, v___x_693_);
    leanh::lean_dec(v___x_692_);
    v___x_695_ = l_Int_toNat(v___x_694_);
    leanh::lean_dec(v___x_694_);
    return v___x_695_;
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___lam__0___boxed(
    mut v_lo_696_: *mut leanh::LeanObject,
    mut v_hi_697_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lo_boxed_698_: u8 = 0;
    let mut v_hi_boxed_699_: u8 = 0;
    let mut v_res_700_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_lo_boxed_698_ = (leanh::lean_unbox(v_lo_696_) as u8);
    v_hi_boxed_699_ = (leanh::lean_unbox(v_hi_697_) as u8);
    v_res_700_ = l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___lam__0(
        v_lo_boxed_698_,
        v_hi_boxed_699_,
    );
    return v_res_700_;
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instRxcHasSize___redArg___lam__0(
    mut v_m_703_: *mut leanh::LeanObject,
    mut v_inst_704_: *mut leanh::LeanObject,
    mut v_lo_705_: *mut leanh::LeanObject,
    mut v_hi_706_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_encode_707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_710_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_encode_707_ = leanh::lean_ctor_get(v_m_703_, 0);
    leanh::lean_inc_n(v_encode_707_, 2);
    leanh::lean_dec_ref(v_m_703_);
    v___x_708_ = leanh::lean_apply_1(v_encode_707_, v_lo_705_);
    v___x_709_ = leanh::lean_apply_1(v_encode_707_, v_hi_706_);
    v___x_710_ = leanh::lean_apply_2(v_inst_704_, v___x_708_, v___x_709_);
    return v___x_710_;
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instRxcHasSize___redArg(
    mut v_m_711_: *mut leanh::LeanObject,
    mut v_inst_712_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_713_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_713_ = leanh::lean_alloc_closure(
        l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instRxcHasSize___redArg___lam__0
            as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___f_713_, 0, v_m_711_);
    leanh::lean_closure_set(v___f_713_, 1, v_inst_712_);
    return v___f_713_;
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instRxcHasSize(
    mut v_00_u03b1_714_: *mut leanh::LeanObject,
    mut v_inst_715_: *mut leanh::LeanObject,
    mut v_inst_716_: *mut leanh::LeanObject,
    mut v_00_u03b2_717_: *mut leanh::LeanObject,
    mut v_inst_718_: *mut leanh::LeanObject,
    mut v_inst_719_: *mut leanh::LeanObject,
    mut v_inst_720_: *mut leanh::LeanObject,
    mut v_inst_721_: *mut leanh::LeanObject,
    mut v_inst_722_: *mut leanh::LeanObject,
    mut v_inst_723_: *mut leanh::LeanObject,
    mut v_m_724_: *mut leanh::LeanObject,
    mut v_inst_725_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_726_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_726_ = leanh::lean_alloc_closure(
        l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instRxcHasSize___redArg___lam__0
            as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___f_726_, 0, v_m_724_);
    leanh::lean_closure_set(v___f_726_, 1, v_inst_725_);
    return v___f_726_;
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instRxcHasSize___boxed(
    mut v_00_u03b1_727_: *mut leanh::LeanObject,
    mut v_inst_728_: *mut leanh::LeanObject,
    mut v_inst_729_: *mut leanh::LeanObject,
    mut v_00_u03b2_730_: *mut leanh::LeanObject,
    mut v_inst_731_: *mut leanh::LeanObject,
    mut v_inst_732_: *mut leanh::LeanObject,
    mut v_inst_733_: *mut leanh::LeanObject,
    mut v_inst_734_: *mut leanh::LeanObject,
    mut v_inst_735_: *mut leanh::LeanObject,
    mut v_inst_736_: *mut leanh::LeanObject,
    mut v_m_737_: *mut leanh::LeanObject,
    mut v_inst_738_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_739_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_739_ = l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instRxcHasSize(
        v_00_u03b1_727_,
        v_inst_728_,
        v_inst_729_,
        v_00_u03b2_730_,
        v_inst_731_,
        v_inst_732_,
        v_inst_733_,
        v_inst_734_,
        v_inst_735_,
        v_inst_736_,
        v_m_737_,
        v_inst_738_,
    );
    leanh::lean_dec_ref(v_inst_733_);
    return v_res_739_;
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instRxiHasSize___redArg___lam__0(
    mut v_m_740_: *mut leanh::LeanObject,
    mut v_inst_741_: *mut leanh::LeanObject,
    mut v_lo_742_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_encode_743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_745_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_encode_743_ = leanh::lean_ctor_get(v_m_740_, 0);
    leanh::lean_inc(v_encode_743_);
    leanh::lean_dec_ref(v_m_740_);
    v___x_744_ = leanh::lean_apply_1(v_encode_743_, v_lo_742_);
    v___x_745_ = leanh::lean_apply_1(v_inst_741_, v___x_744_);
    return v___x_745_;
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instRxiHasSize___redArg(
    mut v_m_746_: *mut leanh::LeanObject,
    mut v_inst_747_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_748_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_748_ = leanh::lean_alloc_closure(
        l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instRxiHasSize___redArg___lam__0
            as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_748_, 0, v_m_746_);
    leanh::lean_closure_set(v___f_748_, 1, v_inst_747_);
    return v___f_748_;
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instRxiHasSize(
    mut v_00_u03b1_749_: *mut leanh::LeanObject,
    mut v_inst_750_: *mut leanh::LeanObject,
    mut v_inst_751_: *mut leanh::LeanObject,
    mut v_00_u03b2_752_: *mut leanh::LeanObject,
    mut v_inst_753_: *mut leanh::LeanObject,
    mut v_inst_754_: *mut leanh::LeanObject,
    mut v_inst_755_: *mut leanh::LeanObject,
    mut v_inst_756_: *mut leanh::LeanObject,
    mut v_inst_757_: *mut leanh::LeanObject,
    mut v_inst_758_: *mut leanh::LeanObject,
    mut v_m_759_: *mut leanh::LeanObject,
    mut v_inst_760_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_761_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_761_ = leanh::lean_alloc_closure(
        l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instRxiHasSize___redArg___lam__0
            as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_761_, 0, v_m_759_);
    leanh::lean_closure_set(v___f_761_, 1, v_inst_760_);
    return v___f_761_;
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instRxiHasSize___boxed(
    mut v_00_u03b1_762_: *mut leanh::LeanObject,
    mut v_inst_763_: *mut leanh::LeanObject,
    mut v_inst_764_: *mut leanh::LeanObject,
    mut v_00_u03b2_765_: *mut leanh::LeanObject,
    mut v_inst_766_: *mut leanh::LeanObject,
    mut v_inst_767_: *mut leanh::LeanObject,
    mut v_inst_768_: *mut leanh::LeanObject,
    mut v_inst_769_: *mut leanh::LeanObject,
    mut v_inst_770_: *mut leanh::LeanObject,
    mut v_inst_771_: *mut leanh::LeanObject,
    mut v_m_772_: *mut leanh::LeanObject,
    mut v_inst_773_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_774_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_774_ = l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instRxiHasSize(
        v_00_u03b1_762_,
        v_inst_763_,
        v_inst_764_,
        v_00_u03b2_765_,
        v_inst_766_,
        v_inst_767_,
        v_inst_768_,
        v_inst_769_,
        v_inst_770_,
        v_inst_771_,
        v_m_772_,
        v_inst_773_,
    );
    leanh::lean_dec_ref(v_inst_768_);
    return v_res_774_;
}
pub unsafe fn _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_minValueSealed___closed__0()
-> u8 {
    let mut v___x_775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_776_: u8 = 0;
    v___x_775_ = leanh::lean_unsigned_to_nat(128);
    v___x_776_ = lean_int8_of_nat(v___x_775_);
    return v___x_776_;
}
pub unsafe fn _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_minValueSealed___closed__1()
-> u8 {
    let mut v___x_777_: u8 = 0;
    let mut v___x_778_: u8 = 0;
    v___x_777_ = leanh::lean_uint8_once(
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_minValueSealed___closed__0
        ),
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_minValueSealed___closed__0_once
        ),
        _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_minValueSealed___closed__0,
    );
    v___x_778_ = lean_int8_neg(v___x_777_);
    return v___x_778_;
}
pub unsafe fn _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_minValueSealed() -> u8 {
    let mut v___x_779_: u8 = 0;
    v___x_779_ = leanh::lean_uint8_once(
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_minValueSealed___closed__1
        ),
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_minValueSealed___closed__1_once
        ),
        _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_minValueSealed___closed__1,
    );
    return v___x_779_;
}
pub unsafe fn _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_maxValueSealed___closed__0()
-> u8 {
    let mut v___x_780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_781_: u8 = 0;
    v___x_780_ = leanh::lean_unsigned_to_nat(127);
    v___x_781_ = lean_int8_of_nat(v___x_780_);
    return v___x_781_;
}
pub unsafe fn _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_maxValueSealed() -> u8 {
    let mut v___x_782_: u8 = 0;
    v___x_782_ = leanh::lean_uint8_once(
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_maxValueSealed___closed__0
        ),
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_maxValueSealed___closed__0_once
        ),
        _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_maxValueSealed___closed__0,
    );
    return v___x_782_;
}
pub unsafe fn _init_l_Int8_instUpwardEnumerable___lam__0___closed__0() -> u8 {
    let mut v___x_783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_784_: u8 = 0;
    v___x_783_ = leanh::lean_unsigned_to_nat(1);
    v___x_784_ = lean_int8_of_nat(v___x_783_);
    return v___x_784_;
}
pub unsafe fn l_Int8_instUpwardEnumerable___lam__0(
    mut v_i_785_: u8,
) -> *mut leanh::LeanObject {
    let mut v___x_786_: u8 = 0;
    let mut v___x_787_: u8 = 0;
    let mut v___x_788_: u8 = 0;
    let mut v___x_789_: u8 = 0;
    v___x_786_ = leanh::lean_uint8_once(
        core::ptr::addr_of_mut!(l_Int8_instUpwardEnumerable___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Int8_instUpwardEnumerable___lam__0___closed__0_once),
        _init_l_Int8_instUpwardEnumerable___lam__0___closed__0,
    );
    v___x_787_ = lean_int8_add(v_i_785_, v___x_786_);
    v___x_788_ = leanh::lean_uint8_once(
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_minValueSealed___closed__1
        ),
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_minValueSealed___closed__1_once
        ),
        _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_minValueSealed___closed__1,
    );
    v___x_789_ = lean_int8_dec_eq(v___x_787_, v___x_788_);
    if v___x_789_ == 0 {
        let mut v___x_790_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_791_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_790_ = leanh::lean_box((v___x_787_) as usize);
        v___x_791_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_791_, 0, v___x_790_);
        return v___x_791_;
    } else {
        let mut v___x_792_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_792_ = leanh::lean_box(0);
        return v___x_792_;
    }
}
pub unsafe fn l_Int8_instUpwardEnumerable___lam__0___boxed(
    mut v_i_793_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_794_: u8 = 0;
    let mut v_res_795_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_794_ = (leanh::lean_unbox(v_i_793_) as u8);
    v_res_795_ = l_Int8_instUpwardEnumerable___lam__0(v_i_boxed_794_);
    return v_res_795_;
}
pub unsafe fn _init_l_Int8_instUpwardEnumerable___lam__1___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_796_: u8 = 0;
    let mut v___x_797_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_796_ = leanh::lean_uint8_once(
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_maxValueSealed___closed__0
        ),
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_maxValueSealed___closed__0_once
        ),
        _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_maxValueSealed___closed__0,
    );
    v___x_797_ = lean_int8_to_int(v___x_796_);
    return v___x_797_;
}
pub unsafe fn l_Int8_instUpwardEnumerable___lam__1(
    mut v_n_798_: *mut leanh::LeanObject,
    mut v_i_799_: u8,
) -> *mut leanh::LeanObject {
    let mut v___x_800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_804_: u8 = 0;
    v___x_800_ = lean_int8_to_int(v_i_799_);
    v___x_801_ = lean_nat_to_int(v_n_798_);
    v___x_802_ = lean_int_add(v___x_800_, v___x_801_);
    leanh::lean_dec(v___x_801_);
    v___x_803_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Int8_instUpwardEnumerable___lam__1___closed__0),
        core::ptr::addr_of_mut!(l_Int8_instUpwardEnumerable___lam__1___closed__0_once),
        _init_l_Int8_instUpwardEnumerable___lam__1___closed__0,
    );
    v___x_804_ = lean_int_dec_le(v___x_802_, v___x_803_);
    if v___x_804_ == 0 {
        let mut v___x_805_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v___x_802_);
        v___x_805_ = leanh::lean_box(0);
        return v___x_805_;
    } else {
        let mut v___x_806_: u8 = 0;
        let mut v___x_807_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_808_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_806_ = lean_int8_of_int(v___x_802_);
        leanh::lean_dec(v___x_802_);
        v___x_807_ = leanh::lean_box((v___x_806_) as usize);
        v___x_808_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_808_, 0, v___x_807_);
        return v___x_808_;
    }
}
pub unsafe fn l_Int8_instUpwardEnumerable___lam__1___boxed(
    mut v_n_809_: *mut leanh::LeanObject,
    mut v_i_810_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_811_: u8 = 0;
    let mut v_res_812_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_811_ = (leanh::lean_unbox(v_i_810_) as u8);
    v_res_812_ = l_Int8_instUpwardEnumerable___lam__1(v_n_809_, v_i_boxed_811_);
    return v_res_812_;
}
pub unsafe fn _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_instLeast_x3f___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_819_: u8 = 0;
    let mut v___x_820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_821_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_819_ = leanh::lean_uint8_once(
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_minValueSealed___closed__1
        ),
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_minValueSealed___closed__1_once
        ),
        _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_minValueSealed___closed__1,
    );
    v___x_820_ = leanh::lean_box((v___x_819_) as usize);
    v___x_821_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_821_, 0, v___x_820_);
    return v___x_821_;
}
pub unsafe fn _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_instLeast_x3f()
-> *mut leanh::LeanObject {
    let mut v___x_822_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_822_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_instLeast_x3f___closed__0
        ),
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_instLeast_x3f___closed__0_once
        ),
        _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_instLeast_x3f___closed__0,
    );
    return v___x_822_;
}
pub unsafe fn _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_instHasModelBitVecOfNatNat___closed__1()
-> *mut leanh::LeanObject {
    let mut v___f_824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_826_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_824_ =
        leanh::lean_alloc_closure(l_UInt8_ofBitVec___boxed as *mut core::ffi::c_void, 1, 0);
    v___f_825_ =
        l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_instHasModelBitVecOfNatNat___closed__0;
    v___x_826_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_826_, 0, v___f_825_);
    leanh::lean_ctor_set(v___x_826_, 1, v___f_824_);
    return v___x_826_;
}
pub unsafe fn _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_instHasModelBitVecOfNatNat()
-> *mut leanh::LeanObject {
    let mut v___x_827_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_827_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_instHasModelBitVecOfNatNat___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_instHasModelBitVecOfNatNat___closed__1_once), _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_instHasModelBitVecOfNatNat___closed__1);
    return v___x_827_;
}
pub unsafe fn l_Int8_instRxoHasSize___lam__0(
    mut v_lo_829_: u8,
    mut v_hi_830_: u8,
) -> *mut leanh::LeanObject {
    let mut v___x_831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_838_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_831_ = lean_int8_to_int(v_hi_830_);
    v___x_832_ = leanh::lean_unsigned_to_nat(1);
    v___x_833_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___lam__0___closed__0), core::ptr::addr_of_mut!(l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___lam__0___closed__0_once), _init_l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___lam__0___closed__0);
    v___x_834_ = lean_int_add(v___x_831_, v___x_833_);
    v___x_835_ = lean_int8_to_int(v_lo_829_);
    v___x_836_ = lean_int_sub(v___x_834_, v___x_835_);
    leanh::lean_dec(v___x_834_);
    v___x_837_ = l_Int_toNat(v___x_836_);
    leanh::lean_dec(v___x_836_);
    v___x_838_ = lean_nat_sub(v___x_837_, v___x_832_);
    leanh::lean_dec(v___x_837_);
    return v___x_838_;
}
pub unsafe fn l_Int8_instRxoHasSize___lam__0___boxed(
    mut v_lo_839_: *mut leanh::LeanObject,
    mut v_hi_840_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lo_boxed_841_: u8 = 0;
    let mut v_hi_boxed_842_: u8 = 0;
    let mut v_res_843_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_lo_boxed_841_ = (leanh::lean_unbox(v_lo_839_) as u8);
    v_hi_boxed_842_ = (leanh::lean_unbox(v_hi_840_) as u8);
    v_res_843_ = l_Int8_instRxoHasSize___lam__0(v_lo_boxed_841_, v_hi_boxed_842_);
    return v_res_843_;
}
pub unsafe fn _init_l_Int8_instRxiHasSize___lam__0___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_847_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_846_ = leanh::lean_unsigned_to_nat(2);
    v___x_847_ = lean_nat_to_int(v___x_846_);
    return v___x_847_;
}
pub unsafe fn _init_l_Int8_instRxiHasSize___lam__0___closed__1() -> *mut leanh::LeanObject {
    let mut v___x_848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_850_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_848_ = leanh::lean_unsigned_to_nat(7);
    v___x_849_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Int8_instRxiHasSize___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Int8_instRxiHasSize___lam__0___closed__0_once),
        _init_l_Int8_instRxiHasSize___lam__0___closed__0,
    );
    v___x_850_ = l_Int_pow(v___x_849_, v___x_848_);
    return v___x_850_;
}
pub unsafe fn l_Int8_instRxiHasSize___lam__0(mut v_lo_851_: u8) -> *mut leanh::LeanObject {
    let mut v___x_852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_855_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_852_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Int8_instRxiHasSize___lam__0___closed__1),
        core::ptr::addr_of_mut!(l_Int8_instRxiHasSize___lam__0___closed__1_once),
        _init_l_Int8_instRxiHasSize___lam__0___closed__1,
    );
    v___x_853_ = lean_int8_to_int(v_lo_851_);
    v___x_854_ = lean_int_sub(v___x_852_, v___x_853_);
    v___x_855_ = l_Int_toNat(v___x_854_);
    leanh::lean_dec(v___x_854_);
    return v___x_855_;
}
pub unsafe fn l_Int8_instRxiHasSize___lam__0___boxed(
    mut v_lo_856_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lo_boxed_857_: u8 = 0;
    let mut v_res_858_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_lo_boxed_857_ = (leanh::lean_unbox(v_lo_856_) as u8);
    v_res_858_ = l_Int8_instRxiHasSize___lam__0(v_lo_boxed_857_);
    return v_res_858_;
}
pub unsafe fn _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_minValueSealed___closed__0()
-> u16 {
    let mut v___x_861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_862_: u16 = 0;
    v___x_861_ = leanh::lean_unsigned_to_nat(32768);
    v___x_862_ = lean_int16_of_nat(v___x_861_);
    return v___x_862_;
}
pub unsafe fn _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_minValueSealed___closed__1()
-> u16 {
    let mut v___x_863_: u16 = 0;
    let mut v___x_864_: u16 = 0;
    v___x_863_ = leanh::lean_uint16_once(
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_minValueSealed___closed__0
        ),
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_minValueSealed___closed__0_once
        ),
        _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_minValueSealed___closed__0,
    );
    v___x_864_ = lean_int16_neg(v___x_863_);
    return v___x_864_;
}
pub unsafe fn _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_minValueSealed() -> u16 {
    let mut v___x_865_: u16 = 0;
    v___x_865_ = leanh::lean_uint16_once(
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_minValueSealed___closed__1
        ),
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_minValueSealed___closed__1_once
        ),
        _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_minValueSealed___closed__1,
    );
    return v___x_865_;
}
pub unsafe fn _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_maxValueSealed___closed__0()
-> u16 {
    let mut v___x_866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_867_: u16 = 0;
    v___x_866_ = leanh::lean_unsigned_to_nat(32767);
    v___x_867_ = lean_int16_of_nat(v___x_866_);
    return v___x_867_;
}
pub unsafe fn _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_maxValueSealed() -> u16 {
    let mut v___x_868_: u16 = 0;
    v___x_868_ = leanh::lean_uint16_once(
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_maxValueSealed___closed__0
        ),
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_maxValueSealed___closed__0_once
        ),
        _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_maxValueSealed___closed__0,
    );
    return v___x_868_;
}
pub unsafe fn _init_l_Int16_instUpwardEnumerable___lam__0___closed__0() -> u16 {
    let mut v___x_869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_870_: u16 = 0;
    v___x_869_ = leanh::lean_unsigned_to_nat(1);
    v___x_870_ = lean_int16_of_nat(v___x_869_);
    return v___x_870_;
}
pub unsafe fn l_Int16_instUpwardEnumerable___lam__0(
    mut v_i_871_: u16,
) -> *mut leanh::LeanObject {
    let mut v___x_872_: u16 = 0;
    let mut v___x_873_: u16 = 0;
    let mut v___x_874_: u16 = 0;
    let mut v___x_875_: u8 = 0;
    v___x_872_ = leanh::lean_uint16_once(
        core::ptr::addr_of_mut!(l_Int16_instUpwardEnumerable___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Int16_instUpwardEnumerable___lam__0___closed__0_once),
        _init_l_Int16_instUpwardEnumerable___lam__0___closed__0,
    );
    v___x_873_ = lean_int16_add(v_i_871_, v___x_872_);
    v___x_874_ = leanh::lean_uint16_once(
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_minValueSealed___closed__1
        ),
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_minValueSealed___closed__1_once
        ),
        _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_minValueSealed___closed__1,
    );
    v___x_875_ = lean_int16_dec_eq(v___x_873_, v___x_874_);
    if v___x_875_ == 0 {
        let mut v___x_876_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_877_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_876_ = leanh::lean_box((v___x_873_) as usize);
        v___x_877_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_877_, 0, v___x_876_);
        return v___x_877_;
    } else {
        let mut v___x_878_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_878_ = leanh::lean_box(0);
        return v___x_878_;
    }
}
pub unsafe fn l_Int16_instUpwardEnumerable___lam__0___boxed(
    mut v_i_879_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_880_: u16 = 0;
    let mut v_res_881_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_880_ = (leanh::lean_unbox(v_i_879_) as u16);
    v_res_881_ = l_Int16_instUpwardEnumerable___lam__0(v_i_boxed_880_);
    return v_res_881_;
}
pub unsafe fn _init_l_Int16_instUpwardEnumerable___lam__1___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_882_: u16 = 0;
    let mut v___x_883_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_882_ = leanh::lean_uint16_once(
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_maxValueSealed___closed__0
        ),
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_maxValueSealed___closed__0_once
        ),
        _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_maxValueSealed___closed__0,
    );
    v___x_883_ = lean_int16_to_int(v___x_882_);
    return v___x_883_;
}
pub unsafe fn l_Int16_instUpwardEnumerable___lam__1(
    mut v_n_884_: *mut leanh::LeanObject,
    mut v_i_885_: u16,
) -> *mut leanh::LeanObject {
    let mut v___x_886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_890_: u8 = 0;
    v___x_886_ = lean_int16_to_int(v_i_885_);
    v___x_887_ = lean_nat_to_int(v_n_884_);
    v___x_888_ = lean_int_add(v___x_886_, v___x_887_);
    leanh::lean_dec(v___x_887_);
    v___x_889_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Int16_instUpwardEnumerable___lam__1___closed__0),
        core::ptr::addr_of_mut!(l_Int16_instUpwardEnumerable___lam__1___closed__0_once),
        _init_l_Int16_instUpwardEnumerable___lam__1___closed__0,
    );
    v___x_890_ = lean_int_dec_le(v___x_888_, v___x_889_);
    if v___x_890_ == 0 {
        let mut v___x_891_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v___x_888_);
        v___x_891_ = leanh::lean_box(0);
        return v___x_891_;
    } else {
        let mut v___x_892_: u16 = 0;
        let mut v___x_893_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_894_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_892_ = lean_int16_of_int(v___x_888_);
        leanh::lean_dec(v___x_888_);
        v___x_893_ = leanh::lean_box((v___x_892_) as usize);
        v___x_894_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_894_, 0, v___x_893_);
        return v___x_894_;
    }
}
pub unsafe fn l_Int16_instUpwardEnumerable___lam__1___boxed(
    mut v_n_895_: *mut leanh::LeanObject,
    mut v_i_896_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_897_: u16 = 0;
    let mut v_res_898_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_897_ = (leanh::lean_unbox(v_i_896_) as u16);
    v_res_898_ = l_Int16_instUpwardEnumerable___lam__1(v_n_895_, v_i_boxed_897_);
    return v_res_898_;
}
pub unsafe fn _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_instLeast_x3f___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_905_: u16 = 0;
    let mut v___x_906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_907_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_905_ = leanh::lean_uint16_once(
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_minValueSealed___closed__1
        ),
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_minValueSealed___closed__1_once
        ),
        _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_minValueSealed___closed__1,
    );
    v___x_906_ = leanh::lean_box((v___x_905_) as usize);
    v___x_907_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_907_, 0, v___x_906_);
    return v___x_907_;
}
pub unsafe fn _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_instLeast_x3f()
-> *mut leanh::LeanObject {
    let mut v___x_908_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_908_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_instLeast_x3f___closed__0
        ),
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_instLeast_x3f___closed__0_once
        ),
        _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_instLeast_x3f___closed__0,
    );
    return v___x_908_;
}
pub unsafe fn _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_instHasModelBitVecOfNatNat___closed__1()
-> *mut leanh::LeanObject {
    let mut v___f_910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_912_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_910_ =
        leanh::lean_alloc_closure(l_UInt16_ofBitVec___boxed as *mut core::ffi::c_void, 1, 0);
    v___f_911_ = l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_instHasModelBitVecOfNatNat___closed__0;
    v___x_912_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_912_, 0, v___f_911_);
    leanh::lean_ctor_set(v___x_912_, 1, v___f_910_);
    return v___x_912_;
}
pub unsafe fn _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_instHasModelBitVecOfNatNat()
-> *mut leanh::LeanObject {
    let mut v___x_913_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_913_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_instHasModelBitVecOfNatNat___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_instHasModelBitVecOfNatNat___closed__1_once), _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_instHasModelBitVecOfNatNat___closed__1);
    return v___x_913_;
}
pub unsafe fn l_Int16_instRxcHasSize___lam__0(
    mut v_lo_914_: u16,
    mut v_hi_915_: u16,
) -> *mut leanh::LeanObject {
    let mut v___x_916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_921_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_916_ = lean_int16_to_int(v_hi_915_);
    v___x_917_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___lam__0___closed__0), core::ptr::addr_of_mut!(l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___lam__0___closed__0_once), _init_l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___lam__0___closed__0);
    v___x_918_ = lean_int_add(v___x_916_, v___x_917_);
    v___x_919_ = lean_int16_to_int(v_lo_914_);
    v___x_920_ = lean_int_sub(v___x_918_, v___x_919_);
    leanh::lean_dec(v___x_918_);
    v___x_921_ = l_Int_toNat(v___x_920_);
    leanh::lean_dec(v___x_920_);
    return v___x_921_;
}
pub unsafe fn l_Int16_instRxcHasSize___lam__0___boxed(
    mut v_lo_922_: *mut leanh::LeanObject,
    mut v_hi_923_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lo_boxed_924_: u16 = 0;
    let mut v_hi_boxed_925_: u16 = 0;
    let mut v_res_926_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_lo_boxed_924_ = (leanh::lean_unbox(v_lo_922_) as u16);
    v_hi_boxed_925_ = (leanh::lean_unbox(v_hi_923_) as u16);
    v_res_926_ = l_Int16_instRxcHasSize___lam__0(v_lo_boxed_924_, v_hi_boxed_925_);
    return v_res_926_;
}
pub unsafe fn l_Int16_instRxoHasSize___lam__0(
    mut v_lo_929_: u16,
    mut v_hi_930_: u16,
) -> *mut leanh::LeanObject {
    let mut v___x_931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_938_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_931_ = lean_int16_to_int(v_hi_930_);
    v___x_932_ = leanh::lean_unsigned_to_nat(1);
    v___x_933_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___lam__0___closed__0), core::ptr::addr_of_mut!(l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___lam__0___closed__0_once), _init_l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___lam__0___closed__0);
    v___x_934_ = lean_int_add(v___x_931_, v___x_933_);
    v___x_935_ = lean_int16_to_int(v_lo_929_);
    v___x_936_ = lean_int_sub(v___x_934_, v___x_935_);
    leanh::lean_dec(v___x_934_);
    v___x_937_ = l_Int_toNat(v___x_936_);
    leanh::lean_dec(v___x_936_);
    v___x_938_ = lean_nat_sub(v___x_937_, v___x_932_);
    leanh::lean_dec(v___x_937_);
    return v___x_938_;
}
pub unsafe fn l_Int16_instRxoHasSize___lam__0___boxed(
    mut v_lo_939_: *mut leanh::LeanObject,
    mut v_hi_940_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lo_boxed_941_: u16 = 0;
    let mut v_hi_boxed_942_: u16 = 0;
    let mut v_res_943_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_lo_boxed_941_ = (leanh::lean_unbox(v_lo_939_) as u16);
    v_hi_boxed_942_ = (leanh::lean_unbox(v_hi_940_) as u16);
    v_res_943_ = l_Int16_instRxoHasSize___lam__0(v_lo_boxed_941_, v_hi_boxed_942_);
    return v_res_943_;
}
pub unsafe fn _init_l_Int16_instRxiHasSize___lam__0___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_948_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_946_ = leanh::lean_unsigned_to_nat(15);
    v___x_947_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Int8_instRxiHasSize___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Int8_instRxiHasSize___lam__0___closed__0_once),
        _init_l_Int8_instRxiHasSize___lam__0___closed__0,
    );
    v___x_948_ = l_Int_pow(v___x_947_, v___x_946_);
    return v___x_948_;
}
pub unsafe fn l_Int16_instRxiHasSize___lam__0(mut v_lo_949_: u16) -> *mut leanh::LeanObject {
    let mut v___x_950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_953_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_950_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Int16_instRxiHasSize___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Int16_instRxiHasSize___lam__0___closed__0_once),
        _init_l_Int16_instRxiHasSize___lam__0___closed__0,
    );
    v___x_951_ = lean_int16_to_int(v_lo_949_);
    v___x_952_ = lean_int_sub(v___x_950_, v___x_951_);
    v___x_953_ = l_Int_toNat(v___x_952_);
    leanh::lean_dec(v___x_952_);
    return v___x_953_;
}
pub unsafe fn l_Int16_instRxiHasSize___lam__0___boxed(
    mut v_lo_954_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lo_boxed_955_: u16 = 0;
    let mut v_res_956_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_lo_boxed_955_ = (leanh::lean_unbox(v_lo_954_) as u16);
    v_res_956_ = l_Int16_instRxiHasSize___lam__0(v_lo_boxed_955_);
    return v_res_956_;
}
pub unsafe fn _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_minValueSealed___closed__0()
-> u32 {
    let mut v___x_959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_960_: u32 = 0;
    v___x_959_ = leanh::lean_unsigned_to_nat(2147483648);
    v___x_960_ = lean_int32_of_nat(v___x_959_);
    return v___x_960_;
}
pub unsafe fn _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_minValueSealed___closed__1()
-> u32 {
    let mut v___x_961_: u32 = 0;
    let mut v___x_962_: u32 = 0;
    v___x_961_ = leanh::lean_uint32_once(
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_minValueSealed___closed__0
        ),
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_minValueSealed___closed__0_once
        ),
        _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_minValueSealed___closed__0,
    );
    v___x_962_ = lean_int32_neg(v___x_961_);
    return v___x_962_;
}
pub unsafe fn _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_minValueSealed() -> u32 {
    let mut v___x_963_: u32 = 0;
    v___x_963_ = leanh::lean_uint32_once(
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_minValueSealed___closed__1
        ),
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_minValueSealed___closed__1_once
        ),
        _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_minValueSealed___closed__1,
    );
    return v___x_963_;
}
pub unsafe fn _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_maxValueSealed___closed__0()
-> u32 {
    let mut v___x_964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_965_: u32 = 0;
    v___x_964_ = leanh::lean_unsigned_to_nat(2147483647);
    v___x_965_ = lean_int32_of_nat(v___x_964_);
    return v___x_965_;
}
pub unsafe fn _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_maxValueSealed() -> u32 {
    let mut v___x_966_: u32 = 0;
    v___x_966_ = leanh::lean_uint32_once(
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_maxValueSealed___closed__0
        ),
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_maxValueSealed___closed__0_once
        ),
        _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_maxValueSealed___closed__0,
    );
    return v___x_966_;
}
pub unsafe fn _init_l_Int32_instUpwardEnumerable___lam__0___closed__0() -> u32 {
    let mut v___x_967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_968_: u32 = 0;
    v___x_967_ = leanh::lean_unsigned_to_nat(1);
    v___x_968_ = lean_int32_of_nat(v___x_967_);
    return v___x_968_;
}
pub unsafe fn l_Int32_instUpwardEnumerable___lam__0(
    mut v_i_969_: u32,
) -> *mut leanh::LeanObject {
    let mut v___x_970_: u32 = 0;
    let mut v___x_971_: u32 = 0;
    let mut v___x_972_: u32 = 0;
    let mut v___x_973_: u8 = 0;
    v___x_970_ = leanh::lean_uint32_once(
        core::ptr::addr_of_mut!(l_Int32_instUpwardEnumerable___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Int32_instUpwardEnumerable___lam__0___closed__0_once),
        _init_l_Int32_instUpwardEnumerable___lam__0___closed__0,
    );
    v___x_971_ = lean_int32_add(v_i_969_, v___x_970_);
    v___x_972_ = leanh::lean_uint32_once(
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_minValueSealed___closed__1
        ),
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_minValueSealed___closed__1_once
        ),
        _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_minValueSealed___closed__1,
    );
    v___x_973_ = lean_int32_dec_eq(v___x_971_, v___x_972_);
    if v___x_973_ == 0 {
        let mut v___x_974_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_975_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_974_ = leanh::lean_box_uint32(v___x_971_);
        v___x_975_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_975_, 0, v___x_974_);
        return v___x_975_;
    } else {
        let mut v___x_976_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_976_ = leanh::lean_box(0);
        return v___x_976_;
    }
}
pub unsafe fn l_Int32_instUpwardEnumerable___lam__0___boxed(
    mut v_i_977_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_978_: u32 = 0;
    let mut v_res_979_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_978_ = leanh::lean_unbox_uint32(v_i_977_);
    leanh::lean_dec(v_i_977_);
    v_res_979_ = l_Int32_instUpwardEnumerable___lam__0(v_i_boxed_978_);
    return v_res_979_;
}
pub unsafe fn _init_l_Int32_instUpwardEnumerable___lam__1___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_980_: u32 = 0;
    let mut v___x_981_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_980_ = leanh::lean_uint32_once(
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_maxValueSealed___closed__0
        ),
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_maxValueSealed___closed__0_once
        ),
        _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_maxValueSealed___closed__0,
    );
    v___x_981_ = lean_int32_to_int(v___x_980_);
    return v___x_981_;
}
pub unsafe fn l_Int32_instUpwardEnumerable___lam__1(
    mut v_n_982_: *mut leanh::LeanObject,
    mut v_i_983_: u32,
) -> *mut leanh::LeanObject {
    let mut v___x_984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_988_: u8 = 0;
    v___x_984_ = lean_int32_to_int(v_i_983_);
    v___x_985_ = lean_nat_to_int(v_n_982_);
    v___x_986_ = lean_int_add(v___x_984_, v___x_985_);
    leanh::lean_dec(v___x_985_);
    leanh::lean_dec(v___x_984_);
    v___x_987_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Int32_instUpwardEnumerable___lam__1___closed__0),
        core::ptr::addr_of_mut!(l_Int32_instUpwardEnumerable___lam__1___closed__0_once),
        _init_l_Int32_instUpwardEnumerable___lam__1___closed__0,
    );
    v___x_988_ = lean_int_dec_le(v___x_986_, v___x_987_);
    if v___x_988_ == 0 {
        let mut v___x_989_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v___x_986_);
        v___x_989_ = leanh::lean_box(0);
        return v___x_989_;
    } else {
        let mut v___x_990_: u32 = 0;
        let mut v___x_991_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_992_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_990_ = lean_int32_of_int(v___x_986_);
        leanh::lean_dec(v___x_986_);
        v___x_991_ = leanh::lean_box_uint32(v___x_990_);
        v___x_992_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_992_, 0, v___x_991_);
        return v___x_992_;
    }
}
pub unsafe fn l_Int32_instUpwardEnumerable___lam__1___boxed(
    mut v_n_993_: *mut leanh::LeanObject,
    mut v_i_994_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_995_: u32 = 0;
    let mut v_res_996_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_995_ = leanh::lean_unbox_uint32(v_i_994_);
    leanh::lean_dec(v_i_994_);
    v_res_996_ = l_Int32_instUpwardEnumerable___lam__1(v_n_993_, v_i_boxed_995_);
    return v_res_996_;
}
pub unsafe fn _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_instLeast_x3f___closed__0___boxed__const__1()
-> *mut leanh::LeanObject {
    let mut v___x_1003_: u32 = 0;
    let mut v___x_1004_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1003_ = leanh::lean_uint32_once(
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_minValueSealed___closed__1
        ),
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_minValueSealed___closed__1_once
        ),
        _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_minValueSealed___closed__1,
    );
    v___x_1004_ = leanh::lean_box_uint32(v___x_1003_);
    return v___x_1004_;
}
pub unsafe fn _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_instLeast_x3f___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1006_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1005_ = l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_instLeast_x3f___closed__0___boxed__const__1;
    v___x_1006_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1006_, 0, v___x_1005_);
    return v___x_1006_;
}
pub unsafe fn _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_instLeast_x3f()
-> *mut leanh::LeanObject {
    let mut v___x_1007_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1007_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_instLeast_x3f___closed__0
        ),
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_instLeast_x3f___closed__0_once
        ),
        _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_instLeast_x3f___closed__0,
    );
    return v___x_1007_;
}
pub unsafe fn _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_instHasModelBitVecOfNatNat___closed__1()
-> *mut leanh::LeanObject {
    let mut v___f_1009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1011_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1009_ =
        leanh::lean_alloc_closure(l_UInt32_ofBitVec___boxed as *mut core::ffi::c_void, 1, 0);
    v___f_1010_ = l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_instHasModelBitVecOfNatNat___closed__0;
    v___x_1011_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1011_, 0, v___f_1010_);
    leanh::lean_ctor_set(v___x_1011_, 1, v___f_1009_);
    return v___x_1011_;
}
pub unsafe fn _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_instHasModelBitVecOfNatNat()
-> *mut leanh::LeanObject {
    let mut v___x_1012_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1012_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_instHasModelBitVecOfNatNat___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_instHasModelBitVecOfNatNat___closed__1_once), _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_instHasModelBitVecOfNatNat___closed__1);
    return v___x_1012_;
}
pub unsafe fn l_Int32_instRxcHasSize___lam__0(
    mut v_lo_1013_: u32,
    mut v_hi_1014_: u32,
) -> *mut leanh::LeanObject {
    let mut v___x_1015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1020_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1015_ = lean_int32_to_int(v_hi_1014_);
    v___x_1016_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___lam__0___closed__0), core::ptr::addr_of_mut!(l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___lam__0___closed__0_once), _init_l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___lam__0___closed__0);
    v___x_1017_ = lean_int_add(v___x_1015_, v___x_1016_);
    leanh::lean_dec(v___x_1015_);
    v___x_1018_ = lean_int32_to_int(v_lo_1013_);
    v___x_1019_ = lean_int_sub(v___x_1017_, v___x_1018_);
    leanh::lean_dec(v___x_1018_);
    leanh::lean_dec(v___x_1017_);
    v___x_1020_ = l_Int_toNat(v___x_1019_);
    leanh::lean_dec(v___x_1019_);
    return v___x_1020_;
}
pub unsafe fn l_Int32_instRxcHasSize___lam__0___boxed(
    mut v_lo_1021_: *mut leanh::LeanObject,
    mut v_hi_1022_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lo_boxed_1023_: u32 = 0;
    let mut v_hi_boxed_1024_: u32 = 0;
    let mut v_res_1025_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_lo_boxed_1023_ = leanh::lean_unbox_uint32(v_lo_1021_);
    leanh::lean_dec(v_lo_1021_);
    v_hi_boxed_1024_ = leanh::lean_unbox_uint32(v_hi_1022_);
    leanh::lean_dec(v_hi_1022_);
    v_res_1025_ = l_Int32_instRxcHasSize___lam__0(v_lo_boxed_1023_, v_hi_boxed_1024_);
    return v_res_1025_;
}
pub unsafe fn l_Int32_instRxoHasSize___lam__0(
    mut v_lo_1028_: u32,
    mut v_hi_1029_: u32,
) -> *mut leanh::LeanObject {
    let mut v___x_1030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1037_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1030_ = lean_int32_to_int(v_hi_1029_);
    v___x_1031_ = leanh::lean_unsigned_to_nat(1);
    v___x_1032_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___lam__0___closed__0), core::ptr::addr_of_mut!(l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___lam__0___closed__0_once), _init_l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___lam__0___closed__0);
    v___x_1033_ = lean_int_add(v___x_1030_, v___x_1032_);
    leanh::lean_dec(v___x_1030_);
    v___x_1034_ = lean_int32_to_int(v_lo_1028_);
    v___x_1035_ = lean_int_sub(v___x_1033_, v___x_1034_);
    leanh::lean_dec(v___x_1034_);
    leanh::lean_dec(v___x_1033_);
    v___x_1036_ = l_Int_toNat(v___x_1035_);
    leanh::lean_dec(v___x_1035_);
    v___x_1037_ = lean_nat_sub(v___x_1036_, v___x_1031_);
    leanh::lean_dec(v___x_1036_);
    return v___x_1037_;
}
pub unsafe fn l_Int32_instRxoHasSize___lam__0___boxed(
    mut v_lo_1038_: *mut leanh::LeanObject,
    mut v_hi_1039_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lo_boxed_1040_: u32 = 0;
    let mut v_hi_boxed_1041_: u32 = 0;
    let mut v_res_1042_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_lo_boxed_1040_ = leanh::lean_unbox_uint32(v_lo_1038_);
    leanh::lean_dec(v_lo_1038_);
    v_hi_boxed_1041_ = leanh::lean_unbox_uint32(v_hi_1039_);
    leanh::lean_dec(v_hi_1039_);
    v_res_1042_ = l_Int32_instRxoHasSize___lam__0(v_lo_boxed_1040_, v_hi_boxed_1041_);
    return v_res_1042_;
}
pub unsafe fn _init_l_Int32_instRxiHasSize___lam__0___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_1045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1047_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1045_ = leanh::lean_unsigned_to_nat(31);
    v___x_1046_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Int8_instRxiHasSize___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Int8_instRxiHasSize___lam__0___closed__0_once),
        _init_l_Int8_instRxiHasSize___lam__0___closed__0,
    );
    v___x_1047_ = l_Int_pow(v___x_1046_, v___x_1045_);
    return v___x_1047_;
}
pub unsafe fn l_Int32_instRxiHasSize___lam__0(
    mut v_lo_1048_: u32,
) -> *mut leanh::LeanObject {
    let mut v___x_1049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1052_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1049_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Int32_instRxiHasSize___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Int32_instRxiHasSize___lam__0___closed__0_once),
        _init_l_Int32_instRxiHasSize___lam__0___closed__0,
    );
    v___x_1050_ = lean_int32_to_int(v_lo_1048_);
    v___x_1051_ = lean_int_sub(v___x_1049_, v___x_1050_);
    leanh::lean_dec(v___x_1050_);
    v___x_1052_ = l_Int_toNat(v___x_1051_);
    leanh::lean_dec(v___x_1051_);
    return v___x_1052_;
}
pub unsafe fn l_Int32_instRxiHasSize___lam__0___boxed(
    mut v_lo_1053_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lo_boxed_1054_: u32 = 0;
    let mut v_res_1055_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_lo_boxed_1054_ = leanh::lean_unbox_uint32(v_lo_1053_);
    leanh::lean_dec(v_lo_1053_);
    v_res_1055_ = l_Int32_instRxiHasSize___lam__0(v_lo_boxed_1054_);
    return v_res_1055_;
}
pub unsafe fn _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_minValueSealed___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1058_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1058_ = leanh::lean_cstr_to_nat(b"9223372036854775808\0".as_ptr().cast());
    return v___x_1058_;
}
pub unsafe fn _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_minValueSealed___closed__1()
-> u64 {
    let mut v___x_1059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1060_: u64 = 0;
    v___x_1059_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_minValueSealed___closed__0
        ),
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_minValueSealed___closed__0_once
        ),
        _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_minValueSealed___closed__0,
    );
    v___x_1060_ = lean_int64_of_nat(v___x_1059_);
    return v___x_1060_;
}
pub unsafe fn _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_minValueSealed___closed__2()
-> u64 {
    let mut v___x_1061_: u64 = 0;
    let mut v___x_1062_: u64 = 0;
    v___x_1061_ = leanh::lean_uint64_once(
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_minValueSealed___closed__1
        ),
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_minValueSealed___closed__1_once
        ),
        _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_minValueSealed___closed__1,
    );
    v___x_1062_ = lean_int64_neg(v___x_1061_);
    return v___x_1062_;
}
pub unsafe fn _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_minValueSealed() -> u64 {
    let mut v___x_1063_: u64 = 0;
    v___x_1063_ = leanh::lean_uint64_once(
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_minValueSealed___closed__2
        ),
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_minValueSealed___closed__2_once
        ),
        _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_minValueSealed___closed__2,
    );
    return v___x_1063_;
}
pub unsafe fn _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_maxValueSealed___closed__0()
-> u64 {
    let mut v___x_1064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1065_: u64 = 0;
    v___x_1064_ = leanh::lean_cstr_to_nat(b"9223372036854775807\0".as_ptr().cast());
    v___x_1065_ = lean_int64_of_nat(v___x_1064_);
    return v___x_1065_;
}
pub unsafe fn _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_maxValueSealed() -> u64 {
    let mut v___x_1066_: u64 = 0;
    v___x_1066_ = leanh::lean_uint64_once(
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_maxValueSealed___closed__0
        ),
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_maxValueSealed___closed__0_once
        ),
        _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_maxValueSealed___closed__0,
    );
    return v___x_1066_;
}
pub unsafe fn _init_l_Int64_instUpwardEnumerable___lam__0___closed__0() -> u64 {
    let mut v___x_1067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1068_: u64 = 0;
    v___x_1067_ = leanh::lean_unsigned_to_nat(1);
    v___x_1068_ = lean_int64_of_nat(v___x_1067_);
    return v___x_1068_;
}
pub unsafe fn l_Int64_instUpwardEnumerable___lam__0(
    mut v_i_1069_: u64,
) -> *mut leanh::LeanObject {
    let mut v___x_1070_: u64 = 0;
    let mut v___x_1071_: u64 = 0;
    let mut v___x_1072_: u64 = 0;
    let mut v___x_1073_: u8 = 0;
    v___x_1070_ = leanh::lean_uint64_once(
        core::ptr::addr_of_mut!(l_Int64_instUpwardEnumerable___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Int64_instUpwardEnumerable___lam__0___closed__0_once),
        _init_l_Int64_instUpwardEnumerable___lam__0___closed__0,
    );
    v___x_1071_ = lean_int64_add(v_i_1069_, v___x_1070_);
    v___x_1072_ = leanh::lean_uint64_once(
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_minValueSealed___closed__2
        ),
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_minValueSealed___closed__2_once
        ),
        _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_minValueSealed___closed__2,
    );
    v___x_1073_ = lean_int64_dec_eq(v___x_1071_, v___x_1072_);
    if v___x_1073_ == 0 {
        let mut v___x_1074_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1075_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1074_ = leanh::lean_box_uint64(v___x_1071_);
        v___x_1075_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_1075_, 0, v___x_1074_);
        return v___x_1075_;
    } else {
        let mut v___x_1076_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1076_ = leanh::lean_box(0);
        return v___x_1076_;
    }
}
pub unsafe fn l_Int64_instUpwardEnumerable___lam__0___boxed(
    mut v_i_1077_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_1078_: u64 = 0;
    let mut v_res_1079_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1078_ = leanh::lean_unbox_uint64(v_i_1077_);
    leanh::lean_dec_ref(v_i_1077_);
    v_res_1079_ = l_Int64_instUpwardEnumerable___lam__0(v_i_boxed_1078_);
    return v_res_1079_;
}
pub unsafe fn _init_l_Int64_instUpwardEnumerable___lam__1___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1080_: u64 = 0;
    let mut v___x_1081_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1080_ = leanh::lean_uint64_once(
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_maxValueSealed___closed__0
        ),
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_maxValueSealed___closed__0_once
        ),
        _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_maxValueSealed___closed__0,
    );
    v___x_1081_ = lean_int64_to_int_sint(v___x_1080_);
    return v___x_1081_;
}
pub unsafe fn l_Int64_instUpwardEnumerable___lam__1(
    mut v_n_1082_: *mut leanh::LeanObject,
    mut v_i_1083_: u64,
) -> *mut leanh::LeanObject {
    let mut v___x_1084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1088_: u8 = 0;
    v___x_1084_ = lean_int64_to_int_sint(v_i_1083_);
    v___x_1085_ = lean_nat_to_int(v_n_1082_);
    v___x_1086_ = lean_int_add(v___x_1084_, v___x_1085_);
    leanh::lean_dec(v___x_1085_);
    leanh::lean_dec(v___x_1084_);
    v___x_1087_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Int64_instUpwardEnumerable___lam__1___closed__0),
        core::ptr::addr_of_mut!(l_Int64_instUpwardEnumerable___lam__1___closed__0_once),
        _init_l_Int64_instUpwardEnumerable___lam__1___closed__0,
    );
    v___x_1088_ = lean_int_dec_le(v___x_1086_, v___x_1087_);
    if v___x_1088_ == 0 {
        let mut v___x_1089_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v___x_1086_);
        v___x_1089_ = leanh::lean_box(0);
        return v___x_1089_;
    } else {
        let mut v___x_1090_: u64 = 0;
        let mut v___x_1091_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1092_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1090_ = lean_int64_of_int(v___x_1086_);
        leanh::lean_dec(v___x_1086_);
        v___x_1091_ = leanh::lean_box_uint64(v___x_1090_);
        v___x_1092_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_1092_, 0, v___x_1091_);
        return v___x_1092_;
    }
}
pub unsafe fn l_Int64_instUpwardEnumerable___lam__1___boxed(
    mut v_n_1093_: *mut leanh::LeanObject,
    mut v_i_1094_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_1095_: u64 = 0;
    let mut v_res_1096_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1095_ = leanh::lean_unbox_uint64(v_i_1094_);
    leanh::lean_dec_ref(v_i_1094_);
    v_res_1096_ = l_Int64_instUpwardEnumerable___lam__1(v_n_1093_, v_i_boxed_1095_);
    return v_res_1096_;
}
pub unsafe fn _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_instLeast_x3f___closed__0___boxed__const__1()
-> *mut leanh::LeanObject {
    let mut v___x_1103_: u64 = 0;
    let mut v___x_1104_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1103_ = leanh::lean_uint64_once(
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_minValueSealed___closed__2
        ),
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_minValueSealed___closed__2_once
        ),
        _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_minValueSealed___closed__2,
    );
    v___x_1104_ = leanh::lean_box_uint64(v___x_1103_);
    return v___x_1104_;
}
pub unsafe fn _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_instLeast_x3f___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1106_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1105_ = l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_instLeast_x3f___closed__0___boxed__const__1;
    v___x_1106_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1106_, 0, v___x_1105_);
    return v___x_1106_;
}
pub unsafe fn _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_instLeast_x3f()
-> *mut leanh::LeanObject {
    let mut v___x_1107_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1107_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_instLeast_x3f___closed__0
        ),
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_instLeast_x3f___closed__0_once
        ),
        _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_instLeast_x3f___closed__0,
    );
    return v___x_1107_;
}
pub unsafe fn _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_instHasModelBitVecOfNatNat___closed__1()
-> *mut leanh::LeanObject {
    let mut v___f_1109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1111_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1109_ =
        leanh::lean_alloc_closure(l_UInt64_ofBitVec___boxed as *mut core::ffi::c_void, 1, 0);
    v___f_1110_ = l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_instHasModelBitVecOfNatNat___closed__0;
    v___x_1111_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1111_, 0, v___f_1110_);
    leanh::lean_ctor_set(v___x_1111_, 1, v___f_1109_);
    return v___x_1111_;
}
pub unsafe fn _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_instHasModelBitVecOfNatNat()
-> *mut leanh::LeanObject {
    let mut v___x_1112_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1112_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_instHasModelBitVecOfNatNat___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_instHasModelBitVecOfNatNat___closed__1_once), _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_instHasModelBitVecOfNatNat___closed__1);
    return v___x_1112_;
}
pub unsafe fn l_Int64_instRxcHasSize___lam__0(
    mut v_lo_1113_: u64,
    mut v_hi_1114_: u64,
) -> *mut leanh::LeanObject {
    let mut v___x_1115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1120_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1115_ = lean_int64_to_int_sint(v_hi_1114_);
    v___x_1116_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___lam__0___closed__0), core::ptr::addr_of_mut!(l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___lam__0___closed__0_once), _init_l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___lam__0___closed__0);
    v___x_1117_ = lean_int_add(v___x_1115_, v___x_1116_);
    leanh::lean_dec(v___x_1115_);
    v___x_1118_ = lean_int64_to_int_sint(v_lo_1113_);
    v___x_1119_ = lean_int_sub(v___x_1117_, v___x_1118_);
    leanh::lean_dec(v___x_1118_);
    leanh::lean_dec(v___x_1117_);
    v___x_1120_ = l_Int_toNat(v___x_1119_);
    leanh::lean_dec(v___x_1119_);
    return v___x_1120_;
}
pub unsafe fn l_Int64_instRxcHasSize___lam__0___boxed(
    mut v_lo_1121_: *mut leanh::LeanObject,
    mut v_hi_1122_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lo_boxed_1123_: u64 = 0;
    let mut v_hi_boxed_1124_: u64 = 0;
    let mut v_res_1125_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_lo_boxed_1123_ = leanh::lean_unbox_uint64(v_lo_1121_);
    leanh::lean_dec_ref(v_lo_1121_);
    v_hi_boxed_1124_ = leanh::lean_unbox_uint64(v_hi_1122_);
    leanh::lean_dec_ref(v_hi_1122_);
    v_res_1125_ = l_Int64_instRxcHasSize___lam__0(v_lo_boxed_1123_, v_hi_boxed_1124_);
    return v_res_1125_;
}
pub unsafe fn l_Int64_instRxoHasSize___lam__0(
    mut v_lo_1128_: u64,
    mut v_hi_1129_: u64,
) -> *mut leanh::LeanObject {
    let mut v___x_1130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1137_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1130_ = lean_int64_to_int_sint(v_hi_1129_);
    v___x_1131_ = leanh::lean_unsigned_to_nat(1);
    v___x_1132_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___lam__0___closed__0), core::ptr::addr_of_mut!(l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___lam__0___closed__0_once), _init_l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___lam__0___closed__0);
    v___x_1133_ = lean_int_add(v___x_1130_, v___x_1132_);
    leanh::lean_dec(v___x_1130_);
    v___x_1134_ = lean_int64_to_int_sint(v_lo_1128_);
    v___x_1135_ = lean_int_sub(v___x_1133_, v___x_1134_);
    leanh::lean_dec(v___x_1134_);
    leanh::lean_dec(v___x_1133_);
    v___x_1136_ = l_Int_toNat(v___x_1135_);
    leanh::lean_dec(v___x_1135_);
    v___x_1137_ = lean_nat_sub(v___x_1136_, v___x_1131_);
    leanh::lean_dec(v___x_1136_);
    return v___x_1137_;
}
pub unsafe fn l_Int64_instRxoHasSize___lam__0___boxed(
    mut v_lo_1138_: *mut leanh::LeanObject,
    mut v_hi_1139_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lo_boxed_1140_: u64 = 0;
    let mut v_hi_boxed_1141_: u64 = 0;
    let mut v_res_1142_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_lo_boxed_1140_ = leanh::lean_unbox_uint64(v_lo_1138_);
    leanh::lean_dec_ref(v_lo_1138_);
    v_hi_boxed_1141_ = leanh::lean_unbox_uint64(v_hi_1139_);
    leanh::lean_dec_ref(v_hi_1139_);
    v_res_1142_ = l_Int64_instRxoHasSize___lam__0(v_lo_boxed_1140_, v_hi_boxed_1141_);
    return v_res_1142_;
}
pub unsafe fn _init_l_Int64_instRxiHasSize___lam__0___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_1145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1147_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1145_ = leanh::lean_unsigned_to_nat(63);
    v___x_1146_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Int8_instRxiHasSize___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Int8_instRxiHasSize___lam__0___closed__0_once),
        _init_l_Int8_instRxiHasSize___lam__0___closed__0,
    );
    v___x_1147_ = l_Int_pow(v___x_1146_, v___x_1145_);
    return v___x_1147_;
}
pub unsafe fn l_Int64_instRxiHasSize___lam__0(
    mut v_lo_1148_: u64,
) -> *mut leanh::LeanObject {
    let mut v___x_1149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1152_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1149_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Int64_instRxiHasSize___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Int64_instRxiHasSize___lam__0___closed__0_once),
        _init_l_Int64_instRxiHasSize___lam__0___closed__0,
    );
    v___x_1150_ = lean_int64_to_int_sint(v_lo_1148_);
    v___x_1151_ = lean_int_sub(v___x_1149_, v___x_1150_);
    leanh::lean_dec(v___x_1150_);
    v___x_1152_ = l_Int_toNat(v___x_1151_);
    leanh::lean_dec(v___x_1151_);
    return v___x_1152_;
}
pub unsafe fn l_Int64_instRxiHasSize___lam__0___boxed(
    mut v_lo_1153_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lo_boxed_1154_: u64 = 0;
    let mut v_res_1155_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_lo_boxed_1154_ = leanh::lean_unbox_uint64(v_lo_1153_);
    leanh::lean_dec_ref(v_lo_1153_);
    v_res_1155_ = l_Int64_instRxiHasSize___lam__0(v_lo_boxed_1154_);
    return v_res_1155_;
}
pub unsafe fn _init_l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_minValueSealed___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1160_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1158_ = leanh::lean_unsigned_to_nat(1);
    v___x_1159_ = l_System_Platform_numBits;
    v___x_1160_ = lean_nat_sub(v___x_1159_, v___x_1158_);
    return v___x_1160_;
}
pub unsafe fn _init_l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_minValueSealed___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1163_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1161_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_minValueSealed___closed__0
        ),
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_minValueSealed___closed__0_once
        ),
        _init_l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_minValueSealed___closed__0,
    );
    v___x_1162_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Int8_instRxiHasSize___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Int8_instRxiHasSize___lam__0___closed__0_once),
        _init_l_Int8_instRxiHasSize___lam__0___closed__0,
    );
    v___x_1163_ = l_Int_pow(v___x_1162_, v___x_1161_);
    return v___x_1163_;
}
pub unsafe fn _init_l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_minValueSealed___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_1164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1165_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1164_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_minValueSealed___closed__1
        ),
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_minValueSealed___closed__1_once
        ),
        _init_l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_minValueSealed___closed__1,
    );
    v___x_1165_ = lean_int_neg(v___x_1164_);
    return v___x_1165_;
}
pub unsafe fn _init_l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_minValueSealed___closed__3()
-> usize {
    let mut v___x_1166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1167_: usize = 0;
    v___x_1166_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_minValueSealed___closed__2
        ),
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_minValueSealed___closed__2_once
        ),
        _init_l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_minValueSealed___closed__2,
    );
    v___x_1167_ = lean_isize_of_int(v___x_1166_);
    return v___x_1167_;
}
pub unsafe fn _init_l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_minValueSealed() -> usize
{
    let mut v___x_1168_: usize = 0;
    v___x_1168_ = leanh::lean_usize_once(
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_minValueSealed___closed__3
        ),
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_minValueSealed___closed__3_once
        ),
        _init_l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_minValueSealed___closed__3,
    );
    return v___x_1168_;
}
pub unsafe fn _init_l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_maxValueSealed___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1171_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1169_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___lam__0___closed__0), core::ptr::addr_of_mut!(l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___lam__0___closed__0_once), _init_l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___lam__0___closed__0);
    v___x_1170_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_minValueSealed___closed__1
        ),
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_minValueSealed___closed__1_once
        ),
        _init_l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_minValueSealed___closed__1,
    );
    v___x_1171_ = lean_int_sub(v___x_1170_, v___x_1169_);
    return v___x_1171_;
}
pub unsafe fn _init_l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_maxValueSealed___closed__1()
-> usize {
    let mut v___x_1172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1173_: usize = 0;
    v___x_1172_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_maxValueSealed___closed__0
        ),
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_maxValueSealed___closed__0_once
        ),
        _init_l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_maxValueSealed___closed__0,
    );
    v___x_1173_ = lean_isize_of_int(v___x_1172_);
    return v___x_1173_;
}
pub unsafe fn _init_l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_maxValueSealed() -> usize
{
    let mut v___x_1174_: usize = 0;
    v___x_1174_ = leanh::lean_usize_once(
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_maxValueSealed___closed__1
        ),
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_maxValueSealed___closed__1_once
        ),
        _init_l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_maxValueSealed___closed__1,
    );
    return v___x_1174_;
}
pub unsafe fn _init_l_ISize_instUpwardEnumerable___lam__0___closed__0() -> usize {
    let mut v___x_1175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1176_: usize = 0;
    v___x_1175_ = leanh::lean_unsigned_to_nat(1);
    v___x_1176_ = lean_isize_of_nat(v___x_1175_);
    return v___x_1176_;
}
pub unsafe fn l_ISize_instUpwardEnumerable___lam__0(
    mut v_i_1177_: usize,
) -> *mut leanh::LeanObject {
    let mut v___x_1178_: usize = 0;
    let mut v___x_1179_: usize = 0;
    let mut v___x_1180_: usize = 0;
    let mut v___x_1181_: u8 = 0;
    v___x_1178_ = leanh::lean_usize_once(
        core::ptr::addr_of_mut!(l_ISize_instUpwardEnumerable___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_ISize_instUpwardEnumerable___lam__0___closed__0_once),
        _init_l_ISize_instUpwardEnumerable___lam__0___closed__0,
    );
    v___x_1179_ = lean_isize_add(v_i_1177_, v___x_1178_);
    v___x_1180_ = leanh::lean_usize_once(
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_minValueSealed___closed__3
        ),
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_minValueSealed___closed__3_once
        ),
        _init_l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_minValueSealed___closed__3,
    );
    v___x_1181_ = lean_isize_dec_eq(v___x_1179_, v___x_1180_);
    if v___x_1181_ == 0 {
        let mut v___x_1182_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1183_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1182_ = leanh::lean_box_usize(v___x_1179_);
        v___x_1183_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_1183_, 0, v___x_1182_);
        return v___x_1183_;
    } else {
        let mut v___x_1184_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1184_ = leanh::lean_box(0);
        return v___x_1184_;
    }
}
pub unsafe fn l_ISize_instUpwardEnumerable___lam__0___boxed(
    mut v_i_1185_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_1186_: usize = 0;
    let mut v_res_1187_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1186_ = leanh::lean_unbox_usize(v_i_1185_);
    leanh::lean_dec(v_i_1185_);
    v_res_1187_ = l_ISize_instUpwardEnumerable___lam__0(v_i_boxed_1186_);
    return v_res_1187_;
}
pub unsafe fn _init_l_ISize_instUpwardEnumerable___lam__1___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1188_: usize = 0;
    let mut v___x_1189_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1188_ = leanh::lean_usize_once(
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_maxValueSealed___closed__1
        ),
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_maxValueSealed___closed__1_once
        ),
        _init_l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_maxValueSealed___closed__1,
    );
    v___x_1189_ = lean_isize_to_int(v___x_1188_);
    return v___x_1189_;
}
pub unsafe fn l_ISize_instUpwardEnumerable___lam__1(
    mut v_n_1190_: *mut leanh::LeanObject,
    mut v_i_1191_: usize,
) -> *mut leanh::LeanObject {
    let mut v___x_1192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1196_: u8 = 0;
    v___x_1192_ = lean_isize_to_int(v_i_1191_);
    v___x_1193_ = lean_nat_to_int(v_n_1190_);
    v___x_1194_ = lean_int_add(v___x_1192_, v___x_1193_);
    leanh::lean_dec(v___x_1193_);
    leanh::lean_dec(v___x_1192_);
    v___x_1195_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_ISize_instUpwardEnumerable___lam__1___closed__0),
        core::ptr::addr_of_mut!(l_ISize_instUpwardEnumerable___lam__1___closed__0_once),
        _init_l_ISize_instUpwardEnumerable___lam__1___closed__0,
    );
    v___x_1196_ = lean_int_dec_le(v___x_1194_, v___x_1195_);
    if v___x_1196_ == 0 {
        let mut v___x_1197_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v___x_1194_);
        v___x_1197_ = leanh::lean_box(0);
        return v___x_1197_;
    } else {
        let mut v___x_1198_: usize = 0;
        let mut v___x_1199_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1200_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1198_ = lean_isize_of_int(v___x_1194_);
        leanh::lean_dec(v___x_1194_);
        v___x_1199_ = leanh::lean_box_usize(v___x_1198_);
        v___x_1200_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_1200_, 0, v___x_1199_);
        return v___x_1200_;
    }
}
pub unsafe fn l_ISize_instUpwardEnumerable___lam__1___boxed(
    mut v_n_1201_: *mut leanh::LeanObject,
    mut v_i_1202_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_1203_: usize = 0;
    let mut v_res_1204_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1203_ = leanh::lean_unbox_usize(v_i_1202_);
    leanh::lean_dec(v_i_1202_);
    v_res_1204_ = l_ISize_instUpwardEnumerable___lam__1(v_n_1201_, v_i_boxed_1203_);
    return v_res_1204_;
}
pub unsafe fn _init_l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_instLeast_x3f___closed__0___boxed__const__1()
-> *mut leanh::LeanObject {
    let mut v___x_1211_: usize = 0;
    let mut v___x_1212_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1211_ = leanh::lean_usize_once(
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_minValueSealed___closed__3
        ),
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_minValueSealed___closed__3_once
        ),
        _init_l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_minValueSealed___closed__3,
    );
    v___x_1212_ = leanh::lean_box_usize(v___x_1211_);
    return v___x_1212_;
}
pub unsafe fn _init_l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_instLeast_x3f___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1214_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1213_ = l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_instLeast_x3f___closed__0___boxed__const__1;
    v___x_1214_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1214_, 0, v___x_1213_);
    return v___x_1214_;
}
pub unsafe fn _init_l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_instLeast_x3f()
-> *mut leanh::LeanObject {
    let mut v___x_1215_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1215_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_instLeast_x3f___closed__0
        ),
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_instLeast_x3f___closed__0_once
        ),
        _init_l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_instLeast_x3f___closed__0,
    );
    return v___x_1215_;
}
pub unsafe fn _init_l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_instHasModelBitVecNumBits___closed__1()
-> *mut leanh::LeanObject {
    let mut v___f_1217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1219_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1217_ =
        leanh::lean_alloc_closure(l_USize_ofBitVec___boxed as *mut core::ffi::c_void, 1, 0);
    v___f_1218_ =
        l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_instHasModelBitVecNumBits___closed__0;
    v___x_1219_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1219_, 0, v___f_1218_);
    leanh::lean_ctor_set(v___x_1219_, 1, v___f_1217_);
    return v___x_1219_;
}
pub unsafe fn _init_l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_instHasModelBitVecNumBits()
-> *mut leanh::LeanObject {
    let mut v___x_1220_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1220_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_instHasModelBitVecNumBits___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_instHasModelBitVecNumBits___closed__1_once), _init_l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_instHasModelBitVecNumBits___closed__1);
    return v___x_1220_;
}
pub unsafe fn l_ISize_instRxcHasSize___lam__0(
    mut v_lo_1221_: usize,
    mut v_hi_1222_: usize,
) -> *mut leanh::LeanObject {
    let mut v___x_1223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1228_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1223_ = lean_isize_to_int(v_hi_1222_);
    v___x_1224_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___lam__0___closed__0), core::ptr::addr_of_mut!(l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___lam__0___closed__0_once), _init_l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___lam__0___closed__0);
    v___x_1225_ = lean_int_add(v___x_1223_, v___x_1224_);
    leanh::lean_dec(v___x_1223_);
    v___x_1226_ = lean_isize_to_int(v_lo_1221_);
    v___x_1227_ = lean_int_sub(v___x_1225_, v___x_1226_);
    leanh::lean_dec(v___x_1226_);
    leanh::lean_dec(v___x_1225_);
    v___x_1228_ = l_Int_toNat(v___x_1227_);
    leanh::lean_dec(v___x_1227_);
    return v___x_1228_;
}
pub unsafe fn l_ISize_instRxcHasSize___lam__0___boxed(
    mut v_lo_1229_: *mut leanh::LeanObject,
    mut v_hi_1230_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lo_boxed_1231_: usize = 0;
    let mut v_hi_boxed_1232_: usize = 0;
    let mut v_res_1233_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_lo_boxed_1231_ = leanh::lean_unbox_usize(v_lo_1229_);
    leanh::lean_dec(v_lo_1229_);
    v_hi_boxed_1232_ = leanh::lean_unbox_usize(v_hi_1230_);
    leanh::lean_dec(v_hi_1230_);
    v_res_1233_ = l_ISize_instRxcHasSize___lam__0(v_lo_boxed_1231_, v_hi_boxed_1232_);
    return v_res_1233_;
}
pub unsafe fn l_ISize_instRxoHasSize___lam__0(
    mut v_lo_1236_: usize,
    mut v_hi_1237_: usize,
) -> *mut leanh::LeanObject {
    let mut v___x_1238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1245_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1238_ = lean_isize_to_int(v_hi_1237_);
    v___x_1239_ = leanh::lean_unsigned_to_nat(1);
    v___x_1240_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___lam__0___closed__0), core::ptr::addr_of_mut!(l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___lam__0___closed__0_once), _init_l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___lam__0___closed__0);
    v___x_1241_ = lean_int_add(v___x_1238_, v___x_1240_);
    leanh::lean_dec(v___x_1238_);
    v___x_1242_ = lean_isize_to_int(v_lo_1236_);
    v___x_1243_ = lean_int_sub(v___x_1241_, v___x_1242_);
    leanh::lean_dec(v___x_1242_);
    leanh::lean_dec(v___x_1241_);
    v___x_1244_ = l_Int_toNat(v___x_1243_);
    leanh::lean_dec(v___x_1243_);
    v___x_1245_ = lean_nat_sub(v___x_1244_, v___x_1239_);
    leanh::lean_dec(v___x_1244_);
    return v___x_1245_;
}
pub unsafe fn l_ISize_instRxoHasSize___lam__0___boxed(
    mut v_lo_1246_: *mut leanh::LeanObject,
    mut v_hi_1247_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lo_boxed_1248_: usize = 0;
    let mut v_hi_boxed_1249_: usize = 0;
    let mut v_res_1250_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_lo_boxed_1248_ = leanh::lean_unbox_usize(v_lo_1246_);
    leanh::lean_dec(v_lo_1246_);
    v_hi_boxed_1249_ = leanh::lean_unbox_usize(v_hi_1247_);
    leanh::lean_dec(v_hi_1247_);
    v_res_1250_ = l_ISize_instRxoHasSize___lam__0(v_lo_boxed_1248_, v_hi_boxed_1249_);
    return v_res_1250_;
}
pub unsafe fn l_ISize_instRxiHasSize___lam__0(
    mut v_lo_1253_: usize,
) -> *mut leanh::LeanObject {
    let mut v___x_1254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1257_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1254_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_minValueSealed___closed__1
        ),
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_minValueSealed___closed__1_once
        ),
        _init_l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_minValueSealed___closed__1,
    );
    v___x_1255_ = lean_isize_to_int(v_lo_1253_);
    v___x_1256_ = lean_int_sub(v___x_1254_, v___x_1255_);
    leanh::lean_dec(v___x_1255_);
    v___x_1257_ = l_Int_toNat(v___x_1256_);
    leanh::lean_dec(v___x_1256_);
    return v___x_1257_;
}
pub unsafe fn l_ISize_instRxiHasSize___lam__0___boxed(
    mut v_lo_1258_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lo_boxed_1259_: usize = 0;
    let mut v_res_1260_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_lo_boxed_1259_ = leanh::lean_unbox_usize(v_lo_1258_);
    leanh::lean_dec(v_lo_1258_);
    v_res_1260_ = l_ISize_instRxiHasSize___lam__0(v_lo_boxed_1259_);
    return v_res_1260_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Range_Polymorphic_SInt(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Range_Polymorphic_Instances(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_SInt(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_SInt_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic_Internal_SignedBitVec(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_ByCases(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Int_LemmasAux(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_System_Platform(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_minValueSealed =
        _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_minValueSealed();
    l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_maxValueSealed =
        _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_maxValueSealed();
    l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_instLeast_x3f =
        _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_instLeast_x3f();
    leanh::lean_mark_persistent(
        l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_instLeast_x3f,
    );
    l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_instHasModelBitVecOfNatNat =
        _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_instHasModelBitVecOfNatNat();
    leanh::lean_mark_persistent(
        l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_instHasModelBitVecOfNatNat,
    );
    l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_minValueSealed =
        _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_minValueSealed();
    l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_maxValueSealed =
        _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_maxValueSealed();
    l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_instLeast_x3f =
        _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_instLeast_x3f();
    leanh::lean_mark_persistent(
        l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_instLeast_x3f,
    );
    l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_instHasModelBitVecOfNatNat =
        _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_instHasModelBitVecOfNatNat();
    leanh::lean_mark_persistent(
        l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_instHasModelBitVecOfNatNat,
    );
    l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_minValueSealed =
        _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_minValueSealed();
    l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_maxValueSealed =
        _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_maxValueSealed();
    l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_instLeast_x3f___closed__0___boxed__const__1 = _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_instLeast_x3f___closed__0___boxed__const__1();
    leanh::lean_mark_persistent(l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_instLeast_x3f___closed__0___boxed__const__1);
    l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_instLeast_x3f =
        _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_instLeast_x3f();
    leanh::lean_mark_persistent(
        l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_instLeast_x3f,
    );
    l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_instHasModelBitVecOfNatNat =
        _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_instHasModelBitVecOfNatNat();
    leanh::lean_mark_persistent(
        l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_instHasModelBitVecOfNatNat,
    );
    l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_minValueSealed =
        _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_minValueSealed();
    l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_maxValueSealed =
        _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_maxValueSealed();
    l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_instLeast_x3f___closed__0___boxed__const__1 = _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_instLeast_x3f___closed__0___boxed__const__1();
    leanh::lean_mark_persistent(l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_instLeast_x3f___closed__0___boxed__const__1);
    l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_instLeast_x3f =
        _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_instLeast_x3f();
    leanh::lean_mark_persistent(
        l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_instLeast_x3f,
    );
    l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_instHasModelBitVecOfNatNat =
        _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_instHasModelBitVecOfNatNat();
    leanh::lean_mark_persistent(
        l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_instHasModelBitVecOfNatNat,
    );
    l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_minValueSealed =
        _init_l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_minValueSealed();
    l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_maxValueSealed =
        _init_l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_maxValueSealed();
    l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_instLeast_x3f___closed__0___boxed__const__1 = _init_l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_instLeast_x3f___closed__0___boxed__const__1();
    leanh::lean_mark_persistent(l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_instLeast_x3f___closed__0___boxed__const__1);
    l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_instLeast_x3f =
        _init_l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_instLeast_x3f();
    leanh::lean_mark_persistent(
        l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_instLeast_x3f,
    );
    l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_instHasModelBitVecNumBits =
        _init_l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_instHasModelBitVecNumBits();
    leanh::lean_mark_persistent(
        l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_instHasModelBitVecNumBits,
    );
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Range_Polymorphic_SInt(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Range_Polymorphic_SInt(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Range_Polymorphic_Instances(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_SInt(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_SInt_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Range_Polymorphic_Internal_SignedBitVec(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_ByCases(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Int_LemmasAux(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_System_Platform(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic_SInt(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Range_Polymorphic_SInt(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_Range_Polymorphic_SInt(builtin);
}