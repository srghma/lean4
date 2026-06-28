// Lean compiler output
// Module: Init.Prelude
// Imports:
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_3, lean_apply_4, lean_box, lean_box_uint32, lean_box_uint64,
    lean_box_usize, lean_closure_set, lean_cstr_to_nat, lean_ctor_get, lean_ctor_get_uint8,
    lean_ctor_get_uint64, lean_ctor_set, lean_ctor_set_uint8, lean_ctor_set_uint64, lean_dec,
    lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_n, lean_inc_ref,
    lean_inc_ref_n, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_mark_persistent, lean_obj_once, lean_obj_tag, lean_uint8_once, lean_uint16_once,
    lean_uint32_once, lean_uint64_once, lean_unbox, lean_unbox_uint32, lean_unbox_uint64,
    lean_unbox_usize, lean_unsigned_to_nat, lean_usize_once,
};
pub static mut l_Unit_unit: *mut LeanObject = core::ptr::null_mut();
pub static mut l_instInhabitedSort: *mut LeanObject = core::ptr::null_mut();
pub static mut l_instInhabitedBool_default: u8 = 0;
pub static mut l_instInhabitedBool: u8 = 0;
pub static mut l_instInhabitedNonemptyType: *mut LeanObject = core::ptr::null_mut();
pub static mut l_instInhabitedNat: *mut LeanObject = core::ptr::null_mut();
pub static l_instTransEq___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instTransEq___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instTransEq___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instTransEq___closed__0_value) as *mut LeanObject;
pub static l_instTransEq__1___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instTransEq__1___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instTransEq__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instTransEq__1___closed__0_value) as *mut LeanObject;
pub static l_instAddNat___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Nat_add___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instAddNat___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instAddNat___closed__0_value) as *mut LeanObject;
pub static mut l_instAddNat: *mut LeanObject =
    core::ptr::addr_of!(l_instAddNat___closed__0_value) as *mut LeanObject;
pub static l_instMulNat___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Nat_mul___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instMulNat___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instMulNat___closed__0_value) as *mut LeanObject;
pub static mut l_instMulNat: *mut LeanObject =
    core::ptr::addr_of!(l_instMulNat___closed__0_value) as *mut LeanObject;
pub static l_instNatPowNat___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Nat_pow___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instNatPowNat___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instNatPowNat___closed__0_value) as *mut LeanObject;
pub static mut l_instNatPowNat: *mut LeanObject =
    core::ptr::addr_of!(l_instNatPowNat___closed__0_value) as *mut LeanObject;
pub static mut l_instLENat: *mut LeanObject = core::ptr::null_mut();
pub static mut l_instLTNat: *mut LeanObject = core::ptr::null_mut();
pub static l_instMinNat___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instMinNat___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instMinNat___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instMinNat___closed__0_value) as *mut LeanObject;
pub static mut l_instMinNat: *mut LeanObject =
    core::ptr::addr_of!(l_instMinNat___closed__0_value) as *mut LeanObject;
pub static l_instSubNat___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Nat_sub___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instSubNat___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instSubNat___closed__0_value) as *mut LeanObject;
pub static mut l_instSubNat: *mut LeanObject =
    core::ptr::addr_of!(l_instSubNat___closed__0_value) as *mut LeanObject;
pub static l_Nat_instDiv___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Nat_div___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Nat_instDiv___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Nat_instDiv___closed__0_value) as *mut LeanObject;
pub static mut l_Nat_instDiv: *mut LeanObject =
    core::ptr::addr_of!(l_Nat_instDiv___closed__0_value) as *mut LeanObject;
pub static l_Nat_instMod___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Nat_mod___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Nat_instMod___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Nat_instMod___closed__0_value) as *mut LeanObject;
pub static mut l_Nat_instMod: *mut LeanObject =
    core::ptr::addr_of!(l_Nat_instMod___closed__0_value) as *mut LeanObject;
static mut l_System_Platform_numBits___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_System_Platform_numBits___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static mut l_System_Platform_numBits: *mut LeanObject = core::ptr::null_mut();
pub static mut l_UInt8_size: *mut LeanObject = core::ptr::null_mut();
static mut l_instInhabitedUInt8___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_instInhabitedUInt8___closed__0: u8 = 0;
pub static mut l_instInhabitedUInt8: u8 = 0;
pub static mut l_instLTUInt8: *mut LeanObject = core::ptr::null_mut();
pub static mut l_instLEUInt8: *mut LeanObject = core::ptr::null_mut();
pub static mut l_UInt16_size: *mut LeanObject = core::ptr::null_mut();
static mut l_instInhabitedUInt16___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_instInhabitedUInt16___closed__0: u16 = 0;
pub static mut l_instInhabitedUInt16: u16 = 0;
pub static mut l_UInt32_size: *mut LeanObject = core::ptr::null_mut();
static mut l_instInhabitedUInt32___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_instInhabitedUInt32___closed__0: u32 = 0;
pub static mut l_instInhabitedUInt32: u32 = 0;
pub static mut l_instLTUInt32: *mut LeanObject = core::ptr::null_mut();
pub static mut l_instLEUInt32: *mut LeanObject = core::ptr::null_mut();
pub static l_instMaxUInt32___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instMaxUInt32___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instMaxUInt32___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instMaxUInt32___closed__0_value) as *mut LeanObject;
pub static mut l_instMaxUInt32: *mut LeanObject =
    core::ptr::addr_of!(l_instMaxUInt32___closed__0_value) as *mut LeanObject;
pub static l_instMinUInt32___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instMinUInt32___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instMinUInt32___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instMinUInt32___closed__0_value) as *mut LeanObject;
pub static mut l_instMinUInt32: *mut LeanObject =
    core::ptr::addr_of!(l_instMinUInt32___closed__0_value) as *mut LeanObject;
static mut l_UInt64_size___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_UInt64_size___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static mut l_UInt64_size: *mut LeanObject = core::ptr::null_mut();
static mut l_instInhabitedUInt64___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_instInhabitedUInt64___closed__0: u64 = 0;
pub static mut l_instInhabitedUInt64: u64 = 0;
static mut l_USize_size___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_USize_size___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static mut l_USize_size: *mut LeanObject = core::ptr::null_mut();
static mut l_instInhabitedUSize___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_instInhabitedUSize___closed__0: usize = 0;
pub static mut l_instInhabitedUSize: usize = 0;
static mut l_Char_ofNat___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Char_ofNat___closed__0: u32 = 0;
static mut l_Char_utf8Size___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Char_utf8Size___closed__0: u32 = 0;
static mut l_Char_utf8Size___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Char_utf8Size___closed__1: u32 = 0;
static mut l_Char_utf8Size___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Char_utf8Size___closed__2: u32 = 0;
pub static l_Array_empty___closed__0_value: LeanArrayObject<0> = LeanArrayObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Array_empty___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Array_empty___closed__0_value) as *mut LeanObject;
static mut l_ByteArray_empty___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_ByteArray_empty___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static mut l_ByteArray_empty: *mut LeanObject = core::ptr::null_mut();
pub static mut l_instInhabitedRaw: *mut LeanObject = core::ptr::null_mut();
pub static l_instInhabitedRaw__1___closed__0_value: LeanStringObject<1> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 1,
    m_capacity: 1,
    m_length: 0,
    m_data: [0],
};
static mut l_instInhabitedRaw__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instInhabitedRaw__1___closed__0_value) as *mut LeanObject;
pub static l_instInhabitedRaw__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_instInhabitedRaw__1___closed__0_value) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_instInhabitedRaw__1___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_instInhabitedRaw__1___closed__1_value) as *mut LeanObject;
pub static mut l_instInhabitedRaw__1: *mut LeanObject =
    core::ptr::addr_of!(l_instInhabitedRaw__1___closed__1_value) as *mut LeanObject;
pub static l_instMonadLiftT___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instMonadLiftT___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instMonadLiftT___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instMonadLiftT___closed__0_value) as *mut LeanObject;
pub static l_monadFunctorRefl___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_monadFunctorRefl___lam__0 as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_monadFunctorRefl___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_monadFunctorRefl___closed__0_value) as *mut LeanObject;
pub static l_ReaderT_instMonadLift___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_ReaderT_instMonadLift___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_ReaderT_instMonadLift___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_ReaderT_instMonadLift___closed__0_value) as *mut LeanObject;
pub static l_ReaderT_instMonadFunctor___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_ReaderT_instMonadFunctor___lam__0 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_ReaderT_instMonadFunctor___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_ReaderT_instMonadFunctor___closed__0_value) as *mut LeanObject;
pub static l_instMonadWithReaderOfReaderT___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_instMonadWithReaderOfReaderT___lam__0 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instMonadWithReaderOfReaderT___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instMonadWithReaderOfReaderT___closed__0_value) as *mut LeanObject;
pub static l_EStateM_instMonad___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_EStateM_instMonad___lam__0 as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_EStateM_instMonad___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_EStateM_instMonad___closed__0_value) as *mut LeanObject;
pub static l_EStateM_instMonad___closed__1_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_EStateM_instMonad___lam__1 as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_EStateM_instMonad___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_EStateM_instMonad___closed__1_value) as *mut LeanObject;
pub static l_EStateM_instMonad___closed__2_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_EStateM_instMonad___lam__2 as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_EStateM_instMonad___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_EStateM_instMonad___closed__2_value) as *mut LeanObject;
pub static l_EStateM_instMonad___closed__3_value: LeanClosureObject<2> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_EStateM_map as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 2,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_EStateM_instMonad___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_EStateM_instMonad___closed__3_value) as *mut LeanObject;
pub static l_EStateM_instMonad___closed__4_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_EStateM_instMonad___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_EStateM_instMonad___closed__0_value) as *mut LeanObject,
    ],
};
static mut l_EStateM_instMonad___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_EStateM_instMonad___closed__4_value) as *mut LeanObject;
pub static l_EStateM_instMonad___closed__5_value: LeanClosureObject<2> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_EStateM_pure as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 2,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_EStateM_instMonad___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_EStateM_instMonad___closed__5_value) as *mut LeanObject;
pub static l_EStateM_instMonad___closed__6_value: LeanClosureObject<2> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_EStateM_seqRight as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 2,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_EStateM_instMonad___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_EStateM_instMonad___closed__6_value) as *mut LeanObject;
pub static l_EStateM_instMonad___closed__7_value: LeanCtorObject<5> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_EStateM_instMonad___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_EStateM_instMonad___closed__5_value) as *mut LeanObject,
        core::ptr::addr_of!(l_EStateM_instMonad___closed__1_value) as *mut LeanObject,
        core::ptr::addr_of!(l_EStateM_instMonad___closed__2_value) as *mut LeanObject,
        core::ptr::addr_of!(l_EStateM_instMonad___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_EStateM_instMonad___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_EStateM_instMonad___closed__7_value) as *mut LeanObject;
pub static l_EStateM_instMonad___closed__8_value: LeanClosureObject<2> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_EStateM_bind as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 2,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_EStateM_instMonad___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_EStateM_instMonad___closed__8_value) as *mut LeanObject;
pub static l_EStateM_instMonad___closed__9_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_EStateM_instMonad___closed__7_value) as *mut LeanObject,
        core::ptr::addr_of!(l_EStateM_instMonad___closed__8_value) as *mut LeanObject,
    ],
};
static mut l_EStateM_instMonad___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_EStateM_instMonad___closed__9_value) as *mut LeanObject;
pub static l_EStateM_instMonadStateOf___closed__0_value: LeanClosureObject<2> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_EStateM_get as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 2,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_EStateM_instMonadStateOf___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_EStateM_instMonadStateOf___closed__0_value) as *mut LeanObject;
pub static l_EStateM_instMonadStateOf___closed__1_value: LeanClosureObject<2> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_EStateM_set___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 2,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_EStateM_instMonadStateOf___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_EStateM_instMonadStateOf___closed__1_value) as *mut LeanObject;
pub static l_EStateM_instMonadStateOf___closed__2_value: LeanClosureObject<2> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_EStateM_modifyGet as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 2,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_EStateM_instMonadStateOf___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_EStateM_instMonadStateOf___closed__2_value) as *mut LeanObject;
pub static l_EStateM_instMonadStateOf___closed__3_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_EStateM_instMonadStateOf___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_EStateM_instMonadStateOf___closed__1_value) as *mut LeanObject,
        core::ptr::addr_of!(l_EStateM_instMonadStateOf___closed__2_value) as *mut LeanObject,
    ],
};
static mut l_EStateM_instMonadStateOf___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_EStateM_instMonadStateOf___closed__3_value) as *mut LeanObject;
pub static l_EStateM_instMonadExceptOfOfBacktrackable___redArg___closed__0_value:
    LeanClosureObject<2> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_EStateM_throw as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 2,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_EStateM_instMonadExceptOfOfBacktrackable___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_EStateM_instMonadExceptOfOfBacktrackable___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_EStateM_nonBacktrackable___closed__0_value: LeanClosureObject<1> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_EStateM_dummySave___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 1,
    m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
};
static mut l_EStateM_nonBacktrackable___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_EStateM_nonBacktrackable___closed__0_value) as *mut LeanObject;
pub static l_EStateM_nonBacktrackable___closed__1_value: LeanClosureObject<1> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_EStateM_dummyRestore___boxed as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 1,
    m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
};
static mut l_EStateM_nonBacktrackable___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_EStateM_nonBacktrackable___closed__1_value) as *mut LeanObject;
pub static l_EStateM_nonBacktrackable___closed__2_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_EStateM_nonBacktrackable___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_EStateM_nonBacktrackable___closed__1_value) as *mut LeanObject,
    ],
};
static mut l_EStateM_nonBacktrackable___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_EStateM_nonBacktrackable___closed__2_value) as *mut LeanObject;
pub static l_instHashableString___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_String_hash___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instHashableString___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instHashableString___closed__0_value) as *mut LeanObject;
pub static mut l_instHashableString: *mut LeanObject =
    core::ptr::addr_of!(l_instHashableString___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Name_anonymous___override: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Name_str___override___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Name_str___override___closed__0: u64 = 0;
static mut l_Lean_Name_num___override___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Name_num___override___closed__0: u64 = 0;
pub static mut l_Lean_instInhabitedName: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_instHashableName___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Name_hash___override___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_instHashableName___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instHashableName___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_instHashableName: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instHashableName___closed__0_value) as *mut LeanObject;
pub static l_Lean_Name_instBEq___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Name_beq___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Name_instBEq___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Name_instBEq___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Name_instBEq: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Name_instBEq___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_defaultMaxRecDepth: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_maxRecDepthErrorMessage___closed__0_value: LeanStringObject<158> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 158,
        m_capacity: 158,
        m_length: 157,
        m_data: [
            109, 97, 120, 105, 109, 117, 109, 32, 114, 101, 99, 117, 114, 115, 105, 111, 110, 32,
            100, 101, 112, 116, 104, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99,
            104, 101, 100, 10, 117, 115, 101, 32, 96, 115, 101, 116, 95, 111, 112, 116, 105, 111,
            110, 32, 109, 97, 120, 82, 101, 99, 68, 101, 112, 116, 104, 32, 60, 110, 117, 109, 62,
            96, 32, 116, 111, 32, 105, 110, 99, 114, 101, 97, 115, 101, 32, 108, 105, 109, 105,
            116, 10, 117, 115, 101, 32, 96, 115, 101, 116, 95, 111, 112, 116, 105, 111, 110, 32,
            100, 105, 97, 103, 110, 111, 115, 116, 105, 99, 115, 32, 116, 114, 117, 101, 96, 32,
            116, 111, 32, 103, 101, 116, 32, 100, 105, 97, 103, 110, 111, 115, 116, 105, 99, 32,
            105, 110, 102, 111, 114, 109, 97, 116, 105, 111, 110, 0,
        ],
    };
static mut l_Lean_maxRecDepthErrorMessage___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_maxRecDepthErrorMessage___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_maxRecDepthErrorMessage: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_maxRecDepthErrorMessage___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_instInhabitedSourceInfo: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_instInhabitedSyntax: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_choiceKind___closed__0_value: LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [99, 104, 111, 105, 99, 101, 0],
};
static mut l_Lean_choiceKind___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_choiceKind___closed__0_value) as *mut LeanObject;
pub static l_Lean_choiceKind___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_choiceKind___closed__0_value) as *mut LeanObject,
        11985596712582660667 as *mut LeanObject,
    ],
};
static mut l_Lean_choiceKind___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_choiceKind___closed__1_value) as *mut LeanObject;
pub static mut l_Lean_choiceKind: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_choiceKind___closed__1_value) as *mut LeanObject;
pub static l_Lean_nullKind___closed__0_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [110, 117, 108, 108, 0],
};
static mut l_Lean_nullKind___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_nullKind___closed__0_value) as *mut LeanObject;
pub static l_Lean_nullKind___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_nullKind___closed__0_value) as *mut LeanObject,
        9855511589286918680 as *mut LeanObject,
    ],
};
static mut l_Lean_nullKind___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_nullKind___closed__1_value) as *mut LeanObject;
pub static mut l_Lean_nullKind: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_nullKind___closed__1_value) as *mut LeanObject;
pub static l_Lean_groupKind___closed__0_value: LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [103, 114, 111, 117, 112, 0],
};
static mut l_Lean_groupKind___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_groupKind___closed__0_value) as *mut LeanObject;
pub static l_Lean_groupKind___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_groupKind___closed__0_value) as *mut LeanObject,
        2214559063752339918 as *mut LeanObject,
    ],
};
static mut l_Lean_groupKind___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_groupKind___closed__1_value) as *mut LeanObject;
pub static mut l_Lean_groupKind: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_groupKind___closed__1_value) as *mut LeanObject;
pub static l_Lean_identKind___closed__0_value: LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [105, 100, 101, 110, 116, 0],
};
static mut l_Lean_identKind___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_identKind___closed__0_value) as *mut LeanObject;
pub static l_Lean_identKind___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_identKind___closed__0_value) as *mut LeanObject,
        5117844058249666356 as *mut LeanObject,
    ],
};
static mut l_Lean_identKind___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_identKind___closed__1_value) as *mut LeanObject;
pub static mut l_Lean_identKind: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_identKind___closed__1_value) as *mut LeanObject;
pub static l_Lean_strLitKind___closed__0_value: LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [115, 116, 114, 0],
};
static mut l_Lean_strLitKind___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_strLitKind___closed__0_value) as *mut LeanObject;
pub static l_Lean_strLitKind___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_strLitKind___closed__0_value) as *mut LeanObject,
        9232979286016572671 as *mut LeanObject,
    ],
};
static mut l_Lean_strLitKind___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_strLitKind___closed__1_value) as *mut LeanObject;
pub static mut l_Lean_strLitKind: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_strLitKind___closed__1_value) as *mut LeanObject;
pub static l_Lean_charLitKind___closed__0_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [99, 104, 97, 114, 0],
};
static mut l_Lean_charLitKind___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_charLitKind___closed__0_value) as *mut LeanObject;
pub static l_Lean_charLitKind___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_charLitKind___closed__0_value) as *mut LeanObject,
        16760301032635233067 as *mut LeanObject,
    ],
};
static mut l_Lean_charLitKind___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_charLitKind___closed__1_value) as *mut LeanObject;
pub static mut l_Lean_charLitKind: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_charLitKind___closed__1_value) as *mut LeanObject;
pub static l_Lean_numLitKind___closed__0_value: LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [110, 117, 109, 0],
};
static mut l_Lean_numLitKind___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_numLitKind___closed__0_value) as *mut LeanObject;
pub static l_Lean_numLitKind___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_numLitKind___closed__0_value) as *mut LeanObject,
        6110315075117401315 as *mut LeanObject,
    ],
};
static mut l_Lean_numLitKind___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_numLitKind___closed__1_value) as *mut LeanObject;
pub static mut l_Lean_numLitKind: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_numLitKind___closed__1_value) as *mut LeanObject;
pub static l_Lean_hexnumKind___closed__0_value: LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [104, 101, 120, 110, 117, 109, 0],
};
static mut l_Lean_hexnumKind___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_hexnumKind___closed__0_value) as *mut LeanObject;
pub static l_Lean_hexnumKind___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_hexnumKind___closed__0_value) as *mut LeanObject,
        11510626477845773464 as *mut LeanObject,
    ],
};
static mut l_Lean_hexnumKind___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_hexnumKind___closed__1_value) as *mut LeanObject;
pub static mut l_Lean_hexnumKind: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_hexnumKind___closed__1_value) as *mut LeanObject;
pub static l_Lean_scientificLitKind___closed__0_value: LeanStringObject<11> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [115, 99, 105, 101, 110, 116, 105, 102, 105, 99, 0],
};
static mut l_Lean_scientificLitKind___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_scientificLitKind___closed__0_value) as *mut LeanObject;
pub static l_Lean_scientificLitKind___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_scientificLitKind___closed__0_value) as *mut LeanObject,
        12926801259741997275 as *mut LeanObject,
    ],
};
static mut l_Lean_scientificLitKind___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_scientificLitKind___closed__1_value) as *mut LeanObject;
pub static mut l_Lean_scientificLitKind: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_scientificLitKind___closed__1_value) as *mut LeanObject;
pub static l_Lean_nameLitKind___closed__0_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [110, 97, 109, 101, 0],
};
static mut l_Lean_nameLitKind___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_nameLitKind___closed__0_value) as *mut LeanObject;
pub static l_Lean_nameLitKind___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_nameLitKind___closed__0_value) as *mut LeanObject,
        5949480926448383572 as *mut LeanObject,
    ],
};
static mut l_Lean_nameLitKind___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_nameLitKind___closed__1_value) as *mut LeanObject;
pub static mut l_Lean_nameLitKind: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_nameLitKind___closed__1_value) as *mut LeanObject;
pub static l_Lean_fieldIdxKind___closed__0_value: LeanStringObject<9> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [102, 105, 101, 108, 100, 73, 100, 120, 0],
};
static mut l_Lean_fieldIdxKind___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_fieldIdxKind___closed__0_value) as *mut LeanObject;
pub static l_Lean_fieldIdxKind___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_fieldIdxKind___closed__0_value) as *mut LeanObject,
        11762790821414669811 as *mut LeanObject,
    ],
};
static mut l_Lean_fieldIdxKind___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_fieldIdxKind___closed__1_value) as *mut LeanObject;
pub static mut l_Lean_fieldIdxKind: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_fieldIdxKind___closed__1_value) as *mut LeanObject;
pub static l_Lean_hygieneInfoKind___closed__0_value: LeanStringObject<12> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [104, 121, 103, 105, 101, 110, 101, 73, 110, 102, 111, 0],
};
static mut l_Lean_hygieneInfoKind___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_hygieneInfoKind___closed__0_value) as *mut LeanObject;
pub static l_Lean_hygieneInfoKind___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_hygieneInfoKind___closed__0_value) as *mut LeanObject,
        9871775667037945883 as *mut LeanObject,
    ],
};
static mut l_Lean_hygieneInfoKind___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_hygieneInfoKind___closed__1_value) as *mut LeanObject;
pub static mut l_Lean_hygieneInfoKind: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_hygieneInfoKind___closed__1_value) as *mut LeanObject;
pub static l_Lean_interpolatedStrLitKind___closed__0_value: LeanStringObject<23> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 23,
        m_capacity: 23,
        m_length: 22,
        m_data: [
            105, 110, 116, 101, 114, 112, 111, 108, 97, 116, 101, 100, 83, 116, 114, 76, 105, 116,
            75, 105, 110, 100, 0,
        ],
    };
static mut l_Lean_interpolatedStrLitKind___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_interpolatedStrLitKind___closed__0_value) as *mut LeanObject;
pub static l_Lean_interpolatedStrLitKind___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_interpolatedStrLitKind___closed__0_value) as *mut LeanObject,
        3105859046792672728 as *mut LeanObject,
    ],
};
static mut l_Lean_interpolatedStrLitKind___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_interpolatedStrLitKind___closed__1_value) as *mut LeanObject;
pub static mut l_Lean_interpolatedStrLitKind: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_interpolatedStrLitKind___closed__1_value) as *mut LeanObject;
pub static l_Lean_interpolatedStrKind___closed__0_value: LeanStringObject<20> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        105, 110, 116, 101, 114, 112, 111, 108, 97, 116, 101, 100, 83, 116, 114, 75, 105, 110, 100,
        0,
    ],
};
static mut l_Lean_interpolatedStrKind___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_interpolatedStrKind___closed__0_value) as *mut LeanObject;
pub static l_Lean_interpolatedStrKind___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_interpolatedStrKind___closed__0_value) as *mut LeanObject,
        14298422259736409839 as *mut LeanObject,
    ],
};
static mut l_Lean_interpolatedStrKind___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_interpolatedStrKind___closed__1_value) as *mut LeanObject;
pub static mut l_Lean_interpolatedStrKind: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_interpolatedStrKind___closed__1_value) as *mut LeanObject;
pub static l_Lean_Syntax_getKind___closed__0_value: LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [109, 105, 115, 115, 105, 110, 103, 0],
};
static mut l_Lean_Syntax_getKind___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_getKind___closed__0_value) as *mut LeanObject;
pub static l_Lean_Syntax_getKind___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Syntax_getKind___closed__0_value) as *mut LeanObject,
        15418396913758677644 as *mut LeanObject,
    ],
};
static mut l_Lean_Syntax_getKind___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_getKind___closed__1_value) as *mut LeanObject;
pub static l_Lean_Syntax_getArgs___closed__0_value: LeanArrayObject<0> = LeanArrayObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_Syntax_getArgs___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_getArgs___closed__0_value) as *mut LeanObject;
pub static l_Lean_instInhabitedParserDescr___closed__0_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_instInhabitedRaw__1___closed__0_value) as *mut LeanObject],
};
static mut l_Lean_instInhabitedParserDescr___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedParserDescr___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_instInhabitedParserDescr: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedParserDescr___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_reservedMacroScope: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_firstFrontendMacroScope: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Name_hasMacroScopes___closed__0_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [95, 104, 121, 103, 0],
};
static mut l_Lean_Name_hasMacroScopes___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Name_hasMacroScopes___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Prelude_0__Lean_eraseMacroScopesAux___closed__0_value:
    LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [95, 64, 0],
};
static mut l___private_Init_Prelude_0__Lean_eraseMacroScopesAux___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l___private_Init_Prelude_0__Lean_eraseMacroScopesAux___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_instInhabitedMacroScopesView___closed__0_value: LeanCtorObject<4> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 4
                + 0) as u16,
            other: 4,
            tag: 0,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_instInhabitedMacroScopesView___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedMacroScopesView___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_instInhabitedMacroScopesView: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedMacroScopesView___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Prelude_0__Lean_assembleParts___closed__0_value: LeanStringObject<35> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 35,
        m_capacity: 35,
        m_length: 34,
        m_data: [
            69, 114, 114, 111, 114, 58, 32, 117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32,
            64, 32, 97, 115, 115, 101, 109, 98, 108, 101, 80, 97, 114, 116, 115, 0,
        ],
    };
static mut l___private_Init_Prelude_0__Lean_assembleParts___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l___private_Init_Prelude_0__Lean_assembleParts___closed__0_value)
        as *mut LeanObject;
pub static l___private_Init_Prelude_0__Lean_extractImported___closed__0_value: LeanStringObject<
    37,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 37,
    m_capacity: 37,
    m_length: 36,
    m_data: [
        69, 114, 114, 111, 114, 58, 32, 117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 64,
        32, 101, 120, 116, 114, 97, 99, 116, 73, 109, 112, 111, 114, 116, 101, 100, 0,
    ],
};
static mut l___private_Init_Prelude_0__Lean_extractImported___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l___private_Init_Prelude_0__Lean_extractImported___closed__0_value)
        as *mut LeanObject;
pub static l___private_Init_Prelude_0__Lean_extractMainModule___closed__0_value: LeanStringObject<
    39,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 39,
    m_capacity: 39,
    m_length: 38,
    m_data: [
        69, 114, 114, 111, 114, 58, 32, 117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 64,
        32, 101, 120, 116, 114, 97, 99, 116, 77, 97, 105, 110, 77, 111, 100, 117, 108, 101, 0,
    ],
};
static mut l___private_Init_Prelude_0__Lean_extractMainModule___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l___private_Init_Prelude_0__Lean_extractMainModule___closed__0_value)
        as *mut LeanObject;
pub static l___private_Init_Prelude_0__Lean_extractMacroScopesAux___closed__0_value:
    LeanStringObject<43> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 43,
    m_capacity: 43,
    m_length: 42,
    m_data: [
        69, 114, 114, 111, 114, 58, 32, 117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 64,
        32, 101, 120, 116, 114, 97, 99, 116, 77, 97, 99, 114, 111, 83, 99, 111, 112, 101, 115, 65,
        117, 120, 0,
    ],
};
static mut l___private_Init_Prelude_0__Lean_extractMacroScopesAux___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l___private_Init_Prelude_0__Lean_extractMacroScopesAux___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Name_append___closed__0_value: LeanStringObject<98> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 98,
    m_capacity: 98,
    m_length: 97,
    m_data: [
        69, 114, 114, 111, 114, 58, 32, 105, 110, 118, 97, 108, 105, 100, 32, 96, 78, 97, 109, 101,
        46, 97, 112, 112, 101, 110, 100, 96, 44, 32, 98, 111, 116, 104, 32, 97, 114, 103, 117, 109,
        101, 110, 116, 115, 32, 104, 97, 118, 101, 32, 109, 97, 99, 114, 111, 32, 115, 99, 111,
        112, 101, 115, 44, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 117, 115, 105, 110, 103,
        32, 96, 101, 114, 97, 115, 101, 77, 97, 99, 114, 111, 83, 99, 111, 112, 101, 115, 96, 0,
    ],
};
static mut l_Lean_Name_append___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Name_append___closed__0_value) as *mut LeanObject;
pub static l_Lean_instAppendName___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Name_append as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_instAppendName___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instAppendName___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_instAppendName: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instAppendName___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Macro_MethodsRefPointed: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Macro_instInhabitedState_default___closed__0_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 0,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Macro_instInhabitedState_default___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Macro_instInhabitedState_default___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Macro_instInhabitedState_default: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Macro_instInhabitedState_default___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Macro_instInhabitedState: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Macro_instInhabitedState_default___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Macro_instMonadRefMacroM___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Macro_instMonadRefMacroM___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Macro_instMonadRefMacroM___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Macro_instMonadRefMacroM___closed__0_value) as *mut LeanObject;
pub static l_Lean_Macro_instMonadRefMacroM___closed__1_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Macro_instMonadRefMacroM___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Macro_instMonadRefMacroM___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Macro_instMonadRefMacroM___closed__1_value) as *mut LeanObject;
pub static l_Lean_Macro_instMonadRefMacroM___closed__2_value: LeanClosureObject<3> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 3) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_ReaderT_read___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 3,
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_EStateM_instMonad___closed__9_value) as *mut LeanObject,
        ],
    };
static mut l_Lean_Macro_instMonadRefMacroM___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Macro_instMonadRefMacroM___closed__2_value) as *mut LeanObject;
pub static l_Lean_Macro_instMonadRefMacroM___closed__3_value: LeanClosureObject<7> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 7) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_ReaderT_bind___boxed as *const core::ffi::c_void,
        m_arity: 8,
        m_num_fixed: 7,
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_EStateM_instMonad___closed__9_value) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Macro_instMonadRefMacroM___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Macro_instMonadRefMacroM___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Macro_instMonadRefMacroM___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Macro_instMonadRefMacroM___closed__3_value) as *mut LeanObject;
pub static l_Lean_Macro_instMonadRefMacroM___closed__4_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Macro_instMonadRefMacroM___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Macro_instMonadRefMacroM___closed__1_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Macro_instMonadRefMacroM___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Macro_instMonadRefMacroM___closed__4_value) as *mut LeanObject;
pub static mut l_Lean_Macro_instMonadRefMacroM: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Macro_instMonadRefMacroM___closed__4_value) as *mut LeanObject;
pub static l_Lean_Macro_instMonadQuotationMacroM___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Macro_instMonadQuotationMacroM___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Macro_instMonadQuotationMacroM___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Macro_instMonadQuotationMacroM___closed__0_value) as *mut LeanObject;
pub static l_Lean_Macro_instMonadQuotationMacroM___closed__1_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Macro_instMonadQuotationMacroM___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Macro_instMonadQuotationMacroM___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Macro_instMonadQuotationMacroM___closed__1_value) as *mut LeanObject;
pub static l_Lean_Macro_instMonadQuotationMacroM___closed__2_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Macro_withFreshMacroScope___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Macro_instMonadQuotationMacroM___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Macro_instMonadQuotationMacroM___closed__2_value) as *mut LeanObject;
pub static l_Lean_Macro_instMonadQuotationMacroM___closed__3_value: LeanCtorObject<4> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 4
                + 0) as u16,
            other: 4,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Macro_instMonadRefMacroM___closed__4_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Macro_instMonadQuotationMacroM___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Macro_instMonadQuotationMacroM___closed__1_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Macro_instMonadQuotationMacroM___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Macro_instMonadQuotationMacroM___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Macro_instMonadQuotationMacroM___closed__3_value) as *mut LeanObject;
pub static mut l_Lean_Macro_instMonadQuotationMacroM: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Macro_instMonadQuotationMacroM___closed__3_value) as *mut LeanObject;
pub static l_Lean_Macro_instInhabitedMethods_default___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Macro_instInhabitedMethods_default___lam__0___boxed
            as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Macro_instInhabitedMethods_default___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Macro_instInhabitedMethods_default___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Macro_instInhabitedMethods_default___closed__1_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Macro_instInhabitedMethods_default___lam__1___boxed
            as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Macro_instInhabitedMethods_default___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Macro_instInhabitedMethods_default___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Macro_instInhabitedMethods_default___closed__2_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Macro_instInhabitedMethods_default___lam__2___boxed
            as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Macro_instInhabitedMethods_default___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Macro_instInhabitedMethods_default___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Macro_instInhabitedMethods_default___closed__3_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Macro_instInhabitedMethods_default___lam__3___boxed
            as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Macro_instInhabitedMethods_default___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Macro_instInhabitedMethods_default___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Macro_instInhabitedMethods_default___closed__4_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Macro_instInhabitedMethods_default___lam__4___boxed
            as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Macro_instInhabitedMethods_default___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Macro_instInhabitedMethods_default___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Macro_instInhabitedMethods_default___closed__5_value: LeanCtorObject<5> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 5
                + 0) as u16,
            other: 5,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Macro_instInhabitedMethods_default___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Macro_instInhabitedMethods_default___closed__1_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Macro_instInhabitedMethods_default___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Macro_instInhabitedMethods_default___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Macro_instInhabitedMethods_default___closed__4_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Macro_instInhabitedMethods_default___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Macro_instInhabitedMethods_default___closed__5_value)
        as *mut LeanObject;
pub static mut l_Lean_Macro_instInhabitedMethods_default: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Macro_instInhabitedMethods_default___closed__5_value)
        as *mut LeanObject;
pub static mut l_Lean_Macro_instInhabitedMethods: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Macro_instInhabitedMethods_default___closed__5_value)
        as *mut LeanObject;
pub static mut l_Lean_Macro_instInhabitedMethodsRef: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Macro_instInhabitedMethods_default___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_PrettyPrinter_instMonadQuotationUnexpandM___closed__0_value: LeanClosureObject<
    0,
> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_PrettyPrinter_instMonadQuotationUnexpandM___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_PrettyPrinter_instMonadQuotationUnexpandM___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_PrettyPrinter_instMonadQuotationUnexpandM___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_PrettyPrinter_instMonadQuotationUnexpandM___closed__1_value: LeanClosureObject<
    0,
> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_PrettyPrinter_instMonadQuotationUnexpandM___lam__1___boxed
        as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_PrettyPrinter_instMonadQuotationUnexpandM___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_PrettyPrinter_instMonadQuotationUnexpandM___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_PrettyPrinter_instMonadQuotationUnexpandM___closed__2_value: LeanClosureObject<
    3,
> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 3) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_ReaderT_read___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 3,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_EStateM_instMonad___closed__9_value) as *mut LeanObject,
    ],
};
static mut l_Lean_PrettyPrinter_instMonadQuotationUnexpandM___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_PrettyPrinter_instMonadQuotationUnexpandM___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_PrettyPrinter_instMonadQuotationUnexpandM___closed__3_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_PrettyPrinter_instMonadQuotationUnexpandM___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_PrettyPrinter_instMonadQuotationUnexpandM___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_PrettyPrinter_instMonadQuotationUnexpandM___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_PrettyPrinter_instMonadQuotationUnexpandM___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_PrettyPrinter_instMonadQuotationUnexpandM___closed__4_value: LeanClosureObject<
    5,
> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 5) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_ReaderT_pure___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 5,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_EStateM_instMonad___closed__9_value) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lean_PrettyPrinter_instMonadQuotationUnexpandM___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_PrettyPrinter_instMonadQuotationUnexpandM___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_PrettyPrinter_instMonadQuotationUnexpandM___closed__5_value: LeanStringObject<9> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [95, 102, 97, 107, 101, 77, 111, 100, 0],
    };
static mut l_Lean_PrettyPrinter_instMonadQuotationUnexpandM___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_PrettyPrinter_instMonadQuotationUnexpandM___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_PrettyPrinter_instMonadQuotationUnexpandM___closed__6_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_PrettyPrinter_instMonadQuotationUnexpandM___closed__5_value)
                as *mut LeanObject,
            3838192344338869416 as *mut LeanObject,
        ],
    };
static mut l_Lean_PrettyPrinter_instMonadQuotationUnexpandM___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_PrettyPrinter_instMonadQuotationUnexpandM___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_PrettyPrinter_instMonadQuotationUnexpandM___closed__7_value: LeanClosureObject<
    5,
> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 5) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_ReaderT_pure___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 5,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_EStateM_instMonad___closed__9_value) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_PrettyPrinter_instMonadQuotationUnexpandM___closed__6_value)
            as *mut LeanObject,
    ],
};
static mut l_Lean_PrettyPrinter_instMonadQuotationUnexpandM___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_PrettyPrinter_instMonadQuotationUnexpandM___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_PrettyPrinter_instMonadQuotationUnexpandM___closed__8_value: LeanCtorObject<4> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 4
                + 0) as u16,
            other: 4,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_PrettyPrinter_instMonadQuotationUnexpandM___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_PrettyPrinter_instMonadQuotationUnexpandM___closed__4_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_PrettyPrinter_instMonadQuotationUnexpandM___closed__7_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_PrettyPrinter_instMonadQuotationUnexpandM___closed__1_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_PrettyPrinter_instMonadQuotationUnexpandM___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_PrettyPrinter_instMonadQuotationUnexpandM___closed__8_value)
        as *mut LeanObject;
pub static mut l_Lean_PrettyPrinter_instMonadQuotationUnexpandM: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_PrettyPrinter_instMonadQuotationUnexpandM___closed__8_value)
        as *mut LeanObject;
pub unsafe fn l_Eq_ndrec___redArg(mut v_m_5433_: *mut LeanObject) -> *mut LeanObject {
    lean_inc(v_m_5433_);
    return v_m_5433_;
}
pub unsafe fn l_Eq_ndrec___redArg___boxed(mut v_m_5434_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_5435_: *mut LeanObject = core::ptr::null_mut();
    v_res_5435_ = l_Eq_ndrec___redArg(v_m_5434_);
    lean_dec(v_m_5434_);
    return v_res_5435_;
}
pub unsafe fn l_Eq_ndrec(
    mut v_00_u03b1_5436_: *mut LeanObject,
    mut v_a_5437_: *mut LeanObject,
    mut v_motive_5438_: *mut LeanObject,
    mut v_m_5439_: *mut LeanObject,
    mut v_b_5440_: *mut LeanObject,
    mut v_h_5441_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_m_5439_);
    return v_m_5439_;
}
pub unsafe fn l_Eq_ndrec___boxed(
    mut v_00_u03b1_5442_: *mut LeanObject,
    mut v_a_5443_: *mut LeanObject,
    mut v_motive_5444_: *mut LeanObject,
    mut v_m_5445_: *mut LeanObject,
    mut v_b_5446_: *mut LeanObject,
    mut v_h_5447_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5448_: *mut LeanObject = core::ptr::null_mut();
    v_res_5448_ = l_Eq_ndrec(
        v_00_u03b1_5442_,
        v_a_5443_,
        v_motive_5444_,
        v_m_5445_,
        v_b_5446_,
        v_h_5447_,
    );
    lean_dec(v_b_5446_);
    lean_dec(v_m_5445_);
    lean_dec(v_a_5443_);
    return v_res_5448_;
}
pub unsafe fn l_isScalarObj___boxed(
    mut v_00_u03b1_5451_: *mut LeanObject,
    mut v_x_5452_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5453_: u8 = 0;
    let mut v_r_5454_: *mut LeanObject = core::ptr::null_mut();
    v_res_5453_ = lean_is_scalar(v_x_5452_);
    v_r_5454_ = lean_box((v_res_5453_) as usize);
    return v_r_5454_;
}
pub unsafe fn l_id___redArg(mut v_a_5455_: *mut LeanObject) -> *mut LeanObject {
    lean_inc(v_a_5455_);
    return v_a_5455_;
}
pub unsafe fn l_id___redArg___boxed(mut v_a_5456_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_5457_: *mut LeanObject = core::ptr::null_mut();
    v_res_5457_ = l_id___redArg(v_a_5456_);
    lean_dec(v_a_5456_);
    return v_res_5457_;
}
pub unsafe fn l_id(
    mut v_00_u03b1_5458_: *mut LeanObject,
    mut v_a_5459_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_a_5459_);
    return v_a_5459_;
}
pub unsafe fn l_id___boxed(
    mut v_00_u03b1_5460_: *mut LeanObject,
    mut v_a_5461_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5462_: *mut LeanObject = core::ptr::null_mut();
    v_res_5462_ = l_id(v_00_u03b1_5460_, v_a_5461_);
    lean_dec(v_a_5461_);
    return v_res_5462_;
}
pub unsafe fn l_Function_comp___redArg(
    mut v_f_5463_: *mut LeanObject,
    mut v_g_5464_: *mut LeanObject,
    mut v_x_5465_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5467_: *mut LeanObject = core::ptr::null_mut();
    v___x_5466_ = lean_apply_1(v_g_5464_, v_x_5465_);
    v___x_5467_ = lean_apply_1(v_f_5463_, v___x_5466_);
    return v___x_5467_;
}
pub unsafe fn l_Function_comp(
    mut v_00_u03b1_5468_: *mut LeanObject,
    mut v_00_u03b2_5469_: *mut LeanObject,
    mut v_00_u03b4_5470_: *mut LeanObject,
    mut v_f_5471_: *mut LeanObject,
    mut v_g_5472_: *mut LeanObject,
    mut v_x_5473_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5475_: *mut LeanObject = core::ptr::null_mut();
    v___x_5474_ = lean_apply_1(v_g_5472_, v_x_5473_);
    v___x_5475_ = lean_apply_1(v_f_5471_, v___x_5474_);
    return v___x_5475_;
}
pub unsafe fn l_Function_const___redArg(mut v_a_5476_: *mut LeanObject) -> *mut LeanObject {
    lean_inc(v_a_5476_);
    return v_a_5476_;
}
pub unsafe fn l_Function_const___redArg___boxed(mut v_a_5477_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_5478_: *mut LeanObject = core::ptr::null_mut();
    v_res_5478_ = l_Function_const___redArg(v_a_5477_);
    lean_dec(v_a_5477_);
    return v_res_5478_;
}
pub unsafe fn l_Function_const(
    mut v_00_u03b1_5479_: *mut LeanObject,
    mut v_00_u03b2_5480_: *mut LeanObject,
    mut v_a_5481_: *mut LeanObject,
    mut v_x_5482_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_a_5481_);
    return v_a_5481_;
}
pub unsafe fn l_Function_const___boxed(
    mut v_00_u03b1_5483_: *mut LeanObject,
    mut v_00_u03b2_5484_: *mut LeanObject,
    mut v_a_5485_: *mut LeanObject,
    mut v_x_5486_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5487_: *mut LeanObject = core::ptr::null_mut();
    v_res_5487_ = l_Function_const(v_00_u03b1_5483_, v_00_u03b2_5484_, v_a_5485_, v_x_5486_);
    lean_dec(v_x_5486_);
    lean_dec(v_a_5485_);
    return v_res_5487_;
}
pub unsafe fn l_letFun___redArg(
    mut v_v_5488_: *mut LeanObject,
    mut v_f_5489_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5490_: *mut LeanObject = core::ptr::null_mut();
    v___x_5490_ = lean_apply_1(v_f_5489_, v_v_5488_);
    return v___x_5490_;
}
pub unsafe fn l_letFun(
    mut v_00_u03b1_5491_: *mut LeanObject,
    mut v_00_u03b2_5492_: *mut LeanObject,
    mut v_v_5493_: *mut LeanObject,
    mut v_f_5494_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5495_: *mut LeanObject = core::ptr::null_mut();
    v___x_5495_ = lean_apply_1(v_f_5494_, v_v_5493_);
    return v___x_5495_;
}
pub unsafe fn l_inferInstance___redArg(mut v_i_5496_: *mut LeanObject) -> *mut LeanObject {
    lean_inc(v_i_5496_);
    return v_i_5496_;
}
pub unsafe fn l_inferInstance___redArg___boxed(mut v_i_5497_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_5498_: *mut LeanObject = core::ptr::null_mut();
    v_res_5498_ = l_inferInstance___redArg(v_i_5497_);
    lean_dec(v_i_5497_);
    return v_res_5498_;
}
pub unsafe fn l_inferInstance(
    mut v_00_u03b1_5499_: *mut LeanObject,
    mut v_i_5500_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_i_5500_);
    return v_i_5500_;
}
pub unsafe fn l_inferInstance___boxed(
    mut v_00_u03b1_5501_: *mut LeanObject,
    mut v_i_5502_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5503_: *mut LeanObject = core::ptr::null_mut();
    v_res_5503_ = l_inferInstance(v_00_u03b1_5501_, v_i_5502_);
    lean_dec(v_i_5502_);
    return v_res_5503_;
}
pub unsafe fn l_inferInstanceAs___redArg(mut v_i_5504_: *mut LeanObject) -> *mut LeanObject {
    lean_inc(v_i_5504_);
    return v_i_5504_;
}
pub unsafe fn l_inferInstanceAs___redArg___boxed(
    mut v_i_5505_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5506_: *mut LeanObject = core::ptr::null_mut();
    v_res_5506_ = l_inferInstanceAs___redArg(v_i_5505_);
    lean_dec(v_i_5505_);
    return v_res_5506_;
}
pub unsafe fn l_inferInstanceAs(
    mut v_00_u03b1_5507_: *mut LeanObject,
    mut v_i_5508_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_i_5508_);
    return v_i_5508_;
}
pub unsafe fn l_inferInstanceAs___boxed(
    mut v_00_u03b1_5509_: *mut LeanObject,
    mut v_i_5510_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5511_: *mut LeanObject = core::ptr::null_mut();
    v_res_5511_ = l_inferInstanceAs(v_00_u03b1_5509_, v_i_5510_);
    lean_dec(v_i_5510_);
    return v_res_5511_;
}
pub unsafe fn _init_l_Unit_unit() -> *mut LeanObject {
    let mut v___x_5512_: *mut LeanObject = core::ptr::null_mut();
    v___x_5512_ = lean_box(0);
    return v___x_5512_;
}
pub unsafe fn l_Eq_ndrec__symm___redArg(mut v_m_5513_: *mut LeanObject) -> *mut LeanObject {
    lean_inc(v_m_5513_);
    return v_m_5513_;
}
pub unsafe fn l_Eq_ndrec__symm___redArg___boxed(mut v_m_5514_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_5515_: *mut LeanObject = core::ptr::null_mut();
    v_res_5515_ = l_Eq_ndrec__symm___redArg(v_m_5514_);
    lean_dec(v_m_5514_);
    return v_res_5515_;
}
pub unsafe fn l_Eq_ndrec__symm(
    mut v_00_u03b1_5516_: *mut LeanObject,
    mut v_a_5517_: *mut LeanObject,
    mut v_motive_5518_: *mut LeanObject,
    mut v_m_5519_: *mut LeanObject,
    mut v_b_5520_: *mut LeanObject,
    mut v_h_5521_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_m_5519_);
    return v_m_5519_;
}
pub unsafe fn l_Eq_ndrec__symm___boxed(
    mut v_00_u03b1_5522_: *mut LeanObject,
    mut v_a_5523_: *mut LeanObject,
    mut v_motive_5524_: *mut LeanObject,
    mut v_m_5525_: *mut LeanObject,
    mut v_b_5526_: *mut LeanObject,
    mut v_h_5527_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5528_: *mut LeanObject = core::ptr::null_mut();
    v_res_5528_ = l_Eq_ndrec__symm(
        v_00_u03b1_5522_,
        v_a_5523_,
        v_motive_5524_,
        v_m_5525_,
        v_b_5526_,
        v_h_5527_,
    );
    lean_dec(v_b_5526_);
    lean_dec(v_m_5525_);
    lean_dec(v_a_5523_);
    return v_res_5528_;
}
pub unsafe fn l_namedPattern___redArg(mut v_a_5529_: *mut LeanObject) -> *mut LeanObject {
    lean_inc(v_a_5529_);
    return v_a_5529_;
}
pub unsafe fn l_namedPattern___redArg___boxed(mut v_a_5530_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_5531_: *mut LeanObject = core::ptr::null_mut();
    v_res_5531_ = l_namedPattern___redArg(v_a_5530_);
    lean_dec(v_a_5530_);
    return v_res_5531_;
}
pub unsafe fn l_namedPattern(
    mut v_00_u03b1_5532_: *mut LeanObject,
    mut v_x_5533_: *mut LeanObject,
    mut v_a_5534_: *mut LeanObject,
    mut v_h_5535_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_a_5534_);
    return v_a_5534_;
}
pub unsafe fn l_namedPattern___boxed(
    mut v_00_u03b1_5536_: *mut LeanObject,
    mut v_x_5537_: *mut LeanObject,
    mut v_a_5538_: *mut LeanObject,
    mut v_h_5539_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5540_: *mut LeanObject = core::ptr::null_mut();
    v_res_5540_ = l_namedPattern(v_00_u03b1_5536_, v_x_5537_, v_a_5538_, v_h_5539_);
    lean_dec(v_a_5538_);
    lean_dec(v_x_5537_);
    return v_res_5540_;
}
pub unsafe fn l_sorryAx___boxed(
    mut v_00_u03b1_5543_: *mut LeanObject,
    mut v_synthetic_5544_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_synthetic_boxed_5545_: u8 = 0;
    let mut v_res_5546_: *mut LeanObject = core::ptr::null_mut();
    v_synthetic_boxed_5545_ = (lean_unbox(v_synthetic_5544_) as u8);
    v_res_5546_ = lean_sorry(v_synthetic_boxed_5545_);
    return v_res_5546_;
}
pub unsafe fn _init_l_instInhabitedSort() -> *mut LeanObject {
    let mut v___x_5547_: *mut LeanObject = core::ptr::null_mut();
    v___x_5547_ = lean_box(0);
    return v___x_5547_;
}
pub unsafe fn l_instInhabitedForall___redArg___lam__0(
    mut v_inst_5548_: *mut LeanObject,
    mut v_x_5549_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_inst_5548_);
    return v_inst_5548_;
}
pub unsafe fn l_instInhabitedForall___redArg___lam__0___boxed(
    mut v_inst_5550_: *mut LeanObject,
    mut v_x_5551_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5552_: *mut LeanObject = core::ptr::null_mut();
    v_res_5552_ = l_instInhabitedForall___redArg___lam__0(v_inst_5550_, v_x_5551_);
    lean_dec(v_x_5551_);
    lean_dec(v_inst_5550_);
    return v_res_5552_;
}
pub unsafe fn l_instInhabitedForall___redArg(mut v_inst_5553_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_5554_: *mut LeanObject = core::ptr::null_mut();
    v___f_5554_ = lean_alloc_closure(
        l_instInhabitedForall___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_5554_, 0, v_inst_5553_);
    return v___f_5554_;
}
pub unsafe fn l_instInhabitedForall(
    mut v_00_u03b1_5555_: *mut LeanObject,
    mut v_00_u03b2_5556_: *mut LeanObject,
    mut v_inst_5557_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5558_: *mut LeanObject = core::ptr::null_mut();
    v___f_5558_ = lean_alloc_closure(
        l_instInhabitedForall___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_5558_, 0, v_inst_5557_);
    return v___f_5558_;
}
pub unsafe fn l_Pi_instInhabited___redArg___lam__0(
    mut v_inst_5559_: *mut LeanObject,
    mut v_x_5560_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5561_: *mut LeanObject = core::ptr::null_mut();
    v___x_5561_ = lean_apply_1(v_inst_5559_, v_x_5560_);
    return v___x_5561_;
}
pub unsafe fn l_Pi_instInhabited___redArg(mut v_inst_5562_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_5563_: *mut LeanObject = core::ptr::null_mut();
    v___f_5563_ = lean_alloc_closure(
        l_Pi_instInhabited___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_5563_, 0, v_inst_5562_);
    return v___f_5563_;
}
pub unsafe fn l_Pi_instInhabited(
    mut v_00_u03b1_5564_: *mut LeanObject,
    mut v_00_u03b2_5565_: *mut LeanObject,
    mut v_inst_5566_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5567_: *mut LeanObject = core::ptr::null_mut();
    v___f_5567_ = lean_alloc_closure(
        l_Pi_instInhabited___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_5567_, 0, v_inst_5566_);
    return v___f_5567_;
}
pub unsafe fn _init_l_instInhabitedBool_default() -> u8 {
    let mut v___x_5568_: u8 = 0;
    v___x_5568_ = 0;
    return v___x_5568_;
}
pub unsafe fn _init_l_instInhabitedBool() -> u8 {
    let mut v___x_5569_: u8 = 0;
    v___x_5569_ = 0;
    return v___x_5569_;
}
pub unsafe fn _init_l_instInhabitedNonemptyType() -> *mut LeanObject {
    let mut v___x_5570_: *mut LeanObject = core::ptr::null_mut();
    v___x_5570_ = lean_box(0);
    return v___x_5570_;
}
pub unsafe fn l_instInhabitedULift___redArg(mut v_inst_5571_: *mut LeanObject) -> *mut LeanObject {
    lean_inc(v_inst_5571_);
    return v_inst_5571_;
}
pub unsafe fn l_instInhabitedULift___redArg___boxed(
    mut v_inst_5572_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5573_: *mut LeanObject = core::ptr::null_mut();
    v_res_5573_ = l_instInhabitedULift___redArg(v_inst_5572_);
    lean_dec(v_inst_5572_);
    return v_res_5573_;
}
pub unsafe fn l_instInhabitedULift(
    mut v_00_u03b1_5574_: *mut LeanObject,
    mut v_inst_5575_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_inst_5575_);
    return v_inst_5575_;
}
pub unsafe fn l_instInhabitedULift___boxed(
    mut v_00_u03b1_5576_: *mut LeanObject,
    mut v_inst_5577_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5578_: *mut LeanObject = core::ptr::null_mut();
    v_res_5578_ = l_instInhabitedULift(v_00_u03b1_5576_, v_inst_5577_);
    lean_dec(v_inst_5577_);
    return v_res_5578_;
}
pub unsafe fn l_Decidable_decide___redArg(mut v_h_5579_: u8) -> u8 {
    return v_h_5579_;
}
pub unsafe fn l_Decidable_decide___redArg___boxed(
    mut v_h_5580_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_h_boxed_5581_: u8 = 0;
    let mut v_res_5582_: u8 = 0;
    let mut v_r_5583_: *mut LeanObject = core::ptr::null_mut();
    v_h_boxed_5581_ = (lean_unbox(v_h_5580_) as u8);
    v_res_5582_ = l_Decidable_decide___redArg(v_h_boxed_5581_);
    v_r_5583_ = lean_box((v_res_5582_) as usize);
    return v_r_5583_;
}
pub unsafe fn l_Decidable_decide(mut v_p_5584_: *mut LeanObject, mut v_h_5585_: u8) -> u8 {
    let mut v___x_5586_: u8 = 0;
    v___x_5586_ = l_Decidable_decide___redArg(v_h_5585_);
    return v___x_5586_;
}
pub unsafe fn l_Decidable_decide___boxed(
    mut v_p_5587_: *mut LeanObject,
    mut v_h_5588_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_h_boxed_5589_: u8 = 0;
    let mut v_res_5590_: u8 = 0;
    let mut v_r_5591_: *mut LeanObject = core::ptr::null_mut();
    v_h_boxed_5589_ = (lean_unbox(v_h_5588_) as u8);
    v_res_5590_ = l_Decidable_decide(v_p_5587_, v_h_boxed_5589_);
    v_r_5591_ = lean_box((v_res_5590_) as usize);
    return v_r_5591_;
}
pub unsafe fn l_decEq___redArg(
    mut v_inst_5592_: *mut LeanObject,
    mut v_a_5593_: *mut LeanObject,
    mut v_b_5594_: *mut LeanObject,
) -> u8 {
    let mut v___x_5595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5596_: u8 = 0;
    v___x_5595_ = lean_apply_2(v_inst_5592_, v_a_5593_, v_b_5594_);
    v___x_5596_ = (lean_unbox(v___x_5595_) as u8);
    return v___x_5596_;
}
pub unsafe fn l_decEq___redArg___boxed(
    mut v_inst_5597_: *mut LeanObject,
    mut v_a_5598_: *mut LeanObject,
    mut v_b_5599_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5600_: u8 = 0;
    let mut v_r_5601_: *mut LeanObject = core::ptr::null_mut();
    v_res_5600_ = l_decEq___redArg(v_inst_5597_, v_a_5598_, v_b_5599_);
    v_r_5601_ = lean_box((v_res_5600_) as usize);
    return v_r_5601_;
}
pub unsafe fn l_decEq(
    mut v_00_u03b1_5602_: *mut LeanObject,
    mut v_inst_5603_: *mut LeanObject,
    mut v_a_5604_: *mut LeanObject,
    mut v_b_5605_: *mut LeanObject,
) -> u8 {
    let mut v___x_5606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5607_: u8 = 0;
    v___x_5606_ = lean_apply_2(v_inst_5603_, v_a_5604_, v_b_5605_);
    v___x_5607_ = (lean_unbox(v___x_5606_) as u8);
    return v___x_5607_;
}
pub unsafe fn l_decEq___boxed(
    mut v_00_u03b1_5608_: *mut LeanObject,
    mut v_inst_5609_: *mut LeanObject,
    mut v_a_5610_: *mut LeanObject,
    mut v_b_5611_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5612_: u8 = 0;
    let mut v_r_5613_: *mut LeanObject = core::ptr::null_mut();
    v_res_5612_ = l_decEq(v_00_u03b1_5608_, v_inst_5609_, v_a_5610_, v_b_5611_);
    v_r_5613_ = lean_box((v_res_5612_) as usize);
    return v_r_5613_;
}
pub unsafe fn l_Bool_decEq(mut v_a_5614_: u8, mut v_b_5615_: u8) -> u8 {
    if v_a_5614_ == 0 {
        if v_b_5615_ == 0 {
            let mut v___x_5616_: u8 = 0;
            v___x_5616_ = 1;
            return v___x_5616_;
        } else {
            return v_a_5614_;
        }
    } else {
        return v_b_5615_;
    }
}
pub unsafe fn l_Bool_decEq___boxed(
    mut v_a_5617_: *mut LeanObject,
    mut v_b_5618_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_5619_: u8 = 0;
    let mut v_b_boxed_5620_: u8 = 0;
    let mut v_res_5621_: u8 = 0;
    let mut v_r_5622_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_5619_ = (lean_unbox(v_a_5617_) as u8);
    v_b_boxed_5620_ = (lean_unbox(v_b_5618_) as u8);
    v_res_5621_ = l_Bool_decEq(v_a_boxed_5619_, v_b_boxed_5620_);
    v_r_5622_ = lean_box((v_res_5621_) as usize);
    return v_r_5622_;
}
pub unsafe fn l_instDecidableEqBool(mut v_a_5623_: u8, mut v_b_5624_: u8) -> u8 {
    if v_a_5623_ == 0 {
        if v_b_5624_ == 0 {
            let mut v___x_5625_: u8 = 0;
            v___x_5625_ = 1;
            return v___x_5625_;
        } else {
            return v_a_5623_;
        }
    } else {
        return v_b_5624_;
    }
}
pub unsafe fn l_instDecidableEqBool___boxed(
    mut v_a_5626_: *mut LeanObject,
    mut v_b_5627_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_5628_: u8 = 0;
    let mut v_b_boxed_5629_: u8 = 0;
    let mut v_res_5630_: u8 = 0;
    let mut v_r_5631_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_5628_ = (lean_unbox(v_a_5626_) as u8);
    v_b_boxed_5629_ = (lean_unbox(v_b_5627_) as u8);
    v_res_5630_ = l_instDecidableEqBool(v_a_boxed_5628_, v_b_boxed_5629_);
    v_r_5631_ = lean_box((v_res_5630_) as usize);
    return v_r_5631_;
}
pub unsafe fn l_instBEqOfDecidableEq___redArg___lam__0(
    mut v_inst_5632_: *mut LeanObject,
    mut v_a_5633_: *mut LeanObject,
    mut v_b_5634_: *mut LeanObject,
) -> u8 {
    let mut v___x_5635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5636_: u8 = 0;
    v___x_5635_ = lean_apply_2(v_inst_5632_, v_a_5633_, v_b_5634_);
    v___x_5636_ = (lean_unbox(v___x_5635_) as u8);
    return v___x_5636_;
}
pub unsafe fn l_instBEqOfDecidableEq___redArg___lam__0___boxed(
    mut v_inst_5637_: *mut LeanObject,
    mut v_a_5638_: *mut LeanObject,
    mut v_b_5639_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5640_: u8 = 0;
    let mut v_r_5641_: *mut LeanObject = core::ptr::null_mut();
    v_res_5640_ = l_instBEqOfDecidableEq___redArg___lam__0(v_inst_5637_, v_a_5638_, v_b_5639_);
    v_r_5641_ = lean_box((v_res_5640_) as usize);
    return v_r_5641_;
}
pub unsafe fn l_instBEqOfDecidableEq___redArg(
    mut v_inst_5642_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5643_: *mut LeanObject = core::ptr::null_mut();
    v___f_5643_ = lean_alloc_closure(
        l_instBEqOfDecidableEq___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_5643_, 0, v_inst_5642_);
    return v___f_5643_;
}
pub unsafe fn l_instBEqOfDecidableEq(
    mut v_00_u03b1_5644_: *mut LeanObject,
    mut v_inst_5645_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5646_: *mut LeanObject = core::ptr::null_mut();
    v___f_5646_ = lean_alloc_closure(
        l_instBEqOfDecidableEq___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_5646_, 0, v_inst_5645_);
    return v___f_5646_;
}
pub unsafe fn l_instDecidableNot___redArg(mut v_dp_5647_: u8) -> u8 {
    if v_dp_5647_ == 0 {
        let mut v___x_5648_: u8 = 0;
        v___x_5648_ = 1;
        return v___x_5648_;
    } else {
        let mut v___x_5649_: u8 = 0;
        v___x_5649_ = 0;
        return v___x_5649_;
    }
}
pub unsafe fn l_instDecidableNot___redArg___boxed(
    mut v_dp_5650_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_dp_boxed_5651_: u8 = 0;
    let mut v_res_5652_: u8 = 0;
    let mut v_r_5653_: *mut LeanObject = core::ptr::null_mut();
    v_dp_boxed_5651_ = (lean_unbox(v_dp_5650_) as u8);
    v_res_5652_ = l_instDecidableNot___redArg(v_dp_boxed_5651_);
    v_r_5653_ = lean_box((v_res_5652_) as usize);
    return v_r_5653_;
}
pub unsafe fn l_instDecidableNot(mut v_p_5654_: *mut LeanObject, mut v_dp_5655_: u8) -> u8 {
    if v_dp_5655_ == 0 {
        let mut v___x_5656_: u8 = 0;
        v___x_5656_ = 1;
        return v___x_5656_;
    } else {
        let mut v___x_5657_: u8 = 0;
        v___x_5657_ = 0;
        return v___x_5657_;
    }
}
pub unsafe fn l_instDecidableNot___boxed(
    mut v_p_5658_: *mut LeanObject,
    mut v_dp_5659_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_dp_boxed_5660_: u8 = 0;
    let mut v_res_5661_: u8 = 0;
    let mut v_r_5662_: *mut LeanObject = core::ptr::null_mut();
    v_dp_boxed_5660_ = (lean_unbox(v_dp_5659_) as u8);
    v_res_5661_ = l_instDecidableNot(v_p_5658_, v_dp_boxed_5660_);
    v_r_5662_ = lean_box((v_res_5661_) as usize);
    return v_r_5662_;
}
pub unsafe fn l_Bool_not(mut v_x_5663_: u8) -> u8 {
    if v_x_5663_ == 0 {
        let mut v___x_5664_: u8 = 0;
        v___x_5664_ = 1;
        return v___x_5664_;
    } else {
        let mut v___x_5665_: u8 = 0;
        v___x_5665_ = 0;
        return v___x_5665_;
    }
}
pub unsafe fn l_Bool_not___boxed(mut v_x_5666_: *mut LeanObject) -> *mut LeanObject {
    let mut v_x_18__boxed_5667_: u8 = 0;
    let mut v_res_5668_: u8 = 0;
    let mut v_r_5669_: *mut LeanObject = core::ptr::null_mut();
    v_x_18__boxed_5667_ = (lean_unbox(v_x_5666_) as u8);
    v_res_5668_ = l_Bool_not(v_x_18__boxed_5667_);
    v_r_5669_ = lean_box((v_res_5668_) as usize);
    return v_r_5669_;
}
pub unsafe fn _init_l_instInhabitedNat() -> *mut LeanObject {
    let mut v___x_5670_: *mut LeanObject = core::ptr::null_mut();
    v___x_5670_ = lean_unsigned_to_nat(0);
    return v___x_5670_;
}
pub unsafe fn l_instOfNatNat(mut v_n_5671_: *mut LeanObject) -> *mut LeanObject {
    lean_inc(v_n_5671_);
    return v_n_5671_;
}
pub unsafe fn l_instOfNatNat___boxed(mut v_n_5672_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_5673_: *mut LeanObject = core::ptr::null_mut();
    v_res_5673_ = l_instOfNatNat(v_n_5672_);
    lean_dec(v_n_5672_);
    return v_res_5673_;
}
pub unsafe fn l_maxOfLe___redArg___lam__0(
    mut v_inst_5674_: *mut LeanObject,
    mut v_x_5675_: *mut LeanObject,
    mut v_y_5676_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5678_: u8 = 0;
    lean_inc(v_y_5676_);
    lean_inc(v_x_5675_);
    v___x_5677_ = lean_apply_2(v_inst_5674_, v_x_5675_, v_y_5676_);
    v___x_5678_ = (lean_unbox(v___x_5677_) as u8);
    if v___x_5678_ == 0 {
        lean_dec(v_y_5676_);
        return v_x_5675_;
    } else {
        lean_dec(v_x_5675_);
        return v_y_5676_;
    }
}
pub unsafe fn l_maxOfLe___redArg(mut v_inst_5679_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_5680_: *mut LeanObject = core::ptr::null_mut();
    v___f_5680_ = lean_alloc_closure(l_maxOfLe___redArg___lam__0 as *mut core::ffi::c_void, 3, 1);
    lean_closure_set(v___f_5680_, 0, v_inst_5679_);
    return v___f_5680_;
}
pub unsafe fn l_maxOfLe(
    mut v_00_u03b1_5681_: *mut LeanObject,
    mut v_inst_5682_: *mut LeanObject,
    mut v_inst_5683_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5684_: *mut LeanObject = core::ptr::null_mut();
    v___f_5684_ = lean_alloc_closure(l_maxOfLe___redArg___lam__0 as *mut core::ffi::c_void, 3, 1);
    lean_closure_set(v___f_5684_, 0, v_inst_5683_);
    return v___f_5684_;
}
pub unsafe fn l_minOfLe___redArg___lam__0(
    mut v_inst_5685_: *mut LeanObject,
    mut v_x_5686_: *mut LeanObject,
    mut v_y_5687_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5689_: u8 = 0;
    lean_inc(v_y_5687_);
    lean_inc(v_x_5686_);
    v___x_5688_ = lean_apply_2(v_inst_5685_, v_x_5686_, v_y_5687_);
    v___x_5689_ = (lean_unbox(v___x_5688_) as u8);
    if v___x_5689_ == 0 {
        lean_dec(v_x_5686_);
        return v_y_5687_;
    } else {
        lean_dec(v_y_5687_);
        return v_x_5686_;
    }
}
pub unsafe fn l_minOfLe___redArg(mut v_inst_5690_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_5691_: *mut LeanObject = core::ptr::null_mut();
    v___f_5691_ = lean_alloc_closure(l_minOfLe___redArg___lam__0 as *mut core::ffi::c_void, 3, 1);
    lean_closure_set(v___f_5691_, 0, v_inst_5690_);
    return v___f_5691_;
}
pub unsafe fn l_minOfLe(
    mut v_00_u03b1_5692_: *mut LeanObject,
    mut v_inst_5693_: *mut LeanObject,
    mut v_inst_5694_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5695_: *mut LeanObject = core::ptr::null_mut();
    v___f_5695_ = lean_alloc_closure(l_minOfLe___redArg___lam__0 as *mut core::ffi::c_void, 3, 1);
    lean_closure_set(v___f_5695_, 0, v_inst_5694_);
    return v___f_5695_;
}
pub unsafe fn l_instTransEq___lam__0(
    mut v_a_5696_: *mut LeanObject,
    mut v_b_5697_: *mut LeanObject,
    mut v_c_5698_: *mut LeanObject,
    mut v_heq_5699_: *mut LeanObject,
    mut v_h_x27_5700_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_h_x27_5700_);
    return v_h_x27_5700_;
}
pub unsafe fn l_instTransEq___lam__0___boxed(
    mut v_a_5701_: *mut LeanObject,
    mut v_b_5702_: *mut LeanObject,
    mut v_c_5703_: *mut LeanObject,
    mut v_heq_5704_: *mut LeanObject,
    mut v_h_x27_5705_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5706_: *mut LeanObject = core::ptr::null_mut();
    v_res_5706_ =
        l_instTransEq___lam__0(v_a_5701_, v_b_5702_, v_c_5703_, v_heq_5704_, v_h_x27_5705_);
    lean_dec(v_h_x27_5705_);
    lean_dec(v_c_5703_);
    lean_dec(v_b_5702_);
    lean_dec(v_a_5701_);
    return v_res_5706_;
}
pub unsafe fn l_instTransEq(
    mut v_00_u03b1_5708_: *mut LeanObject,
    mut v_00_u03b3_5709_: *mut LeanObject,
    mut v_r_5710_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5711_: *mut LeanObject = core::ptr::null_mut();
    v___f_5711_ = l_instTransEq___closed__0;
    return v___f_5711_;
}
pub unsafe fn l_instTransEq__1___lam__0(
    mut v_a_5712_: *mut LeanObject,
    mut v_b_5713_: *mut LeanObject,
    mut v_c_5714_: *mut LeanObject,
    mut v_h_x27_5715_: *mut LeanObject,
    mut v_heq_5716_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_h_x27_5715_);
    return v_h_x27_5715_;
}
pub unsafe fn l_instTransEq__1___lam__0___boxed(
    mut v_a_5717_: *mut LeanObject,
    mut v_b_5718_: *mut LeanObject,
    mut v_c_5719_: *mut LeanObject,
    mut v_h_x27_5720_: *mut LeanObject,
    mut v_heq_5721_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5722_: *mut LeanObject = core::ptr::null_mut();
    v_res_5722_ =
        l_instTransEq__1___lam__0(v_a_5717_, v_b_5718_, v_c_5719_, v_h_x27_5720_, v_heq_5721_);
    lean_dec(v_h_x27_5720_);
    lean_dec(v_c_5719_);
    lean_dec(v_b_5718_);
    lean_dec(v_a_5717_);
    return v_res_5722_;
}
pub unsafe fn l_instTransEq__1(
    mut v_00_u03b1_5724_: *mut LeanObject,
    mut v_00_u03b2_5725_: *mut LeanObject,
    mut v_r_5726_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5727_: *mut LeanObject = core::ptr::null_mut();
    v___f_5727_ = l_instTransEq__1___closed__0;
    return v___f_5727_;
}
pub unsafe fn l_instHAdd___redArg___lam__0(
    mut v_inst_5728_: *mut LeanObject,
    mut v_a_5729_: *mut LeanObject,
    mut v_b_5730_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5731_: *mut LeanObject = core::ptr::null_mut();
    v___x_5731_ = lean_apply_2(v_inst_5728_, v_a_5729_, v_b_5730_);
    return v___x_5731_;
}
pub unsafe fn l_instHAdd___redArg(mut v_inst_5732_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_5733_: *mut LeanObject = core::ptr::null_mut();
    v___f_5733_ = lean_alloc_closure(l_instHAdd___redArg___lam__0 as *mut core::ffi::c_void, 3, 1);
    lean_closure_set(v___f_5733_, 0, v_inst_5732_);
    return v___f_5733_;
}
pub unsafe fn l_instHAdd(
    mut v_00_u03b1_5734_: *mut LeanObject,
    mut v_inst_5735_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5736_: *mut LeanObject = core::ptr::null_mut();
    v___f_5736_ = lean_alloc_closure(l_instHAdd___redArg___lam__0 as *mut core::ffi::c_void, 3, 1);
    lean_closure_set(v___f_5736_, 0, v_inst_5735_);
    return v___f_5736_;
}
pub unsafe fn l_instHSub___redArg(mut v_inst_5737_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_5738_: *mut LeanObject = core::ptr::null_mut();
    v___f_5738_ = lean_alloc_closure(l_instHAdd___redArg___lam__0 as *mut core::ffi::c_void, 3, 1);
    lean_closure_set(v___f_5738_, 0, v_inst_5737_);
    return v___f_5738_;
}
pub unsafe fn l_instHSub(
    mut v_00_u03b1_5739_: *mut LeanObject,
    mut v_inst_5740_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5741_: *mut LeanObject = core::ptr::null_mut();
    v___f_5741_ = lean_alloc_closure(l_instHAdd___redArg___lam__0 as *mut core::ffi::c_void, 3, 1);
    lean_closure_set(v___f_5741_, 0, v_inst_5740_);
    return v___f_5741_;
}
pub unsafe fn l_instHMul___redArg(mut v_inst_5742_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_5743_: *mut LeanObject = core::ptr::null_mut();
    v___f_5743_ = lean_alloc_closure(l_instHAdd___redArg___lam__0 as *mut core::ffi::c_void, 3, 1);
    lean_closure_set(v___f_5743_, 0, v_inst_5742_);
    return v___f_5743_;
}
pub unsafe fn l_instHMul(
    mut v_00_u03b1_5744_: *mut LeanObject,
    mut v_inst_5745_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5746_: *mut LeanObject = core::ptr::null_mut();
    v___f_5746_ = lean_alloc_closure(l_instHAdd___redArg___lam__0 as *mut core::ffi::c_void, 3, 1);
    lean_closure_set(v___f_5746_, 0, v_inst_5745_);
    return v___f_5746_;
}
pub unsafe fn l_instHDiv___redArg(mut v_inst_5747_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_5748_: *mut LeanObject = core::ptr::null_mut();
    v___f_5748_ = lean_alloc_closure(l_instHAdd___redArg___lam__0 as *mut core::ffi::c_void, 3, 1);
    lean_closure_set(v___f_5748_, 0, v_inst_5747_);
    return v___f_5748_;
}
pub unsafe fn l_instHDiv(
    mut v_00_u03b1_5749_: *mut LeanObject,
    mut v_inst_5750_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5751_: *mut LeanObject = core::ptr::null_mut();
    v___f_5751_ = lean_alloc_closure(l_instHAdd___redArg___lam__0 as *mut core::ffi::c_void, 3, 1);
    lean_closure_set(v___f_5751_, 0, v_inst_5750_);
    return v___f_5751_;
}
pub unsafe fn l_instHMod___redArg(mut v_inst_5752_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_5753_: *mut LeanObject = core::ptr::null_mut();
    v___f_5753_ = lean_alloc_closure(l_instHAdd___redArg___lam__0 as *mut core::ffi::c_void, 3, 1);
    lean_closure_set(v___f_5753_, 0, v_inst_5752_);
    return v___f_5753_;
}
pub unsafe fn l_instHMod(
    mut v_00_u03b1_5754_: *mut LeanObject,
    mut v_inst_5755_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5756_: *mut LeanObject = core::ptr::null_mut();
    v___f_5756_ = lean_alloc_closure(l_instHAdd___redArg___lam__0 as *mut core::ffi::c_void, 3, 1);
    lean_closure_set(v___f_5756_, 0, v_inst_5755_);
    return v___f_5756_;
}
pub unsafe fn l_instHPow___redArg(mut v_inst_5757_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_5758_: *mut LeanObject = core::ptr::null_mut();
    v___f_5758_ = lean_alloc_closure(l_instHAdd___redArg___lam__0 as *mut core::ffi::c_void, 3, 1);
    lean_closure_set(v___f_5758_, 0, v_inst_5757_);
    return v___f_5758_;
}
pub unsafe fn l_instHPow(
    mut v_00_u03b1_5759_: *mut LeanObject,
    mut v_00_u03b2_5760_: *mut LeanObject,
    mut v_inst_5761_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5762_: *mut LeanObject = core::ptr::null_mut();
    v___f_5762_ = lean_alloc_closure(l_instHAdd___redArg___lam__0 as *mut core::ffi::c_void, 3, 1);
    lean_closure_set(v___f_5762_, 0, v_inst_5761_);
    return v___f_5762_;
}
pub unsafe fn l_instPowNat___redArg___lam__0(
    mut v_inst_5763_: *mut LeanObject,
    mut v_a_5764_: *mut LeanObject,
    mut v_n_5765_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5766_: *mut LeanObject = core::ptr::null_mut();
    v___x_5766_ = lean_apply_2(v_inst_5763_, v_a_5764_, v_n_5765_);
    return v___x_5766_;
}
pub unsafe fn l_instPowNat___redArg(mut v_inst_5767_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_5768_: *mut LeanObject = core::ptr::null_mut();
    v___f_5768_ = lean_alloc_closure(
        l_instPowNat___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_5768_, 0, v_inst_5767_);
    return v___f_5768_;
}
pub unsafe fn l_instPowNat(
    mut v_00_u03b1_5769_: *mut LeanObject,
    mut v_inst_5770_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5771_: *mut LeanObject = core::ptr::null_mut();
    v___f_5771_ = lean_alloc_closure(
        l_instPowNat___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_5771_, 0, v_inst_5770_);
    return v___f_5771_;
}
pub unsafe fn l_instPowOfHomogeneousPow___redArg(
    mut v_inst_5772_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5773_: *mut LeanObject = core::ptr::null_mut();
    v___f_5773_ = lean_alloc_closure(l_instHAdd___redArg___lam__0 as *mut core::ffi::c_void, 3, 1);
    lean_closure_set(v___f_5773_, 0, v_inst_5772_);
    return v___f_5773_;
}
pub unsafe fn l_instPowOfHomogeneousPow(
    mut v_00_u03b1_5774_: *mut LeanObject,
    mut v_inst_5775_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5776_: *mut LeanObject = core::ptr::null_mut();
    v___f_5776_ = lean_alloc_closure(l_instHAdd___redArg___lam__0 as *mut core::ffi::c_void, 3, 1);
    lean_closure_set(v___f_5776_, 0, v_inst_5775_);
    return v___f_5776_;
}
pub unsafe fn l_instHSMul___redArg(mut v_inst_5777_: *mut LeanObject) -> *mut LeanObject {
    lean_inc(v_inst_5777_);
    return v_inst_5777_;
}
pub unsafe fn l_instHSMul___redArg___boxed(mut v_inst_5778_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_5779_: *mut LeanObject = core::ptr::null_mut();
    v_res_5779_ = l_instHSMul___redArg(v_inst_5778_);
    lean_dec(v_inst_5778_);
    return v_res_5779_;
}
pub unsafe fn l_instHSMul(
    mut v_00_u03b1_5780_: *mut LeanObject,
    mut v_00_u03b2_5781_: *mut LeanObject,
    mut v_inst_5782_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_inst_5782_);
    return v_inst_5782_;
}
pub unsafe fn l_instHSMul___boxed(
    mut v_00_u03b1_5783_: *mut LeanObject,
    mut v_00_u03b2_5784_: *mut LeanObject,
    mut v_inst_5785_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5786_: *mut LeanObject = core::ptr::null_mut();
    v_res_5786_ = l_instHSMul(v_00_u03b1_5783_, v_00_u03b2_5784_, v_inst_5785_);
    lean_dec(v_inst_5785_);
    return v_res_5786_;
}
pub unsafe fn l_instSMulOfMul___redArg___lam__0(
    mut v_inst_5787_: *mut LeanObject,
    mut v_x_5788_: *mut LeanObject,
    mut v_y_5789_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5790_: *mut LeanObject = core::ptr::null_mut();
    v___x_5790_ = lean_apply_2(v_inst_5787_, v_x_5788_, v_y_5789_);
    return v___x_5790_;
}
pub unsafe fn l_instSMulOfMul___redArg(mut v_inst_5791_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_5792_: *mut LeanObject = core::ptr::null_mut();
    v___f_5792_ = lean_alloc_closure(
        l_instSMulOfMul___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_5792_, 0, v_inst_5791_);
    return v___f_5792_;
}
pub unsafe fn l_instSMulOfMul(
    mut v_00_u03b1_5793_: *mut LeanObject,
    mut v_inst_5794_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5795_: *mut LeanObject = core::ptr::null_mut();
    v___f_5795_ = lean_alloc_closure(
        l_instSMulOfMul___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_5795_, 0, v_inst_5794_);
    return v___f_5795_;
}
pub unsafe fn l_instHAppendOfAppend___redArg(mut v_inst_5796_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_5797_: *mut LeanObject = core::ptr::null_mut();
    v___f_5797_ = lean_alloc_closure(l_instHAdd___redArg___lam__0 as *mut core::ffi::c_void, 3, 1);
    lean_closure_set(v___f_5797_, 0, v_inst_5796_);
    return v___f_5797_;
}
pub unsafe fn l_instHAppendOfAppend(
    mut v_00_u03b1_5798_: *mut LeanObject,
    mut v_inst_5799_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5800_: *mut LeanObject = core::ptr::null_mut();
    v___f_5800_ = lean_alloc_closure(l_instHAdd___redArg___lam__0 as *mut core::ffi::c_void, 3, 1);
    lean_closure_set(v___f_5800_, 0, v_inst_5799_);
    return v___f_5800_;
}
pub unsafe fn l_instHOrElseOfOrElse___redArg___lam__0(
    mut v_inst_5801_: *mut LeanObject,
    mut v_a_5802_: *mut LeanObject,
    mut v_b_5803_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5804_: *mut LeanObject = core::ptr::null_mut();
    v___x_5804_ = lean_apply_2(v_inst_5801_, v_a_5802_, v_b_5803_);
    return v___x_5804_;
}
pub unsafe fn l_instHOrElseOfOrElse___redArg(mut v_inst_5805_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_5806_: *mut LeanObject = core::ptr::null_mut();
    v___f_5806_ = lean_alloc_closure(
        l_instHOrElseOfOrElse___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_5806_, 0, v_inst_5805_);
    return v___f_5806_;
}
pub unsafe fn l_instHOrElseOfOrElse(
    mut v_00_u03b1_5807_: *mut LeanObject,
    mut v_inst_5808_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5809_: *mut LeanObject = core::ptr::null_mut();
    v___f_5809_ = lean_alloc_closure(
        l_instHOrElseOfOrElse___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_5809_, 0, v_inst_5808_);
    return v___f_5809_;
}
pub unsafe fn l_instHAndThenOfAndThen___redArg(
    mut v_inst_5810_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5811_: *mut LeanObject = core::ptr::null_mut();
    v___f_5811_ = lean_alloc_closure(
        l_instHOrElseOfOrElse___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_5811_, 0, v_inst_5810_);
    return v___f_5811_;
}
pub unsafe fn l_instHAndThenOfAndThen(
    mut v_00_u03b1_5812_: *mut LeanObject,
    mut v_inst_5813_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5814_: *mut LeanObject = core::ptr::null_mut();
    v___f_5814_ = lean_alloc_closure(
        l_instHOrElseOfOrElse___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_5814_, 0, v_inst_5813_);
    return v___f_5814_;
}
pub unsafe fn l_instHAndOfAndOp___redArg(mut v_inst_5815_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_5816_: *mut LeanObject = core::ptr::null_mut();
    v___f_5816_ = lean_alloc_closure(l_instHAdd___redArg___lam__0 as *mut core::ffi::c_void, 3, 1);
    lean_closure_set(v___f_5816_, 0, v_inst_5815_);
    return v___f_5816_;
}
pub unsafe fn l_instHAndOfAndOp(
    mut v_00_u03b1_5817_: *mut LeanObject,
    mut v_inst_5818_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5819_: *mut LeanObject = core::ptr::null_mut();
    v___f_5819_ = lean_alloc_closure(l_instHAdd___redArg___lam__0 as *mut core::ffi::c_void, 3, 1);
    lean_closure_set(v___f_5819_, 0, v_inst_5818_);
    return v___f_5819_;
}
pub unsafe fn l_instHXorOfXorOp___redArg(mut v_inst_5820_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_5821_: *mut LeanObject = core::ptr::null_mut();
    v___f_5821_ = lean_alloc_closure(l_instHAdd___redArg___lam__0 as *mut core::ffi::c_void, 3, 1);
    lean_closure_set(v___f_5821_, 0, v_inst_5820_);
    return v___f_5821_;
}
pub unsafe fn l_instHXorOfXorOp(
    mut v_00_u03b1_5822_: *mut LeanObject,
    mut v_inst_5823_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5824_: *mut LeanObject = core::ptr::null_mut();
    v___f_5824_ = lean_alloc_closure(l_instHAdd___redArg___lam__0 as *mut core::ffi::c_void, 3, 1);
    lean_closure_set(v___f_5824_, 0, v_inst_5823_);
    return v___f_5824_;
}
pub unsafe fn l_instHOrOfOrOp___redArg(mut v_inst_5825_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_5826_: *mut LeanObject = core::ptr::null_mut();
    v___f_5826_ = lean_alloc_closure(l_instHAdd___redArg___lam__0 as *mut core::ffi::c_void, 3, 1);
    lean_closure_set(v___f_5826_, 0, v_inst_5825_);
    return v___f_5826_;
}
pub unsafe fn l_instHOrOfOrOp(
    mut v_00_u03b1_5827_: *mut LeanObject,
    mut v_inst_5828_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5829_: *mut LeanObject = core::ptr::null_mut();
    v___f_5829_ = lean_alloc_closure(l_instHAdd___redArg___lam__0 as *mut core::ffi::c_void, 3, 1);
    lean_closure_set(v___f_5829_, 0, v_inst_5828_);
    return v___f_5829_;
}
pub unsafe fn l_instHShiftLeftOfShiftLeft___redArg(
    mut v_inst_5830_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5831_: *mut LeanObject = core::ptr::null_mut();
    v___f_5831_ = lean_alloc_closure(l_instHAdd___redArg___lam__0 as *mut core::ffi::c_void, 3, 1);
    lean_closure_set(v___f_5831_, 0, v_inst_5830_);
    return v___f_5831_;
}
pub unsafe fn l_instHShiftLeftOfShiftLeft(
    mut v_00_u03b1_5832_: *mut LeanObject,
    mut v_inst_5833_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5834_: *mut LeanObject = core::ptr::null_mut();
    v___f_5834_ = lean_alloc_closure(l_instHAdd___redArg___lam__0 as *mut core::ffi::c_void, 3, 1);
    lean_closure_set(v___f_5834_, 0, v_inst_5833_);
    return v___f_5834_;
}
pub unsafe fn l_instHShiftRightOfShiftRight___redArg(
    mut v_inst_5835_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5836_: *mut LeanObject = core::ptr::null_mut();
    v___f_5836_ = lean_alloc_closure(l_instHAdd___redArg___lam__0 as *mut core::ffi::c_void, 3, 1);
    lean_closure_set(v___f_5836_, 0, v_inst_5835_);
    return v___f_5836_;
}
pub unsafe fn l_instHShiftRightOfShiftRight(
    mut v_00_u03b1_5837_: *mut LeanObject,
    mut v_inst_5838_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5839_: *mut LeanObject = core::ptr::null_mut();
    v___f_5839_ = lean_alloc_closure(l_instHAdd___redArg___lam__0 as *mut core::ffi::c_void, 3, 1);
    lean_closure_set(v___f_5839_, 0, v_inst_5838_);
    return v___f_5839_;
}
pub unsafe fn l_Nat_add___boxed(
    mut v_a_00___x40___internal___hyg_5842_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_5843_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5844_: *mut LeanObject = core::ptr::null_mut();
    v_res_5844_ = lean_nat_add(
        v_a_00___x40___internal___hyg_5842_,
        v_a_00___x40___internal___hyg_5843_,
    );
    lean_dec(v_a_00___x40___internal___hyg_5843_);
    lean_dec(v_a_00___x40___internal___hyg_5842_);
    return v_res_5844_;
}
pub unsafe fn l_Nat_mul___boxed(
    mut v_a_00___x40___internal___hyg_5849_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_5850_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5851_: *mut LeanObject = core::ptr::null_mut();
    v_res_5851_ = lean_nat_mul(
        v_a_00___x40___internal___hyg_5849_,
        v_a_00___x40___internal___hyg_5850_,
    );
    lean_dec(v_a_00___x40___internal___hyg_5850_);
    lean_dec(v_a_00___x40___internal___hyg_5849_);
    return v_res_5851_;
}
pub unsafe fn l_Nat_pow___boxed(
    mut v_m_5856_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_5857_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5858_: *mut LeanObject = core::ptr::null_mut();
    v_res_5858_ = lean_nat_pow(v_m_5856_, v_a_00___x40___internal___hyg_5857_);
    lean_dec(v_a_00___x40___internal___hyg_5857_);
    lean_dec(v_m_5856_);
    return v_res_5858_;
}
pub unsafe fn l_Nat_beq___boxed(
    mut v_a_00___x40___internal___hyg_5863_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_5864_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5865_: u8 = 0;
    let mut v_r_5866_: *mut LeanObject = core::ptr::null_mut();
    v_res_5865_ = lean_nat_dec_eq(
        v_a_00___x40___internal___hyg_5863_,
        v_a_00___x40___internal___hyg_5864_,
    );
    lean_dec(v_a_00___x40___internal___hyg_5864_);
    lean_dec(v_a_00___x40___internal___hyg_5863_);
    v_r_5866_ = lean_box((v_res_5865_) as usize);
    return v_r_5866_;
}
pub unsafe fn l_Nat_decEq___boxed(
    mut v_n_5869_: *mut LeanObject,
    mut v_m_5870_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5871_: u8 = 0;
    let mut v_r_5872_: *mut LeanObject = core::ptr::null_mut();
    v_res_5871_ = lean_nat_dec_eq(v_n_5869_, v_m_5870_);
    lean_dec(v_m_5870_);
    lean_dec(v_n_5869_);
    v_r_5872_ = lean_box((v_res_5871_) as usize);
    return v_r_5872_;
}
pub unsafe fn l_instDecidableEqNat(
    mut v_n_5873_: *mut LeanObject,
    mut v_m_5874_: *mut LeanObject,
) -> u8 {
    let mut v___x_5875_: u8 = 0;
    v___x_5875_ = lean_nat_dec_eq(v_n_5873_, v_m_5874_);
    return v___x_5875_;
}
pub unsafe fn l_instDecidableEqNat___boxed(
    mut v_n_5876_: *mut LeanObject,
    mut v_m_5877_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5878_: u8 = 0;
    let mut v_r_5879_: *mut LeanObject = core::ptr::null_mut();
    v_res_5878_ = l_instDecidableEqNat(v_n_5876_, v_m_5877_);
    lean_dec(v_m_5877_);
    lean_dec(v_n_5876_);
    v_r_5879_ = lean_box((v_res_5878_) as usize);
    return v_r_5879_;
}
pub unsafe fn l_Nat_ble___boxed(
    mut v_a_00___x40___internal___hyg_5882_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_5883_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5884_: u8 = 0;
    let mut v_r_5885_: *mut LeanObject = core::ptr::null_mut();
    v_res_5884_ = lean_nat_dec_le(
        v_a_00___x40___internal___hyg_5882_,
        v_a_00___x40___internal___hyg_5883_,
    );
    lean_dec(v_a_00___x40___internal___hyg_5883_);
    lean_dec(v_a_00___x40___internal___hyg_5882_);
    v_r_5885_ = lean_box((v_res_5884_) as usize);
    return v_r_5885_;
}
pub unsafe fn l_Bool_ctorIdx(mut v_x_5886_: u8) -> *mut LeanObject {
    if v_x_5886_ == 0 {
        let mut v___x_5887_: *mut LeanObject = core::ptr::null_mut();
        v___x_5887_ = lean_unsigned_to_nat(0);
        return v___x_5887_;
    } else {
        let mut v___x_5888_: *mut LeanObject = core::ptr::null_mut();
        v___x_5888_ = lean_unsigned_to_nat(1);
        return v___x_5888_;
    }
}
pub unsafe fn l_Bool_ctorIdx___boxed(mut v_x_5889_: *mut LeanObject) -> *mut LeanObject {
    let mut v_x_boxed_5890_: u8 = 0;
    let mut v_res_5891_: *mut LeanObject = core::ptr::null_mut();
    v_x_boxed_5890_ = (lean_unbox(v_x_5889_) as u8);
    v_res_5891_ = l_Bool_ctorIdx(v_x_boxed_5890_);
    return v_res_5891_;
}
pub unsafe fn l_Bool_toCtorIdx(mut v_x_5892_: u8) -> *mut LeanObject {
    let mut v___x_5893_: *mut LeanObject = core::ptr::null_mut();
    v___x_5893_ = l_Bool_ctorIdx(v_x_5892_);
    return v___x_5893_;
}
pub unsafe fn l_Bool_toCtorIdx___boxed(mut v_x_5894_: *mut LeanObject) -> *mut LeanObject {
    let mut v_x_4__boxed_5895_: u8 = 0;
    let mut v_res_5896_: *mut LeanObject = core::ptr::null_mut();
    v_x_4__boxed_5895_ = (lean_unbox(v_x_5894_) as u8);
    v_res_5896_ = l_Bool_toCtorIdx(v_x_4__boxed_5895_);
    return v_res_5896_;
}
pub unsafe fn l_Bool_ctorElim___redArg(mut v_k_5897_: *mut LeanObject) -> *mut LeanObject {
    lean_inc(v_k_5897_);
    return v_k_5897_;
}
pub unsafe fn l_Bool_ctorElim___redArg___boxed(mut v_k_5898_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_5899_: *mut LeanObject = core::ptr::null_mut();
    v_res_5899_ = l_Bool_ctorElim___redArg(v_k_5898_);
    lean_dec(v_k_5898_);
    return v_res_5899_;
}
pub unsafe fn l_Bool_ctorElim(
    mut v_motive_5900_: *mut LeanObject,
    mut v_ctorIdx_5901_: *mut LeanObject,
    mut v_t_5902_: u8,
    mut v_h_5903_: *mut LeanObject,
    mut v_k_5904_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_k_5904_);
    return v_k_5904_;
}
pub unsafe fn l_Bool_ctorElim___boxed(
    mut v_motive_5905_: *mut LeanObject,
    mut v_ctorIdx_5906_: *mut LeanObject,
    mut v_t_5907_: *mut LeanObject,
    mut v_h_5908_: *mut LeanObject,
    mut v_k_5909_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_5910_: u8 = 0;
    let mut v_res_5911_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_5910_ = (lean_unbox(v_t_5907_) as u8);
    v_res_5911_ = l_Bool_ctorElim(
        v_motive_5905_,
        v_ctorIdx_5906_,
        v_t_boxed_5910_,
        v_h_5908_,
        v_k_5909_,
    );
    lean_dec(v_k_5909_);
    lean_dec(v_ctorIdx_5906_);
    return v_res_5911_;
}
pub unsafe fn l_Bool_false_elim___redArg(mut v_false_5912_: *mut LeanObject) -> *mut LeanObject {
    lean_inc(v_false_5912_);
    return v_false_5912_;
}
pub unsafe fn l_Bool_false_elim___redArg___boxed(
    mut v_false_5913_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5914_: *mut LeanObject = core::ptr::null_mut();
    v_res_5914_ = l_Bool_false_elim___redArg(v_false_5913_);
    lean_dec(v_false_5913_);
    return v_res_5914_;
}
pub unsafe fn l_Bool_false_elim(
    mut v_motive_5915_: *mut LeanObject,
    mut v_t_5916_: u8,
    mut v_h_5917_: *mut LeanObject,
    mut v_false_5918_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_false_5918_);
    return v_false_5918_;
}
pub unsafe fn l_Bool_false_elim___boxed(
    mut v_motive_5919_: *mut LeanObject,
    mut v_t_5920_: *mut LeanObject,
    mut v_h_5921_: *mut LeanObject,
    mut v_false_5922_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_5923_: u8 = 0;
    let mut v_res_5924_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_5923_ = (lean_unbox(v_t_5920_) as u8);
    v_res_5924_ = l_Bool_false_elim(v_motive_5919_, v_t_boxed_5923_, v_h_5921_, v_false_5922_);
    lean_dec(v_false_5922_);
    return v_res_5924_;
}
pub unsafe fn l_Bool_true_elim___redArg(mut v_true_5925_: *mut LeanObject) -> *mut LeanObject {
    lean_inc(v_true_5925_);
    return v_true_5925_;
}
pub unsafe fn l_Bool_true_elim___redArg___boxed(
    mut v_true_5926_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5927_: *mut LeanObject = core::ptr::null_mut();
    v_res_5927_ = l_Bool_true_elim___redArg(v_true_5926_);
    lean_dec(v_true_5926_);
    return v_res_5927_;
}
pub unsafe fn l_Bool_true_elim(
    mut v_motive_5928_: *mut LeanObject,
    mut v_t_5929_: u8,
    mut v_h_5930_: *mut LeanObject,
    mut v_true_5931_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_true_5931_);
    return v_true_5931_;
}
pub unsafe fn l_Bool_true_elim___boxed(
    mut v_motive_5932_: *mut LeanObject,
    mut v_t_5933_: *mut LeanObject,
    mut v_h_5934_: *mut LeanObject,
    mut v_true_5935_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_5936_: u8 = 0;
    let mut v_res_5937_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_5936_ = (lean_unbox(v_t_5933_) as u8);
    v_res_5937_ = l_Bool_true_elim(v_motive_5932_, v_t_boxed_5936_, v_h_5934_, v_true_5935_);
    lean_dec(v_true_5935_);
    return v_res_5937_;
}
pub unsafe fn _init_l_instLENat() -> *mut LeanObject {
    let mut v___x_5938_: *mut LeanObject = core::ptr::null_mut();
    v___x_5938_ = lean_box(0);
    return v___x_5938_;
}
pub unsafe fn _init_l_instLTNat() -> *mut LeanObject {
    let mut v___x_5939_: *mut LeanObject = core::ptr::null_mut();
    v___x_5939_ = lean_box(0);
    return v___x_5939_;
}
pub unsafe fn l_Nat_pred___boxed(
    mut v_a_00___x40___internal___hyg_5941_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5942_: *mut LeanObject = core::ptr::null_mut();
    v_res_5942_ = lean_nat_pred(v_a_00___x40___internal___hyg_5941_);
    lean_dec(v_a_00___x40___internal___hyg_5941_);
    return v_res_5942_;
}
pub unsafe fn l_Nat_decLe___boxed(
    mut v_n_5945_: *mut LeanObject,
    mut v_m_5946_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5947_: u8 = 0;
    let mut v_r_5948_: *mut LeanObject = core::ptr::null_mut();
    v_res_5947_ = lean_nat_dec_le(v_n_5945_, v_m_5946_);
    lean_dec(v_m_5946_);
    lean_dec(v_n_5945_);
    v_r_5948_ = lean_box((v_res_5947_) as usize);
    return v_r_5948_;
}
pub unsafe fn l_Nat_decLt___boxed(
    mut v_n_5951_: *mut LeanObject,
    mut v_m_5952_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5953_: u8 = 0;
    let mut v_r_5954_: *mut LeanObject = core::ptr::null_mut();
    v_res_5953_ = lean_nat_dec_lt(v_n_5951_, v_m_5952_);
    lean_dec(v_m_5952_);
    lean_dec(v_n_5951_);
    v_r_5954_ = lean_box((v_res_5953_) as usize);
    return v_r_5954_;
}
pub unsafe fn l_instMinNat___lam__0(
    mut v_x_5955_: *mut LeanObject,
    mut v_y_5956_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5957_: u8 = 0;
    v___x_5957_ = lean_nat_dec_le(v_x_5955_, v_y_5956_);
    if v___x_5957_ == 0 {
        lean_inc(v_y_5956_);
        return v_y_5956_;
    } else {
        lean_inc(v_x_5955_);
        return v_x_5955_;
    }
}
pub unsafe fn l_instMinNat___lam__0___boxed(
    mut v_x_5958_: *mut LeanObject,
    mut v_y_5959_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5960_: *mut LeanObject = core::ptr::null_mut();
    v_res_5960_ = l_instMinNat___lam__0(v_x_5958_, v_y_5959_);
    lean_dec(v_y_5959_);
    lean_dec(v_x_5958_);
    return v_res_5960_;
}
pub unsafe fn l_Nat_sub___boxed(
    mut v_a_00___x40___internal___hyg_5965_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_5966_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5967_: *mut LeanObject = core::ptr::null_mut();
    v_res_5967_ = lean_nat_sub(
        v_a_00___x40___internal___hyg_5965_,
        v_a_00___x40___internal___hyg_5966_,
    );
    lean_dec(v_a_00___x40___internal___hyg_5966_);
    lean_dec(v_a_00___x40___internal___hyg_5965_);
    return v_res_5967_;
}
pub unsafe fn l_Nat_ctorIdx(mut v_x_5968_: *mut LeanObject) -> *mut LeanObject {
    let mut v_zero_5969_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_5970_: u8 = 0;
    v_zero_5969_ = lean_unsigned_to_nat(0);
    v_isZero_5970_ = lean_nat_dec_eq(v_x_5968_, v_zero_5969_);
    if v_isZero_5970_ == 1 {
        return v_zero_5969_;
    } else {
        let mut v___x_5971_: *mut LeanObject = core::ptr::null_mut();
        v___x_5971_ = lean_unsigned_to_nat(1);
        return v___x_5971_;
    }
}
pub unsafe fn l_Nat_ctorIdx___boxed(mut v_x_5972_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_5973_: *mut LeanObject = core::ptr::null_mut();
    v_res_5973_ = l_Nat_ctorIdx(v_x_5972_);
    lean_dec(v_x_5972_);
    return v_res_5973_;
}
pub unsafe fn l_Nat_ctorElim___redArg(
    mut v_t_5974_: *mut LeanObject,
    mut v_k_5975_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_5976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_5977_: u8 = 0;
    v_zero_5976_ = lean_unsigned_to_nat(0);
    v_isZero_5977_ = lean_nat_dec_eq(v_t_5974_, v_zero_5976_);
    if v_isZero_5977_ == 1 {
        return v_k_5975_;
    } else {
        let mut v_one_5978_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_5979_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5980_: *mut LeanObject = core::ptr::null_mut();
        v_one_5978_ = lean_unsigned_to_nat(1);
        v_n_5979_ = lean_nat_sub(v_t_5974_, v_one_5978_);
        v___x_5980_ = lean_apply_1(v_k_5975_, v_n_5979_);
        return v___x_5980_;
    }
}
pub unsafe fn l_Nat_ctorElim___redArg___boxed(
    mut v_t_5981_: *mut LeanObject,
    mut v_k_5982_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5983_: *mut LeanObject = core::ptr::null_mut();
    v_res_5983_ = l_Nat_ctorElim___redArg(v_t_5981_, v_k_5982_);
    lean_dec(v_t_5981_);
    return v_res_5983_;
}
pub unsafe fn l_Nat_ctorElim(
    mut v_motive_5984_: *mut LeanObject,
    mut v_ctorIdx_5985_: *mut LeanObject,
    mut v_t_5986_: *mut LeanObject,
    mut v_h_5987_: *mut LeanObject,
    mut v_k_5988_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5989_: *mut LeanObject = core::ptr::null_mut();
    v___x_5989_ = l_Nat_ctorElim___redArg(v_t_5986_, v_k_5988_);
    return v___x_5989_;
}
pub unsafe fn l_Nat_ctorElim___boxed(
    mut v_motive_5990_: *mut LeanObject,
    mut v_ctorIdx_5991_: *mut LeanObject,
    mut v_t_5992_: *mut LeanObject,
    mut v_h_5993_: *mut LeanObject,
    mut v_k_5994_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5995_: *mut LeanObject = core::ptr::null_mut();
    v_res_5995_ = l_Nat_ctorElim(
        v_motive_5990_,
        v_ctorIdx_5991_,
        v_t_5992_,
        v_h_5993_,
        v_k_5994_,
    );
    lean_dec(v_t_5992_);
    lean_dec(v_ctorIdx_5991_);
    return v_res_5995_;
}
pub unsafe fn l_Nat_zero_elim___redArg(
    mut v_t_5996_: *mut LeanObject,
    mut v_zero_5997_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5998_: *mut LeanObject = core::ptr::null_mut();
    v___x_5998_ = l_Nat_ctorElim___redArg(v_t_5996_, v_zero_5997_);
    return v___x_5998_;
}
pub unsafe fn l_Nat_zero_elim___redArg___boxed(
    mut v_t_5999_: *mut LeanObject,
    mut v_zero_6000_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6001_: *mut LeanObject = core::ptr::null_mut();
    v_res_6001_ = l_Nat_zero_elim___redArg(v_t_5999_, v_zero_6000_);
    lean_dec(v_t_5999_);
    return v_res_6001_;
}
pub unsafe fn l_Nat_zero_elim(
    mut v_motive_6002_: *mut LeanObject,
    mut v_t_6003_: *mut LeanObject,
    mut v_h_6004_: *mut LeanObject,
    mut v_zero_6005_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6006_: *mut LeanObject = core::ptr::null_mut();
    v___x_6006_ = l_Nat_ctorElim___redArg(v_t_6003_, v_zero_6005_);
    return v___x_6006_;
}
pub unsafe fn l_Nat_zero_elim___boxed(
    mut v_motive_6007_: *mut LeanObject,
    mut v_t_6008_: *mut LeanObject,
    mut v_h_6009_: *mut LeanObject,
    mut v_zero_6010_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6011_: *mut LeanObject = core::ptr::null_mut();
    v_res_6011_ = l_Nat_zero_elim(v_motive_6007_, v_t_6008_, v_h_6009_, v_zero_6010_);
    lean_dec(v_t_6008_);
    return v_res_6011_;
}
pub unsafe fn l_Nat_succ_elim___redArg(
    mut v_t_6012_: *mut LeanObject,
    mut v_succ_6013_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6014_: *mut LeanObject = core::ptr::null_mut();
    v___x_6014_ = l_Nat_ctorElim___redArg(v_t_6012_, v_succ_6013_);
    return v___x_6014_;
}
pub unsafe fn l_Nat_succ_elim___redArg___boxed(
    mut v_t_6015_: *mut LeanObject,
    mut v_succ_6016_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6017_: *mut LeanObject = core::ptr::null_mut();
    v_res_6017_ = l_Nat_succ_elim___redArg(v_t_6015_, v_succ_6016_);
    lean_dec(v_t_6015_);
    return v_res_6017_;
}
pub unsafe fn l_Nat_succ_elim(
    mut v_motive_6018_: *mut LeanObject,
    mut v_t_6019_: *mut LeanObject,
    mut v_h_6020_: *mut LeanObject,
    mut v_succ_6021_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6022_: *mut LeanObject = core::ptr::null_mut();
    v___x_6022_ = l_Nat_ctorElim___redArg(v_t_6019_, v_succ_6021_);
    return v___x_6022_;
}
pub unsafe fn l_Nat_succ_elim___boxed(
    mut v_motive_6023_: *mut LeanObject,
    mut v_t_6024_: *mut LeanObject,
    mut v_h_6025_: *mut LeanObject,
    mut v_succ_6026_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6027_: *mut LeanObject = core::ptr::null_mut();
    v_res_6027_ = l_Nat_succ_elim(v_motive_6023_, v_t_6024_, v_h_6025_, v_succ_6026_);
    lean_dec(v_t_6024_);
    return v_res_6027_;
}
pub unsafe fn l_Nat_div_go___redArg(
    mut v_y_6030_: *mut LeanObject,
    mut v_fuel_6031_: *mut LeanObject,
    mut v_x_6032_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_6033_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_6034_: u8 = 0;
    let mut v___x_6035_: u8 = 0;
    v_zero_6033_ = lean_unsigned_to_nat(0);
    v_isZero_6034_ = lean_nat_dec_eq(v_fuel_6031_, v_zero_6033_);
    v___x_6035_ = lean_nat_dec_le(v_y_6030_, v_x_6032_);
    if v___x_6035_ == 0 {
        return v_zero_6033_;
    } else {
        let mut v_one_6036_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_6037_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6038_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6039_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6040_: *mut LeanObject = core::ptr::null_mut();
        v_one_6036_ = lean_unsigned_to_nat(1);
        v_n_6037_ = lean_nat_sub(v_fuel_6031_, v_one_6036_);
        v___x_6038_ = lean_nat_sub(v_x_6032_, v_y_6030_);
        v___x_6039_ = l_Nat_div_go___redArg(v_y_6030_, v_n_6037_, v___x_6038_);
        lean_dec(v___x_6038_);
        lean_dec(v_n_6037_);
        v___x_6040_ = lean_nat_add(v___x_6039_, v_one_6036_);
        lean_dec(v___x_6039_);
        return v___x_6040_;
    }
}
pub unsafe fn l_Nat_div_go___redArg___boxed(
    mut v_y_6041_: *mut LeanObject,
    mut v_fuel_6042_: *mut LeanObject,
    mut v_x_6043_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6044_: *mut LeanObject = core::ptr::null_mut();
    v_res_6044_ = l_Nat_div_go___redArg(v_y_6041_, v_fuel_6042_, v_x_6043_);
    lean_dec(v_x_6043_);
    lean_dec(v_fuel_6042_);
    lean_dec(v_y_6041_);
    return v_res_6044_;
}
pub unsafe fn l_Nat_div_go(
    mut v_y_6045_: *mut LeanObject,
    mut v_hy_6046_: *mut LeanObject,
    mut v_fuel_6047_: *mut LeanObject,
    mut v_x_6048_: *mut LeanObject,
    mut v_hfuel_6049_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6050_: *mut LeanObject = core::ptr::null_mut();
    v___x_6050_ = l_Nat_div_go___redArg(v_y_6045_, v_fuel_6047_, v_x_6048_);
    return v___x_6050_;
}
pub unsafe fn l_Nat_div_go___boxed(
    mut v_y_6051_: *mut LeanObject,
    mut v_hy_6052_: *mut LeanObject,
    mut v_fuel_6053_: *mut LeanObject,
    mut v_x_6054_: *mut LeanObject,
    mut v_hfuel_6055_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6056_: *mut LeanObject = core::ptr::null_mut();
    v_res_6056_ = l_Nat_div_go(
        v_y_6051_,
        v_hy_6052_,
        v_fuel_6053_,
        v_x_6054_,
        v_hfuel_6055_,
    );
    lean_dec(v_x_6054_);
    lean_dec(v_fuel_6053_);
    lean_dec(v_y_6051_);
    return v_res_6056_;
}
pub unsafe fn l_Nat_div___boxed(
    mut v_x_6059_: *mut LeanObject,
    mut v_y_6060_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6061_: *mut LeanObject = core::ptr::null_mut();
    v_res_6061_ = lean_nat_div(v_x_6059_, v_y_6060_);
    lean_dec(v_y_6060_);
    lean_dec(v_x_6059_);
    return v_res_6061_;
}
pub unsafe fn l_Nat_mod___boxed(
    mut v_a_00___x40___internal___hyg_6066_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_6067_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6068_: *mut LeanObject = core::ptr::null_mut();
    v_res_6068_ = lean_nat_mod(
        v_a_00___x40___internal___hyg_6066_,
        v_a_00___x40___internal___hyg_6067_,
    );
    lean_dec(v_a_00___x40___internal___hyg_6067_);
    lean_dec(v_a_00___x40___internal___hyg_6066_);
    return v_res_6068_;
}
pub unsafe fn l_System_Platform_getNumBits___boxed(
    mut v_a_00___x40___internal___hyg_6072_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6073_: *mut LeanObject = core::ptr::null_mut();
    v_res_6073_ = lean_system_platform_nbits(v_a_00___x40___internal___hyg_6072_);
    return v_res_6073_;
}
pub unsafe fn _init_l_System_Platform_numBits___closed__0() -> *mut LeanObject {
    let mut v___x_6074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6075_: *mut LeanObject = core::ptr::null_mut();
    v___x_6074_ = lean_box(0);
    v___x_6075_ = lean_system_platform_nbits(v___x_6074_);
    return v___x_6075_;
}
pub unsafe fn _init_l_System_Platform_numBits() -> *mut LeanObject {
    let mut v___x_6076_: *mut LeanObject = core::ptr::null_mut();
    v___x_6076_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_System_Platform_numBits___closed__0),
        core::ptr::addr_of_mut!(l_System_Platform_numBits___closed__0_once),
        _init_l_System_Platform_numBits___closed__0,
    );
    return v___x_6076_;
}
pub unsafe fn l_instDecidableEqFin___redArg(
    mut v_i_6077_: *mut LeanObject,
    mut v_j_6078_: *mut LeanObject,
) -> u8 {
    let mut v___x_6079_: u8 = 0;
    v___x_6079_ = lean_nat_dec_eq(v_i_6077_, v_j_6078_);
    return v___x_6079_;
}
pub unsafe fn l_instDecidableEqFin___redArg___boxed(
    mut v_i_6080_: *mut LeanObject,
    mut v_j_6081_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6082_: u8 = 0;
    let mut v_r_6083_: *mut LeanObject = core::ptr::null_mut();
    v_res_6082_ = l_instDecidableEqFin___redArg(v_i_6080_, v_j_6081_);
    lean_dec(v_j_6081_);
    lean_dec(v_i_6080_);
    v_r_6083_ = lean_box((v_res_6082_) as usize);
    return v_r_6083_;
}
pub unsafe fn l_instDecidableEqFin(
    mut v_n_6084_: *mut LeanObject,
    mut v_i_6085_: *mut LeanObject,
    mut v_j_6086_: *mut LeanObject,
) -> u8 {
    let mut v___x_6087_: u8 = 0;
    v___x_6087_ = lean_nat_dec_eq(v_i_6085_, v_j_6086_);
    return v___x_6087_;
}
pub unsafe fn l_instDecidableEqFin___boxed(
    mut v_n_6088_: *mut LeanObject,
    mut v_i_6089_: *mut LeanObject,
    mut v_j_6090_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6091_: u8 = 0;
    let mut v_r_6092_: *mut LeanObject = core::ptr::null_mut();
    v_res_6091_ = l_instDecidableEqFin(v_n_6088_, v_i_6089_, v_j_6090_);
    lean_dec(v_j_6090_);
    lean_dec(v_i_6089_);
    lean_dec(v_n_6088_);
    v_r_6092_ = lean_box((v_res_6091_) as usize);
    return v_r_6092_;
}
pub unsafe fn l_instLTFin(mut v_n_6093_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_6094_: *mut LeanObject = core::ptr::null_mut();
    v___x_6094_ = lean_box(0);
    return v___x_6094_;
}
pub unsafe fn l_instLTFin___boxed(mut v_n_6095_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_6096_: *mut LeanObject = core::ptr::null_mut();
    v_res_6096_ = l_instLTFin(v_n_6095_);
    lean_dec(v_n_6095_);
    return v_res_6096_;
}
pub unsafe fn l_instLEFin(mut v_n_6097_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_6098_: *mut LeanObject = core::ptr::null_mut();
    v___x_6098_ = lean_box(0);
    return v___x_6098_;
}
pub unsafe fn l_instLEFin___boxed(mut v_n_6099_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_6100_: *mut LeanObject = core::ptr::null_mut();
    v_res_6100_ = l_instLEFin(v_n_6099_);
    lean_dec(v_n_6099_);
    return v_res_6100_;
}
pub unsafe fn l_Fin_decLt___redArg(
    mut v_a_6101_: *mut LeanObject,
    mut v_b_6102_: *mut LeanObject,
) -> u8 {
    let mut v___x_6103_: u8 = 0;
    v___x_6103_ = lean_nat_dec_lt(v_a_6101_, v_b_6102_);
    return v___x_6103_;
}
pub unsafe fn l_Fin_decLt___redArg___boxed(
    mut v_a_6104_: *mut LeanObject,
    mut v_b_6105_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6106_: u8 = 0;
    let mut v_r_6107_: *mut LeanObject = core::ptr::null_mut();
    v_res_6106_ = l_Fin_decLt___redArg(v_a_6104_, v_b_6105_);
    lean_dec(v_b_6105_);
    lean_dec(v_a_6104_);
    v_r_6107_ = lean_box((v_res_6106_) as usize);
    return v_r_6107_;
}
pub unsafe fn l_Fin_decLt(
    mut v_n_6108_: *mut LeanObject,
    mut v_a_6109_: *mut LeanObject,
    mut v_b_6110_: *mut LeanObject,
) -> u8 {
    let mut v___x_6111_: u8 = 0;
    v___x_6111_ = lean_nat_dec_lt(v_a_6109_, v_b_6110_);
    return v___x_6111_;
}
pub unsafe fn l_Fin_decLt___boxed(
    mut v_n_6112_: *mut LeanObject,
    mut v_a_6113_: *mut LeanObject,
    mut v_b_6114_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6115_: u8 = 0;
    let mut v_r_6116_: *mut LeanObject = core::ptr::null_mut();
    v_res_6115_ = l_Fin_decLt(v_n_6112_, v_a_6113_, v_b_6114_);
    lean_dec(v_b_6114_);
    lean_dec(v_a_6113_);
    lean_dec(v_n_6112_);
    v_r_6116_ = lean_box((v_res_6115_) as usize);
    return v_r_6116_;
}
pub unsafe fn l_Fin_decLe___redArg(
    mut v_a_6117_: *mut LeanObject,
    mut v_b_6118_: *mut LeanObject,
) -> u8 {
    let mut v___x_6119_: u8 = 0;
    v___x_6119_ = lean_nat_dec_le(v_a_6117_, v_b_6118_);
    return v___x_6119_;
}
pub unsafe fn l_Fin_decLe___redArg___boxed(
    mut v_a_6120_: *mut LeanObject,
    mut v_b_6121_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6122_: u8 = 0;
    let mut v_r_6123_: *mut LeanObject = core::ptr::null_mut();
    v_res_6122_ = l_Fin_decLe___redArg(v_a_6120_, v_b_6121_);
    lean_dec(v_b_6121_);
    lean_dec(v_a_6120_);
    v_r_6123_ = lean_box((v_res_6122_) as usize);
    return v_r_6123_;
}
pub unsafe fn l_Fin_decLe(
    mut v_n_6124_: *mut LeanObject,
    mut v_a_6125_: *mut LeanObject,
    mut v_b_6126_: *mut LeanObject,
) -> u8 {
    let mut v___x_6127_: u8 = 0;
    v___x_6127_ = lean_nat_dec_le(v_a_6125_, v_b_6126_);
    return v___x_6127_;
}
pub unsafe fn l_Fin_decLe___boxed(
    mut v_n_6128_: *mut LeanObject,
    mut v_a_6129_: *mut LeanObject,
    mut v_b_6130_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6131_: u8 = 0;
    let mut v_r_6132_: *mut LeanObject = core::ptr::null_mut();
    v_res_6131_ = l_Fin_decLe(v_n_6128_, v_a_6129_, v_b_6130_);
    lean_dec(v_b_6130_);
    lean_dec(v_a_6129_);
    lean_dec(v_n_6128_);
    v_r_6132_ = lean_box((v_res_6131_) as usize);
    return v_r_6132_;
}
pub unsafe fn l_Fin_Internal_ofNat___redArg(
    mut v_n_6133_: *mut LeanObject,
    mut v_a_6134_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6135_: *mut LeanObject = core::ptr::null_mut();
    v___x_6135_ = lean_nat_mod(v_a_6134_, v_n_6133_);
    return v___x_6135_;
}
pub unsafe fn l_Fin_Internal_ofNat___redArg___boxed(
    mut v_n_6136_: *mut LeanObject,
    mut v_a_6137_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6138_: *mut LeanObject = core::ptr::null_mut();
    v_res_6138_ = l_Fin_Internal_ofNat___redArg(v_n_6136_, v_a_6137_);
    lean_dec(v_a_6137_);
    lean_dec(v_n_6136_);
    return v_res_6138_;
}
pub unsafe fn l_Fin_Internal_ofNat(
    mut v_n_6139_: *mut LeanObject,
    mut v_hn_6140_: *mut LeanObject,
    mut v_a_6141_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6142_: *mut LeanObject = core::ptr::null_mut();
    v___x_6142_ = lean_nat_mod(v_a_6141_, v_n_6139_);
    return v___x_6142_;
}
pub unsafe fn l_Fin_Internal_ofNat___boxed(
    mut v_n_6143_: *mut LeanObject,
    mut v_hn_6144_: *mut LeanObject,
    mut v_a_6145_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6146_: *mut LeanObject = core::ptr::null_mut();
    v_res_6146_ = l_Fin_Internal_ofNat(v_n_6143_, v_hn_6144_, v_a_6145_);
    lean_dec(v_a_6145_);
    lean_dec(v_n_6143_);
    return v_res_6146_;
}
pub unsafe fn l_BitVec_decEq___redArg(
    mut v_x_6147_: *mut LeanObject,
    mut v_y_6148_: *mut LeanObject,
) -> u8 {
    let mut v___x_6149_: u8 = 0;
    v___x_6149_ = lean_nat_dec_eq(v_x_6147_, v_y_6148_);
    return v___x_6149_;
}
pub unsafe fn l_BitVec_decEq___redArg___boxed(
    mut v_x_6150_: *mut LeanObject,
    mut v_y_6151_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6152_: u8 = 0;
    let mut v_r_6153_: *mut LeanObject = core::ptr::null_mut();
    v_res_6152_ = l_BitVec_decEq___redArg(v_x_6150_, v_y_6151_);
    lean_dec(v_y_6151_);
    lean_dec(v_x_6150_);
    v_r_6153_ = lean_box((v_res_6152_) as usize);
    return v_r_6153_;
}
pub unsafe fn l_BitVec_decEq(
    mut v_w_6154_: *mut LeanObject,
    mut v_x_6155_: *mut LeanObject,
    mut v_y_6156_: *mut LeanObject,
) -> u8 {
    let mut v___x_6157_: u8 = 0;
    v___x_6157_ = lean_nat_dec_eq(v_x_6155_, v_y_6156_);
    return v___x_6157_;
}
pub unsafe fn l_BitVec_decEq___boxed(
    mut v_w_6158_: *mut LeanObject,
    mut v_x_6159_: *mut LeanObject,
    mut v_y_6160_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6161_: u8 = 0;
    let mut v_r_6162_: *mut LeanObject = core::ptr::null_mut();
    v_res_6161_ = l_BitVec_decEq(v_w_6158_, v_x_6159_, v_y_6160_);
    lean_dec(v_y_6160_);
    lean_dec(v_x_6159_);
    lean_dec(v_w_6158_);
    v_r_6162_ = lean_box((v_res_6161_) as usize);
    return v_r_6162_;
}
pub unsafe fn l_instDecidableEqBitVec___redArg(
    mut v_x_6163_: *mut LeanObject,
    mut v_y_6164_: *mut LeanObject,
) -> u8 {
    let mut v___x_6165_: u8 = 0;
    v___x_6165_ = lean_nat_dec_eq(v_x_6163_, v_y_6164_);
    return v___x_6165_;
}
pub unsafe fn l_instDecidableEqBitVec___redArg___boxed(
    mut v_x_6166_: *mut LeanObject,
    mut v_y_6167_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6168_: u8 = 0;
    let mut v_r_6169_: *mut LeanObject = core::ptr::null_mut();
    v_res_6168_ = l_instDecidableEqBitVec___redArg(v_x_6166_, v_y_6167_);
    lean_dec(v_y_6167_);
    lean_dec(v_x_6166_);
    v_r_6169_ = lean_box((v_res_6168_) as usize);
    return v_r_6169_;
}
pub unsafe fn l_instDecidableEqBitVec(
    mut v_w_6170_: *mut LeanObject,
    mut v_x_6171_: *mut LeanObject,
    mut v_y_6172_: *mut LeanObject,
) -> u8 {
    let mut v___x_6173_: u8 = 0;
    v___x_6173_ = lean_nat_dec_eq(v_x_6171_, v_y_6172_);
    return v___x_6173_;
}
pub unsafe fn l_instDecidableEqBitVec___boxed(
    mut v_w_6174_: *mut LeanObject,
    mut v_x_6175_: *mut LeanObject,
    mut v_y_6176_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6177_: u8 = 0;
    let mut v_r_6178_: *mut LeanObject = core::ptr::null_mut();
    v_res_6177_ = l_instDecidableEqBitVec(v_w_6174_, v_x_6175_, v_y_6176_);
    lean_dec(v_y_6176_);
    lean_dec(v_x_6175_);
    lean_dec(v_w_6174_);
    v_r_6178_ = lean_box((v_res_6177_) as usize);
    return v_r_6178_;
}
pub unsafe fn l_BitVec_ofNatLT___redArg(mut v_i_6179_: *mut LeanObject) -> *mut LeanObject {
    lean_inc(v_i_6179_);
    return v_i_6179_;
}
pub unsafe fn l_BitVec_ofNatLT___redArg___boxed(mut v_i_6180_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_6181_: *mut LeanObject = core::ptr::null_mut();
    v_res_6181_ = l_BitVec_ofNatLT___redArg(v_i_6180_);
    lean_dec(v_i_6180_);
    return v_res_6181_;
}
pub unsafe fn l_BitVec_ofNatLT(
    mut v_w_6182_: *mut LeanObject,
    mut v_i_6183_: *mut LeanObject,
    mut v_p_6184_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_i_6183_);
    return v_i_6183_;
}
pub unsafe fn l_BitVec_ofNatLT___boxed(
    mut v_w_6185_: *mut LeanObject,
    mut v_i_6186_: *mut LeanObject,
    mut v_p_6187_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6188_: *mut LeanObject = core::ptr::null_mut();
    v_res_6188_ = l_BitVec_ofNatLT(v_w_6185_, v_i_6186_, v_p_6187_);
    lean_dec(v_i_6186_);
    lean_dec(v_w_6185_);
    return v_res_6188_;
}
pub unsafe fn l_BitVec_ofNat(
    mut v_n_6189_: *mut LeanObject,
    mut v_i_6190_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6193_: *mut LeanObject = core::ptr::null_mut();
    v___x_6191_ = lean_unsigned_to_nat(2);
    v___x_6192_ = lean_nat_pow(v___x_6191_, v_n_6189_);
    v___x_6193_ = lean_nat_mod(v_i_6190_, v___x_6192_);
    lean_dec(v___x_6192_);
    return v___x_6193_;
}
pub unsafe fn l_BitVec_ofNat___boxed(
    mut v_n_6194_: *mut LeanObject,
    mut v_i_6195_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6196_: *mut LeanObject = core::ptr::null_mut();
    v_res_6196_ = l_BitVec_ofNat(v_n_6194_, v_i_6195_);
    lean_dec(v_i_6195_);
    lean_dec(v_n_6194_);
    return v_res_6196_;
}
pub unsafe fn l_BitVec_toNat___redArg(mut v_x_6197_: *mut LeanObject) -> *mut LeanObject {
    lean_inc(v_x_6197_);
    return v_x_6197_;
}
pub unsafe fn l_BitVec_toNat___redArg___boxed(mut v_x_6198_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_6199_: *mut LeanObject = core::ptr::null_mut();
    v_res_6199_ = l_BitVec_toNat___redArg(v_x_6198_);
    lean_dec(v_x_6198_);
    return v_res_6199_;
}
pub unsafe fn l_BitVec_toNat(
    mut v_w_6200_: *mut LeanObject,
    mut v_x_6201_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_x_6201_);
    return v_x_6201_;
}
pub unsafe fn l_BitVec_toNat___boxed(
    mut v_w_6202_: *mut LeanObject,
    mut v_x_6203_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6204_: *mut LeanObject = core::ptr::null_mut();
    v_res_6204_ = l_BitVec_toNat(v_w_6202_, v_x_6203_);
    lean_dec(v_x_6203_);
    lean_dec(v_w_6202_);
    return v_res_6204_;
}
pub unsafe fn l_instLTBitVec(mut v_w_6205_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_6206_: *mut LeanObject = core::ptr::null_mut();
    v___x_6206_ = lean_box(0);
    return v___x_6206_;
}
pub unsafe fn l_instLTBitVec___boxed(mut v_w_6207_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_6208_: *mut LeanObject = core::ptr::null_mut();
    v_res_6208_ = l_instLTBitVec(v_w_6207_);
    lean_dec(v_w_6207_);
    return v_res_6208_;
}
pub unsafe fn l_instDecidableLtBitVec___redArg(
    mut v_x_6209_: *mut LeanObject,
    mut v_y_6210_: *mut LeanObject,
) -> u8 {
    let mut v___x_6211_: u8 = 0;
    v___x_6211_ = lean_nat_dec_lt(v_x_6209_, v_y_6210_);
    return v___x_6211_;
}
pub unsafe fn l_instDecidableLtBitVec___redArg___boxed(
    mut v_x_6212_: *mut LeanObject,
    mut v_y_6213_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6214_: u8 = 0;
    let mut v_r_6215_: *mut LeanObject = core::ptr::null_mut();
    v_res_6214_ = l_instDecidableLtBitVec___redArg(v_x_6212_, v_y_6213_);
    lean_dec(v_y_6213_);
    lean_dec(v_x_6212_);
    v_r_6215_ = lean_box((v_res_6214_) as usize);
    return v_r_6215_;
}
pub unsafe fn l_instDecidableLtBitVec(
    mut v_w_6216_: *mut LeanObject,
    mut v_x_6217_: *mut LeanObject,
    mut v_y_6218_: *mut LeanObject,
) -> u8 {
    let mut v___x_6219_: u8 = 0;
    v___x_6219_ = lean_nat_dec_lt(v_x_6217_, v_y_6218_);
    return v___x_6219_;
}
pub unsafe fn l_instDecidableLtBitVec___boxed(
    mut v_w_6220_: *mut LeanObject,
    mut v_x_6221_: *mut LeanObject,
    mut v_y_6222_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6223_: u8 = 0;
    let mut v_r_6224_: *mut LeanObject = core::ptr::null_mut();
    v_res_6223_ = l_instDecidableLtBitVec(v_w_6220_, v_x_6221_, v_y_6222_);
    lean_dec(v_y_6222_);
    lean_dec(v_x_6221_);
    lean_dec(v_w_6220_);
    v_r_6224_ = lean_box((v_res_6223_) as usize);
    return v_r_6224_;
}
pub unsafe fn l_instLEBitVec(mut v_w_6225_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_6226_: *mut LeanObject = core::ptr::null_mut();
    v___x_6226_ = lean_box(0);
    return v___x_6226_;
}
pub unsafe fn l_instLEBitVec___boxed(mut v_w_6227_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_6228_: *mut LeanObject = core::ptr::null_mut();
    v_res_6228_ = l_instLEBitVec(v_w_6227_);
    lean_dec(v_w_6227_);
    return v_res_6228_;
}
pub unsafe fn l_instDecidableLeBitVec___redArg(
    mut v_x_6229_: *mut LeanObject,
    mut v_y_6230_: *mut LeanObject,
) -> u8 {
    let mut v___x_6231_: u8 = 0;
    v___x_6231_ = lean_nat_dec_le(v_x_6229_, v_y_6230_);
    return v___x_6231_;
}
pub unsafe fn l_instDecidableLeBitVec___redArg___boxed(
    mut v_x_6232_: *mut LeanObject,
    mut v_y_6233_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6234_: u8 = 0;
    let mut v_r_6235_: *mut LeanObject = core::ptr::null_mut();
    v_res_6234_ = l_instDecidableLeBitVec___redArg(v_x_6232_, v_y_6233_);
    lean_dec(v_y_6233_);
    lean_dec(v_x_6232_);
    v_r_6235_ = lean_box((v_res_6234_) as usize);
    return v_r_6235_;
}
pub unsafe fn l_instDecidableLeBitVec(
    mut v_w_6236_: *mut LeanObject,
    mut v_x_6237_: *mut LeanObject,
    mut v_y_6238_: *mut LeanObject,
) -> u8 {
    let mut v___x_6239_: u8 = 0;
    v___x_6239_ = lean_nat_dec_le(v_x_6237_, v_y_6238_);
    return v___x_6239_;
}
pub unsafe fn l_instDecidableLeBitVec___boxed(
    mut v_w_6240_: *mut LeanObject,
    mut v_x_6241_: *mut LeanObject,
    mut v_y_6242_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6243_: u8 = 0;
    let mut v_r_6244_: *mut LeanObject = core::ptr::null_mut();
    v_res_6243_ = l_instDecidableLeBitVec(v_w_6240_, v_x_6241_, v_y_6242_);
    lean_dec(v_y_6242_);
    lean_dec(v_x_6241_);
    lean_dec(v_w_6240_);
    v_r_6244_ = lean_box((v_res_6243_) as usize);
    return v_r_6244_;
}
pub unsafe fn _init_l_UInt8_size() -> *mut LeanObject {
    let mut v___x_6245_: *mut LeanObject = core::ptr::null_mut();
    v___x_6245_ = lean_unsigned_to_nat(256);
    return v___x_6245_;
}
pub unsafe fn l_UInt8_ofBitVec___boxed(mut v_toBitVec_6247_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_6248_: u8 = 0;
    let mut v_r_6249_: *mut LeanObject = core::ptr::null_mut();
    v_res_6248_ = lean_uint8_of_nat_mk(v_toBitVec_6247_);
    v_r_6249_ = lean_box((v_res_6248_) as usize);
    return v_r_6249_;
}
pub unsafe fn l_UInt8_toBitVec___boxed(mut v_self_6251_: *mut LeanObject) -> *mut LeanObject {
    let mut v_self_boxed_6252_: u8 = 0;
    let mut v_res_6253_: *mut LeanObject = core::ptr::null_mut();
    v_self_boxed_6252_ = (lean_unbox(v_self_6251_) as u8);
    v_res_6253_ = lean_uint8_to_nat(v_self_boxed_6252_);
    return v_res_6253_;
}
pub unsafe fn l_UInt8_ofNatLT___boxed(
    mut v_n_6256_: *mut LeanObject,
    mut v_h_6257_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6258_: u8 = 0;
    let mut v_r_6259_: *mut LeanObject = core::ptr::null_mut();
    v_res_6258_ = lean_uint8_of_nat(v_n_6256_);
    lean_dec(v_n_6256_);
    v_r_6259_ = lean_box((v_res_6258_) as usize);
    return v_r_6259_;
}
pub unsafe fn l_UInt8_ofNat___boxed(mut v_n_6261_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_6262_: u8 = 0;
    let mut v_r_6263_: *mut LeanObject = core::ptr::null_mut();
    v_res_6262_ = lean_uint8_of_nat(v_n_6261_);
    lean_dec(v_n_6261_);
    v_r_6263_ = lean_box((v_res_6262_) as usize);
    return v_r_6263_;
}
pub unsafe fn l_UInt8_decEq___boxed(
    mut v_a_6266_: *mut LeanObject,
    mut v_b_6267_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_6268_: u8 = 0;
    let mut v_b_boxed_6269_: u8 = 0;
    let mut v_res_6270_: u8 = 0;
    let mut v_r_6271_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_6268_ = (lean_unbox(v_a_6266_) as u8);
    v_b_boxed_6269_ = (lean_unbox(v_b_6267_) as u8);
    v_res_6270_ = lean_uint8_dec_eq(v_a_boxed_6268_, v_b_boxed_6269_);
    v_r_6271_ = lean_box((v_res_6270_) as usize);
    return v_r_6271_;
}
pub unsafe fn l_instDecidableEqUInt8(mut v_a_6272_: u8, mut v_b_6273_: u8) -> u8 {
    let mut v___x_6274_: u8 = 0;
    v___x_6274_ = lean_uint8_dec_eq(v_a_6272_, v_b_6273_);
    return v___x_6274_;
}
pub unsafe fn l_instDecidableEqUInt8___boxed(
    mut v_a_6275_: *mut LeanObject,
    mut v_b_6276_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_6277_: u8 = 0;
    let mut v_b_boxed_6278_: u8 = 0;
    let mut v_res_6279_: u8 = 0;
    let mut v_r_6280_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_6277_ = (lean_unbox(v_a_6275_) as u8);
    v_b_boxed_6278_ = (lean_unbox(v_b_6276_) as u8);
    v_res_6279_ = l_instDecidableEqUInt8(v_a_boxed_6277_, v_b_boxed_6278_);
    v_r_6280_ = lean_box((v_res_6279_) as usize);
    return v_r_6280_;
}
pub unsafe fn _init_l_instInhabitedUInt8___closed__0() -> u8 {
    let mut v___x_6281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6282_: u8 = 0;
    v___x_6281_ = lean_unsigned_to_nat(0);
    v___x_6282_ = lean_uint8_of_nat(v___x_6281_);
    return v___x_6282_;
}
pub unsafe fn _init_l_instInhabitedUInt8() -> u8 {
    let mut v___x_6283_: u8 = 0;
    v___x_6283_ = lean_uint8_once(
        core::ptr::addr_of_mut!(l_instInhabitedUInt8___closed__0),
        core::ptr::addr_of_mut!(l_instInhabitedUInt8___closed__0_once),
        _init_l_instInhabitedUInt8___closed__0,
    );
    return v___x_6283_;
}
pub unsafe fn _init_l_instLTUInt8() -> *mut LeanObject {
    let mut v___x_6284_: *mut LeanObject = core::ptr::null_mut();
    v___x_6284_ = lean_box(0);
    return v___x_6284_;
}
pub unsafe fn _init_l_instLEUInt8() -> *mut LeanObject {
    let mut v___x_6285_: *mut LeanObject = core::ptr::null_mut();
    v___x_6285_ = lean_box(0);
    return v___x_6285_;
}
pub unsafe fn l_UInt8_decLt___aux__1(mut v_a_6286_: u8, mut v_b_6287_: u8) -> u8 {
    let mut v___x_6288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6290_: u8 = 0;
    v___x_6288_ = lean_uint8_to_nat(v_a_6286_);
    v___x_6289_ = lean_uint8_to_nat(v_b_6287_);
    v___x_6290_ = lean_nat_dec_lt(v___x_6288_, v___x_6289_);
    lean_dec(v___x_6289_);
    lean_dec(v___x_6288_);
    return v___x_6290_;
}
pub unsafe fn l_UInt8_decLt___aux__1___boxed(
    mut v_a_6291_: *mut LeanObject,
    mut v_b_6292_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_6293_: u8 = 0;
    let mut v_b_boxed_6294_: u8 = 0;
    let mut v_res_6295_: u8 = 0;
    let mut v_r_6296_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_6293_ = (lean_unbox(v_a_6291_) as u8);
    v_b_boxed_6294_ = (lean_unbox(v_b_6292_) as u8);
    v_res_6295_ = l_UInt8_decLt___aux__1(v_a_boxed_6293_, v_b_boxed_6294_);
    v_r_6296_ = lean_box((v_res_6295_) as usize);
    return v_r_6296_;
}
pub unsafe fn l_UInt8_decLt___boxed(
    mut v_a_6299_: *mut LeanObject,
    mut v_b_6300_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_6301_: u8 = 0;
    let mut v_b_boxed_6302_: u8 = 0;
    let mut v_res_6303_: u8 = 0;
    let mut v_r_6304_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_6301_ = (lean_unbox(v_a_6299_) as u8);
    v_b_boxed_6302_ = (lean_unbox(v_b_6300_) as u8);
    v_res_6303_ = lean_uint8_dec_lt(v_a_boxed_6301_, v_b_boxed_6302_);
    v_r_6304_ = lean_box((v_res_6303_) as usize);
    return v_r_6304_;
}
pub unsafe fn l_UInt8_decLe___aux__1(mut v_a_6305_: u8, mut v_b_6306_: u8) -> u8 {
    let mut v___x_6307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6309_: u8 = 0;
    v___x_6307_ = lean_uint8_to_nat(v_a_6305_);
    v___x_6308_ = lean_uint8_to_nat(v_b_6306_);
    v___x_6309_ = lean_nat_dec_le(v___x_6307_, v___x_6308_);
    lean_dec(v___x_6308_);
    lean_dec(v___x_6307_);
    return v___x_6309_;
}
pub unsafe fn l_UInt8_decLe___aux__1___boxed(
    mut v_a_6310_: *mut LeanObject,
    mut v_b_6311_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_6312_: u8 = 0;
    let mut v_b_boxed_6313_: u8 = 0;
    let mut v_res_6314_: u8 = 0;
    let mut v_r_6315_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_6312_ = (lean_unbox(v_a_6310_) as u8);
    v_b_boxed_6313_ = (lean_unbox(v_b_6311_) as u8);
    v_res_6314_ = l_UInt8_decLe___aux__1(v_a_boxed_6312_, v_b_boxed_6313_);
    v_r_6315_ = lean_box((v_res_6314_) as usize);
    return v_r_6315_;
}
pub unsafe fn l_UInt8_decLe___boxed(
    mut v_a_6318_: *mut LeanObject,
    mut v_b_6319_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_6320_: u8 = 0;
    let mut v_b_boxed_6321_: u8 = 0;
    let mut v_res_6322_: u8 = 0;
    let mut v_r_6323_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_6320_ = (lean_unbox(v_a_6318_) as u8);
    v_b_boxed_6321_ = (lean_unbox(v_b_6319_) as u8);
    v_res_6322_ = lean_uint8_dec_le(v_a_boxed_6320_, v_b_boxed_6321_);
    v_r_6323_ = lean_box((v_res_6322_) as usize);
    return v_r_6323_;
}
pub unsafe fn _init_l_UInt16_size() -> *mut LeanObject {
    let mut v___x_6324_: *mut LeanObject = core::ptr::null_mut();
    v___x_6324_ = lean_unsigned_to_nat(65536);
    return v___x_6324_;
}
pub unsafe fn l_UInt16_ofBitVec___boxed(mut v_toBitVec_6326_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_6327_: u16 = 0;
    let mut v_r_6328_: *mut LeanObject = core::ptr::null_mut();
    v_res_6327_ = lean_uint16_of_nat_mk(v_toBitVec_6326_);
    v_r_6328_ = lean_box((v_res_6327_) as usize);
    return v_r_6328_;
}
pub unsafe fn l_UInt16_toBitVec___boxed(mut v_self_6330_: *mut LeanObject) -> *mut LeanObject {
    let mut v_self_boxed_6331_: u16 = 0;
    let mut v_res_6332_: *mut LeanObject = core::ptr::null_mut();
    v_self_boxed_6331_ = (lean_unbox(v_self_6330_) as u16);
    v_res_6332_ = lean_uint16_to_nat(v_self_boxed_6331_);
    return v_res_6332_;
}
pub unsafe fn l_UInt16_ofNatLT___boxed(
    mut v_n_6335_: *mut LeanObject,
    mut v_h_6336_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6337_: u16 = 0;
    let mut v_r_6338_: *mut LeanObject = core::ptr::null_mut();
    v_res_6337_ = lean_uint16_of_nat(v_n_6335_);
    lean_dec(v_n_6335_);
    v_r_6338_ = lean_box((v_res_6337_) as usize);
    return v_r_6338_;
}
pub unsafe fn l_UInt16_decEq___boxed(
    mut v_a_6341_: *mut LeanObject,
    mut v_b_6342_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_6343_: u16 = 0;
    let mut v_b_boxed_6344_: u16 = 0;
    let mut v_res_6345_: u8 = 0;
    let mut v_r_6346_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_6343_ = (lean_unbox(v_a_6341_) as u16);
    v_b_boxed_6344_ = (lean_unbox(v_b_6342_) as u16);
    v_res_6345_ = lean_uint16_dec_eq(v_a_boxed_6343_, v_b_boxed_6344_);
    v_r_6346_ = lean_box((v_res_6345_) as usize);
    return v_r_6346_;
}
pub unsafe fn l_instDecidableEqUInt16(mut v_a_6347_: u16, mut v_b_6348_: u16) -> u8 {
    let mut v___x_6349_: u8 = 0;
    v___x_6349_ = lean_uint16_dec_eq(v_a_6347_, v_b_6348_);
    return v___x_6349_;
}
pub unsafe fn l_instDecidableEqUInt16___boxed(
    mut v_a_6350_: *mut LeanObject,
    mut v_b_6351_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_6352_: u16 = 0;
    let mut v_b_boxed_6353_: u16 = 0;
    let mut v_res_6354_: u8 = 0;
    let mut v_r_6355_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_6352_ = (lean_unbox(v_a_6350_) as u16);
    v_b_boxed_6353_ = (lean_unbox(v_b_6351_) as u16);
    v_res_6354_ = l_instDecidableEqUInt16(v_a_boxed_6352_, v_b_boxed_6353_);
    v_r_6355_ = lean_box((v_res_6354_) as usize);
    return v_r_6355_;
}
pub unsafe fn _init_l_instInhabitedUInt16___closed__0() -> u16 {
    let mut v___x_6356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6357_: u16 = 0;
    v___x_6356_ = lean_unsigned_to_nat(0);
    v___x_6357_ = lean_uint16_of_nat(v___x_6356_);
    return v___x_6357_;
}
pub unsafe fn _init_l_instInhabitedUInt16() -> u16 {
    let mut v___x_6358_: u16 = 0;
    v___x_6358_ = lean_uint16_once(
        core::ptr::addr_of_mut!(l_instInhabitedUInt16___closed__0),
        core::ptr::addr_of_mut!(l_instInhabitedUInt16___closed__0_once),
        _init_l_instInhabitedUInt16___closed__0,
    );
    return v___x_6358_;
}
pub unsafe fn _init_l_UInt32_size() -> *mut LeanObject {
    let mut v___x_6359_: *mut LeanObject = core::ptr::null_mut();
    v___x_6359_ = lean_cstr_to_nat(b"4294967296\0".as_ptr().cast());
    return v___x_6359_;
}
pub unsafe fn l_UInt32_ofBitVec___boxed(mut v_toBitVec_6361_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_6362_: u32 = 0;
    let mut v_r_6363_: *mut LeanObject = core::ptr::null_mut();
    v_res_6362_ = lean_uint32_of_nat_mk(v_toBitVec_6361_);
    v_r_6363_ = lean_box_uint32(v_res_6362_);
    return v_r_6363_;
}
pub unsafe fn l_UInt32_toBitVec___boxed(mut v_self_6365_: *mut LeanObject) -> *mut LeanObject {
    let mut v_self_boxed_6366_: u32 = 0;
    let mut v_res_6367_: *mut LeanObject = core::ptr::null_mut();
    v_self_boxed_6366_ = lean_unbox_uint32(v_self_6365_);
    lean_dec(v_self_6365_);
    v_res_6367_ = lean_uint32_to_nat(v_self_boxed_6366_);
    return v_res_6367_;
}
pub unsafe fn l_UInt32_ofNatLT___boxed(
    mut v_n_6370_: *mut LeanObject,
    mut v_h_6371_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6372_: u32 = 0;
    let mut v_r_6373_: *mut LeanObject = core::ptr::null_mut();
    v_res_6372_ = lean_uint32_of_nat(v_n_6370_);
    lean_dec(v_n_6370_);
    v_r_6373_ = lean_box_uint32(v_res_6372_);
    return v_r_6373_;
}
pub unsafe fn l_UInt32_toNat___boxed(mut v_n_6375_: *mut LeanObject) -> *mut LeanObject {
    let mut v_n_boxed_6376_: u32 = 0;
    let mut v_res_6377_: *mut LeanObject = core::ptr::null_mut();
    v_n_boxed_6376_ = lean_unbox_uint32(v_n_6375_);
    lean_dec(v_n_6375_);
    v_res_6377_ = lean_uint32_to_nat(v_n_boxed_6376_);
    return v_res_6377_;
}
pub unsafe fn l_UInt32_decEq___boxed(
    mut v_a_6380_: *mut LeanObject,
    mut v_b_6381_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_6382_: u32 = 0;
    let mut v_b_boxed_6383_: u32 = 0;
    let mut v_res_6384_: u8 = 0;
    let mut v_r_6385_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_6382_ = lean_unbox_uint32(v_a_6380_);
    lean_dec(v_a_6380_);
    v_b_boxed_6383_ = lean_unbox_uint32(v_b_6381_);
    lean_dec(v_b_6381_);
    v_res_6384_ = lean_uint32_dec_eq(v_a_boxed_6382_, v_b_boxed_6383_);
    v_r_6385_ = lean_box((v_res_6384_) as usize);
    return v_r_6385_;
}
pub unsafe fn l_instDecidableEqUInt32(mut v_a_6386_: u32, mut v_b_6387_: u32) -> u8 {
    let mut v___x_6388_: u8 = 0;
    v___x_6388_ = lean_uint32_dec_eq(v_a_6386_, v_b_6387_);
    return v___x_6388_;
}
pub unsafe fn l_instDecidableEqUInt32___boxed(
    mut v_a_6389_: *mut LeanObject,
    mut v_b_6390_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_6391_: u32 = 0;
    let mut v_b_boxed_6392_: u32 = 0;
    let mut v_res_6393_: u8 = 0;
    let mut v_r_6394_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_6391_ = lean_unbox_uint32(v_a_6389_);
    lean_dec(v_a_6389_);
    v_b_boxed_6392_ = lean_unbox_uint32(v_b_6390_);
    lean_dec(v_b_6390_);
    v_res_6393_ = l_instDecidableEqUInt32(v_a_boxed_6391_, v_b_boxed_6392_);
    v_r_6394_ = lean_box((v_res_6393_) as usize);
    return v_r_6394_;
}
pub unsafe fn _init_l_instInhabitedUInt32___closed__0() -> u32 {
    let mut v___x_6395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6396_: u32 = 0;
    v___x_6395_ = lean_unsigned_to_nat(0);
    v___x_6396_ = lean_uint32_of_nat(v___x_6395_);
    return v___x_6396_;
}
pub unsafe fn _init_l_instInhabitedUInt32() -> u32 {
    let mut v___x_6397_: u32 = 0;
    v___x_6397_ = lean_uint32_once(
        core::ptr::addr_of_mut!(l_instInhabitedUInt32___closed__0),
        core::ptr::addr_of_mut!(l_instInhabitedUInt32___closed__0_once),
        _init_l_instInhabitedUInt32___closed__0,
    );
    return v___x_6397_;
}
pub unsafe fn _init_l_instLTUInt32() -> *mut LeanObject {
    let mut v___x_6398_: *mut LeanObject = core::ptr::null_mut();
    v___x_6398_ = lean_box(0);
    return v___x_6398_;
}
pub unsafe fn _init_l_instLEUInt32() -> *mut LeanObject {
    let mut v___x_6399_: *mut LeanObject = core::ptr::null_mut();
    v___x_6399_ = lean_box(0);
    return v___x_6399_;
}
pub unsafe fn l_UInt32_decLt___boxed(
    mut v_a_6402_: *mut LeanObject,
    mut v_b_6403_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_6404_: u32 = 0;
    let mut v_b_boxed_6405_: u32 = 0;
    let mut v_res_6406_: u8 = 0;
    let mut v_r_6407_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_6404_ = lean_unbox_uint32(v_a_6402_);
    lean_dec(v_a_6402_);
    v_b_boxed_6405_ = lean_unbox_uint32(v_b_6403_);
    lean_dec(v_b_6403_);
    v_res_6406_ = lean_uint32_dec_lt(v_a_boxed_6404_, v_b_boxed_6405_);
    v_r_6407_ = lean_box((v_res_6406_) as usize);
    return v_r_6407_;
}
pub unsafe fn l_UInt32_decLe___boxed(
    mut v_a_6410_: *mut LeanObject,
    mut v_b_6411_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_6412_: u32 = 0;
    let mut v_b_boxed_6413_: u32 = 0;
    let mut v_res_6414_: u8 = 0;
    let mut v_r_6415_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_6412_ = lean_unbox_uint32(v_a_6410_);
    lean_dec(v_a_6410_);
    v_b_boxed_6413_ = lean_unbox_uint32(v_b_6411_);
    lean_dec(v_b_6411_);
    v_res_6414_ = lean_uint32_dec_le(v_a_boxed_6412_, v_b_boxed_6413_);
    v_r_6415_ = lean_box((v_res_6414_) as usize);
    return v_r_6415_;
}
pub unsafe fn l_instMaxUInt32___lam__0(mut v_x_6416_: u32, mut v_y_6417_: u32) -> u32 {
    let mut v___x_6418_: u8 = 0;
    v___x_6418_ = lean_uint32_dec_le(v_x_6416_, v_y_6417_);
    if v___x_6418_ == 0 {
        return v_x_6416_;
    } else {
        return v_y_6417_;
    }
}
pub unsafe fn l_instMaxUInt32___lam__0___boxed(
    mut v_x_6419_: *mut LeanObject,
    mut v_y_6420_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_boxed_6421_: u32 = 0;
    let mut v_y_boxed_6422_: u32 = 0;
    let mut v_res_6423_: u32 = 0;
    let mut v_r_6424_: *mut LeanObject = core::ptr::null_mut();
    v_x_boxed_6421_ = lean_unbox_uint32(v_x_6419_);
    lean_dec(v_x_6419_);
    v_y_boxed_6422_ = lean_unbox_uint32(v_y_6420_);
    lean_dec(v_y_6420_);
    v_res_6423_ = l_instMaxUInt32___lam__0(v_x_boxed_6421_, v_y_boxed_6422_);
    v_r_6424_ = lean_box_uint32(v_res_6423_);
    return v_r_6424_;
}
pub unsafe fn l_instMinUInt32___lam__0(mut v_x_6427_: u32, mut v_y_6428_: u32) -> u32 {
    let mut v___x_6429_: u8 = 0;
    v___x_6429_ = lean_uint32_dec_le(v_x_6427_, v_y_6428_);
    if v___x_6429_ == 0 {
        return v_y_6428_;
    } else {
        return v_x_6427_;
    }
}
pub unsafe fn l_instMinUInt32___lam__0___boxed(
    mut v_x_6430_: *mut LeanObject,
    mut v_y_6431_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_boxed_6432_: u32 = 0;
    let mut v_y_boxed_6433_: u32 = 0;
    let mut v_res_6434_: u32 = 0;
    let mut v_r_6435_: *mut LeanObject = core::ptr::null_mut();
    v_x_boxed_6432_ = lean_unbox_uint32(v_x_6430_);
    lean_dec(v_x_6430_);
    v_y_boxed_6433_ = lean_unbox_uint32(v_y_6431_);
    lean_dec(v_y_6431_);
    v_res_6434_ = l_instMinUInt32___lam__0(v_x_boxed_6432_, v_y_boxed_6433_);
    v_r_6435_ = lean_box_uint32(v_res_6434_);
    return v_r_6435_;
}
pub unsafe fn _init_l_UInt64_size___closed__0() -> *mut LeanObject {
    let mut v___x_6438_: *mut LeanObject = core::ptr::null_mut();
    v___x_6438_ = lean_cstr_to_nat(b"18446744073709551616\0".as_ptr().cast());
    return v___x_6438_;
}
pub unsafe fn _init_l_UInt64_size() -> *mut LeanObject {
    let mut v___x_6439_: *mut LeanObject = core::ptr::null_mut();
    v___x_6439_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_UInt64_size___closed__0),
        core::ptr::addr_of_mut!(l_UInt64_size___closed__0_once),
        _init_l_UInt64_size___closed__0,
    );
    return v___x_6439_;
}
pub unsafe fn l_UInt64_ofBitVec___boxed(mut v_toBitVec_6441_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_6442_: u64 = 0;
    let mut v_r_6443_: *mut LeanObject = core::ptr::null_mut();
    v_res_6442_ = lean_uint64_of_nat_mk(v_toBitVec_6441_);
    v_r_6443_ = lean_box_uint64(v_res_6442_);
    return v_r_6443_;
}
pub unsafe fn l_UInt64_toBitVec___boxed(mut v_self_6445_: *mut LeanObject) -> *mut LeanObject {
    let mut v_self_boxed_6446_: u64 = 0;
    let mut v_res_6447_: *mut LeanObject = core::ptr::null_mut();
    v_self_boxed_6446_ = lean_unbox_uint64(v_self_6445_);
    lean_dec_ref(v_self_6445_);
    v_res_6447_ = lean_uint64_to_nat(v_self_boxed_6446_);
    return v_res_6447_;
}
pub unsafe fn l_UInt64_ofNatLT___boxed(
    mut v_n_6450_: *mut LeanObject,
    mut v_h_6451_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6452_: u64 = 0;
    let mut v_r_6453_: *mut LeanObject = core::ptr::null_mut();
    v_res_6452_ = lean_uint64_of_nat(v_n_6450_);
    lean_dec(v_n_6450_);
    v_r_6453_ = lean_box_uint64(v_res_6452_);
    return v_r_6453_;
}
pub unsafe fn l_UInt64_decEq___boxed(
    mut v_a_6456_: *mut LeanObject,
    mut v_b_6457_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_6458_: u64 = 0;
    let mut v_b_boxed_6459_: u64 = 0;
    let mut v_res_6460_: u8 = 0;
    let mut v_r_6461_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_6458_ = lean_unbox_uint64(v_a_6456_);
    lean_dec_ref(v_a_6456_);
    v_b_boxed_6459_ = lean_unbox_uint64(v_b_6457_);
    lean_dec_ref(v_b_6457_);
    v_res_6460_ = lean_uint64_dec_eq(v_a_boxed_6458_, v_b_boxed_6459_);
    v_r_6461_ = lean_box((v_res_6460_) as usize);
    return v_r_6461_;
}
pub unsafe fn l_instDecidableEqUInt64(mut v_a_6462_: u64, mut v_b_6463_: u64) -> u8 {
    let mut v___x_6464_: u8 = 0;
    v___x_6464_ = lean_uint64_dec_eq(v_a_6462_, v_b_6463_);
    return v___x_6464_;
}
pub unsafe fn l_instDecidableEqUInt64___boxed(
    mut v_a_6465_: *mut LeanObject,
    mut v_b_6466_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_6467_: u64 = 0;
    let mut v_b_boxed_6468_: u64 = 0;
    let mut v_res_6469_: u8 = 0;
    let mut v_r_6470_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_6467_ = lean_unbox_uint64(v_a_6465_);
    lean_dec_ref(v_a_6465_);
    v_b_boxed_6468_ = lean_unbox_uint64(v_b_6466_);
    lean_dec_ref(v_b_6466_);
    v_res_6469_ = l_instDecidableEqUInt64(v_a_boxed_6467_, v_b_boxed_6468_);
    v_r_6470_ = lean_box((v_res_6469_) as usize);
    return v_r_6470_;
}
pub unsafe fn _init_l_instInhabitedUInt64___closed__0() -> u64 {
    let mut v___x_6471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6472_: u64 = 0;
    v___x_6471_ = lean_unsigned_to_nat(0);
    v___x_6472_ = lean_uint64_of_nat(v___x_6471_);
    return v___x_6472_;
}
pub unsafe fn _init_l_instInhabitedUInt64() -> u64 {
    let mut v___x_6473_: u64 = 0;
    v___x_6473_ = lean_uint64_once(
        core::ptr::addr_of_mut!(l_instInhabitedUInt64___closed__0),
        core::ptr::addr_of_mut!(l_instInhabitedUInt64___closed__0_once),
        _init_l_instInhabitedUInt64___closed__0,
    );
    return v___x_6473_;
}
pub unsafe fn _init_l_USize_size___closed__0() -> *mut LeanObject {
    let mut v___x_6474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6476_: *mut LeanObject = core::ptr::null_mut();
    v___x_6474_ = l_System_Platform_numBits;
    v___x_6475_ = lean_unsigned_to_nat(2);
    v___x_6476_ = lean_nat_pow(v___x_6475_, v___x_6474_);
    return v___x_6476_;
}
pub unsafe fn _init_l_USize_size() -> *mut LeanObject {
    let mut v___x_6477_: *mut LeanObject = core::ptr::null_mut();
    v___x_6477_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_USize_size___closed__0),
        core::ptr::addr_of_mut!(l_USize_size___closed__0_once),
        _init_l_USize_size___closed__0,
    );
    return v___x_6477_;
}
pub unsafe fn l_USize_ofBitVec___boxed(mut v_toBitVec_6479_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_6480_: usize = 0;
    let mut v_r_6481_: *mut LeanObject = core::ptr::null_mut();
    v_res_6480_ = lean_usize_of_nat_mk(v_toBitVec_6479_);
    v_r_6481_ = lean_box_usize(v_res_6480_);
    return v_r_6481_;
}
pub unsafe fn l_USize_toBitVec___boxed(mut v_self_6483_: *mut LeanObject) -> *mut LeanObject {
    let mut v_self_boxed_6484_: usize = 0;
    let mut v_res_6485_: *mut LeanObject = core::ptr::null_mut();
    v_self_boxed_6484_ = lean_unbox_usize(v_self_6483_);
    lean_dec(v_self_6483_);
    v_res_6485_ = lean_usize_to_nat(v_self_boxed_6484_);
    return v_res_6485_;
}
pub unsafe fn l_USize_ofNatLT___boxed(
    mut v_n_6488_: *mut LeanObject,
    mut v_h_6489_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6490_: usize = 0;
    let mut v_r_6491_: *mut LeanObject = core::ptr::null_mut();
    v_res_6490_ = lean_usize_of_nat(v_n_6488_);
    lean_dec(v_n_6488_);
    v_r_6491_ = lean_box_usize(v_res_6490_);
    return v_r_6491_;
}
pub unsafe fn l_USize_decEq___boxed(
    mut v_a_6494_: *mut LeanObject,
    mut v_b_6495_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_6496_: usize = 0;
    let mut v_b_boxed_6497_: usize = 0;
    let mut v_res_6498_: u8 = 0;
    let mut v_r_6499_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_6496_ = lean_unbox_usize(v_a_6494_);
    lean_dec(v_a_6494_);
    v_b_boxed_6497_ = lean_unbox_usize(v_b_6495_);
    lean_dec(v_b_6495_);
    v_res_6498_ = lean_usize_dec_eq(v_a_boxed_6496_, v_b_boxed_6497_);
    v_r_6499_ = lean_box((v_res_6498_) as usize);
    return v_r_6499_;
}
pub unsafe fn l_instDecidableEqUSize(mut v_a_6500_: usize, mut v_b_6501_: usize) -> u8 {
    let mut v___x_6502_: u8 = 0;
    v___x_6502_ = lean_usize_dec_eq(v_a_6500_, v_b_6501_);
    return v___x_6502_;
}
pub unsafe fn l_instDecidableEqUSize___boxed(
    mut v_a_6503_: *mut LeanObject,
    mut v_b_6504_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_6505_: usize = 0;
    let mut v_b_boxed_6506_: usize = 0;
    let mut v_res_6507_: u8 = 0;
    let mut v_r_6508_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_6505_ = lean_unbox_usize(v_a_6503_);
    lean_dec(v_a_6503_);
    v_b_boxed_6506_ = lean_unbox_usize(v_b_6504_);
    lean_dec(v_b_6504_);
    v_res_6507_ = l_instDecidableEqUSize(v_a_boxed_6505_, v_b_boxed_6506_);
    v_r_6508_ = lean_box((v_res_6507_) as usize);
    return v_r_6508_;
}
pub unsafe fn _init_l_instInhabitedUSize___closed__0() -> usize {
    let mut v___x_6509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6510_: usize = 0;
    v___x_6509_ = lean_unsigned_to_nat(0);
    v___x_6510_ = lean_usize_of_nat(v___x_6509_);
    return v___x_6510_;
}
pub unsafe fn _init_l_instInhabitedUSize() -> usize {
    let mut v___x_6511_: usize = 0;
    v___x_6511_ = lean_usize_once(
        core::ptr::addr_of_mut!(l_instInhabitedUSize___closed__0),
        core::ptr::addr_of_mut!(l_instInhabitedUSize___closed__0_once),
        _init_l_instInhabitedUSize___closed__0,
    );
    return v___x_6511_;
}
pub unsafe fn l_Char_ofNatAux___boxed(
    mut v_n_6514_: *mut LeanObject,
    mut v_h_6515_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6516_: u32 = 0;
    let mut v_r_6517_: *mut LeanObject = core::ptr::null_mut();
    v_res_6516_ = lean_uint32_of_nat(v_n_6514_);
    lean_dec(v_n_6514_);
    v_r_6517_ = lean_box_uint32(v_res_6516_);
    return v_r_6517_;
}
pub unsafe fn _init_l_Char_ofNat___closed__0() -> u32 {
    let mut v___x_6518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6519_: u32 = 0;
    v___x_6518_ = lean_unsigned_to_nat(0);
    v___x_6519_ = lean_uint32_of_nat_mk(v___x_6518_);
    return v___x_6519_;
}
pub unsafe fn l_Char_ofNat(mut v_n_6520_: *mut LeanObject) -> u32 {
    let mut v___x_6522_: u32 = 0;
    let mut v___x_6523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6524_: u8 = 0;
    let mut v___x_6525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6526_: u8 = 0;
    let mut v___x_6527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6528_: u8 = 0;
    let mut v___x_6529_: u32 = 0;
    let mut v___x_6530_: u32 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6523_ = lean_unsigned_to_nat(55296);
                v___x_6524_ = lean_nat_dec_lt(v_n_6520_, v___x_6523_);
                if v___x_6524_ == 0 {
                    v___x_6525_ = lean_unsigned_to_nat(57343);
                    v___x_6526_ = lean_nat_dec_lt(v___x_6525_, v_n_6520_);
                    if v___x_6526_ == 0 {
                        state = 1;
                        continue;
                    } else {
                        v___x_6527_ = lean_unsigned_to_nat(1114112);
                        v___x_6528_ = lean_nat_dec_lt(v_n_6520_, v___x_6527_);
                        if v___x_6528_ == 0 {
                            state = 1;
                            continue;
                        } else {
                            v___x_6529_ = lean_uint32_of_nat(v_n_6520_);
                            return v___x_6529_;
                        }
                    }
                } else {
                    v___x_6530_ = lean_uint32_of_nat(v_n_6520_);
                    return v___x_6530_;
                }
            }
            1 => {
                v___x_6522_ = lean_uint32_once(
                    core::ptr::addr_of_mut!(l_Char_ofNat___closed__0),
                    core::ptr::addr_of_mut!(l_Char_ofNat___closed__0_once),
                    _init_l_Char_ofNat___closed__0,
                );
                return v___x_6522_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Char_ofNat___boxed(mut v_n_6531_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_6532_: u32 = 0;
    let mut v_r_6533_: *mut LeanObject = core::ptr::null_mut();
    v_res_6532_ = l_Char_ofNat(v_n_6531_);
    lean_dec(v_n_6531_);
    v_r_6533_ = lean_box_uint32(v_res_6532_);
    return v_r_6533_;
}
pub unsafe fn l_instDecidableEqChar(mut v_c_6534_: u32, mut v_d_6535_: u32) -> u8 {
    let mut v___x_6536_: u8 = 0;
    v___x_6536_ = lean_uint32_dec_eq(v_c_6534_, v_d_6535_);
    return v___x_6536_;
}
pub unsafe fn l_instDecidableEqChar___boxed(
    mut v_c_6537_: *mut LeanObject,
    mut v_d_6538_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_c_boxed_6539_: u32 = 0;
    let mut v_d_boxed_6540_: u32 = 0;
    let mut v_res_6541_: u8 = 0;
    let mut v_r_6542_: *mut LeanObject = core::ptr::null_mut();
    v_c_boxed_6539_ = lean_unbox_uint32(v_c_6537_);
    lean_dec(v_c_6537_);
    v_d_boxed_6540_ = lean_unbox_uint32(v_d_6538_);
    lean_dec(v_d_6538_);
    v_res_6541_ = l_instDecidableEqChar(v_c_boxed_6539_, v_d_boxed_6540_);
    v_r_6542_ = lean_box((v_res_6541_) as usize);
    return v_r_6542_;
}
pub unsafe fn _init_l_Char_utf8Size___closed__0() -> u32 {
    let mut v___x_6543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6544_: u32 = 0;
    v___x_6543_ = lean_unsigned_to_nat(127);
    v___x_6544_ = lean_uint32_of_nat(v___x_6543_);
    return v___x_6544_;
}
pub unsafe fn _init_l_Char_utf8Size___closed__1() -> u32 {
    let mut v___x_6545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6546_: u32 = 0;
    v___x_6545_ = lean_unsigned_to_nat(2047);
    v___x_6546_ = lean_uint32_of_nat(v___x_6545_);
    return v___x_6546_;
}
pub unsafe fn _init_l_Char_utf8Size___closed__2() -> u32 {
    let mut v___x_6547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6548_: u32 = 0;
    v___x_6547_ = lean_unsigned_to_nat(65535);
    v___x_6548_ = lean_uint32_of_nat(v___x_6547_);
    return v___x_6548_;
}
pub unsafe fn l_Char_utf8Size(mut v_c_6549_: u32) -> *mut LeanObject {
    let mut v___x_6550_: u32 = 0;
    let mut v___x_6551_: u8 = 0;
    v___x_6550_ = lean_uint32_once(
        core::ptr::addr_of_mut!(l_Char_utf8Size___closed__0),
        core::ptr::addr_of_mut!(l_Char_utf8Size___closed__0_once),
        _init_l_Char_utf8Size___closed__0,
    );
    v___x_6551_ = lean_uint32_dec_le(v_c_6549_, v___x_6550_);
    if v___x_6551_ == 0 {
        let mut v___x_6552_: u32 = 0;
        let mut v___x_6553_: u8 = 0;
        v___x_6552_ = lean_uint32_once(
            core::ptr::addr_of_mut!(l_Char_utf8Size___closed__1),
            core::ptr::addr_of_mut!(l_Char_utf8Size___closed__1_once),
            _init_l_Char_utf8Size___closed__1,
        );
        v___x_6553_ = lean_uint32_dec_le(v_c_6549_, v___x_6552_);
        if v___x_6553_ == 0 {
            let mut v___x_6554_: u32 = 0;
            let mut v___x_6555_: u8 = 0;
            v___x_6554_ = lean_uint32_once(
                core::ptr::addr_of_mut!(l_Char_utf8Size___closed__2),
                core::ptr::addr_of_mut!(l_Char_utf8Size___closed__2_once),
                _init_l_Char_utf8Size___closed__2,
            );
            v___x_6555_ = lean_uint32_dec_le(v_c_6549_, v___x_6554_);
            if v___x_6555_ == 0 {
                let mut v___x_6556_: *mut LeanObject = core::ptr::null_mut();
                v___x_6556_ = lean_unsigned_to_nat(4);
                return v___x_6556_;
            } else {
                let mut v___x_6557_: *mut LeanObject = core::ptr::null_mut();
                v___x_6557_ = lean_unsigned_to_nat(3);
                return v___x_6557_;
            }
        } else {
            let mut v___x_6558_: *mut LeanObject = core::ptr::null_mut();
            v___x_6558_ = lean_unsigned_to_nat(2);
            return v___x_6558_;
        }
    } else {
        let mut v___x_6559_: *mut LeanObject = core::ptr::null_mut();
        v___x_6559_ = lean_unsigned_to_nat(1);
        return v___x_6559_;
    }
}
pub unsafe fn l_Char_utf8Size___boxed(mut v_c_6560_: *mut LeanObject) -> *mut LeanObject {
    let mut v_c_boxed_6561_: u32 = 0;
    let mut v_res_6562_: *mut LeanObject = core::ptr::null_mut();
    v_c_boxed_6561_ = lean_unbox_uint32(v_c_6560_);
    lean_dec(v_c_6560_);
    v_res_6562_ = l_Char_utf8Size(v_c_boxed_6561_);
    return v_res_6562_;
}
pub unsafe fn l_Option_ctorIdx___redArg(mut v_x_6563_: *mut LeanObject) -> *mut LeanObject {
    if lean_obj_tag(v_x_6563_) == 0 {
        let mut v___x_6564_: *mut LeanObject = core::ptr::null_mut();
        v___x_6564_ = lean_unsigned_to_nat(0);
        return v___x_6564_;
    } else {
        let mut v___x_6565_: *mut LeanObject = core::ptr::null_mut();
        v___x_6565_ = lean_unsigned_to_nat(1);
        return v___x_6565_;
    }
}
pub unsafe fn l_Option_ctorIdx___redArg___boxed(mut v_x_6566_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_6567_: *mut LeanObject = core::ptr::null_mut();
    v_res_6567_ = l_Option_ctorIdx___redArg(v_x_6566_);
    lean_dec(v_x_6566_);
    return v_res_6567_;
}
pub unsafe fn l_Option_ctorIdx(
    mut v_00_u03b1_6568_: *mut LeanObject,
    mut v_x_6569_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6570_: *mut LeanObject = core::ptr::null_mut();
    v___x_6570_ = l_Option_ctorIdx___redArg(v_x_6569_);
    return v___x_6570_;
}
pub unsafe fn l_Option_ctorIdx___boxed(
    mut v_00_u03b1_6571_: *mut LeanObject,
    mut v_x_6572_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6573_: *mut LeanObject = core::ptr::null_mut();
    v_res_6573_ = l_Option_ctorIdx(v_00_u03b1_6571_, v_x_6572_);
    lean_dec(v_x_6572_);
    return v_res_6573_;
}
pub unsafe fn l_Option_ctorElim___redArg(
    mut v_t_6574_: *mut LeanObject,
    mut v_k_6575_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_t_6574_) == 0 {
        return v_k_6575_;
    } else {
        let mut v_val_6576_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6577_: *mut LeanObject = core::ptr::null_mut();
        v_val_6576_ = lean_ctor_get(v_t_6574_, 0);
        lean_inc(v_val_6576_);
        lean_dec_ref_known(v_t_6574_, 1);
        v___x_6577_ = lean_apply_1(v_k_6575_, v_val_6576_);
        return v___x_6577_;
    }
}
pub unsafe fn l_Option_ctorElim(
    mut v_00_u03b1_6578_: *mut LeanObject,
    mut v_motive_6579_: *mut LeanObject,
    mut v_ctorIdx_6580_: *mut LeanObject,
    mut v_t_6581_: *mut LeanObject,
    mut v_h_6582_: *mut LeanObject,
    mut v_k_6583_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6584_: *mut LeanObject = core::ptr::null_mut();
    v___x_6584_ = l_Option_ctorElim___redArg(v_t_6581_, v_k_6583_);
    return v___x_6584_;
}
pub unsafe fn l_Option_ctorElim___boxed(
    mut v_00_u03b1_6585_: *mut LeanObject,
    mut v_motive_6586_: *mut LeanObject,
    mut v_ctorIdx_6587_: *mut LeanObject,
    mut v_t_6588_: *mut LeanObject,
    mut v_h_6589_: *mut LeanObject,
    mut v_k_6590_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6591_: *mut LeanObject = core::ptr::null_mut();
    v_res_6591_ = l_Option_ctorElim(
        v_00_u03b1_6585_,
        v_motive_6586_,
        v_ctorIdx_6587_,
        v_t_6588_,
        v_h_6589_,
        v_k_6590_,
    );
    lean_dec(v_ctorIdx_6587_);
    return v_res_6591_;
}
pub unsafe fn l_Option_none_elim___redArg(
    mut v_t_6592_: *mut LeanObject,
    mut v_none_6593_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6594_: *mut LeanObject = core::ptr::null_mut();
    v___x_6594_ = l_Option_ctorElim___redArg(v_t_6592_, v_none_6593_);
    return v___x_6594_;
}
pub unsafe fn l_Option_none_elim(
    mut v_00_u03b1_6595_: *mut LeanObject,
    mut v_motive_6596_: *mut LeanObject,
    mut v_t_6597_: *mut LeanObject,
    mut v_h_6598_: *mut LeanObject,
    mut v_none_6599_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6600_: *mut LeanObject = core::ptr::null_mut();
    v___x_6600_ = l_Option_ctorElim___redArg(v_t_6597_, v_none_6599_);
    return v___x_6600_;
}
pub unsafe fn l_Option_some_elim___redArg(
    mut v_t_6601_: *mut LeanObject,
    mut v_some_6602_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6603_: *mut LeanObject = core::ptr::null_mut();
    v___x_6603_ = l_Option_ctorElim___redArg(v_t_6601_, v_some_6602_);
    return v___x_6603_;
}
pub unsafe fn l_Option_some_elim(
    mut v_00_u03b1_6604_: *mut LeanObject,
    mut v_motive_6605_: *mut LeanObject,
    mut v_t_6606_: *mut LeanObject,
    mut v_h_6607_: *mut LeanObject,
    mut v_some_6608_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6609_: *mut LeanObject = core::ptr::null_mut();
    v___x_6609_ = l_Option_ctorElim___redArg(v_t_6606_, v_some_6608_);
    return v___x_6609_;
}
pub unsafe fn l_instInhabitedOption(mut v_00_u03b1_6610_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_6611_: *mut LeanObject = core::ptr::null_mut();
    v___x_6611_ = lean_box(0);
    return v___x_6611_;
}
pub unsafe fn l_Option_map___redArg(
    mut v_f_6612_: *mut LeanObject,
    mut v_x_6613_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6614_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6618_: u8 = 0;
    let mut v___x_6619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6621_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6622_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6623_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_6613_) == 0 {
                    lean_dec(v_f_6612_);
                    v___x_6614_ = lean_box(0);
                    return v___x_6614_;
                } else {
                    v_val_6615_ = lean_ctor_get(v_x_6613_, 0);
                    v_isSharedCheck_6623_ = (!lean_is_exclusive(v_x_6613_)) as u8;
                    if v_isSharedCheck_6623_ == 0 {
                        v___x_6617_ = v_x_6613_;
                        v_isShared_6618_ = v_isSharedCheck_6623_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_6615_);
                        lean_dec(v_x_6613_);
                        v___x_6617_ = lean_box(0);
                        v_isShared_6618_ = v_isSharedCheck_6623_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6619_ = lean_apply_1(v_f_6612_, v_val_6615_);
                if v_isShared_6618_ == 0 {
                    lean_ctor_set(v___x_6617_, 0, v___x_6619_);
                    v___x_6621_ = v___x_6617_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6622_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6622_, 0, v___x_6619_);
                    v___x_6621_ = v_reuseFailAlloc_6622_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6621_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Option_map(
    mut v_00_u03b1_6624_: *mut LeanObject,
    mut v_00_u03b2_6625_: *mut LeanObject,
    mut v_f_6626_: *mut LeanObject,
    mut v_x_6627_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6628_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6631_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6632_: u8 = 0;
    let mut v___x_6633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6635_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6636_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6637_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_6627_) == 0 {
                    lean_dec(v_f_6626_);
                    v___x_6628_ = lean_box(0);
                    return v___x_6628_;
                } else {
                    v_val_6629_ = lean_ctor_get(v_x_6627_, 0);
                    v_isSharedCheck_6637_ = (!lean_is_exclusive(v_x_6627_)) as u8;
                    if v_isSharedCheck_6637_ == 0 {
                        v___x_6631_ = v_x_6627_;
                        v_isShared_6632_ = v_isSharedCheck_6637_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_6629_);
                        lean_dec(v_x_6627_);
                        v___x_6631_ = lean_box(0);
                        v_isShared_6632_ = v_isSharedCheck_6637_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6633_ = lean_apply_1(v_f_6626_, v_val_6629_);
                if v_isShared_6632_ == 0 {
                    lean_ctor_set(v___x_6631_, 0, v___x_6633_);
                    v___x_6635_ = v___x_6631_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6636_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6636_, 0, v___x_6633_);
                    v___x_6635_ = v_reuseFailAlloc_6636_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6635_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_ctorIdx___redArg(mut v_x_6638_: *mut LeanObject) -> *mut LeanObject {
    if lean_obj_tag(v_x_6638_) == 0 {
        let mut v___x_6639_: *mut LeanObject = core::ptr::null_mut();
        v___x_6639_ = lean_unsigned_to_nat(0);
        return v___x_6639_;
    } else {
        let mut v___x_6640_: *mut LeanObject = core::ptr::null_mut();
        v___x_6640_ = lean_unsigned_to_nat(1);
        return v___x_6640_;
    }
}
pub unsafe fn l_List_ctorIdx___redArg___boxed(mut v_x_6641_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_6642_: *mut LeanObject = core::ptr::null_mut();
    v_res_6642_ = l_List_ctorIdx___redArg(v_x_6641_);
    lean_dec(v_x_6641_);
    return v_res_6642_;
}
pub unsafe fn l_List_ctorIdx(
    mut v_00_u03b1_6643_: *mut LeanObject,
    mut v_x_6644_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6645_: *mut LeanObject = core::ptr::null_mut();
    v___x_6645_ = l_List_ctorIdx___redArg(v_x_6644_);
    return v___x_6645_;
}
pub unsafe fn l_List_ctorIdx___boxed(
    mut v_00_u03b1_6646_: *mut LeanObject,
    mut v_x_6647_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6648_: *mut LeanObject = core::ptr::null_mut();
    v_res_6648_ = l_List_ctorIdx(v_00_u03b1_6646_, v_x_6647_);
    lean_dec(v_x_6647_);
    return v_res_6648_;
}
pub unsafe fn l_List_ctorElim___redArg(
    mut v_t_6649_: *mut LeanObject,
    mut v_k_6650_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_t_6649_) == 0 {
        return v_k_6650_;
    } else {
        let mut v_head_6651_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_6652_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6653_: *mut LeanObject = core::ptr::null_mut();
        v_head_6651_ = lean_ctor_get(v_t_6649_, 0);
        lean_inc(v_head_6651_);
        v_tail_6652_ = lean_ctor_get(v_t_6649_, 1);
        lean_inc(v_tail_6652_);
        lean_dec_ref_known(v_t_6649_, 2);
        v___x_6653_ = lean_apply_2(v_k_6650_, v_head_6651_, v_tail_6652_);
        return v___x_6653_;
    }
}
pub unsafe fn l_List_ctorElim(
    mut v_00_u03b1_6654_: *mut LeanObject,
    mut v_motive_6655_: *mut LeanObject,
    mut v_ctorIdx_6656_: *mut LeanObject,
    mut v_t_6657_: *mut LeanObject,
    mut v_h_6658_: *mut LeanObject,
    mut v_k_6659_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6660_: *mut LeanObject = core::ptr::null_mut();
    v___x_6660_ = l_List_ctorElim___redArg(v_t_6657_, v_k_6659_);
    return v___x_6660_;
}
pub unsafe fn l_List_ctorElim___boxed(
    mut v_00_u03b1_6661_: *mut LeanObject,
    mut v_motive_6662_: *mut LeanObject,
    mut v_ctorIdx_6663_: *mut LeanObject,
    mut v_t_6664_: *mut LeanObject,
    mut v_h_6665_: *mut LeanObject,
    mut v_k_6666_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6667_: *mut LeanObject = core::ptr::null_mut();
    v_res_6667_ = l_List_ctorElim(
        v_00_u03b1_6661_,
        v_motive_6662_,
        v_ctorIdx_6663_,
        v_t_6664_,
        v_h_6665_,
        v_k_6666_,
    );
    lean_dec(v_ctorIdx_6663_);
    return v_res_6667_;
}
pub unsafe fn l_List_nil_elim___redArg(
    mut v_t_6668_: *mut LeanObject,
    mut v_nil_6669_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6670_: *mut LeanObject = core::ptr::null_mut();
    v___x_6670_ = l_List_ctorElim___redArg(v_t_6668_, v_nil_6669_);
    return v___x_6670_;
}
pub unsafe fn l_List_nil_elim(
    mut v_00_u03b1_6671_: *mut LeanObject,
    mut v_motive_6672_: *mut LeanObject,
    mut v_t_6673_: *mut LeanObject,
    mut v_h_6674_: *mut LeanObject,
    mut v_nil_6675_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6676_: *mut LeanObject = core::ptr::null_mut();
    v___x_6676_ = l_List_ctorElim___redArg(v_t_6673_, v_nil_6675_);
    return v___x_6676_;
}
pub unsafe fn l_List_cons_elim___redArg(
    mut v_t_6677_: *mut LeanObject,
    mut v_cons_6678_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6679_: *mut LeanObject = core::ptr::null_mut();
    v___x_6679_ = l_List_ctorElim___redArg(v_t_6677_, v_cons_6678_);
    return v___x_6679_;
}
pub unsafe fn l_List_cons_elim(
    mut v_00_u03b1_6680_: *mut LeanObject,
    mut v_motive_6681_: *mut LeanObject,
    mut v_t_6682_: *mut LeanObject,
    mut v_h_6683_: *mut LeanObject,
    mut v_cons_6684_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6685_: *mut LeanObject = core::ptr::null_mut();
    v___x_6685_ = l_List_ctorElim___redArg(v_t_6682_, v_cons_6684_);
    return v___x_6685_;
}
pub unsafe fn l_instInhabitedList(mut v_00_u03b1_6686_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_6687_: *mut LeanObject = core::ptr::null_mut();
    v___x_6687_ = lean_box(0);
    return v___x_6687_;
}
pub unsafe fn l_List_hasDecEq___redArg(
    mut v_inst_6688_: *mut LeanObject,
    mut v_x_6689_: *mut LeanObject,
    mut v_x_6690_: *mut LeanObject,
) -> u8 {
    if lean_obj_tag(v_x_6689_) == 0 {
        lean_dec_ref(v_inst_6688_);
        if lean_obj_tag(v_x_6690_) == 0 {
            let mut v___x_6691_: u8 = 0;
            v___x_6691_ = 1;
            return v___x_6691_;
        } else {
            let mut v___x_6692_: u8 = 0;
            lean_dec_ref_known(v_x_6690_, 2);
            v___x_6692_ = 0;
            return v___x_6692_;
        }
    } else {
        let mut v_head_6693_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_6694_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6695_: u8 = 0;
        v_head_6693_ = lean_ctor_get(v_x_6689_, 0);
        lean_inc(v_head_6693_);
        v_tail_6694_ = lean_ctor_get(v_x_6689_, 1);
        lean_inc(v_tail_6694_);
        lean_dec_ref_known(v_x_6689_, 2);
        v___x_6695_ = 0;
        if lean_obj_tag(v_x_6690_) == 0 {
            lean_dec(v_tail_6694_);
            lean_dec(v_head_6693_);
            lean_dec_ref(v_inst_6688_);
            return v___x_6695_;
        } else {
            let mut v_head_6696_: *mut LeanObject = core::ptr::null_mut();
            let mut v_tail_6697_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6698_: u8 = 0;
            let mut v___x_6699_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6700_: u8 = 0;
            v_head_6696_ = lean_ctor_get(v_x_6690_, 0);
            lean_inc(v_head_6696_);
            v_tail_6697_ = lean_ctor_get(v_x_6690_, 1);
            lean_inc(v_tail_6697_);
            lean_dec_ref_known(v_x_6690_, 2);
            lean_inc_ref(v_inst_6688_);
            v___x_6698_ = l_List_hasDecEq___redArg(v_inst_6688_, v_tail_6694_, v_tail_6697_);
            v___x_6699_ = lean_apply_2(v_inst_6688_, v_head_6693_, v_head_6696_);
            v___x_6700_ = (lean_unbox(v___x_6699_) as u8);
            if v___x_6700_ == 0 {
                return v___x_6695_;
            } else {
                if v___x_6698_ == 0 {
                    return v___x_6695_;
                } else {
                    return v___x_6698_;
                }
            }
        }
    }
}
pub unsafe fn l_List_hasDecEq___redArg___boxed(
    mut v_inst_6701_: *mut LeanObject,
    mut v_x_6702_: *mut LeanObject,
    mut v_x_6703_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6704_: u8 = 0;
    let mut v_r_6705_: *mut LeanObject = core::ptr::null_mut();
    v_res_6704_ = l_List_hasDecEq___redArg(v_inst_6701_, v_x_6702_, v_x_6703_);
    v_r_6705_ = lean_box((v_res_6704_) as usize);
    return v_r_6705_;
}
pub unsafe fn l_List_hasDecEq(
    mut v_00_u03b1_6706_: *mut LeanObject,
    mut v_inst_6707_: *mut LeanObject,
    mut v_x_6708_: *mut LeanObject,
    mut v_x_6709_: *mut LeanObject,
) -> u8 {
    let mut v___x_6710_: u8 = 0;
    v___x_6710_ = l_List_hasDecEq___redArg(v_inst_6707_, v_x_6708_, v_x_6709_);
    return v___x_6710_;
}
pub unsafe fn l_List_hasDecEq___boxed(
    mut v_00_u03b1_6711_: *mut LeanObject,
    mut v_inst_6712_: *mut LeanObject,
    mut v_x_6713_: *mut LeanObject,
    mut v_x_6714_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6715_: u8 = 0;
    let mut v_r_6716_: *mut LeanObject = core::ptr::null_mut();
    v_res_6715_ = l_List_hasDecEq(v_00_u03b1_6711_, v_inst_6712_, v_x_6713_, v_x_6714_);
    v_r_6716_ = lean_box((v_res_6715_) as usize);
    return v_r_6716_;
}
pub unsafe fn l_instDecidableEqList___redArg(
    mut v_inst_6717_: *mut LeanObject,
    mut v_xs_6718_: *mut LeanObject,
    mut v_ys_6719_: *mut LeanObject,
) -> u8 {
    if lean_obj_tag(v_xs_6718_) == 0 {
        lean_dec_ref(v_inst_6717_);
        if lean_obj_tag(v_ys_6719_) == 0 {
            let mut v___x_6720_: u8 = 0;
            v___x_6720_ = 1;
            return v___x_6720_;
        } else {
            let mut v___x_6721_: u8 = 0;
            lean_dec_ref_known(v_ys_6719_, 2);
            v___x_6721_ = 0;
            return v___x_6721_;
        }
    } else {
        if lean_obj_tag(v_ys_6719_) == 0 {
            let mut v___x_6722_: u8 = 0;
            lean_dec_ref_known(v_xs_6718_, 2);
            lean_dec_ref(v_inst_6717_);
            v___x_6722_ = 0;
            return v___x_6722_;
        } else {
            let mut v_head_6723_: *mut LeanObject = core::ptr::null_mut();
            let mut v_tail_6724_: *mut LeanObject = core::ptr::null_mut();
            let mut v_head_6725_: *mut LeanObject = core::ptr::null_mut();
            let mut v_tail_6726_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6727_: u8 = 0;
            let mut v___x_6728_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6729_: u8 = 0;
            v_head_6723_ = lean_ctor_get(v_xs_6718_, 0);
            lean_inc(v_head_6723_);
            v_tail_6724_ = lean_ctor_get(v_xs_6718_, 1);
            lean_inc(v_tail_6724_);
            lean_dec_ref_known(v_xs_6718_, 2);
            v_head_6725_ = lean_ctor_get(v_ys_6719_, 0);
            lean_inc(v_head_6725_);
            v_tail_6726_ = lean_ctor_get(v_ys_6719_, 1);
            lean_inc(v_tail_6726_);
            lean_dec_ref_known(v_ys_6719_, 2);
            lean_inc_ref(v_inst_6717_);
            v___x_6727_ = l_List_hasDecEq___redArg(v_inst_6717_, v_tail_6724_, v_tail_6726_);
            v___x_6728_ = lean_apply_2(v_inst_6717_, v_head_6723_, v_head_6725_);
            v___x_6729_ = (lean_unbox(v___x_6728_) as u8);
            if v___x_6729_ == 0 {
                let mut v___x_6730_: u8 = 0;
                v___x_6730_ = (lean_unbox(v___x_6728_) as u8);
                return v___x_6730_;
            } else {
                return v___x_6727_;
            }
        }
    }
}
pub unsafe fn l_instDecidableEqList___redArg___boxed(
    mut v_inst_6731_: *mut LeanObject,
    mut v_xs_6732_: *mut LeanObject,
    mut v_ys_6733_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6734_: u8 = 0;
    let mut v_r_6735_: *mut LeanObject = core::ptr::null_mut();
    v_res_6734_ = l_instDecidableEqList___redArg(v_inst_6731_, v_xs_6732_, v_ys_6733_);
    v_r_6735_ = lean_box((v_res_6734_) as usize);
    return v_r_6735_;
}
pub unsafe fn l_instDecidableEqList(
    mut v_00_u03b1_6736_: *mut LeanObject,
    mut v_inst_6737_: *mut LeanObject,
    mut v_xs_6738_: *mut LeanObject,
    mut v_ys_6739_: *mut LeanObject,
) -> u8 {
    let mut v___x_6740_: u8 = 0;
    v___x_6740_ = l_instDecidableEqList___redArg(v_inst_6737_, v_xs_6738_, v_ys_6739_);
    return v___x_6740_;
}
pub unsafe fn l_instDecidableEqList___boxed(
    mut v_00_u03b1_6741_: *mut LeanObject,
    mut v_inst_6742_: *mut LeanObject,
    mut v_xs_6743_: *mut LeanObject,
    mut v_ys_6744_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6745_: u8 = 0;
    let mut v_r_6746_: *mut LeanObject = core::ptr::null_mut();
    v_res_6745_ = l_instDecidableEqList(v_00_u03b1_6741_, v_inst_6742_, v_xs_6743_, v_ys_6744_);
    v_r_6746_ = lean_box((v_res_6745_) as usize);
    return v_r_6746_;
}
pub unsafe fn l_List_instDecidableNilEq___redArg(mut v_a_6747_: *mut LeanObject) -> u8 {
    if lean_obj_tag(v_a_6747_) == 0 {
        let mut v___x_6748_: u8 = 0;
        v___x_6748_ = 1;
        return v___x_6748_;
    } else {
        let mut v___x_6749_: u8 = 0;
        v___x_6749_ = 0;
        return v___x_6749_;
    }
}
pub unsafe fn l_List_instDecidableNilEq___redArg___boxed(
    mut v_a_6750_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6751_: u8 = 0;
    let mut v_r_6752_: *mut LeanObject = core::ptr::null_mut();
    v_res_6751_ = l_List_instDecidableNilEq___redArg(v_a_6750_);
    lean_dec(v_a_6750_);
    v_r_6752_ = lean_box((v_res_6751_) as usize);
    return v_r_6752_;
}
pub unsafe fn l_List_instDecidableNilEq(
    mut v_00_u03b1_6753_: *mut LeanObject,
    mut v_a_6754_: *mut LeanObject,
) -> u8 {
    let mut v___x_6755_: u8 = 0;
    v___x_6755_ = l_List_instDecidableNilEq___redArg(v_a_6754_);
    return v___x_6755_;
}
pub unsafe fn l_List_instDecidableNilEq___boxed(
    mut v_00_u03b1_6756_: *mut LeanObject,
    mut v_a_6757_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6758_: u8 = 0;
    let mut v_r_6759_: *mut LeanObject = core::ptr::null_mut();
    v_res_6758_ = l_List_instDecidableNilEq(v_00_u03b1_6756_, v_a_6757_);
    lean_dec(v_a_6757_);
    v_r_6759_ = lean_box((v_res_6758_) as usize);
    return v_r_6759_;
}
pub unsafe fn l_List_instDecidableEqNil___redArg(mut v_a_6760_: *mut LeanObject) -> u8 {
    if lean_obj_tag(v_a_6760_) == 0 {
        let mut v___x_6761_: u8 = 0;
        v___x_6761_ = 1;
        return v___x_6761_;
    } else {
        let mut v___x_6762_: u8 = 0;
        v___x_6762_ = 0;
        return v___x_6762_;
    }
}
pub unsafe fn l_List_instDecidableEqNil___redArg___boxed(
    mut v_a_6763_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6764_: u8 = 0;
    let mut v_r_6765_: *mut LeanObject = core::ptr::null_mut();
    v_res_6764_ = l_List_instDecidableEqNil___redArg(v_a_6763_);
    lean_dec(v_a_6763_);
    v_r_6765_ = lean_box((v_res_6764_) as usize);
    return v_r_6765_;
}
pub unsafe fn l_List_instDecidableEqNil(
    mut v_00_u03b1_6766_: *mut LeanObject,
    mut v_a_6767_: *mut LeanObject,
) -> u8 {
    let mut v___x_6768_: u8 = 0;
    v___x_6768_ = l_List_instDecidableEqNil___redArg(v_a_6767_);
    return v___x_6768_;
}
pub unsafe fn l_List_instDecidableEqNil___boxed(
    mut v_00_u03b1_6769_: *mut LeanObject,
    mut v_a_6770_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6771_: u8 = 0;
    let mut v_r_6772_: *mut LeanObject = core::ptr::null_mut();
    v_res_6771_ = l_List_instDecidableEqNil(v_00_u03b1_6769_, v_a_6770_);
    lean_dec(v_a_6770_);
    v_r_6772_ = lean_box((v_res_6771_) as usize);
    return v_r_6772_;
}
pub unsafe fn l_List_length___redArg(mut v_x_6773_: *mut LeanObject) -> *mut LeanObject {
    if lean_obj_tag(v_x_6773_) == 0 {
        let mut v___x_6774_: *mut LeanObject = core::ptr::null_mut();
        v___x_6774_ = lean_unsigned_to_nat(0);
        return v___x_6774_;
    } else {
        let mut v_tail_6775_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6776_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6777_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6778_: *mut LeanObject = core::ptr::null_mut();
        v_tail_6775_ = lean_ctor_get(v_x_6773_, 1);
        v___x_6776_ = l_List_length___redArg(v_tail_6775_);
        v___x_6777_ = lean_unsigned_to_nat(1);
        v___x_6778_ = lean_nat_add(v___x_6776_, v___x_6777_);
        lean_dec(v___x_6776_);
        return v___x_6778_;
    }
}
pub unsafe fn l_List_length___redArg___boxed(mut v_x_6779_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_6780_: *mut LeanObject = core::ptr::null_mut();
    v_res_6780_ = l_List_length___redArg(v_x_6779_);
    lean_dec(v_x_6779_);
    return v_res_6780_;
}
pub unsafe fn l_List_length(
    mut v_00_u03b1_6781_: *mut LeanObject,
    mut v_x_6782_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6783_: *mut LeanObject = core::ptr::null_mut();
    v___x_6783_ = l_List_length___redArg(v_x_6782_);
    return v___x_6783_;
}
pub unsafe fn l_List_length___boxed(
    mut v_00_u03b1_6784_: *mut LeanObject,
    mut v_x_6785_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6786_: *mut LeanObject = core::ptr::null_mut();
    v_res_6786_ = l_List_length(v_00_u03b1_6784_, v_x_6785_);
    lean_dec(v_x_6785_);
    return v_res_6786_;
}
pub unsafe fn l_List_lengthTRAux___redArg(
    mut v_x_6787_: *mut LeanObject,
    mut v_x_6788_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_tail_6789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6791_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_6787_) == 0 {
                    return v_x_6788_;
                } else {
                    v_tail_6789_ = lean_ctor_get(v_x_6787_, 1);
                    v___x_6790_ = lean_unsigned_to_nat(1);
                    v___x_6791_ = lean_nat_add(v_x_6788_, v___x_6790_);
                    lean_dec(v_x_6788_);
                    v_x_6787_ = v_tail_6789_;
                    v_x_6788_ = v___x_6791_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_lengthTRAux___redArg___boxed(
    mut v_x_6793_: *mut LeanObject,
    mut v_x_6794_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6795_: *mut LeanObject = core::ptr::null_mut();
    v_res_6795_ = l_List_lengthTRAux___redArg(v_x_6793_, v_x_6794_);
    lean_dec(v_x_6793_);
    return v_res_6795_;
}
pub unsafe fn l_List_lengthTRAux(
    mut v_00_u03b1_6796_: *mut LeanObject,
    mut v_x_6797_: *mut LeanObject,
    mut v_x_6798_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6799_: *mut LeanObject = core::ptr::null_mut();
    v___x_6799_ = l_List_lengthTRAux___redArg(v_x_6797_, v_x_6798_);
    return v___x_6799_;
}
pub unsafe fn l_List_lengthTRAux___boxed(
    mut v_00_u03b1_6800_: *mut LeanObject,
    mut v_x_6801_: *mut LeanObject,
    mut v_x_6802_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6803_: *mut LeanObject = core::ptr::null_mut();
    v_res_6803_ = l_List_lengthTRAux(v_00_u03b1_6800_, v_x_6801_, v_x_6802_);
    lean_dec(v_x_6801_);
    return v_res_6803_;
}
pub unsafe fn l_List_lengthTR___redArg(mut v_as_6804_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_6805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6806_: *mut LeanObject = core::ptr::null_mut();
    v___x_6805_ = lean_unsigned_to_nat(0);
    v___x_6806_ = l_List_lengthTRAux___redArg(v_as_6804_, v___x_6805_);
    return v___x_6806_;
}
pub unsafe fn l_List_lengthTR___redArg___boxed(mut v_as_6807_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_6808_: *mut LeanObject = core::ptr::null_mut();
    v_res_6808_ = l_List_lengthTR___redArg(v_as_6807_);
    lean_dec(v_as_6807_);
    return v_res_6808_;
}
pub unsafe fn l_List_lengthTR(
    mut v_00_u03b1_6809_: *mut LeanObject,
    mut v_as_6810_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6811_: *mut LeanObject = core::ptr::null_mut();
    v___x_6811_ = l_List_lengthTR___redArg(v_as_6810_);
    return v___x_6811_;
}
pub unsafe fn l_List_lengthTR___boxed(
    mut v_00_u03b1_6812_: *mut LeanObject,
    mut v_as_6813_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6814_: *mut LeanObject = core::ptr::null_mut();
    v_res_6814_ = l_List_lengthTR(v_00_u03b1_6812_, v_as_6813_);
    lean_dec(v_as_6813_);
    return v_res_6814_;
}
pub unsafe fn l_List_get___redArg(
    mut v_x_6815_: *mut LeanObject,
    mut v_x_6816_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_6817_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_6818_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zero_6819_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_6820_: u8 = 0;
    let mut v_one_6821_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_6822_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_head_6817_ = lean_ctor_get(v_x_6815_, 0);
                v_tail_6818_ = lean_ctor_get(v_x_6815_, 1);
                v_zero_6819_ = lean_unsigned_to_nat(0);
                v_isZero_6820_ = lean_nat_dec_eq(v_x_6816_, v_zero_6819_);
                if v_isZero_6820_ == 1 {
                    lean_dec(v_x_6816_);
                    lean_inc(v_head_6817_);
                    return v_head_6817_;
                } else {
                    v_one_6821_ = lean_unsigned_to_nat(1);
                    v_n_6822_ = lean_nat_sub(v_x_6816_, v_one_6821_);
                    lean_dec(v_x_6816_);
                    v_x_6815_ = v_tail_6818_;
                    v_x_6816_ = v_n_6822_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_get___redArg___boxed(
    mut v_x_6824_: *mut LeanObject,
    mut v_x_6825_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6826_: *mut LeanObject = core::ptr::null_mut();
    v_res_6826_ = l_List_get___redArg(v_x_6824_, v_x_6825_);
    lean_dec(v_x_6824_);
    return v_res_6826_;
}
pub unsafe fn l_List_get(
    mut v_00_u03b1_6827_: *mut LeanObject,
    mut v_x_6828_: *mut LeanObject,
    mut v_x_6829_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6830_: *mut LeanObject = core::ptr::null_mut();
    v___x_6830_ = l_List_get___redArg(v_x_6828_, v_x_6829_);
    return v___x_6830_;
}
pub unsafe fn l_List_get___boxed(
    mut v_00_u03b1_6831_: *mut LeanObject,
    mut v_x_6832_: *mut LeanObject,
    mut v_x_6833_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6834_: *mut LeanObject = core::ptr::null_mut();
    v_res_6834_ = l_List_get(v_00_u03b1_6831_, v_x_6832_, v_x_6833_);
    lean_dec(v_x_6832_);
    return v_res_6834_;
}
pub unsafe fn l_List_set___redArg(
    mut v_x_6835_: *mut LeanObject,
    mut v_x_6836_: *mut LeanObject,
    mut v_x_6837_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_6838_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_6839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6841_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6842_: u8 = 0;
    let mut v_zero_6843_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_6844_: u8 = 0;
    let mut v___x_6846_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_one_6848_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_6849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6852_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6853_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6854_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_6835_) == 0 {
                    lean_dec(v_x_6837_);
                    return v_x_6835_;
                } else {
                    v_head_6838_ = lean_ctor_get(v_x_6835_, 0);
                    v_tail_6839_ = lean_ctor_get(v_x_6835_, 1);
                    v_isSharedCheck_6854_ = (!lean_is_exclusive(v_x_6835_)) as u8;
                    if v_isSharedCheck_6854_ == 0 {
                        v___x_6841_ = v_x_6835_;
                        v_isShared_6842_ = v_isSharedCheck_6854_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_6839_);
                        lean_inc(v_head_6838_);
                        lean_dec(v_x_6835_);
                        v___x_6841_ = lean_box(0);
                        v_isShared_6842_ = v_isSharedCheck_6854_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_zero_6843_ = lean_unsigned_to_nat(0);
                v_isZero_6844_ = lean_nat_dec_eq(v_x_6836_, v_zero_6843_);
                if v_isZero_6844_ == 1 {
                    lean_dec(v_head_6838_);
                    if v_isShared_6842_ == 0 {
                        lean_ctor_set(v___x_6841_, 0, v_x_6837_);
                        v___x_6846_ = v___x_6841_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6847_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6847_, 0, v_x_6837_);
                        lean_ctor_set(v_reuseFailAlloc_6847_, 1, v_tail_6839_);
                        v___x_6846_ = v_reuseFailAlloc_6847_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_one_6848_ = lean_unsigned_to_nat(1);
                    v_n_6849_ = lean_nat_sub(v_x_6836_, v_one_6848_);
                    v___x_6850_ = l_List_set___redArg(v_tail_6839_, v_n_6849_, v_x_6837_);
                    lean_dec(v_n_6849_);
                    if v_isShared_6842_ == 0 {
                        lean_ctor_set(v___x_6841_, 1, v___x_6850_);
                        v___x_6852_ = v___x_6841_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_6853_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6853_, 0, v_head_6838_);
                        lean_ctor_set(v_reuseFailAlloc_6853_, 1, v___x_6850_);
                        v___x_6852_ = v_reuseFailAlloc_6853_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_6846_;
            }
            3 => {
                return v___x_6852_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_set___redArg___boxed(
    mut v_x_6855_: *mut LeanObject,
    mut v_x_6856_: *mut LeanObject,
    mut v_x_6857_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6858_: *mut LeanObject = core::ptr::null_mut();
    v_res_6858_ = l_List_set___redArg(v_x_6855_, v_x_6856_, v_x_6857_);
    lean_dec(v_x_6856_);
    return v_res_6858_;
}
pub unsafe fn l_List_set(
    mut v_00_u03b1_6859_: *mut LeanObject,
    mut v_x_6860_: *mut LeanObject,
    mut v_x_6861_: *mut LeanObject,
    mut v_x_6862_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6863_: *mut LeanObject = core::ptr::null_mut();
    v___x_6863_ = l_List_set___redArg(v_x_6860_, v_x_6861_, v_x_6862_);
    return v___x_6863_;
}
pub unsafe fn l_List_set___boxed(
    mut v_00_u03b1_6864_: *mut LeanObject,
    mut v_x_6865_: *mut LeanObject,
    mut v_x_6866_: *mut LeanObject,
    mut v_x_6867_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6868_: *mut LeanObject = core::ptr::null_mut();
    v_res_6868_ = l_List_set(v_00_u03b1_6864_, v_x_6865_, v_x_6866_, v_x_6867_);
    lean_dec(v_x_6866_);
    return v_res_6868_;
}
pub unsafe fn l_List_foldl___redArg(
    mut v_f_6869_: *mut LeanObject,
    mut v_x_6870_: *mut LeanObject,
    mut v_x_6871_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_6872_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_6873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6874_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_6871_) == 0 {
                    lean_dec(v_f_6869_);
                    return v_x_6870_;
                } else {
                    v_head_6872_ = lean_ctor_get(v_x_6871_, 0);
                    lean_inc(v_head_6872_);
                    v_tail_6873_ = lean_ctor_get(v_x_6871_, 1);
                    lean_inc(v_tail_6873_);
                    lean_dec_ref_known(v_x_6871_, 2);
                    lean_inc(v_f_6869_);
                    v___x_6874_ = lean_apply_2(v_f_6869_, v_x_6870_, v_head_6872_);
                    v_x_6870_ = v___x_6874_;
                    v_x_6871_ = v_tail_6873_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl(
    mut v_00_u03b1_6876_: *mut LeanObject,
    mut v_00_u03b2_6877_: *mut LeanObject,
    mut v_f_6878_: *mut LeanObject,
    mut v_x_6879_: *mut LeanObject,
    mut v_x_6880_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6881_: *mut LeanObject = core::ptr::null_mut();
    v___x_6881_ = l_List_foldl___redArg(v_f_6878_, v_x_6879_, v_x_6880_);
    return v___x_6881_;
}
pub unsafe fn l_List_concat___redArg(
    mut v_x_6882_: *mut LeanObject,
    mut v_x_6883_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6884_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_6885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_6886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6889_: u8 = 0;
    let mut v___x_6890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6893_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6894_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_6882_) == 0 {
                    v___x_6884_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_6884_, 0, v_x_6883_);
                    lean_ctor_set(v___x_6884_, 1, v_x_6882_);
                    return v___x_6884_;
                } else {
                    v_head_6885_ = lean_ctor_get(v_x_6882_, 0);
                    v_tail_6886_ = lean_ctor_get(v_x_6882_, 1);
                    v_isSharedCheck_6894_ = (!lean_is_exclusive(v_x_6882_)) as u8;
                    if v_isSharedCheck_6894_ == 0 {
                        v___x_6888_ = v_x_6882_;
                        v_isShared_6889_ = v_isSharedCheck_6894_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_6886_);
                        lean_inc(v_head_6885_);
                        lean_dec(v_x_6882_);
                        v___x_6888_ = lean_box(0);
                        v_isShared_6889_ = v_isSharedCheck_6894_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6890_ = l_List_concat___redArg(v_tail_6886_, v_x_6883_);
                if v_isShared_6889_ == 0 {
                    lean_ctor_set(v___x_6888_, 1, v___x_6890_);
                    v___x_6892_ = v___x_6888_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6893_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6893_, 0, v_head_6885_);
                    lean_ctor_set(v_reuseFailAlloc_6893_, 1, v___x_6890_);
                    v___x_6892_ = v_reuseFailAlloc_6893_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6892_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_concat(
    mut v_00_u03b1_6895_: *mut LeanObject,
    mut v_x_6896_: *mut LeanObject,
    mut v_x_6897_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6898_: *mut LeanObject = core::ptr::null_mut();
    v___x_6898_ = l_List_concat___redArg(v_x_6896_, v_x_6897_);
    return v___x_6898_;
}
pub unsafe fn l_List_append___redArg(
    mut v_x_6899_: *mut LeanObject,
    mut v_x_6900_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_6901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_6902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6904_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6905_: u8 = 0;
    let mut v___x_6906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6908_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6909_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6910_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_6899_) == 0 {
                    lean_inc(v_x_6900_);
                    return v_x_6900_;
                } else {
                    v_head_6901_ = lean_ctor_get(v_x_6899_, 0);
                    v_tail_6902_ = lean_ctor_get(v_x_6899_, 1);
                    v_isSharedCheck_6910_ = (!lean_is_exclusive(v_x_6899_)) as u8;
                    if v_isSharedCheck_6910_ == 0 {
                        v___x_6904_ = v_x_6899_;
                        v_isShared_6905_ = v_isSharedCheck_6910_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_6902_);
                        lean_inc(v_head_6901_);
                        lean_dec(v_x_6899_);
                        v___x_6904_ = lean_box(0);
                        v_isShared_6905_ = v_isSharedCheck_6910_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6906_ = l_List_append___redArg(v_tail_6902_, v_x_6900_);
                if v_isShared_6905_ == 0 {
                    lean_ctor_set(v___x_6904_, 1, v___x_6906_);
                    v___x_6908_ = v___x_6904_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6909_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6909_, 0, v_head_6901_);
                    lean_ctor_set(v_reuseFailAlloc_6909_, 1, v___x_6906_);
                    v___x_6908_ = v_reuseFailAlloc_6909_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6908_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_append___redArg___boxed(
    mut v_x_6911_: *mut LeanObject,
    mut v_x_6912_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6913_: *mut LeanObject = core::ptr::null_mut();
    v_res_6913_ = l_List_append___redArg(v_x_6911_, v_x_6912_);
    lean_dec(v_x_6912_);
    return v_res_6913_;
}
pub unsafe fn l_List_append(
    mut v_00_u03b1_6914_: *mut LeanObject,
    mut v_x_6915_: *mut LeanObject,
    mut v_x_6916_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6917_: *mut LeanObject = core::ptr::null_mut();
    v___x_6917_ = l_List_append___redArg(v_x_6915_, v_x_6916_);
    return v___x_6917_;
}
pub unsafe fn l_List_append___boxed(
    mut v_00_u03b1_6918_: *mut LeanObject,
    mut v_x_6919_: *mut LeanObject,
    mut v_x_6920_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6921_: *mut LeanObject = core::ptr::null_mut();
    v_res_6921_ = l_List_append(v_00_u03b1_6918_, v_x_6919_, v_x_6920_);
    lean_dec(v_x_6920_);
    return v_res_6921_;
}
pub unsafe fn l_List_map___redArg(
    mut v_f_6922_: *mut LeanObject,
    mut v_x_6923_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6924_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_6925_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_6926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6928_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6929_: u8 = 0;
    let mut v___x_6930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6933_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6935_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_6923_) == 0 {
                    lean_dec(v_f_6922_);
                    v___x_6924_ = lean_box(0);
                    return v___x_6924_;
                } else {
                    v_head_6925_ = lean_ctor_get(v_x_6923_, 0);
                    v_tail_6926_ = lean_ctor_get(v_x_6923_, 1);
                    v_isSharedCheck_6935_ = (!lean_is_exclusive(v_x_6923_)) as u8;
                    if v_isSharedCheck_6935_ == 0 {
                        v___x_6928_ = v_x_6923_;
                        v_isShared_6929_ = v_isSharedCheck_6935_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_6926_);
                        lean_inc(v_head_6925_);
                        lean_dec(v_x_6923_);
                        v___x_6928_ = lean_box(0);
                        v_isShared_6929_ = v_isSharedCheck_6935_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_f_6922_);
                v___x_6930_ = lean_apply_1(v_f_6922_, v_head_6925_);
                v___x_6931_ = l_List_map___redArg(v_f_6922_, v_tail_6926_);
                if v_isShared_6929_ == 0 {
                    lean_ctor_set(v___x_6928_, 1, v___x_6931_);
                    lean_ctor_set(v___x_6928_, 0, v___x_6930_);
                    v___x_6933_ = v___x_6928_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6934_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6934_, 0, v___x_6930_);
                    lean_ctor_set(v_reuseFailAlloc_6934_, 1, v___x_6931_);
                    v___x_6933_ = v_reuseFailAlloc_6934_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6933_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_map(
    mut v_00_u03b1_6936_: *mut LeanObject,
    mut v_00_u03b2_6937_: *mut LeanObject,
    mut v_f_6938_: *mut LeanObject,
    mut v_x_6939_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6940_: *mut LeanObject = core::ptr::null_mut();
    v___x_6940_ = l_List_map___redArg(v_f_6938_, v_x_6939_);
    return v___x_6940_;
}
pub unsafe fn l_Array_toList___boxed(
    mut v_00_u03b1_6943_: *mut LeanObject,
    mut v_self_6944_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6945_: *mut LeanObject = core::ptr::null_mut();
    v_res_6945_ = lean_array_to_list(v_self_6944_);
    return v_res_6945_;
}
pub unsafe fn l_Array_mk___boxed(
    mut v_00_u03b1_6948_: *mut LeanObject,
    mut v_toList_6949_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6950_: *mut LeanObject = core::ptr::null_mut();
    v_res_6950_ = lean_array_mk(v_toList_6949_);
    return v_res_6950_;
}
pub unsafe fn l_List_toArray___redArg(mut v_xs_6951_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_6952_: *mut LeanObject = core::ptr::null_mut();
    v___x_6952_ = lean_array_mk(v_xs_6951_);
    return v___x_6952_;
}
pub unsafe fn l_List_toArray(
    mut v_00_u03b1_6953_: *mut LeanObject,
    mut v_xs_6954_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6955_: *mut LeanObject = core::ptr::null_mut();
    v___x_6955_ = lean_array_mk(v_xs_6954_);
    return v___x_6955_;
}
pub unsafe fn l_Array_mkEmpty___boxed(
    mut v_00_u03b1_6958_: *mut LeanObject,
    mut v_c_6959_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6960_: *mut LeanObject = core::ptr::null_mut();
    v_res_6960_ = lean_mk_empty_array_with_capacity(v_c_6959_);
    lean_dec(v_c_6959_);
    return v_res_6960_;
}
pub unsafe fn l_Array_emptyWithCapacity___boxed(
    mut v_00_u03b1_6963_: *mut LeanObject,
    mut v_c_6964_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6965_: *mut LeanObject = core::ptr::null_mut();
    v_res_6965_ = lean_mk_empty_array_with_capacity(v_c_6964_);
    lean_dec(v_c_6964_);
    return v_res_6965_;
}
pub unsafe fn l_Array_empty(mut v_00_u03b1_6968_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_6969_: *mut LeanObject = core::ptr::null_mut();
    v___x_6969_ = l_Array_empty___closed__0;
    return v___x_6969_;
}
pub unsafe fn l_Array_size___boxed(
    mut v_00_u03b1_6972_: *mut LeanObject,
    mut v_a_6973_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6974_: *mut LeanObject = core::ptr::null_mut();
    v_res_6974_ = lean_array_get_size(v_a_6973_);
    lean_dec_ref(v_a_6973_);
    return v_res_6974_;
}
pub unsafe fn l_Array_getInternalBorrowed___boxed(
    mut v_00_u03b1_6979_: *mut LeanObject,
    mut v_a_6980_: *mut LeanObject,
    mut v_i_6981_: *mut LeanObject,
    mut v_h_6982_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6983_: *mut LeanObject = core::ptr::null_mut();
    v_res_6983_ = lean_array_fget_borrowed(v_a_6980_, v_i_6981_);
    lean_dec(v_i_6981_);
    lean_dec_ref(v_a_6980_);
    return v_res_6983_;
}
pub unsafe fn l_Array_getInternal___boxed(
    mut v_00_u03b1_6988_: *mut LeanObject,
    mut v_a_6989_: *mut LeanObject,
    mut v_i_6990_: *mut LeanObject,
    mut v_h_6991_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6992_: *mut LeanObject = core::ptr::null_mut();
    v_res_6992_ = lean_array_fget(v_a_6989_, v_i_6990_);
    lean_dec(v_i_6990_);
    lean_dec_ref(v_a_6989_);
    return v_res_6992_;
}
pub unsafe fn l_Array_getD___redArg(
    mut v_a_6993_: *mut LeanObject,
    mut v_i_6994_: *mut LeanObject,
    mut v_v_u2080_6995_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6997_: u8 = 0;
    v___x_6996_ = lean_array_get_size(v_a_6993_);
    v___x_6997_ = lean_nat_dec_lt(v_i_6994_, v___x_6996_);
    if v___x_6997_ == 0 {
        lean_inc(v_v_u2080_6995_);
        return v_v_u2080_6995_;
    } else {
        let mut v___x_6998_: *mut LeanObject = core::ptr::null_mut();
        v___x_6998_ = lean_array_fget_borrowed(v_a_6993_, v_i_6994_);
        lean_inc(v___x_6998_);
        return v___x_6998_;
    }
}
pub unsafe fn l_Array_getD___redArg___boxed(
    mut v_a_6999_: *mut LeanObject,
    mut v_i_7000_: *mut LeanObject,
    mut v_v_u2080_7001_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7002_: *mut LeanObject = core::ptr::null_mut();
    v_res_7002_ = l_Array_getD___redArg(v_a_6999_, v_i_7000_, v_v_u2080_7001_);
    lean_dec(v_v_u2080_7001_);
    lean_dec(v_i_7000_);
    lean_dec_ref(v_a_6999_);
    return v_res_7002_;
}
pub unsafe fn l_Array_getD(
    mut v_00_u03b1_7003_: *mut LeanObject,
    mut v_a_7004_: *mut LeanObject,
    mut v_i_7005_: *mut LeanObject,
    mut v_v_u2080_7006_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7008_: u8 = 0;
    v___x_7007_ = lean_array_get_size(v_a_7004_);
    v___x_7008_ = lean_nat_dec_lt(v_i_7005_, v___x_7007_);
    if v___x_7008_ == 0 {
        lean_inc(v_v_u2080_7006_);
        return v_v_u2080_7006_;
    } else {
        let mut v___x_7009_: *mut LeanObject = core::ptr::null_mut();
        v___x_7009_ = lean_array_fget_borrowed(v_a_7004_, v_i_7005_);
        lean_inc(v___x_7009_);
        return v___x_7009_;
    }
}
pub unsafe fn l_Array_getD___boxed(
    mut v_00_u03b1_7010_: *mut LeanObject,
    mut v_a_7011_: *mut LeanObject,
    mut v_i_7012_: *mut LeanObject,
    mut v_v_u2080_7013_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7014_: *mut LeanObject = core::ptr::null_mut();
    v_res_7014_ = l_Array_getD(v_00_u03b1_7010_, v_a_7011_, v_i_7012_, v_v_u2080_7013_);
    lean_dec(v_v_u2080_7013_);
    lean_dec(v_i_7012_);
    lean_dec_ref(v_a_7011_);
    return v_res_7014_;
}
pub unsafe fn l_Array_get_x21InternalBorrowed___boxed(
    mut v_00_u03b1_7019_: *mut LeanObject,
    mut v_inst_00___x40_Init_Prelude_62786769____hygCtx___hyg_7020_: *mut LeanObject,
    mut v_a_7021_: *mut LeanObject,
    mut v_i_7022_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7023_: *mut LeanObject = core::ptr::null_mut();
    v_res_7023_ = lean_array_get_borrowed(
        v_inst_00___x40_Init_Prelude_62786769____hygCtx___hyg_7020_,
        v_a_7021_,
        v_i_7022_,
    );
    lean_dec(v_i_7022_);
    lean_dec_ref(v_a_7021_);
    lean_dec(v_inst_00___x40_Init_Prelude_62786769____hygCtx___hyg_7020_);
    return v_res_7023_;
}
pub unsafe fn l_Array_get_x21Internal___boxed(
    mut v_00_u03b1_7028_: *mut LeanObject,
    mut v_inst_00___x40_Init_Prelude_3471936409____hygCtx___hyg_7029_: *mut LeanObject,
    mut v_a_7030_: *mut LeanObject,
    mut v_i_7031_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7032_: *mut LeanObject = core::ptr::null_mut();
    v_res_7032_ = lean_array_get(
        v_inst_00___x40_Init_Prelude_3471936409____hygCtx___hyg_7029_,
        v_a_7030_,
        v_i_7031_,
    );
    lean_dec(v_i_7031_);
    lean_dec_ref(v_a_7030_);
    lean_dec(v_inst_00___x40_Init_Prelude_3471936409____hygCtx___hyg_7029_);
    return v_res_7032_;
}
pub unsafe fn l_Array_push___boxed(
    mut v_00_u03b1_7036_: *mut LeanObject,
    mut v_a_7037_: *mut LeanObject,
    mut v_v_7038_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7039_: *mut LeanObject = core::ptr::null_mut();
    v_res_7039_ = lean_array_push(v_a_7037_, v_v_7038_);
    return v_res_7039_;
}
pub unsafe fn l_Array_mkArray0(mut v_00_u03b1_7040_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_7041_: *mut LeanObject = core::ptr::null_mut();
    v___x_7041_ = l_Array_empty___closed__0;
    return v___x_7041_;
}
pub unsafe fn l_Array_mkArray1___redArg(mut v_a_u2081_7042_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_7043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7045_: *mut LeanObject = core::ptr::null_mut();
    v___x_7043_ = lean_unsigned_to_nat(1);
    v___x_7044_ = lean_mk_empty_array_with_capacity(v___x_7043_);
    v___x_7045_ = lean_array_push(v___x_7044_, v_a_u2081_7042_);
    return v___x_7045_;
}
pub unsafe fn l_Array_mkArray1(
    mut v_00_u03b1_7046_: *mut LeanObject,
    mut v_a_u2081_7047_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7048_: *mut LeanObject = core::ptr::null_mut();
    v___x_7048_ = l_Array_mkArray1___redArg(v_a_u2081_7047_);
    return v___x_7048_;
}
pub unsafe fn l_Array_mkArray2___redArg(
    mut v_a_u2081_7049_: *mut LeanObject,
    mut v_a_u2082_7050_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7054_: *mut LeanObject = core::ptr::null_mut();
    v___x_7051_ = lean_unsigned_to_nat(2);
    v___x_7052_ = lean_mk_empty_array_with_capacity(v___x_7051_);
    v___x_7053_ = lean_array_push(v___x_7052_, v_a_u2081_7049_);
    v___x_7054_ = lean_array_push(v___x_7053_, v_a_u2082_7050_);
    return v___x_7054_;
}
pub unsafe fn l_Array_mkArray2(
    mut v_00_u03b1_7055_: *mut LeanObject,
    mut v_a_u2081_7056_: *mut LeanObject,
    mut v_a_u2082_7057_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7058_: *mut LeanObject = core::ptr::null_mut();
    v___x_7058_ = l_Array_mkArray2___redArg(v_a_u2081_7056_, v_a_u2082_7057_);
    return v___x_7058_;
}
pub unsafe fn l_Array_mkArray3___redArg(
    mut v_a_u2081_7059_: *mut LeanObject,
    mut v_a_u2082_7060_: *mut LeanObject,
    mut v_a_u2083_7061_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7066_: *mut LeanObject = core::ptr::null_mut();
    v___x_7062_ = lean_unsigned_to_nat(3);
    v___x_7063_ = lean_mk_empty_array_with_capacity(v___x_7062_);
    v___x_7064_ = lean_array_push(v___x_7063_, v_a_u2081_7059_);
    v___x_7065_ = lean_array_push(v___x_7064_, v_a_u2082_7060_);
    v___x_7066_ = lean_array_push(v___x_7065_, v_a_u2083_7061_);
    return v___x_7066_;
}
pub unsafe fn l_Array_mkArray3(
    mut v_00_u03b1_7067_: *mut LeanObject,
    mut v_a_u2081_7068_: *mut LeanObject,
    mut v_a_u2082_7069_: *mut LeanObject,
    mut v_a_u2083_7070_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7071_: *mut LeanObject = core::ptr::null_mut();
    v___x_7071_ = l_Array_mkArray3___redArg(v_a_u2081_7068_, v_a_u2082_7069_, v_a_u2083_7070_);
    return v___x_7071_;
}
pub unsafe fn l_Array_mkArray4___redArg(
    mut v_a_u2081_7072_: *mut LeanObject,
    mut v_a_u2082_7073_: *mut LeanObject,
    mut v_a_u2083_7074_: *mut LeanObject,
    mut v_a_u2084_7075_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7081_: *mut LeanObject = core::ptr::null_mut();
    v___x_7076_ = lean_unsigned_to_nat(4);
    v___x_7077_ = lean_mk_empty_array_with_capacity(v___x_7076_);
    v___x_7078_ = lean_array_push(v___x_7077_, v_a_u2081_7072_);
    v___x_7079_ = lean_array_push(v___x_7078_, v_a_u2082_7073_);
    v___x_7080_ = lean_array_push(v___x_7079_, v_a_u2083_7074_);
    v___x_7081_ = lean_array_push(v___x_7080_, v_a_u2084_7075_);
    return v___x_7081_;
}
pub unsafe fn l_Array_mkArray4(
    mut v_00_u03b1_7082_: *mut LeanObject,
    mut v_a_u2081_7083_: *mut LeanObject,
    mut v_a_u2082_7084_: *mut LeanObject,
    mut v_a_u2083_7085_: *mut LeanObject,
    mut v_a_u2084_7086_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7087_: *mut LeanObject = core::ptr::null_mut();
    v___x_7087_ = l_Array_mkArray4___redArg(
        v_a_u2081_7083_,
        v_a_u2082_7084_,
        v_a_u2083_7085_,
        v_a_u2084_7086_,
    );
    return v___x_7087_;
}
pub unsafe fn l_Array_mkArray5___redArg(
    mut v_a_u2081_7088_: *mut LeanObject,
    mut v_a_u2082_7089_: *mut LeanObject,
    mut v_a_u2083_7090_: *mut LeanObject,
    mut v_a_u2084_7091_: *mut LeanObject,
    mut v_a_u2085_7092_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7099_: *mut LeanObject = core::ptr::null_mut();
    v___x_7093_ = lean_unsigned_to_nat(5);
    v___x_7094_ = lean_mk_empty_array_with_capacity(v___x_7093_);
    v___x_7095_ = lean_array_push(v___x_7094_, v_a_u2081_7088_);
    v___x_7096_ = lean_array_push(v___x_7095_, v_a_u2082_7089_);
    v___x_7097_ = lean_array_push(v___x_7096_, v_a_u2083_7090_);
    v___x_7098_ = lean_array_push(v___x_7097_, v_a_u2084_7091_);
    v___x_7099_ = lean_array_push(v___x_7098_, v_a_u2085_7092_);
    return v___x_7099_;
}
pub unsafe fn l_Array_mkArray5(
    mut v_00_u03b1_7100_: *mut LeanObject,
    mut v_a_u2081_7101_: *mut LeanObject,
    mut v_a_u2082_7102_: *mut LeanObject,
    mut v_a_u2083_7103_: *mut LeanObject,
    mut v_a_u2084_7104_: *mut LeanObject,
    mut v_a_u2085_7105_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7106_: *mut LeanObject = core::ptr::null_mut();
    v___x_7106_ = l_Array_mkArray5___redArg(
        v_a_u2081_7101_,
        v_a_u2082_7102_,
        v_a_u2083_7103_,
        v_a_u2084_7104_,
        v_a_u2085_7105_,
    );
    return v___x_7106_;
}
pub unsafe fn l_Array_mkArray6___redArg(
    mut v_a_u2081_7107_: *mut LeanObject,
    mut v_a_u2082_7108_: *mut LeanObject,
    mut v_a_u2083_7109_: *mut LeanObject,
    mut v_a_u2084_7110_: *mut LeanObject,
    mut v_a_u2085_7111_: *mut LeanObject,
    mut v_a_u2086_7112_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7120_: *mut LeanObject = core::ptr::null_mut();
    v___x_7113_ = lean_unsigned_to_nat(6);
    v___x_7114_ = lean_mk_empty_array_with_capacity(v___x_7113_);
    v___x_7115_ = lean_array_push(v___x_7114_, v_a_u2081_7107_);
    v___x_7116_ = lean_array_push(v___x_7115_, v_a_u2082_7108_);
    v___x_7117_ = lean_array_push(v___x_7116_, v_a_u2083_7109_);
    v___x_7118_ = lean_array_push(v___x_7117_, v_a_u2084_7110_);
    v___x_7119_ = lean_array_push(v___x_7118_, v_a_u2085_7111_);
    v___x_7120_ = lean_array_push(v___x_7119_, v_a_u2086_7112_);
    return v___x_7120_;
}
pub unsafe fn l_Array_mkArray6(
    mut v_00_u03b1_7121_: *mut LeanObject,
    mut v_a_u2081_7122_: *mut LeanObject,
    mut v_a_u2082_7123_: *mut LeanObject,
    mut v_a_u2083_7124_: *mut LeanObject,
    mut v_a_u2084_7125_: *mut LeanObject,
    mut v_a_u2085_7126_: *mut LeanObject,
    mut v_a_u2086_7127_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7128_: *mut LeanObject = core::ptr::null_mut();
    v___x_7128_ = l_Array_mkArray6___redArg(
        v_a_u2081_7122_,
        v_a_u2082_7123_,
        v_a_u2083_7124_,
        v_a_u2084_7125_,
        v_a_u2085_7126_,
        v_a_u2086_7127_,
    );
    return v___x_7128_;
}
pub unsafe fn l_Array_mkArray7___redArg(
    mut v_a_u2081_7129_: *mut LeanObject,
    mut v_a_u2082_7130_: *mut LeanObject,
    mut v_a_u2083_7131_: *mut LeanObject,
    mut v_a_u2084_7132_: *mut LeanObject,
    mut v_a_u2085_7133_: *mut LeanObject,
    mut v_a_u2086_7134_: *mut LeanObject,
    mut v_a_u2087_7135_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7144_: *mut LeanObject = core::ptr::null_mut();
    v___x_7136_ = lean_unsigned_to_nat(7);
    v___x_7137_ = lean_mk_empty_array_with_capacity(v___x_7136_);
    v___x_7138_ = lean_array_push(v___x_7137_, v_a_u2081_7129_);
    v___x_7139_ = lean_array_push(v___x_7138_, v_a_u2082_7130_);
    v___x_7140_ = lean_array_push(v___x_7139_, v_a_u2083_7131_);
    v___x_7141_ = lean_array_push(v___x_7140_, v_a_u2084_7132_);
    v___x_7142_ = lean_array_push(v___x_7141_, v_a_u2085_7133_);
    v___x_7143_ = lean_array_push(v___x_7142_, v_a_u2086_7134_);
    v___x_7144_ = lean_array_push(v___x_7143_, v_a_u2087_7135_);
    return v___x_7144_;
}
pub unsafe fn l_Array_mkArray7(
    mut v_00_u03b1_7145_: *mut LeanObject,
    mut v_a_u2081_7146_: *mut LeanObject,
    mut v_a_u2082_7147_: *mut LeanObject,
    mut v_a_u2083_7148_: *mut LeanObject,
    mut v_a_u2084_7149_: *mut LeanObject,
    mut v_a_u2085_7150_: *mut LeanObject,
    mut v_a_u2086_7151_: *mut LeanObject,
    mut v_a_u2087_7152_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7153_: *mut LeanObject = core::ptr::null_mut();
    v___x_7153_ = l_Array_mkArray7___redArg(
        v_a_u2081_7146_,
        v_a_u2082_7147_,
        v_a_u2083_7148_,
        v_a_u2084_7149_,
        v_a_u2085_7150_,
        v_a_u2086_7151_,
        v_a_u2087_7152_,
    );
    return v___x_7153_;
}
pub unsafe fn l_Array_mkArray8___redArg(
    mut v_a_u2081_7154_: *mut LeanObject,
    mut v_a_u2082_7155_: *mut LeanObject,
    mut v_a_u2083_7156_: *mut LeanObject,
    mut v_a_u2084_7157_: *mut LeanObject,
    mut v_a_u2085_7158_: *mut LeanObject,
    mut v_a_u2086_7159_: *mut LeanObject,
    mut v_a_u2087_7160_: *mut LeanObject,
    mut v_a_u2088_7161_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7171_: *mut LeanObject = core::ptr::null_mut();
    v___x_7162_ = lean_unsigned_to_nat(8);
    v___x_7163_ = lean_mk_empty_array_with_capacity(v___x_7162_);
    v___x_7164_ = lean_array_push(v___x_7163_, v_a_u2081_7154_);
    v___x_7165_ = lean_array_push(v___x_7164_, v_a_u2082_7155_);
    v___x_7166_ = lean_array_push(v___x_7165_, v_a_u2083_7156_);
    v___x_7167_ = lean_array_push(v___x_7166_, v_a_u2084_7157_);
    v___x_7168_ = lean_array_push(v___x_7167_, v_a_u2085_7158_);
    v___x_7169_ = lean_array_push(v___x_7168_, v_a_u2086_7159_);
    v___x_7170_ = lean_array_push(v___x_7169_, v_a_u2087_7160_);
    v___x_7171_ = lean_array_push(v___x_7170_, v_a_u2088_7161_);
    return v___x_7171_;
}
pub unsafe fn l_Array_mkArray8(
    mut v_00_u03b1_7172_: *mut LeanObject,
    mut v_a_u2081_7173_: *mut LeanObject,
    mut v_a_u2082_7174_: *mut LeanObject,
    mut v_a_u2083_7175_: *mut LeanObject,
    mut v_a_u2084_7176_: *mut LeanObject,
    mut v_a_u2085_7177_: *mut LeanObject,
    mut v_a_u2086_7178_: *mut LeanObject,
    mut v_a_u2087_7179_: *mut LeanObject,
    mut v_a_u2088_7180_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7181_: *mut LeanObject = core::ptr::null_mut();
    v___x_7181_ = l_Array_mkArray8___redArg(
        v_a_u2081_7173_,
        v_a_u2082_7174_,
        v_a_u2083_7175_,
        v_a_u2084_7176_,
        v_a_u2085_7177_,
        v_a_u2086_7178_,
        v_a_u2087_7179_,
        v_a_u2088_7180_,
    );
    return v___x_7181_;
}
pub unsafe fn l_Array_appendCore_loop___redArg(
    mut v_bs_7182_: *mut LeanObject,
    mut v_i_7183_: *mut LeanObject,
    mut v_j_7184_: *mut LeanObject,
    mut v_as_7185_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7187_: u8 = 0;
    let mut v_zero_7188_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_7189_: u8 = 0;
    let mut v_one_7190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_7191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7194_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7186_ = lean_array_get_size(v_bs_7182_);
                v___x_7187_ = lean_nat_dec_lt(v_j_7184_, v___x_7186_);
                if v___x_7187_ == 0 {
                    lean_dec(v_j_7184_);
                    lean_dec(v_i_7183_);
                    return v_as_7185_;
                } else {
                    v_zero_7188_ = lean_unsigned_to_nat(0);
                    v_isZero_7189_ = lean_nat_dec_eq(v_i_7183_, v_zero_7188_);
                    if v_isZero_7189_ == 1 {
                        lean_dec(v_j_7184_);
                        lean_dec(v_i_7183_);
                        return v_as_7185_;
                    } else {
                        v_one_7190_ = lean_unsigned_to_nat(1);
                        v_n_7191_ = lean_nat_sub(v_i_7183_, v_one_7190_);
                        lean_dec(v_i_7183_);
                        v___x_7192_ = lean_nat_add(v_j_7184_, v_one_7190_);
                        v___x_7193_ = lean_array_fget_borrowed(v_bs_7182_, v_j_7184_);
                        lean_dec(v_j_7184_);
                        lean_inc(v___x_7193_);
                        v___x_7194_ = lean_array_push(v_as_7185_, v___x_7193_);
                        v_i_7183_ = v_n_7191_;
                        v_j_7184_ = v___x_7192_;
                        v_as_7185_ = v___x_7194_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_appendCore_loop___redArg___boxed(
    mut v_bs_7196_: *mut LeanObject,
    mut v_i_7197_: *mut LeanObject,
    mut v_j_7198_: *mut LeanObject,
    mut v_as_7199_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7200_: *mut LeanObject = core::ptr::null_mut();
    v_res_7200_ = l_Array_appendCore_loop___redArg(v_bs_7196_, v_i_7197_, v_j_7198_, v_as_7199_);
    lean_dec_ref(v_bs_7196_);
    return v_res_7200_;
}
pub unsafe fn l_Array_appendCore_loop(
    mut v_00_u03b1_7201_: *mut LeanObject,
    mut v_bs_7202_: *mut LeanObject,
    mut v_i_7203_: *mut LeanObject,
    mut v_j_7204_: *mut LeanObject,
    mut v_as_7205_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7206_: *mut LeanObject = core::ptr::null_mut();
    v___x_7206_ = l_Array_appendCore_loop___redArg(v_bs_7202_, v_i_7203_, v_j_7204_, v_as_7205_);
    return v___x_7206_;
}
pub unsafe fn l_Array_appendCore_loop___boxed(
    mut v_00_u03b1_7207_: *mut LeanObject,
    mut v_bs_7208_: *mut LeanObject,
    mut v_i_7209_: *mut LeanObject,
    mut v_j_7210_: *mut LeanObject,
    mut v_as_7211_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7212_: *mut LeanObject = core::ptr::null_mut();
    v_res_7212_ = l_Array_appendCore_loop(
        v_00_u03b1_7207_,
        v_bs_7208_,
        v_i_7209_,
        v_j_7210_,
        v_as_7211_,
    );
    lean_dec_ref(v_bs_7208_);
    return v_res_7212_;
}
pub unsafe fn l_Array_appendCore___redArg(
    mut v_as_7213_: *mut LeanObject,
    mut v_bs_7214_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7217_: *mut LeanObject = core::ptr::null_mut();
    v___x_7215_ = lean_array_get_size(v_bs_7214_);
    v___x_7216_ = lean_unsigned_to_nat(0);
    v___x_7217_ =
        l_Array_appendCore_loop___redArg(v_bs_7214_, v___x_7215_, v___x_7216_, v_as_7213_);
    return v___x_7217_;
}
pub unsafe fn l_Array_appendCore___redArg___boxed(
    mut v_as_7218_: *mut LeanObject,
    mut v_bs_7219_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7220_: *mut LeanObject = core::ptr::null_mut();
    v_res_7220_ = l_Array_appendCore___redArg(v_as_7218_, v_bs_7219_);
    lean_dec_ref(v_bs_7219_);
    return v_res_7220_;
}
pub unsafe fn l_Array_appendCore(
    mut v_00_u03b1_7221_: *mut LeanObject,
    mut v_as_7222_: *mut LeanObject,
    mut v_bs_7223_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7224_: *mut LeanObject = core::ptr::null_mut();
    v___x_7224_ = l_Array_appendCore___redArg(v_as_7222_, v_bs_7223_);
    return v___x_7224_;
}
pub unsafe fn l_Array_appendCore___boxed(
    mut v_00_u03b1_7225_: *mut LeanObject,
    mut v_as_7226_: *mut LeanObject,
    mut v_bs_7227_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7228_: *mut LeanObject = core::ptr::null_mut();
    v_res_7228_ = l_Array_appendCore(v_00_u03b1_7225_, v_as_7226_, v_bs_7227_);
    lean_dec_ref(v_bs_7227_);
    return v_res_7228_;
}
pub unsafe fn l_Array_extract_loop___redArg(
    mut v_as_7229_: *mut LeanObject,
    mut v_i_7230_: *mut LeanObject,
    mut v_j_7231_: *mut LeanObject,
    mut v_bs_7232_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7234_: u8 = 0;
    let mut v_zero_7235_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_7236_: u8 = 0;
    let mut v_one_7237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_7238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7241_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7233_ = lean_array_get_size(v_as_7229_);
                v___x_7234_ = lean_nat_dec_lt(v_j_7231_, v___x_7233_);
                if v___x_7234_ == 0 {
                    lean_dec(v_j_7231_);
                    lean_dec(v_i_7230_);
                    return v_bs_7232_;
                } else {
                    v_zero_7235_ = lean_unsigned_to_nat(0);
                    v_isZero_7236_ = lean_nat_dec_eq(v_i_7230_, v_zero_7235_);
                    if v_isZero_7236_ == 1 {
                        lean_dec(v_j_7231_);
                        lean_dec(v_i_7230_);
                        return v_bs_7232_;
                    } else {
                        v_one_7237_ = lean_unsigned_to_nat(1);
                        v_n_7238_ = lean_nat_sub(v_i_7230_, v_one_7237_);
                        lean_dec(v_i_7230_);
                        v___x_7239_ = lean_nat_add(v_j_7231_, v_one_7237_);
                        v___x_7240_ = lean_array_fget_borrowed(v_as_7229_, v_j_7231_);
                        lean_dec(v_j_7231_);
                        lean_inc(v___x_7240_);
                        v___x_7241_ = lean_array_push(v_bs_7232_, v___x_7240_);
                        v_i_7230_ = v_n_7238_;
                        v_j_7231_ = v___x_7239_;
                        v_bs_7232_ = v___x_7241_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_extract_loop___redArg___boxed(
    mut v_as_7243_: *mut LeanObject,
    mut v_i_7244_: *mut LeanObject,
    mut v_j_7245_: *mut LeanObject,
    mut v_bs_7246_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7247_: *mut LeanObject = core::ptr::null_mut();
    v_res_7247_ = l_Array_extract_loop___redArg(v_as_7243_, v_i_7244_, v_j_7245_, v_bs_7246_);
    lean_dec_ref(v_as_7243_);
    return v_res_7247_;
}
pub unsafe fn l_Array_extract_loop(
    mut v_00_u03b1_7248_: *mut LeanObject,
    mut v_as_7249_: *mut LeanObject,
    mut v_i_7250_: *mut LeanObject,
    mut v_j_7251_: *mut LeanObject,
    mut v_bs_7252_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7253_: *mut LeanObject = core::ptr::null_mut();
    v___x_7253_ = l_Array_extract_loop___redArg(v_as_7249_, v_i_7250_, v_j_7251_, v_bs_7252_);
    return v___x_7253_;
}
pub unsafe fn l_Array_extract_loop___boxed(
    mut v_00_u03b1_7254_: *mut LeanObject,
    mut v_as_7255_: *mut LeanObject,
    mut v_i_7256_: *mut LeanObject,
    mut v_j_7257_: *mut LeanObject,
    mut v_bs_7258_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7259_: *mut LeanObject = core::ptr::null_mut();
    v_res_7259_ = l_Array_extract_loop(
        v_00_u03b1_7254_,
        v_as_7255_,
        v_i_7256_,
        v_j_7257_,
        v_bs_7258_,
    );
    lean_dec_ref(v_as_7255_);
    return v_res_7259_;
}
pub unsafe fn l_Array_extract___redArg(
    mut v_as_7260_: *mut LeanObject,
    mut v_start_7261_: *mut LeanObject,
    mut v_stop_7262_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_7264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_x27_7265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7269_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7268_ = lean_array_get_size(v_as_7260_);
                v___x_7269_ = lean_nat_dec_le(v_stop_7262_, v___x_7268_);
                if v___x_7269_ == 0 {
                    lean_dec(v_stop_7262_);
                    v___y_7264_ = v___x_7268_;
                    state = 1;
                    continue;
                } else {
                    v___y_7264_ = v_stop_7262_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_sz_x27_7265_ = lean_nat_sub(v___y_7264_, v_start_7261_);
                lean_dec(v___y_7264_);
                v___x_7266_ = lean_mk_empty_array_with_capacity(v_sz_x27_7265_);
                v___x_7267_ = l_Array_extract_loop___redArg(
                    v_as_7260_,
                    v_sz_x27_7265_,
                    v_start_7261_,
                    v___x_7266_,
                );
                return v___x_7267_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_extract___redArg___boxed(
    mut v_as_7270_: *mut LeanObject,
    mut v_start_7271_: *mut LeanObject,
    mut v_stop_7272_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7273_: *mut LeanObject = core::ptr::null_mut();
    v_res_7273_ = l_Array_extract___redArg(v_as_7270_, v_start_7271_, v_stop_7272_);
    lean_dec_ref(v_as_7270_);
    return v_res_7273_;
}
pub unsafe fn l_Array_extract(
    mut v_00_u03b1_7274_: *mut LeanObject,
    mut v_as_7275_: *mut LeanObject,
    mut v_start_7276_: *mut LeanObject,
    mut v_stop_7277_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7278_: *mut LeanObject = core::ptr::null_mut();
    v___x_7278_ = l_Array_extract___redArg(v_as_7275_, v_start_7276_, v_stop_7277_);
    return v___x_7278_;
}
pub unsafe fn l_Array_extract___boxed(
    mut v_00_u03b1_7279_: *mut LeanObject,
    mut v_as_7280_: *mut LeanObject,
    mut v_start_7281_: *mut LeanObject,
    mut v_stop_7282_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7283_: *mut LeanObject = core::ptr::null_mut();
    v_res_7283_ = l_Array_extract(v_00_u03b1_7279_, v_as_7280_, v_start_7281_, v_stop_7282_);
    lean_dec_ref(v_as_7280_);
    return v_res_7283_;
}
pub unsafe fn l_ByteArray_mk___boxed(mut v_data_7285_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_7286_: *mut LeanObject = core::ptr::null_mut();
    v_res_7286_ = lean_byte_array_mk(v_data_7285_);
    return v_res_7286_;
}
pub unsafe fn l_ByteArray_data___boxed(mut v_self_7288_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_7289_: *mut LeanObject = core::ptr::null_mut();
    v_res_7289_ = lean_byte_array_data(v_self_7288_);
    return v_res_7289_;
}
pub unsafe fn l_ByteArray_emptyWithCapacity___boxed(
    mut v_c_7291_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7292_: *mut LeanObject = core::ptr::null_mut();
    v_res_7292_ = lean_mk_empty_byte_array(v_c_7291_);
    lean_dec(v_c_7291_);
    return v_res_7292_;
}
pub unsafe fn _init_l_ByteArray_empty___closed__0() -> *mut LeanObject {
    let mut v___x_7293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7294_: *mut LeanObject = core::ptr::null_mut();
    v___x_7293_ = lean_unsigned_to_nat(0);
    v___x_7294_ = lean_mk_empty_byte_array(v___x_7293_);
    return v___x_7294_;
}
pub unsafe fn _init_l_ByteArray_empty() -> *mut LeanObject {
    let mut v___x_7295_: *mut LeanObject = core::ptr::null_mut();
    v___x_7295_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_ByteArray_empty___closed__0),
        core::ptr::addr_of_mut!(l_ByteArray_empty___closed__0_once),
        _init_l_ByteArray_empty___closed__0,
    );
    return v___x_7295_;
}
pub unsafe fn l_ByteArray_push___boxed(
    mut v_a_00___x40___internal___hyg_7298_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_7299_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_00___x40___internal___hyg_2__boxed_7300_: u8 = 0;
    let mut v_res_7301_: *mut LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_2__boxed_7300_ =
        (lean_unbox(v_a_00___x40___internal___hyg_7299_) as u8);
    v_res_7301_ = lean_byte_array_push(
        v_a_00___x40___internal___hyg_7298_,
        v_a_00___x40___internal___hyg_2__boxed_7300_,
    );
    return v_res_7301_;
}
pub unsafe fn l_List_toByteArray_loop(
    mut v_x_7302_: *mut LeanObject,
    mut v_x_7303_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_7304_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_7305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7306_: u8 = 0;
    let mut v___x_7307_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_7302_) == 0 {
                    return v_x_7303_;
                } else {
                    v_head_7304_ = lean_ctor_get(v_x_7302_, 0);
                    v_tail_7305_ = lean_ctor_get(v_x_7302_, 1);
                    v___x_7306_ = (lean_unbox(v_head_7304_) as u8);
                    v___x_7307_ = lean_byte_array_push(v_x_7303_, v___x_7306_);
                    v_x_7302_ = v_tail_7305_;
                    v_x_7303_ = v___x_7307_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_toByteArray_loop___boxed(
    mut v_x_7309_: *mut LeanObject,
    mut v_x_7310_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7311_: *mut LeanObject = core::ptr::null_mut();
    v_res_7311_ = l_List_toByteArray_loop(v_x_7309_, v_x_7310_);
    lean_dec(v_x_7309_);
    return v_res_7311_;
}
pub unsafe fn l_List_toByteArray(mut v_bs_7312_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_7313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7314_: *mut LeanObject = core::ptr::null_mut();
    v___x_7313_ = l_ByteArray_empty;
    v___x_7314_ = l_List_toByteArray_loop(v_bs_7312_, v___x_7313_);
    return v___x_7314_;
}
pub unsafe fn l_List_toByteArray___boxed(mut v_bs_7315_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_7316_: *mut LeanObject = core::ptr::null_mut();
    v_res_7316_ = l_List_toByteArray(v_bs_7315_);
    lean_dec(v_bs_7315_);
    return v_res_7316_;
}
pub unsafe fn l_ByteArray_size___boxed(
    mut v_a_00___x40___internal___hyg_7318_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7319_: *mut LeanObject = core::ptr::null_mut();
    v_res_7319_ = lean_byte_array_size(v_a_00___x40___internal___hyg_7318_);
    lean_dec_ref(v_a_00___x40___internal___hyg_7318_);
    return v_res_7319_;
}
pub unsafe fn l_String_utf8EncodeChar(mut v_c_7320_: u32) -> *mut LeanObject {
    let mut v_v_7321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7323_: u8 = 0;
    v_v_7321_ = lean_uint32_to_nat(v_c_7320_);
    v___x_7322_ = lean_unsigned_to_nat(127);
    v___x_7323_ = lean_nat_dec_le(v_v_7321_, v___x_7322_);
    if v___x_7323_ == 0 {
        let mut v___x_7324_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7325_: u8 = 0;
        v___x_7324_ = lean_unsigned_to_nat(2047);
        v___x_7325_ = lean_nat_dec_le(v_v_7321_, v___x_7324_);
        if v___x_7325_ == 0 {
            let mut v___x_7326_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_7327_: u8 = 0;
            v___x_7326_ = lean_unsigned_to_nat(65535);
            v___x_7327_ = lean_nat_dec_le(v_v_7321_, v___x_7326_);
            if v___x_7327_ == 0 {
                let mut v___x_7328_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_7329_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_7330_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_7331_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_7332_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_7333_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_7334_: u8 = 0;
                let mut v___x_7335_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_7336_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_7337_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_7338_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_7339_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_7340_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_7341_: u8 = 0;
                let mut v___x_7342_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_7343_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_7344_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_7345_: u8 = 0;
                let mut v___x_7346_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_7347_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_7348_: u8 = 0;
                let mut v___x_7349_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_7350_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_7351_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_7352_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_7353_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_7354_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_7355_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_7356_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_7357_: *mut LeanObject = core::ptr::null_mut();
                v___x_7328_ = lean_unsigned_to_nat(262144);
                v___x_7329_ = lean_nat_div(v_v_7321_, v___x_7328_);
                v___x_7330_ = lean_unsigned_to_nat(8);
                v___x_7331_ = lean_nat_mod(v___x_7329_, v___x_7330_);
                lean_dec(v___x_7329_);
                v___x_7332_ = lean_unsigned_to_nat(240);
                v___x_7333_ = lean_nat_add(v___x_7331_, v___x_7332_);
                lean_dec(v___x_7331_);
                v___x_7334_ = lean_uint8_of_nat(v___x_7333_);
                lean_dec(v___x_7333_);
                v___x_7335_ = lean_unsigned_to_nat(4096);
                v___x_7336_ = lean_nat_div(v_v_7321_, v___x_7335_);
                v___x_7337_ = lean_unsigned_to_nat(64);
                v___x_7338_ = lean_nat_mod(v___x_7336_, v___x_7337_);
                lean_dec(v___x_7336_);
                v___x_7339_ = lean_unsigned_to_nat(128);
                v___x_7340_ = lean_nat_add(v___x_7338_, v___x_7339_);
                lean_dec(v___x_7338_);
                v___x_7341_ = lean_uint8_of_nat(v___x_7340_);
                lean_dec(v___x_7340_);
                v___x_7342_ = lean_nat_div(v_v_7321_, v___x_7337_);
                v___x_7343_ = lean_nat_mod(v___x_7342_, v___x_7337_);
                lean_dec(v___x_7342_);
                v___x_7344_ = lean_nat_add(v___x_7343_, v___x_7339_);
                lean_dec(v___x_7343_);
                v___x_7345_ = lean_uint8_of_nat(v___x_7344_);
                lean_dec(v___x_7344_);
                v___x_7346_ = lean_nat_mod(v_v_7321_, v___x_7337_);
                lean_dec(v_v_7321_);
                v___x_7347_ = lean_nat_add(v___x_7346_, v___x_7339_);
                lean_dec(v___x_7346_);
                v___x_7348_ = lean_uint8_of_nat(v___x_7347_);
                lean_dec(v___x_7347_);
                v___x_7349_ = lean_box(0);
                v___x_7350_ = lean_box((v___x_7348_) as usize);
                v___x_7351_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_7351_, 0, v___x_7350_);
                lean_ctor_set(v___x_7351_, 1, v___x_7349_);
                v___x_7352_ = lean_box((v___x_7345_) as usize);
                v___x_7353_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_7353_, 0, v___x_7352_);
                lean_ctor_set(v___x_7353_, 1, v___x_7351_);
                v___x_7354_ = lean_box((v___x_7341_) as usize);
                v___x_7355_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_7355_, 0, v___x_7354_);
                lean_ctor_set(v___x_7355_, 1, v___x_7353_);
                v___x_7356_ = lean_box((v___x_7334_) as usize);
                v___x_7357_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_7357_, 0, v___x_7356_);
                lean_ctor_set(v___x_7357_, 1, v___x_7355_);
                return v___x_7357_;
            } else {
                let mut v___x_7358_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_7359_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_7360_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_7361_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_7362_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_7363_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_7364_: u8 = 0;
                let mut v___x_7365_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_7366_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_7367_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_7368_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_7369_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_7370_: u8 = 0;
                let mut v___x_7371_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_7372_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_7373_: u8 = 0;
                let mut v___x_7374_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_7375_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_7376_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_7377_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_7378_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_7379_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_7380_: *mut LeanObject = core::ptr::null_mut();
                v___x_7358_ = lean_unsigned_to_nat(4096);
                v___x_7359_ = lean_nat_div(v_v_7321_, v___x_7358_);
                v___x_7360_ = lean_unsigned_to_nat(16);
                v___x_7361_ = lean_nat_mod(v___x_7359_, v___x_7360_);
                lean_dec(v___x_7359_);
                v___x_7362_ = lean_unsigned_to_nat(224);
                v___x_7363_ = lean_nat_add(v___x_7361_, v___x_7362_);
                lean_dec(v___x_7361_);
                v___x_7364_ = lean_uint8_of_nat(v___x_7363_);
                lean_dec(v___x_7363_);
                v___x_7365_ = lean_unsigned_to_nat(64);
                v___x_7366_ = lean_nat_div(v_v_7321_, v___x_7365_);
                v___x_7367_ = lean_nat_mod(v___x_7366_, v___x_7365_);
                lean_dec(v___x_7366_);
                v___x_7368_ = lean_unsigned_to_nat(128);
                v___x_7369_ = lean_nat_add(v___x_7367_, v___x_7368_);
                lean_dec(v___x_7367_);
                v___x_7370_ = lean_uint8_of_nat(v___x_7369_);
                lean_dec(v___x_7369_);
                v___x_7371_ = lean_nat_mod(v_v_7321_, v___x_7365_);
                lean_dec(v_v_7321_);
                v___x_7372_ = lean_nat_add(v___x_7371_, v___x_7368_);
                lean_dec(v___x_7371_);
                v___x_7373_ = lean_uint8_of_nat(v___x_7372_);
                lean_dec(v___x_7372_);
                v___x_7374_ = lean_box(0);
                v___x_7375_ = lean_box((v___x_7373_) as usize);
                v___x_7376_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_7376_, 0, v___x_7375_);
                lean_ctor_set(v___x_7376_, 1, v___x_7374_);
                v___x_7377_ = lean_box((v___x_7370_) as usize);
                v___x_7378_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_7378_, 0, v___x_7377_);
                lean_ctor_set(v___x_7378_, 1, v___x_7376_);
                v___x_7379_ = lean_box((v___x_7364_) as usize);
                v___x_7380_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_7380_, 0, v___x_7379_);
                lean_ctor_set(v___x_7380_, 1, v___x_7378_);
                return v___x_7380_;
            }
        } else {
            let mut v___x_7381_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_7382_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_7383_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_7384_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_7385_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_7386_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_7387_: u8 = 0;
            let mut v___x_7388_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_7389_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_7390_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_7391_: u8 = 0;
            let mut v___x_7392_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_7393_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_7394_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_7395_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_7396_: *mut LeanObject = core::ptr::null_mut();
            v___x_7381_ = lean_unsigned_to_nat(64);
            v___x_7382_ = lean_nat_div(v_v_7321_, v___x_7381_);
            v___x_7383_ = lean_unsigned_to_nat(32);
            v___x_7384_ = lean_nat_mod(v___x_7382_, v___x_7383_);
            lean_dec(v___x_7382_);
            v___x_7385_ = lean_unsigned_to_nat(192);
            v___x_7386_ = lean_nat_add(v___x_7384_, v___x_7385_);
            lean_dec(v___x_7384_);
            v___x_7387_ = lean_uint8_of_nat(v___x_7386_);
            lean_dec(v___x_7386_);
            v___x_7388_ = lean_nat_mod(v_v_7321_, v___x_7381_);
            lean_dec(v_v_7321_);
            v___x_7389_ = lean_unsigned_to_nat(128);
            v___x_7390_ = lean_nat_add(v___x_7388_, v___x_7389_);
            lean_dec(v___x_7388_);
            v___x_7391_ = lean_uint8_of_nat(v___x_7390_);
            lean_dec(v___x_7390_);
            v___x_7392_ = lean_box(0);
            v___x_7393_ = lean_box((v___x_7391_) as usize);
            v___x_7394_ = lean_alloc_ctor(1, 2, (0) as u32);
            lean_ctor_set(v___x_7394_, 0, v___x_7393_);
            lean_ctor_set(v___x_7394_, 1, v___x_7392_);
            v___x_7395_ = lean_box((v___x_7387_) as usize);
            v___x_7396_ = lean_alloc_ctor(1, 2, (0) as u32);
            lean_ctor_set(v___x_7396_, 0, v___x_7395_);
            lean_ctor_set(v___x_7396_, 1, v___x_7394_);
            return v___x_7396_;
        }
    } else {
        let mut v___x_7397_: u8 = 0;
        let mut v___x_7398_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7399_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7400_: *mut LeanObject = core::ptr::null_mut();
        v___x_7397_ = lean_uint8_of_nat(v_v_7321_);
        lean_dec(v_v_7321_);
        v___x_7398_ = lean_box(0);
        v___x_7399_ = lean_box((v___x_7397_) as usize);
        v___x_7400_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_7400_, 0, v___x_7399_);
        lean_ctor_set(v___x_7400_, 1, v___x_7398_);
        return v___x_7400_;
    }
}
pub unsafe fn l_String_utf8EncodeChar___boxed(mut v_c_7401_: *mut LeanObject) -> *mut LeanObject {
    let mut v_c_boxed_7402_: u32 = 0;
    let mut v_res_7403_: *mut LeanObject = core::ptr::null_mut();
    v_c_boxed_7402_ = lean_unbox_uint32(v_c_7401_);
    lean_dec(v_c_7401_);
    v_res_7403_ = l_String_utf8EncodeChar(v_c_boxed_7402_);
    return v_res_7403_;
}
pub unsafe fn l_String_toByteArray___boxed(mut v_self_7405_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_7406_: *mut LeanObject = core::ptr::null_mut();
    v_res_7406_ = lean_string_to_utf8(v_self_7405_);
    return v_res_7406_;
}
pub unsafe fn l_String_ofByteArray___boxed(
    mut v_toByteArray_7409_: *mut LeanObject,
    mut v_isValidUTF8_7410_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7411_: *mut LeanObject = core::ptr::null_mut();
    v_res_7411_ = lean_string_from_utf8_unchecked(v_toByteArray_7409_);
    return v_res_7411_;
}
pub unsafe fn l_String_ofList___boxed(mut v_data_7413_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_7414_: *mut LeanObject = core::ptr::null_mut();
    v_res_7414_ = lean_string_mk(v_data_7413_);
    return v_res_7414_;
}
pub unsafe fn l_String_decEq___boxed(
    mut v_s_u2081_7417_: *mut LeanObject,
    mut v_s_u2082_7418_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7419_: u8 = 0;
    let mut v_r_7420_: *mut LeanObject = core::ptr::null_mut();
    v_res_7419_ = lean_string_dec_eq(v_s_u2081_7417_, v_s_u2082_7418_);
    lean_dec_ref(v_s_u2082_7418_);
    lean_dec_ref(v_s_u2081_7417_);
    v_r_7420_ = lean_box((v_res_7419_) as usize);
    return v_r_7420_;
}
pub unsafe fn l_instDecidableEqString(
    mut v_s_u2081_7421_: *mut LeanObject,
    mut v_s_u2082_7422_: *mut LeanObject,
) -> u8 {
    let mut v___x_7423_: u8 = 0;
    v___x_7423_ = lean_string_dec_eq(v_s_u2081_7421_, v_s_u2082_7422_);
    return v___x_7423_;
}
pub unsafe fn l_instDecidableEqString___boxed(
    mut v_s_u2081_7424_: *mut LeanObject,
    mut v_s_u2082_7425_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7426_: u8 = 0;
    let mut v_r_7427_: *mut LeanObject = core::ptr::null_mut();
    v_res_7426_ = l_instDecidableEqString(v_s_u2081_7424_, v_s_u2082_7425_);
    lean_dec_ref(v_s_u2082_7425_);
    lean_dec_ref(v_s_u2081_7424_);
    v_r_7427_ = lean_box((v_res_7426_) as usize);
    return v_r_7427_;
}
pub unsafe fn _init_l_instInhabitedRaw() -> *mut LeanObject {
    let mut v___x_7428_: *mut LeanObject = core::ptr::null_mut();
    v___x_7428_ = lean_unsigned_to_nat(0);
    return v___x_7428_;
}
pub unsafe fn l_instDecidableEqRaw(
    mut v_x_7429_: *mut LeanObject,
    mut v_x_7430_: *mut LeanObject,
) -> u8 {
    let mut v___x_7431_: u8 = 0;
    v___x_7431_ = lean_nat_dec_eq(v_x_7429_, v_x_7430_);
    return v___x_7431_;
}
pub unsafe fn l_instDecidableEqRaw___boxed(
    mut v_x_7432_: *mut LeanObject,
    mut v_x_7433_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7434_: u8 = 0;
    let mut v_r_7435_: *mut LeanObject = core::ptr::null_mut();
    v_res_7434_ = l_instDecidableEqRaw(v_x_7432_, v_x_7433_);
    lean_dec(v_x_7433_);
    lean_dec(v_x_7432_);
    v_r_7435_ = lean_box((v_res_7434_) as usize);
    return v_r_7435_;
}
pub unsafe fn l_Substring_Raw_bsize(mut v_x_7441_: *mut LeanObject) -> *mut LeanObject {
    let mut v_startPos_7442_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stopPos_7443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7444_: *mut LeanObject = core::ptr::null_mut();
    v_startPos_7442_ = lean_ctor_get(v_x_7441_, 1);
    v_stopPos_7443_ = lean_ctor_get(v_x_7441_, 2);
    v___x_7444_ = lean_nat_sub(v_stopPos_7443_, v_startPos_7442_);
    return v___x_7444_;
}
pub unsafe fn l_Substring_Raw_bsize___boxed(mut v_x_7445_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_7446_: *mut LeanObject = core::ptr::null_mut();
    v_res_7446_ = l_Substring_Raw_bsize(v_x_7445_);
    lean_dec_ref(v_x_7445_);
    return v_res_7446_;
}
pub unsafe fn l_String_utf8ByteSize___boxed(mut v_s_7448_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_7449_: *mut LeanObject = core::ptr::null_mut();
    v_res_7449_ = lean_string_utf8_byte_size(v_s_7448_);
    lean_dec_ref(v_s_7448_);
    return v_res_7449_;
}
pub unsafe fn l_String_rawEndPos(mut v_s_7450_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_7451_: *mut LeanObject = core::ptr::null_mut();
    v___x_7451_ = lean_string_utf8_byte_size(v_s_7450_);
    return v___x_7451_;
}
pub unsafe fn l_String_rawEndPos___boxed(mut v_s_7452_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_7453_: *mut LeanObject = core::ptr::null_mut();
    v_res_7453_ = l_String_rawEndPos(v_s_7452_);
    lean_dec_ref(v_s_7452_);
    return v_res_7453_;
}
pub unsafe fn l_String_toRawSubstring(mut v_s_7454_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_7455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7457_: *mut LeanObject = core::ptr::null_mut();
    v___x_7455_ = lean_unsigned_to_nat(0);
    v___x_7456_ = lean_string_utf8_byte_size(v_s_7454_);
    v___x_7457_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_7457_, 0, v_s_7454_);
    lean_ctor_set(v___x_7457_, 1, v___x_7455_);
    lean_ctor_set(v___x_7457_, 2, v___x_7456_);
    return v___x_7457_;
}
pub unsafe fn l_String_toRawSubstring_x27(mut v_s_7458_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_7459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7461_: *mut LeanObject = core::ptr::null_mut();
    v___x_7459_ = lean_unsigned_to_nat(0);
    v___x_7460_ = lean_string_utf8_byte_size(v_s_7458_);
    v___x_7461_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_7461_, 0, v_s_7458_);
    lean_ctor_set(v___x_7461_, 1, v___x_7459_);
    lean_ctor_set(v___x_7461_, 2, v___x_7460_);
    return v___x_7461_;
}
pub unsafe fn l_unsafeCast___redArg(mut v_a_7462_: *mut LeanObject) -> *mut LeanObject {
    lean_inc(v_a_7462_);
    return v_a_7462_;
}
pub unsafe fn l_unsafeCast___redArg___boxed(mut v_a_7463_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_7464_: *mut LeanObject = core::ptr::null_mut();
    v_res_7464_ = l_unsafeCast___redArg(v_a_7463_);
    lean_dec(v_a_7463_);
    return v_res_7464_;
}
pub unsafe fn l_unsafeCast(
    mut v_00_u03b1_7465_: *mut LeanObject,
    mut v_00_u03b2_7466_: *mut LeanObject,
    mut v_a_7467_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_a_7467_);
    return v_a_7467_;
}
pub unsafe fn l_unsafeCast___boxed(
    mut v_00_u03b1_7468_: *mut LeanObject,
    mut v_00_u03b2_7469_: *mut LeanObject,
    mut v_a_7470_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7471_: *mut LeanObject = core::ptr::null_mut();
    v_res_7471_ = l_unsafeCast(v_00_u03b1_7468_, v_00_u03b2_7469_, v_a_7470_);
    lean_dec(v_a_7470_);
    return v_res_7471_;
}
pub unsafe fn l_panicCore___boxed(
    mut v_00_u03b1_7475_: *mut LeanObject,
    mut v_inst_00___x40_Init_Prelude_4048948229____hygCtx___hyg_7476_: *mut LeanObject,
    mut v_msg_7477_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7478_: *mut LeanObject = core::ptr::null_mut();
    v_res_7478_ = lean_panic_fn_borrowed(
        v_inst_00___x40_Init_Prelude_4048948229____hygCtx___hyg_7476_,
        v_msg_7477_,
    );
    lean_dec(v_inst_00___x40_Init_Prelude_4048948229____hygCtx___hyg_7476_);
    return v_res_7478_;
}
pub unsafe fn l_panic___redArg(
    mut v_inst_7479_: *mut LeanObject,
    mut v_msg_7480_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7481_: *mut LeanObject = core::ptr::null_mut();
    v___x_7481_ = lean_panic_fn_borrowed(v_inst_7479_, v_msg_7480_);
    return v___x_7481_;
}
pub unsafe fn l_panic___redArg___boxed(
    mut v_inst_7482_: *mut LeanObject,
    mut v_msg_7483_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7484_: *mut LeanObject = core::ptr::null_mut();
    v_res_7484_ = l_panic___redArg(v_inst_7482_, v_msg_7483_);
    lean_dec(v_inst_7482_);
    return v_res_7484_;
}
pub unsafe fn l_panic(
    mut v_00_u03b1_7485_: *mut LeanObject,
    mut v_inst_7486_: *mut LeanObject,
    mut v_msg_7487_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7488_: *mut LeanObject = core::ptr::null_mut();
    v___x_7488_ = l_panic___redArg(v_inst_7486_, v_msg_7487_);
    return v___x_7488_;
}
pub unsafe fn l_panic___boxed(
    mut v_00_u03b1_7489_: *mut LeanObject,
    mut v_inst_7490_: *mut LeanObject,
    mut v_msg_7491_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7492_: *mut LeanObject = core::ptr::null_mut();
    v_res_7492_ = l_panic(v_00_u03b1_7489_, v_inst_7490_, v_msg_7491_);
    lean_dec(v_inst_7490_);
    return v_res_7492_;
}
pub unsafe fn l_instInhabitedForallOfMonad___redArg(
    mut v_inst_7493_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_7494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_7495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7496_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_7494_ = lean_ctor_get(v_inst_7493_, 0);
    lean_inc_ref(v_toApplicative_7494_);
    lean_dec_ref(v_inst_7493_);
    v_toPure_7495_ = lean_ctor_get(v_toApplicative_7494_, 1);
    lean_inc(v_toPure_7495_);
    lean_dec_ref(v_toApplicative_7494_);
    v___x_7496_ = lean_apply_1(v_toPure_7495_, lean_box(0));
    return v___x_7496_;
}
pub unsafe fn l_instInhabitedForallOfMonad(
    mut v_00_u03b1_7497_: *mut LeanObject,
    mut v_m_7498_: *mut LeanObject,
    mut v_inst_7499_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7500_: *mut LeanObject = core::ptr::null_mut();
    v___x_7500_ = l_instInhabitedForallOfMonad___redArg(v_inst_7499_);
    return v___x_7500_;
}
pub unsafe fn l_instInhabitedOfMonad___redArg(
    mut v_inst_7501_: *mut LeanObject,
    mut v_inst_7502_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_7503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_7504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7505_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_7503_ = lean_ctor_get(v_inst_7501_, 0);
    lean_inc_ref(v_toApplicative_7503_);
    lean_dec_ref(v_inst_7501_);
    v_toPure_7504_ = lean_ctor_get(v_toApplicative_7503_, 1);
    lean_inc(v_toPure_7504_);
    lean_dec_ref(v_toApplicative_7503_);
    v___x_7505_ = lean_apply_2(v_toPure_7504_, lean_box(0), v_inst_7502_);
    return v___x_7505_;
}
pub unsafe fn l_instInhabitedOfMonad(
    mut v_00_u03b1_7506_: *mut LeanObject,
    mut v_m_7507_: *mut LeanObject,
    mut v_inst_7508_: *mut LeanObject,
    mut v_inst_7509_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7510_: *mut LeanObject = core::ptr::null_mut();
    v___x_7510_ = l_instInhabitedOfMonad___redArg(v_inst_7508_, v_inst_7509_);
    return v___x_7510_;
}
pub unsafe fn l_liftM___redArg(
    mut v_self_7511_: *mut LeanObject,
    mut v_a_7512_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7513_: *mut LeanObject = core::ptr::null_mut();
    v___x_7513_ = lean_apply_2(v_self_7511_, lean_box(0), v_a_7512_);
    return v___x_7513_;
}
pub unsafe fn l_liftM(
    mut v_m_7514_: *mut LeanObject,
    mut v_n_7515_: *mut LeanObject,
    mut v_self_7516_: *mut LeanObject,
    mut v_00_u03b1_7517_: *mut LeanObject,
    mut v_a_7518_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7519_: *mut LeanObject = core::ptr::null_mut();
    v___x_7519_ = lean_apply_2(v_self_7516_, lean_box(0), v_a_7518_);
    return v___x_7519_;
}
pub unsafe fn l_instMonadLiftTOfMonadLift___redArg___lam__0(
    mut v_inst_7520_: *mut LeanObject,
    mut v_inst_7521_: *mut LeanObject,
    mut v_00_u03b1_7522_: *mut LeanObject,
    mut v_x_7523_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7525_: *mut LeanObject = core::ptr::null_mut();
    v___x_7524_ = lean_apply_2(v_inst_7520_, lean_box(0), v_x_7523_);
    v___x_7525_ = lean_apply_2(v_inst_7521_, lean_box(0), v___x_7524_);
    return v___x_7525_;
}
pub unsafe fn l_instMonadLiftTOfMonadLift___redArg(
    mut v_inst_7526_: *mut LeanObject,
    mut v_inst_7527_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_7528_: *mut LeanObject = core::ptr::null_mut();
    v___f_7528_ = lean_alloc_closure(
        l_instMonadLiftTOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_7528_, 0, v_inst_7527_);
    lean_closure_set(v___f_7528_, 1, v_inst_7526_);
    return v___f_7528_;
}
pub unsafe fn l_instMonadLiftTOfMonadLift(
    mut v_m_7529_: *mut LeanObject,
    mut v_n_7530_: *mut LeanObject,
    mut v_o_7531_: *mut LeanObject,
    mut v_inst_7532_: *mut LeanObject,
    mut v_inst_7533_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_7534_: *mut LeanObject = core::ptr::null_mut();
    v___f_7534_ = lean_alloc_closure(
        l_instMonadLiftTOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_7534_, 0, v_inst_7533_);
    lean_closure_set(v___f_7534_, 1, v_inst_7532_);
    return v___f_7534_;
}
pub unsafe fn l_instMonadLiftT___lam__0(
    mut v_00_u03b1_7535_: *mut LeanObject,
    mut v_x_7536_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_x_7536_);
    return v_x_7536_;
}
pub unsafe fn l_instMonadLiftT___lam__0___boxed(
    mut v_00_u03b1_7537_: *mut LeanObject,
    mut v_x_7538_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7539_: *mut LeanObject = core::ptr::null_mut();
    v_res_7539_ = l_instMonadLiftT___lam__0(v_00_u03b1_7537_, v_x_7538_);
    lean_dec(v_x_7538_);
    return v_res_7539_;
}
pub unsafe fn l_instMonadLiftT(mut v_m_7541_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_7542_: *mut LeanObject = core::ptr::null_mut();
    v___f_7542_ = l_instMonadLiftT___closed__0;
    return v___f_7542_;
}
pub unsafe fn l_instMonadEvalOfMonadLift___redArg___lam__0(
    mut v_inst_7543_: *mut LeanObject,
    mut v_00_u03b1_7544_: *mut LeanObject,
    mut v___y_7545_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7546_: *mut LeanObject = core::ptr::null_mut();
    v___x_7546_ = lean_apply_2(v_inst_7543_, lean_box(0), v___y_7545_);
    return v___x_7546_;
}
pub unsafe fn l_instMonadEvalOfMonadLift___redArg(
    mut v_inst_7547_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_7548_: *mut LeanObject = core::ptr::null_mut();
    v___f_7548_ = lean_alloc_closure(
        l_instMonadEvalOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_7548_, 0, v_inst_7547_);
    return v___f_7548_;
}
pub unsafe fn l_instMonadEvalOfMonadLift(
    mut v_m_7549_: *mut LeanObject,
    mut v_n_7550_: *mut LeanObject,
    mut v_inst_7551_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_7552_: *mut LeanObject = core::ptr::null_mut();
    v___f_7552_ = lean_alloc_closure(
        l_instMonadEvalOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_7552_, 0, v_inst_7551_);
    return v___f_7552_;
}
pub unsafe fn l_instMonadEvalTOfMonadEval___redArg(
    mut v_inst_7553_: *mut LeanObject,
    mut v_inst_7554_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_7555_: *mut LeanObject = core::ptr::null_mut();
    v___f_7555_ = lean_alloc_closure(
        l_instMonadLiftTOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_7555_, 0, v_inst_7554_);
    lean_closure_set(v___f_7555_, 1, v_inst_7553_);
    return v___f_7555_;
}
pub unsafe fn l_instMonadEvalTOfMonadEval(
    mut v_m_7556_: *mut LeanObject,
    mut v_n_7557_: *mut LeanObject,
    mut v_o_7558_: *mut LeanObject,
    mut v_inst_7559_: *mut LeanObject,
    mut v_inst_7560_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_7561_: *mut LeanObject = core::ptr::null_mut();
    v___f_7561_ = lean_alloc_closure(
        l_instMonadLiftTOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_7561_, 0, v_inst_7560_);
    lean_closure_set(v___f_7561_, 1, v_inst_7559_);
    return v___f_7561_;
}
pub unsafe fn l_instMonadEvalT(mut v_m_7562_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_7563_: *mut LeanObject = core::ptr::null_mut();
    v___f_7563_ = l_instMonadLiftT___closed__0;
    return v___f_7563_;
}
pub unsafe fn l_instMonadFunctorTOfMonadFunctor___redArg___lam__0(
    mut v_inst_7564_: *mut LeanObject,
    mut v_f_7565_: *mut LeanObject,
    mut v_00_u03b2_7566_: *mut LeanObject,
    mut v___y_7567_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7568_: *mut LeanObject = core::ptr::null_mut();
    v___x_7568_ = lean_apply_3(v_inst_7564_, lean_box(0), v_f_7565_, v___y_7567_);
    return v___x_7568_;
}
pub unsafe fn l_instMonadFunctorTOfMonadFunctor___redArg___lam__1(
    mut v_inst_7569_: *mut LeanObject,
    mut v_inst_7570_: *mut LeanObject,
    mut v_00_u03b1_7571_: *mut LeanObject,
    mut v_f_7572_: *mut LeanObject,
    mut v___y_7573_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_7574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7575_: *mut LeanObject = core::ptr::null_mut();
    v___f_7574_ = lean_alloc_closure(
        l_instMonadFunctorTOfMonadFunctor___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_7574_, 0, v_inst_7569_);
    lean_closure_set(v___f_7574_, 1, v_f_7572_);
    v___x_7575_ = lean_apply_3(v_inst_7570_, lean_box(0), v___f_7574_, v___y_7573_);
    return v___x_7575_;
}
pub unsafe fn l_instMonadFunctorTOfMonadFunctor___redArg(
    mut v_inst_7576_: *mut LeanObject,
    mut v_inst_7577_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_7578_: *mut LeanObject = core::ptr::null_mut();
    v___f_7578_ = lean_alloc_closure(
        l_instMonadFunctorTOfMonadFunctor___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        2,
    );
    lean_closure_set(v___f_7578_, 0, v_inst_7577_);
    lean_closure_set(v___f_7578_, 1, v_inst_7576_);
    return v___f_7578_;
}
pub unsafe fn l_instMonadFunctorTOfMonadFunctor(
    mut v_m_7579_: *mut LeanObject,
    mut v_n_7580_: *mut LeanObject,
    mut v_o_7581_: *mut LeanObject,
    mut v_inst_7582_: *mut LeanObject,
    mut v_inst_7583_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_7584_: *mut LeanObject = core::ptr::null_mut();
    v___f_7584_ = lean_alloc_closure(
        l_instMonadFunctorTOfMonadFunctor___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        2,
    );
    lean_closure_set(v___f_7584_, 0, v_inst_7583_);
    lean_closure_set(v___f_7584_, 1, v_inst_7582_);
    return v___f_7584_;
}
pub unsafe fn l_monadFunctorRefl___lam__0(
    mut v_00_u03b1_7585_: *mut LeanObject,
    mut v_f_7586_: *mut LeanObject,
    mut v___y_7587_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7588_: *mut LeanObject = core::ptr::null_mut();
    v___x_7588_ = lean_apply_2(v_f_7586_, lean_box(0), v___y_7587_);
    return v___x_7588_;
}
pub unsafe fn l_monadFunctorRefl(mut v_m_7590_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_7591_: *mut LeanObject = core::ptr::null_mut();
    v___f_7591_ = l_monadFunctorRefl___closed__0;
    return v___f_7591_;
}
pub unsafe fn l_Except_ctorIdx___redArg(mut v_x_7592_: *mut LeanObject) -> *mut LeanObject {
    if lean_obj_tag(v_x_7592_) == 0 {
        let mut v___x_7593_: *mut LeanObject = core::ptr::null_mut();
        v___x_7593_ = lean_unsigned_to_nat(0);
        return v___x_7593_;
    } else {
        let mut v___x_7594_: *mut LeanObject = core::ptr::null_mut();
        v___x_7594_ = lean_unsigned_to_nat(1);
        return v___x_7594_;
    }
}
pub unsafe fn l_Except_ctorIdx___redArg___boxed(mut v_x_7595_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_7596_: *mut LeanObject = core::ptr::null_mut();
    v_res_7596_ = l_Except_ctorIdx___redArg(v_x_7595_);
    lean_dec_ref(v_x_7595_);
    return v_res_7596_;
}
pub unsafe fn l_Except_ctorIdx(
    mut v_00_u03b5_7597_: *mut LeanObject,
    mut v_00_u03b1_7598_: *mut LeanObject,
    mut v_x_7599_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7600_: *mut LeanObject = core::ptr::null_mut();
    v___x_7600_ = l_Except_ctorIdx___redArg(v_x_7599_);
    return v___x_7600_;
}
pub unsafe fn l_Except_ctorIdx___boxed(
    mut v_00_u03b5_7601_: *mut LeanObject,
    mut v_00_u03b1_7602_: *mut LeanObject,
    mut v_x_7603_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7604_: *mut LeanObject = core::ptr::null_mut();
    v_res_7604_ = l_Except_ctorIdx(v_00_u03b5_7601_, v_00_u03b1_7602_, v_x_7603_);
    lean_dec_ref(v_x_7603_);
    return v_res_7604_;
}
pub unsafe fn l_Except_ctorElim___redArg(
    mut v_t_7605_: *mut LeanObject,
    mut v_k_7606_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_7607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7608_: *mut LeanObject = core::ptr::null_mut();
    v_a_7607_ = lean_ctor_get(v_t_7605_, 0);
    lean_inc(v_a_7607_);
    lean_dec_ref(v_t_7605_);
    v___x_7608_ = lean_apply_1(v_k_7606_, v_a_7607_);
    return v___x_7608_;
}
pub unsafe fn l_Except_ctorElim(
    mut v_00_u03b5_7609_: *mut LeanObject,
    mut v_00_u03b1_7610_: *mut LeanObject,
    mut v_motive_7611_: *mut LeanObject,
    mut v_ctorIdx_7612_: *mut LeanObject,
    mut v_t_7613_: *mut LeanObject,
    mut v_h_7614_: *mut LeanObject,
    mut v_k_7615_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7616_: *mut LeanObject = core::ptr::null_mut();
    v___x_7616_ = l_Except_ctorElim___redArg(v_t_7613_, v_k_7615_);
    return v___x_7616_;
}
pub unsafe fn l_Except_ctorElim___boxed(
    mut v_00_u03b5_7617_: *mut LeanObject,
    mut v_00_u03b1_7618_: *mut LeanObject,
    mut v_motive_7619_: *mut LeanObject,
    mut v_ctorIdx_7620_: *mut LeanObject,
    mut v_t_7621_: *mut LeanObject,
    mut v_h_7622_: *mut LeanObject,
    mut v_k_7623_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7624_: *mut LeanObject = core::ptr::null_mut();
    v_res_7624_ = l_Except_ctorElim(
        v_00_u03b5_7617_,
        v_00_u03b1_7618_,
        v_motive_7619_,
        v_ctorIdx_7620_,
        v_t_7621_,
        v_h_7622_,
        v_k_7623_,
    );
    lean_dec(v_ctorIdx_7620_);
    return v_res_7624_;
}
pub unsafe fn l_Except_error_elim___redArg(
    mut v_t_7625_: *mut LeanObject,
    mut v_error_7626_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7627_: *mut LeanObject = core::ptr::null_mut();
    v___x_7627_ = l_Except_ctorElim___redArg(v_t_7625_, v_error_7626_);
    return v___x_7627_;
}
pub unsafe fn l_Except_error_elim(
    mut v_00_u03b5_7628_: *mut LeanObject,
    mut v_00_u03b1_7629_: *mut LeanObject,
    mut v_motive_7630_: *mut LeanObject,
    mut v_t_7631_: *mut LeanObject,
    mut v_h_7632_: *mut LeanObject,
    mut v_error_7633_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7634_: *mut LeanObject = core::ptr::null_mut();
    v___x_7634_ = l_Except_ctorElim___redArg(v_t_7631_, v_error_7633_);
    return v___x_7634_;
}
pub unsafe fn l_Except_ok_elim___redArg(
    mut v_t_7635_: *mut LeanObject,
    mut v_ok_7636_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7637_: *mut LeanObject = core::ptr::null_mut();
    v___x_7637_ = l_Except_ctorElim___redArg(v_t_7635_, v_ok_7636_);
    return v___x_7637_;
}
pub unsafe fn l_Except_ok_elim(
    mut v_00_u03b5_7638_: *mut LeanObject,
    mut v_00_u03b1_7639_: *mut LeanObject,
    mut v_motive_7640_: *mut LeanObject,
    mut v_t_7641_: *mut LeanObject,
    mut v_h_7642_: *mut LeanObject,
    mut v_ok_7643_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7644_: *mut LeanObject = core::ptr::null_mut();
    v___x_7644_ = l_Except_ctorElim___redArg(v_t_7641_, v_ok_7643_);
    return v___x_7644_;
}
pub unsafe fn l_instInhabitedExcept___redArg(mut v_inst_7645_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_7646_: *mut LeanObject = core::ptr::null_mut();
    v___x_7646_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_7646_, 0, v_inst_7645_);
    return v___x_7646_;
}
pub unsafe fn l_instInhabitedExcept(
    mut v_00_u03b5_7647_: *mut LeanObject,
    mut v_00_u03b1_7648_: *mut LeanObject,
    mut v_inst_7649_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7650_: *mut LeanObject = core::ptr::null_mut();
    v___x_7650_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_7650_, 0, v_inst_7649_);
    return v___x_7650_;
}
pub unsafe fn l_throwThe___redArg(
    mut v_inst_7651_: *mut LeanObject,
    mut v_e_7652_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_throw_7653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7654_: *mut LeanObject = core::ptr::null_mut();
    v_throw_7653_ = lean_ctor_get(v_inst_7651_, 0);
    lean_inc(v_throw_7653_);
    lean_dec_ref(v_inst_7651_);
    v___x_7654_ = lean_apply_2(v_throw_7653_, lean_box(0), v_e_7652_);
    return v___x_7654_;
}
pub unsafe fn l_throwThe(
    mut v_00_u03b5_7655_: *mut LeanObject,
    mut v_m_7656_: *mut LeanObject,
    mut v_inst_7657_: *mut LeanObject,
    mut v_00_u03b1_7658_: *mut LeanObject,
    mut v_e_7659_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_throw_7660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7661_: *mut LeanObject = core::ptr::null_mut();
    v_throw_7660_ = lean_ctor_get(v_inst_7657_, 0);
    lean_inc(v_throw_7660_);
    lean_dec_ref(v_inst_7657_);
    v___x_7661_ = lean_apply_2(v_throw_7660_, lean_box(0), v_e_7659_);
    return v___x_7661_;
}
pub unsafe fn l_tryCatchThe___redArg(
    mut v_inst_7662_: *mut LeanObject,
    mut v_x_7663_: *mut LeanObject,
    mut v_handle_7664_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_tryCatch_7665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7666_: *mut LeanObject = core::ptr::null_mut();
    v_tryCatch_7665_ = lean_ctor_get(v_inst_7662_, 1);
    lean_inc(v_tryCatch_7665_);
    lean_dec_ref(v_inst_7662_);
    v___x_7666_ = lean_apply_3(v_tryCatch_7665_, lean_box(0), v_x_7663_, v_handle_7664_);
    return v___x_7666_;
}
pub unsafe fn l_tryCatchThe(
    mut v_00_u03b5_7667_: *mut LeanObject,
    mut v_m_7668_: *mut LeanObject,
    mut v_inst_7669_: *mut LeanObject,
    mut v_00_u03b1_7670_: *mut LeanObject,
    mut v_x_7671_: *mut LeanObject,
    mut v_handle_7672_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_tryCatch_7673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7674_: *mut LeanObject = core::ptr::null_mut();
    v_tryCatch_7673_ = lean_ctor_get(v_inst_7669_, 1);
    lean_inc(v_tryCatch_7673_);
    lean_dec_ref(v_inst_7669_);
    v___x_7674_ = lean_apply_3(v_tryCatch_7673_, lean_box(0), v_x_7671_, v_handle_7672_);
    return v___x_7674_;
}
pub unsafe fn l_MonadExcept_ofExcept___redArg(
    mut v_inst_7675_: *mut LeanObject,
    mut v_inst_7676_: *mut LeanObject,
    mut v_x_7677_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_7678_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_7678_ = lean_ctor_get(v_inst_7675_, 0);
    lean_inc_ref(v_toApplicative_7678_);
    lean_dec_ref(v_inst_7675_);
    if lean_obj_tag(v_x_7677_) == 0 {
        let mut v_a_7679_: *mut LeanObject = core::ptr::null_mut();
        let mut v_throw_7680_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7681_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_toApplicative_7678_);
        v_a_7679_ = lean_ctor_get(v_x_7677_, 0);
        lean_inc(v_a_7679_);
        lean_dec_ref_known(v_x_7677_, 1);
        v_throw_7680_ = lean_ctor_get(v_inst_7676_, 0);
        lean_inc(v_throw_7680_);
        lean_dec_ref(v_inst_7676_);
        v___x_7681_ = lean_apply_2(v_throw_7680_, lean_box(0), v_a_7679_);
        return v___x_7681_;
    } else {
        let mut v_toPure_7682_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_7683_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7684_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_inst_7676_);
        v_toPure_7682_ = lean_ctor_get(v_toApplicative_7678_, 1);
        lean_inc(v_toPure_7682_);
        lean_dec_ref(v_toApplicative_7678_);
        v_a_7683_ = lean_ctor_get(v_x_7677_, 0);
        lean_inc(v_a_7683_);
        lean_dec_ref_known(v_x_7677_, 1);
        v___x_7684_ = lean_apply_2(v_toPure_7682_, lean_box(0), v_a_7683_);
        return v___x_7684_;
    }
}
pub unsafe fn l_MonadExcept_ofExcept(
    mut v_m_7685_: *mut LeanObject,
    mut v_00_u03b5_7686_: *mut LeanObject,
    mut v_00_u03b1_7687_: *mut LeanObject,
    mut v_inst_7688_: *mut LeanObject,
    mut v_inst_7689_: *mut LeanObject,
    mut v_x_7690_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7691_: *mut LeanObject = core::ptr::null_mut();
    v___x_7691_ = l_MonadExcept_ofExcept___redArg(v_inst_7688_, v_inst_7689_, v_x_7690_);
    return v___x_7691_;
}
pub unsafe fn l_instMonadExceptOfMonadExceptOf___redArg(
    mut v_inst_7692_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7695_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_inst_7692_);
    v___x_7693_ = lean_alloc_closure(l_throwThe as *mut core::ffi::c_void, 5, 3);
    lean_closure_set(v___x_7693_, 0, lean_box(0));
    lean_closure_set(v___x_7693_, 1, lean_box(0));
    lean_closure_set(v___x_7693_, 2, v_inst_7692_);
    v___x_7694_ = lean_alloc_closure(l_tryCatchThe as *mut core::ffi::c_void, 6, 3);
    lean_closure_set(v___x_7694_, 0, lean_box(0));
    lean_closure_set(v___x_7694_, 1, lean_box(0));
    lean_closure_set(v___x_7694_, 2, v_inst_7692_);
    v___x_7695_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_7695_, 0, v___x_7693_);
    lean_ctor_set(v___x_7695_, 1, v___x_7694_);
    return v___x_7695_;
}
pub unsafe fn l_instMonadExceptOfMonadExceptOf(
    mut v_00_u03b5_7696_: *mut LeanObject,
    mut v_m_7697_: *mut LeanObject,
    mut v_inst_7698_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7699_: *mut LeanObject = core::ptr::null_mut();
    v___x_7699_ = l_instMonadExceptOfMonadExceptOf___redArg(v_inst_7698_);
    return v___x_7699_;
}
pub unsafe fn l_MonadExcept_orElse___redArg___lam__0(
    mut v_t_u2082_7700_: *mut LeanObject,
    mut v_x_7701_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7703_: *mut LeanObject = core::ptr::null_mut();
    v___x_7702_ = lean_box(0);
    v___x_7703_ = lean_apply_1(v_t_u2082_7700_, v___x_7702_);
    return v___x_7703_;
}
pub unsafe fn l_MonadExcept_orElse___redArg___lam__0___boxed(
    mut v_t_u2082_7704_: *mut LeanObject,
    mut v_x_7705_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7706_: *mut LeanObject = core::ptr::null_mut();
    v_res_7706_ = l_MonadExcept_orElse___redArg___lam__0(v_t_u2082_7704_, v_x_7705_);
    lean_dec(v_x_7705_);
    return v_res_7706_;
}
pub unsafe fn l_MonadExcept_orElse___redArg(
    mut v_inst_7707_: *mut LeanObject,
    mut v_t_u2081_7708_: *mut LeanObject,
    mut v_t_u2082_7709_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_tryCatch_7710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7712_: *mut LeanObject = core::ptr::null_mut();
    v_tryCatch_7710_ = lean_ctor_get(v_inst_7707_, 1);
    lean_inc(v_tryCatch_7710_);
    lean_dec_ref(v_inst_7707_);
    v___f_7711_ = lean_alloc_closure(
        l_MonadExcept_orElse___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_7711_, 0, v_t_u2082_7709_);
    v___x_7712_ = lean_apply_3(v_tryCatch_7710_, lean_box(0), v_t_u2081_7708_, v___f_7711_);
    return v___x_7712_;
}
pub unsafe fn l_MonadExcept_orElse(
    mut v_00_u03b5_7713_: *mut LeanObject,
    mut v_m_7714_: *mut LeanObject,
    mut v_inst_7715_: *mut LeanObject,
    mut v_00_u03b1_7716_: *mut LeanObject,
    mut v_t_u2081_7717_: *mut LeanObject,
    mut v_t_u2082_7718_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_tryCatch_7719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7721_: *mut LeanObject = core::ptr::null_mut();
    v_tryCatch_7719_ = lean_ctor_get(v_inst_7715_, 1);
    lean_inc(v_tryCatch_7719_);
    lean_dec_ref(v_inst_7715_);
    v___f_7720_ = lean_alloc_closure(
        l_MonadExcept_orElse___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_7720_, 0, v_t_u2082_7718_);
    v___x_7721_ = lean_apply_3(v_tryCatch_7719_, lean_box(0), v_t_u2081_7717_, v___f_7720_);
    return v___x_7721_;
}
pub unsafe fn l_MonadExcept_instOrElse___redArg(
    mut v_inst_7722_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7723_: *mut LeanObject = core::ptr::null_mut();
    v___x_7723_ = lean_alloc_closure(l_MonadExcept_orElse as *mut core::ffi::c_void, 6, 4);
    lean_closure_set(v___x_7723_, 0, lean_box(0));
    lean_closure_set(v___x_7723_, 1, lean_box(0));
    lean_closure_set(v___x_7723_, 2, v_inst_7722_);
    lean_closure_set(v___x_7723_, 3, lean_box(0));
    return v___x_7723_;
}
pub unsafe fn l_MonadExcept_instOrElse(
    mut v_00_u03b5_7724_: *mut LeanObject,
    mut v_m_7725_: *mut LeanObject,
    mut v_inst_7726_: *mut LeanObject,
    mut v_00_u03b1_7727_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7728_: *mut LeanObject = core::ptr::null_mut();
    v___x_7728_ = lean_alloc_closure(l_MonadExcept_orElse as *mut core::ffi::c_void, 6, 4);
    lean_closure_set(v___x_7728_, 0, lean_box(0));
    lean_closure_set(v___x_7728_, 1, lean_box(0));
    lean_closure_set(v___x_7728_, 2, v_inst_7726_);
    lean_closure_set(v___x_7728_, 3, lean_box(0));
    return v___x_7728_;
}
pub unsafe fn l_ReaderT_mk___redArg(
    mut v_x_7729_: *mut LeanObject,
    mut v_a_7730_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7731_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_a_7730_);
    v___x_7731_ = lean_apply_1(v_x_7729_, v_a_7730_);
    return v___x_7731_;
}
pub unsafe fn l_ReaderT_mk___redArg___boxed(
    mut v_x_7732_: *mut LeanObject,
    mut v_a_7733_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7734_: *mut LeanObject = core::ptr::null_mut();
    v_res_7734_ = l_ReaderT_mk___redArg(v_x_7732_, v_a_7733_);
    lean_dec(v_a_7733_);
    return v_res_7734_;
}
pub unsafe fn l_ReaderT_mk(
    mut v_00_u03c1_7735_: *mut LeanObject,
    mut v_m_7736_: *mut LeanObject,
    mut v_00_u03b1_7737_: *mut LeanObject,
    mut v_x_7738_: *mut LeanObject,
    mut v_a_7739_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7740_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_a_7739_);
    v___x_7740_ = lean_apply_1(v_x_7738_, v_a_7739_);
    return v___x_7740_;
}
pub unsafe fn l_ReaderT_mk___boxed(
    mut v_00_u03c1_7741_: *mut LeanObject,
    mut v_m_7742_: *mut LeanObject,
    mut v_00_u03b1_7743_: *mut LeanObject,
    mut v_x_7744_: *mut LeanObject,
    mut v_a_7745_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7746_: *mut LeanObject = core::ptr::null_mut();
    v_res_7746_ = l_ReaderT_mk(
        v_00_u03c1_7741_,
        v_m_7742_,
        v_00_u03b1_7743_,
        v_x_7744_,
        v_a_7745_,
    );
    lean_dec(v_a_7745_);
    return v_res_7746_;
}
pub unsafe fn l_instInhabitedReaderT___redArg(
    mut v_inst_7747_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_7748_: *mut LeanObject = core::ptr::null_mut();
    v___f_7748_ = lean_alloc_closure(
        l_instInhabitedForall___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_7748_, 0, v_inst_7747_);
    return v___f_7748_;
}
pub unsafe fn l_instInhabitedReaderT(
    mut v_00_u03c1_7749_: *mut LeanObject,
    mut v_m_7750_: *mut LeanObject,
    mut v_00_u03b1_7751_: *mut LeanObject,
    mut v_inst_7752_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_7753_: *mut LeanObject = core::ptr::null_mut();
    v___f_7753_ = lean_alloc_closure(
        l_instInhabitedForall___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_7753_, 0, v_inst_7752_);
    return v___f_7753_;
}
pub unsafe fn l_ReaderT_run___redArg(
    mut v_x_7754_: *mut LeanObject,
    mut v_r_7755_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7756_: *mut LeanObject = core::ptr::null_mut();
    v___x_7756_ = lean_apply_1(v_x_7754_, v_r_7755_);
    return v___x_7756_;
}
pub unsafe fn l_ReaderT_run(
    mut v_00_u03c1_7757_: *mut LeanObject,
    mut v_m_7758_: *mut LeanObject,
    mut v_00_u03b1_7759_: *mut LeanObject,
    mut v_x_7760_: *mut LeanObject,
    mut v_r_7761_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7762_: *mut LeanObject = core::ptr::null_mut();
    v___x_7762_ = lean_apply_1(v_x_7760_, v_r_7761_);
    return v___x_7762_;
}
pub unsafe fn l_ReaderT_instMonadLift___lam__0(
    mut v_00_u03b1_7763_: *mut LeanObject,
    mut v_x_7764_: *mut LeanObject,
    mut v_x_7765_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_x_7764_);
    return v_x_7764_;
}
pub unsafe fn l_ReaderT_instMonadLift___lam__0___boxed(
    mut v_00_u03b1_7766_: *mut LeanObject,
    mut v_x_7767_: *mut LeanObject,
    mut v_x_7768_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7769_: *mut LeanObject = core::ptr::null_mut();
    v_res_7769_ = l_ReaderT_instMonadLift___lam__0(v_00_u03b1_7766_, v_x_7767_, v_x_7768_);
    lean_dec(v_x_7768_);
    lean_dec(v_x_7767_);
    return v_res_7769_;
}
pub unsafe fn l_ReaderT_instMonadLift(
    mut v_00_u03c1_7771_: *mut LeanObject,
    mut v_m_7772_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_7773_: *mut LeanObject = core::ptr::null_mut();
    v___f_7773_ = l_ReaderT_instMonadLift___closed__0;
    return v___f_7773_;
}
pub unsafe fn l_ReaderT_instMonadExceptOf___redArg___lam__0(
    mut v_inst_7774_: *mut LeanObject,
    mut v_00_u03b1_7775_: *mut LeanObject,
    mut v_e_7776_: *mut LeanObject,
    mut v___y_7777_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_throw_7778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7779_: *mut LeanObject = core::ptr::null_mut();
    v_throw_7778_ = lean_ctor_get(v_inst_7774_, 0);
    lean_inc(v_throw_7778_);
    lean_dec_ref(v_inst_7774_);
    v___x_7779_ = lean_apply_2(v_throw_7778_, lean_box(0), v_e_7776_);
    return v___x_7779_;
}
pub unsafe fn l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed(
    mut v_inst_7780_: *mut LeanObject,
    mut v_00_u03b1_7781_: *mut LeanObject,
    mut v_e_7782_: *mut LeanObject,
    mut v___y_7783_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7784_: *mut LeanObject = core::ptr::null_mut();
    v_res_7784_ = l_ReaderT_instMonadExceptOf___redArg___lam__0(
        v_inst_7780_,
        v_00_u03b1_7781_,
        v_e_7782_,
        v___y_7783_,
    );
    lean_dec(v___y_7783_);
    return v_res_7784_;
}
pub unsafe fn l_ReaderT_instMonadExceptOf___redArg___lam__1(
    mut v_c_7785_: *mut LeanObject,
    mut v_r_7786_: *mut LeanObject,
    mut v_e_7787_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7788_: *mut LeanObject = core::ptr::null_mut();
    v___x_7788_ = lean_apply_2(v_c_7785_, v_e_7787_, v_r_7786_);
    return v___x_7788_;
}
pub unsafe fn l_ReaderT_instMonadExceptOf___redArg___lam__2(
    mut v_inst_7789_: *mut LeanObject,
    mut v_00_u03b1_7790_: *mut LeanObject,
    mut v_x_7791_: *mut LeanObject,
    mut v_c_7792_: *mut LeanObject,
    mut v_r_7793_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_tryCatch_7794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7797_: *mut LeanObject = core::ptr::null_mut();
    v_tryCatch_7794_ = lean_ctor_get(v_inst_7789_, 1);
    lean_inc(v_tryCatch_7794_);
    lean_dec_ref(v_inst_7789_);
    lean_inc(v_r_7793_);
    v___f_7795_ = lean_alloc_closure(
        l_ReaderT_instMonadExceptOf___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_7795_, 0, v_c_7792_);
    lean_closure_set(v___f_7795_, 1, v_r_7793_);
    v___x_7796_ = lean_apply_1(v_x_7791_, v_r_7793_);
    v___x_7797_ = lean_apply_3(v_tryCatch_7794_, lean_box(0), v___x_7796_, v___f_7795_);
    return v___x_7797_;
}
pub unsafe fn l_ReaderT_instMonadExceptOf___redArg(
    mut v_inst_7798_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_7799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7801_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_inst_7798_);
    v___f_7799_ = lean_alloc_closure(
        l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_7799_, 0, v_inst_7798_);
    v___f_7800_ = lean_alloc_closure(
        l_ReaderT_instMonadExceptOf___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_7800_, 0, v_inst_7798_);
    v___x_7801_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_7801_, 0, v___f_7799_);
    lean_ctor_set(v___x_7801_, 1, v___f_7800_);
    return v___x_7801_;
}
pub unsafe fn l_ReaderT_instMonadExceptOf(
    mut v_00_u03c1_7802_: *mut LeanObject,
    mut v_m_7803_: *mut LeanObject,
    mut v_00_u03b5_7804_: *mut LeanObject,
    mut v_inst_7805_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_7806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7808_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_inst_7805_);
    v___f_7806_ = lean_alloc_closure(
        l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_7806_, 0, v_inst_7805_);
    v___f_7807_ = lean_alloc_closure(
        l_ReaderT_instMonadExceptOf___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_7807_, 0, v_inst_7805_);
    v___x_7808_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_7808_, 0, v___f_7806_);
    lean_ctor_set(v___x_7808_, 1, v___f_7807_);
    return v___x_7808_;
}
pub unsafe fn l_ReaderT_read___redArg(
    mut v_inst_7809_: *mut LeanObject,
    mut v_a_7810_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_7811_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_7812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7813_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_7811_ = lean_ctor_get(v_inst_7809_, 0);
    lean_inc_ref(v_toApplicative_7811_);
    lean_dec_ref(v_inst_7809_);
    v_toPure_7812_ = lean_ctor_get(v_toApplicative_7811_, 1);
    lean_inc(v_toPure_7812_);
    lean_dec_ref(v_toApplicative_7811_);
    lean_inc(v_a_7810_);
    v___x_7813_ = lean_apply_2(v_toPure_7812_, lean_box(0), v_a_7810_);
    return v___x_7813_;
}
pub unsafe fn l_ReaderT_read___redArg___boxed(
    mut v_inst_7814_: *mut LeanObject,
    mut v_a_7815_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7816_: *mut LeanObject = core::ptr::null_mut();
    v_res_7816_ = l_ReaderT_read___redArg(v_inst_7814_, v_a_7815_);
    lean_dec(v_a_7815_);
    return v_res_7816_;
}
pub unsafe fn l_ReaderT_read(
    mut v_00_u03c1_7817_: *mut LeanObject,
    mut v_m_7818_: *mut LeanObject,
    mut v_inst_7819_: *mut LeanObject,
    mut v_a_7820_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_7821_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_7822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7823_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_7821_ = lean_ctor_get(v_inst_7819_, 0);
    lean_inc_ref(v_toApplicative_7821_);
    lean_dec_ref(v_inst_7819_);
    v_toPure_7822_ = lean_ctor_get(v_toApplicative_7821_, 1);
    lean_inc(v_toPure_7822_);
    lean_dec_ref(v_toApplicative_7821_);
    lean_inc(v_a_7820_);
    v___x_7823_ = lean_apply_2(v_toPure_7822_, lean_box(0), v_a_7820_);
    return v___x_7823_;
}
pub unsafe fn l_ReaderT_read___boxed(
    mut v_00_u03c1_7824_: *mut LeanObject,
    mut v_m_7825_: *mut LeanObject,
    mut v_inst_7826_: *mut LeanObject,
    mut v_a_7827_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7828_: *mut LeanObject = core::ptr::null_mut();
    v_res_7828_ = l_ReaderT_read(v_00_u03c1_7824_, v_m_7825_, v_inst_7826_, v_a_7827_);
    lean_dec(v_a_7827_);
    return v_res_7828_;
}
pub unsafe fn l_ReaderT_pure___redArg(
    mut v_inst_7829_: *mut LeanObject,
    mut v_a_7830_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_7831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_7832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7833_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_7831_ = lean_ctor_get(v_inst_7829_, 0);
    lean_inc_ref(v_toApplicative_7831_);
    lean_dec_ref(v_inst_7829_);
    v_toPure_7832_ = lean_ctor_get(v_toApplicative_7831_, 1);
    lean_inc(v_toPure_7832_);
    lean_dec_ref(v_toApplicative_7831_);
    v___x_7833_ = lean_apply_2(v_toPure_7832_, lean_box(0), v_a_7830_);
    return v___x_7833_;
}
pub unsafe fn l_ReaderT_pure(
    mut v_00_u03c1_7834_: *mut LeanObject,
    mut v_m_7835_: *mut LeanObject,
    mut v_inst_7836_: *mut LeanObject,
    mut v_00_u03b1_7837_: *mut LeanObject,
    mut v_a_7838_: *mut LeanObject,
    mut v_x_7839_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_7840_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_7841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7842_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_7840_ = lean_ctor_get(v_inst_7836_, 0);
    lean_inc_ref(v_toApplicative_7840_);
    lean_dec_ref(v_inst_7836_);
    v_toPure_7841_ = lean_ctor_get(v_toApplicative_7840_, 1);
    lean_inc(v_toPure_7841_);
    lean_dec_ref(v_toApplicative_7840_);
    v___x_7842_ = lean_apply_2(v_toPure_7841_, lean_box(0), v_a_7838_);
    return v___x_7842_;
}
pub unsafe fn l_ReaderT_pure___boxed(
    mut v_00_u03c1_7843_: *mut LeanObject,
    mut v_m_7844_: *mut LeanObject,
    mut v_inst_7845_: *mut LeanObject,
    mut v_00_u03b1_7846_: *mut LeanObject,
    mut v_a_7847_: *mut LeanObject,
    mut v_x_7848_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7849_: *mut LeanObject = core::ptr::null_mut();
    v_res_7849_ = l_ReaderT_pure(
        v_00_u03c1_7843_,
        v_m_7844_,
        v_inst_7845_,
        v_00_u03b1_7846_,
        v_a_7847_,
        v_x_7848_,
    );
    lean_dec(v_x_7848_);
    return v_res_7849_;
}
pub unsafe fn l_ReaderT_bind___redArg___lam__0(
    mut v_f_7850_: *mut LeanObject,
    mut v_r_7851_: *mut LeanObject,
    mut v_a_7852_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7853_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_r_7851_);
    v___x_7853_ = lean_apply_2(v_f_7850_, v_a_7852_, v_r_7851_);
    return v___x_7853_;
}
pub unsafe fn l_ReaderT_bind___redArg___lam__0___boxed(
    mut v_f_7854_: *mut LeanObject,
    mut v_r_7855_: *mut LeanObject,
    mut v_a_7856_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7857_: *mut LeanObject = core::ptr::null_mut();
    v_res_7857_ = l_ReaderT_bind___redArg___lam__0(v_f_7854_, v_r_7855_, v_a_7856_);
    lean_dec(v_r_7855_);
    return v_res_7857_;
}
pub unsafe fn l_ReaderT_bind___redArg(
    mut v_inst_7858_: *mut LeanObject,
    mut v_x_7859_: *mut LeanObject,
    mut v_f_7860_: *mut LeanObject,
    mut v_r_7861_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toBind_7862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7865_: *mut LeanObject = core::ptr::null_mut();
    v_toBind_7862_ = lean_ctor_get(v_inst_7858_, 1);
    lean_inc(v_toBind_7862_);
    lean_dec_ref(v_inst_7858_);
    lean_inc_n(v_r_7861_, 2);
    v___f_7863_ = lean_alloc_closure(
        l_ReaderT_bind___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_7863_, 0, v_f_7860_);
    lean_closure_set(v___f_7863_, 1, v_r_7861_);
    v___x_7864_ = lean_apply_1(v_x_7859_, v_r_7861_);
    v___x_7865_ = lean_apply_4(
        v_toBind_7862_,
        lean_box(0),
        lean_box(0),
        v___x_7864_,
        v___f_7863_,
    );
    return v___x_7865_;
}
pub unsafe fn l_ReaderT_bind___redArg___boxed(
    mut v_inst_7866_: *mut LeanObject,
    mut v_x_7867_: *mut LeanObject,
    mut v_f_7868_: *mut LeanObject,
    mut v_r_7869_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7870_: *mut LeanObject = core::ptr::null_mut();
    v_res_7870_ = l_ReaderT_bind___redArg(v_inst_7866_, v_x_7867_, v_f_7868_, v_r_7869_);
    lean_dec(v_r_7869_);
    return v_res_7870_;
}
pub unsafe fn l_ReaderT_bind(
    mut v_00_u03c1_7871_: *mut LeanObject,
    mut v_m_7872_: *mut LeanObject,
    mut v_inst_7873_: *mut LeanObject,
    mut v_00_u03b1_7874_: *mut LeanObject,
    mut v_00_u03b2_7875_: *mut LeanObject,
    mut v_x_7876_: *mut LeanObject,
    mut v_f_7877_: *mut LeanObject,
    mut v_r_7878_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toBind_7879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7882_: *mut LeanObject = core::ptr::null_mut();
    v_toBind_7879_ = lean_ctor_get(v_inst_7873_, 1);
    lean_inc(v_toBind_7879_);
    lean_dec_ref(v_inst_7873_);
    lean_inc_n(v_r_7878_, 2);
    v___f_7880_ = lean_alloc_closure(
        l_ReaderT_bind___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_7880_, 0, v_f_7877_);
    lean_closure_set(v___f_7880_, 1, v_r_7878_);
    v___x_7881_ = lean_apply_1(v_x_7876_, v_r_7878_);
    v___x_7882_ = lean_apply_4(
        v_toBind_7879_,
        lean_box(0),
        lean_box(0),
        v___x_7881_,
        v___f_7880_,
    );
    return v___x_7882_;
}
pub unsafe fn l_ReaderT_bind___boxed(
    mut v_00_u03c1_7883_: *mut LeanObject,
    mut v_m_7884_: *mut LeanObject,
    mut v_inst_7885_: *mut LeanObject,
    mut v_00_u03b1_7886_: *mut LeanObject,
    mut v_00_u03b2_7887_: *mut LeanObject,
    mut v_x_7888_: *mut LeanObject,
    mut v_f_7889_: *mut LeanObject,
    mut v_r_7890_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7891_: *mut LeanObject = core::ptr::null_mut();
    v_res_7891_ = l_ReaderT_bind(
        v_00_u03c1_7883_,
        v_m_7884_,
        v_inst_7885_,
        v_00_u03b1_7886_,
        v_00_u03b2_7887_,
        v_x_7888_,
        v_f_7889_,
        v_r_7890_,
    );
    lean_dec(v_r_7890_);
    return v_res_7891_;
}
pub unsafe fn l_ReaderT_instFunctorOfMonad___redArg___lam__0(
    mut v_toFunctor_7892_: *mut LeanObject,
    mut v_00_u03b1_7893_: *mut LeanObject,
    mut v_00_u03b2_7894_: *mut LeanObject,
    mut v_f_7895_: *mut LeanObject,
    mut v_x_7896_: *mut LeanObject,
    mut v_r_7897_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_map_7898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7900_: *mut LeanObject = core::ptr::null_mut();
    v_map_7898_ = lean_ctor_get(v_toFunctor_7892_, 0);
    lean_inc(v_map_7898_);
    lean_dec_ref(v_toFunctor_7892_);
    v___x_7899_ = lean_apply_1(v_x_7896_, v_r_7897_);
    v___x_7900_ = lean_apply_4(
        v_map_7898_,
        lean_box(0),
        lean_box(0),
        v_f_7895_,
        v___x_7899_,
    );
    return v___x_7900_;
}
pub unsafe fn l_ReaderT_instFunctorOfMonad___redArg___lam__1(
    mut v_toFunctor_7901_: *mut LeanObject,
    mut v_00_u03b1_7902_: *mut LeanObject,
    mut v_00_u03b2_7903_: *mut LeanObject,
    mut v_a_7904_: *mut LeanObject,
    mut v_x_7905_: *mut LeanObject,
    mut v_r_7906_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_mapConst_7907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7909_: *mut LeanObject = core::ptr::null_mut();
    v_mapConst_7907_ = lean_ctor_get(v_toFunctor_7901_, 1);
    lean_inc(v_mapConst_7907_);
    lean_dec_ref(v_toFunctor_7901_);
    v___x_7908_ = lean_apply_1(v_x_7905_, v_r_7906_);
    v___x_7909_ = lean_apply_4(
        v_mapConst_7907_,
        lean_box(0),
        lean_box(0),
        v_a_7904_,
        v___x_7908_,
    );
    return v___x_7909_;
}
pub unsafe fn l_ReaderT_instFunctorOfMonad___redArg(
    mut v_inst_7910_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_7911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7913_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7914_: u8 = 0;
    let mut v_toFunctor_7915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7920_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7921_: u8 = 0;
    let mut v_unused_7922_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_7911_ = lean_ctor_get(v_inst_7910_, 0);
                v_isSharedCheck_7921_ = (!lean_is_exclusive(v_inst_7910_)) as u8;
                if v_isSharedCheck_7921_ == 0 {
                    v_unused_7922_ = lean_ctor_get(v_inst_7910_, 1);
                    lean_dec(v_unused_7922_);
                    v___x_7913_ = v_inst_7910_;
                    v_isShared_7914_ = v_isSharedCheck_7921_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_toApplicative_7911_);
                    lean_dec(v_inst_7910_);
                    v___x_7913_ = lean_box(0);
                    v_isShared_7914_ = v_isSharedCheck_7921_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_7915_ = lean_ctor_get(v_toApplicative_7911_, 0);
                lean_inc_ref_n(v_toFunctor_7915_, 2);
                lean_dec_ref(v_toApplicative_7911_);
                v___f_7916_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_7916_, 0, v_toFunctor_7915_);
                v___f_7917_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_7917_, 0, v_toFunctor_7915_);
                if v_isShared_7914_ == 0 {
                    lean_ctor_set(v___x_7913_, 1, v___f_7917_);
                    lean_ctor_set(v___x_7913_, 0, v___f_7916_);
                    v___x_7919_ = v___x_7913_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7920_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7920_, 0, v___f_7916_);
                    lean_ctor_set(v_reuseFailAlloc_7920_, 1, v___f_7917_);
                    v___x_7919_ = v_reuseFailAlloc_7920_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7919_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_ReaderT_instFunctorOfMonad(
    mut v_00_u03c1_7923_: *mut LeanObject,
    mut v_m_7924_: *mut LeanObject,
    mut v_inst_7925_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_7926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7928_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7929_: u8 = 0;
    let mut v_toFunctor_7930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7936_: u8 = 0;
    let mut v_unused_7937_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_7926_ = lean_ctor_get(v_inst_7925_, 0);
                v_isSharedCheck_7936_ = (!lean_is_exclusive(v_inst_7925_)) as u8;
                if v_isSharedCheck_7936_ == 0 {
                    v_unused_7937_ = lean_ctor_get(v_inst_7925_, 1);
                    lean_dec(v_unused_7937_);
                    v___x_7928_ = v_inst_7925_;
                    v_isShared_7929_ = v_isSharedCheck_7936_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_toApplicative_7926_);
                    lean_dec(v_inst_7925_);
                    v___x_7928_ = lean_box(0);
                    v_isShared_7929_ = v_isSharedCheck_7936_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_7930_ = lean_ctor_get(v_toApplicative_7926_, 0);
                lean_inc_ref_n(v_toFunctor_7930_, 2);
                lean_dec_ref(v_toApplicative_7926_);
                v___f_7931_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_7931_, 0, v_toFunctor_7930_);
                v___f_7932_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_7932_, 0, v_toFunctor_7930_);
                if v_isShared_7929_ == 0 {
                    lean_ctor_set(v___x_7928_, 1, v___f_7932_);
                    lean_ctor_set(v___x_7928_, 0, v___f_7931_);
                    v___x_7934_ = v___x_7928_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7935_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7935_, 0, v___f_7931_);
                    lean_ctor_set(v_reuseFailAlloc_7935_, 1, v___f_7932_);
                    v___x_7934_ = v_reuseFailAlloc_7935_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7934_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_ReaderT_instApplicativeOfMonad___redArg___lam__0(
    mut v_b_7938_: *mut LeanObject,
    mut v_r_7939_: *mut LeanObject,
    mut v_x_7940_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7942_: *mut LeanObject = core::ptr::null_mut();
    v___x_7941_ = lean_box(0);
    v___x_7942_ = lean_apply_2(v_b_7938_, v___x_7941_, v_r_7939_);
    return v___x_7942_;
}
pub unsafe fn l_ReaderT_instApplicativeOfMonad___redArg___lam__1(
    mut v_toSeqRight_7943_: *mut LeanObject,
    mut v_00_u03b1_7944_: *mut LeanObject,
    mut v_00_u03b2_7945_: *mut LeanObject,
    mut v_a_7946_: *mut LeanObject,
    mut v_b_7947_: *mut LeanObject,
    mut v_r_7948_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_7949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7951_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_r_7948_);
    v___f_7949_ = lean_alloc_closure(
        l_ReaderT_instApplicativeOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_7949_, 0, v_b_7947_);
    lean_closure_set(v___f_7949_, 1, v_r_7948_);
    v___x_7950_ = lean_apply_1(v_a_7946_, v_r_7948_);
    v___x_7951_ = lean_apply_4(
        v_toSeqRight_7943_,
        lean_box(0),
        lean_box(0),
        v___x_7950_,
        v___f_7949_,
    );
    return v___x_7951_;
}
pub unsafe fn l_ReaderT_instApplicativeOfMonad___redArg___lam__3(
    mut v_toSeqLeft_7952_: *mut LeanObject,
    mut v_00_u03b1_7953_: *mut LeanObject,
    mut v_00_u03b2_7954_: *mut LeanObject,
    mut v_a_7955_: *mut LeanObject,
    mut v_b_7956_: *mut LeanObject,
    mut v_r_7957_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_7958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7960_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_r_7957_);
    v___f_7958_ = lean_alloc_closure(
        l_ReaderT_instApplicativeOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_7958_, 0, v_b_7956_);
    lean_closure_set(v___f_7958_, 1, v_r_7957_);
    v___x_7959_ = lean_apply_1(v_a_7955_, v_r_7957_);
    v___x_7960_ = lean_apply_4(
        v_toSeqLeft_7952_,
        lean_box(0),
        lean_box(0),
        v___x_7959_,
        v___f_7958_,
    );
    return v___x_7960_;
}
pub unsafe fn l_ReaderT_instApplicativeOfMonad___redArg___lam__2(
    mut v_x_7961_: *mut LeanObject,
    mut v_r_7962_: *mut LeanObject,
    mut v_x_7963_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7965_: *mut LeanObject = core::ptr::null_mut();
    v___x_7964_ = lean_box(0);
    v___x_7965_ = lean_apply_2(v_x_7961_, v___x_7964_, v_r_7962_);
    return v___x_7965_;
}
pub unsafe fn l_ReaderT_instApplicativeOfMonad___redArg___lam__4(
    mut v_toSeq_7966_: *mut LeanObject,
    mut v_00_u03b1_7967_: *mut LeanObject,
    mut v_00_u03b2_7968_: *mut LeanObject,
    mut v_f_7969_: *mut LeanObject,
    mut v_x_7970_: *mut LeanObject,
    mut v_r_7971_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_7972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7974_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_r_7971_);
    v___f_7972_ = lean_alloc_closure(
        l_ReaderT_instApplicativeOfMonad___redArg___lam__2 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_7972_, 0, v_x_7970_);
    lean_closure_set(v___f_7972_, 1, v_r_7971_);
    v___x_7973_ = lean_apply_1(v_f_7969_, v_r_7971_);
    v___x_7974_ = lean_apply_4(
        v_toSeq_7966_,
        lean_box(0),
        lean_box(0),
        v___x_7973_,
        v___f_7972_,
    );
    return v___x_7974_;
}
pub unsafe fn l_ReaderT_instApplicativeOfMonad___redArg(
    mut v_inst_7975_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_7976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_7977_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeq_7978_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_7979_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_7980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7982_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7983_: u8 = 0;
    let mut v___f_7984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7992_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7993_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7994_: u8 = 0;
    let mut v_unused_7995_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_7976_ = lean_ctor_get(v_inst_7975_, 0);
                lean_inc_ref(v_toApplicative_7976_);
                v_toFunctor_7977_ = lean_ctor_get(v_toApplicative_7976_, 0);
                v_toSeq_7978_ = lean_ctor_get(v_toApplicative_7976_, 2);
                v_toSeqLeft_7979_ = lean_ctor_get(v_toApplicative_7976_, 3);
                v_toSeqRight_7980_ = lean_ctor_get(v_toApplicative_7976_, 4);
                v_isSharedCheck_7994_ = (!lean_is_exclusive(v_toApplicative_7976_)) as u8;
                if v_isSharedCheck_7994_ == 0 {
                    v_unused_7995_ = lean_ctor_get(v_toApplicative_7976_, 1);
                    lean_dec(v_unused_7995_);
                    v___x_7982_ = v_toApplicative_7976_;
                    v_isShared_7983_ = v_isSharedCheck_7994_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_toSeqRight_7980_);
                    lean_inc(v_toSeqLeft_7979_);
                    lean_inc(v_toSeq_7978_);
                    lean_inc(v_toFunctor_7977_);
                    lean_dec(v_toApplicative_7976_);
                    v___x_7982_ = lean_box(0);
                    v_isShared_7983_ = v_isSharedCheck_7994_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_7984_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_7984_, 0, v_toSeqRight_7980_);
                v___f_7985_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_7985_, 0, v_toSeqLeft_7979_);
                v___f_7986_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_7986_, 0, v_toSeq_7978_);
                lean_inc_ref(v_toFunctor_7977_);
                v___f_7987_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_7987_, 0, v_toFunctor_7977_);
                v___f_7988_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_7988_, 0, v_toFunctor_7977_);
                v___x_7989_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_7989_, 0, v___f_7987_);
                lean_ctor_set(v___x_7989_, 1, v___f_7988_);
                v___x_7990_ =
                    lean_alloc_closure(l_ReaderT_pure___boxed as *mut core::ffi::c_void, 6, 3);
                lean_closure_set(v___x_7990_, 0, lean_box(0));
                lean_closure_set(v___x_7990_, 1, lean_box(0));
                lean_closure_set(v___x_7990_, 2, v_inst_7975_);
                if v_isShared_7983_ == 0 {
                    lean_ctor_set(v___x_7982_, 4, v___f_7984_);
                    lean_ctor_set(v___x_7982_, 3, v___f_7985_);
                    lean_ctor_set(v___x_7982_, 2, v___f_7986_);
                    lean_ctor_set(v___x_7982_, 1, v___x_7990_);
                    lean_ctor_set(v___x_7982_, 0, v___x_7989_);
                    v___x_7992_ = v___x_7982_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7993_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7993_, 0, v___x_7989_);
                    lean_ctor_set(v_reuseFailAlloc_7993_, 1, v___x_7990_);
                    lean_ctor_set(v_reuseFailAlloc_7993_, 2, v___f_7986_);
                    lean_ctor_set(v_reuseFailAlloc_7993_, 3, v___f_7985_);
                    lean_ctor_set(v_reuseFailAlloc_7993_, 4, v___f_7984_);
                    v___x_7992_ = v_reuseFailAlloc_7993_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7992_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_ReaderT_instApplicativeOfMonad(
    mut v_00_u03c1_7996_: *mut LeanObject,
    mut v_m_7997_: *mut LeanObject,
    mut v_inst_7998_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_7999_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_8000_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeq_8001_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_8002_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_8003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8006_: u8 = 0;
    let mut v___f_8007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8016_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8017_: u8 = 0;
    let mut v_unused_8018_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_7999_ = lean_ctor_get(v_inst_7998_, 0);
                lean_inc_ref(v_toApplicative_7999_);
                v_toFunctor_8000_ = lean_ctor_get(v_toApplicative_7999_, 0);
                v_toSeq_8001_ = lean_ctor_get(v_toApplicative_7999_, 2);
                v_toSeqLeft_8002_ = lean_ctor_get(v_toApplicative_7999_, 3);
                v_toSeqRight_8003_ = lean_ctor_get(v_toApplicative_7999_, 4);
                v_isSharedCheck_8017_ = (!lean_is_exclusive(v_toApplicative_7999_)) as u8;
                if v_isSharedCheck_8017_ == 0 {
                    v_unused_8018_ = lean_ctor_get(v_toApplicative_7999_, 1);
                    lean_dec(v_unused_8018_);
                    v___x_8005_ = v_toApplicative_7999_;
                    v_isShared_8006_ = v_isSharedCheck_8017_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_toSeqRight_8003_);
                    lean_inc(v_toSeqLeft_8002_);
                    lean_inc(v_toSeq_8001_);
                    lean_inc(v_toFunctor_8000_);
                    lean_dec(v_toApplicative_7999_);
                    v___x_8005_ = lean_box(0);
                    v_isShared_8006_ = v_isSharedCheck_8017_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_8007_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_8007_, 0, v_toSeqRight_8003_);
                v___f_8008_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_8008_, 0, v_toSeqLeft_8002_);
                v___f_8009_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_8009_, 0, v_toSeq_8001_);
                lean_inc_ref(v_toFunctor_8000_);
                v___f_8010_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_8010_, 0, v_toFunctor_8000_);
                v___f_8011_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_8011_, 0, v_toFunctor_8000_);
                v___x_8012_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_8012_, 0, v___f_8010_);
                lean_ctor_set(v___x_8012_, 1, v___f_8011_);
                v___x_8013_ =
                    lean_alloc_closure(l_ReaderT_pure___boxed as *mut core::ffi::c_void, 6, 3);
                lean_closure_set(v___x_8013_, 0, lean_box(0));
                lean_closure_set(v___x_8013_, 1, lean_box(0));
                lean_closure_set(v___x_8013_, 2, v_inst_7998_);
                if v_isShared_8006_ == 0 {
                    lean_ctor_set(v___x_8005_, 4, v___f_8007_);
                    lean_ctor_set(v___x_8005_, 3, v___f_8008_);
                    lean_ctor_set(v___x_8005_, 2, v___f_8009_);
                    lean_ctor_set(v___x_8005_, 1, v___x_8013_);
                    lean_ctor_set(v___x_8005_, 0, v___x_8012_);
                    v___x_8015_ = v___x_8005_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8016_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8016_, 0, v___x_8012_);
                    lean_ctor_set(v_reuseFailAlloc_8016_, 1, v___x_8013_);
                    lean_ctor_set(v_reuseFailAlloc_8016_, 2, v___f_8009_);
                    lean_ctor_set(v_reuseFailAlloc_8016_, 3, v___f_8008_);
                    lean_ctor_set(v_reuseFailAlloc_8016_, 4, v___f_8007_);
                    v___x_8015_ = v_reuseFailAlloc_8016_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_8015_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_ReaderT_instMonad___redArg(mut v_inst_8019_: *mut LeanObject) -> *mut LeanObject {
    let mut v_toApplicative_8020_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_8021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeq_8022_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_8023_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_8024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8026_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8027_: u8 = 0;
    let mut v___f_8028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8039_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8040_: u8 = 0;
    let mut v_unused_8041_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_8020_ = lean_ctor_get(v_inst_8019_, 0);
                lean_inc_ref(v_toApplicative_8020_);
                v_toFunctor_8021_ = lean_ctor_get(v_toApplicative_8020_, 0);
                v_toSeq_8022_ = lean_ctor_get(v_toApplicative_8020_, 2);
                v_toSeqLeft_8023_ = lean_ctor_get(v_toApplicative_8020_, 3);
                v_toSeqRight_8024_ = lean_ctor_get(v_toApplicative_8020_, 4);
                v_isSharedCheck_8040_ = (!lean_is_exclusive(v_toApplicative_8020_)) as u8;
                if v_isSharedCheck_8040_ == 0 {
                    v_unused_8041_ = lean_ctor_get(v_toApplicative_8020_, 1);
                    lean_dec(v_unused_8041_);
                    v___x_8026_ = v_toApplicative_8020_;
                    v_isShared_8027_ = v_isSharedCheck_8040_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_toSeqRight_8024_);
                    lean_inc(v_toSeqLeft_8023_);
                    lean_inc(v_toSeq_8022_);
                    lean_inc(v_toFunctor_8021_);
                    lean_dec(v_toApplicative_8020_);
                    v___x_8026_ = lean_box(0);
                    v_isShared_8027_ = v_isSharedCheck_8040_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_8028_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_8028_, 0, v_toSeqRight_8024_);
                v___f_8029_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_8029_, 0, v_toSeqLeft_8023_);
                v___f_8030_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_8030_, 0, v_toSeq_8022_);
                lean_inc_ref(v_toFunctor_8021_);
                v___f_8031_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_8031_, 0, v_toFunctor_8021_);
                v___f_8032_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_8032_, 0, v_toFunctor_8021_);
                v___x_8033_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_8033_, 0, v___f_8031_);
                lean_ctor_set(v___x_8033_, 1, v___f_8032_);
                lean_inc_ref(v_inst_8019_);
                v___x_8034_ =
                    lean_alloc_closure(l_ReaderT_pure___boxed as *mut core::ffi::c_void, 6, 3);
                lean_closure_set(v___x_8034_, 0, lean_box(0));
                lean_closure_set(v___x_8034_, 1, lean_box(0));
                lean_closure_set(v___x_8034_, 2, v_inst_8019_);
                if v_isShared_8027_ == 0 {
                    lean_ctor_set(v___x_8026_, 4, v___f_8028_);
                    lean_ctor_set(v___x_8026_, 3, v___f_8029_);
                    lean_ctor_set(v___x_8026_, 2, v___f_8030_);
                    lean_ctor_set(v___x_8026_, 1, v___x_8034_);
                    lean_ctor_set(v___x_8026_, 0, v___x_8033_);
                    v___x_8036_ = v___x_8026_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8039_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8039_, 0, v___x_8033_);
                    lean_ctor_set(v_reuseFailAlloc_8039_, 1, v___x_8034_);
                    lean_ctor_set(v_reuseFailAlloc_8039_, 2, v___f_8030_);
                    lean_ctor_set(v_reuseFailAlloc_8039_, 3, v___f_8029_);
                    lean_ctor_set(v_reuseFailAlloc_8039_, 4, v___f_8028_);
                    v___x_8036_ = v_reuseFailAlloc_8039_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_8037_ =
                    lean_alloc_closure(l_ReaderT_bind___boxed as *mut core::ffi::c_void, 8, 3);
                lean_closure_set(v___x_8037_, 0, lean_box(0));
                lean_closure_set(v___x_8037_, 1, lean_box(0));
                lean_closure_set(v___x_8037_, 2, v_inst_8019_);
                v___x_8038_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_8038_, 0, v___x_8036_);
                lean_ctor_set(v___x_8038_, 1, v___x_8037_);
                return v___x_8038_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_ReaderT_instMonad(
    mut v_00_u03c1_8042_: *mut LeanObject,
    mut v_m_8043_: *mut LeanObject,
    mut v_inst_8044_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8045_: *mut LeanObject = core::ptr::null_mut();
    v___x_8045_ = l_ReaderT_instMonad___redArg(v_inst_8044_);
    return v___x_8045_;
}
pub unsafe fn l_ReaderT_instMonadFunctor___lam__0(
    mut v_00_u03b1_8046_: *mut LeanObject,
    mut v_f_8047_: *mut LeanObject,
    mut v_x_8048_: *mut LeanObject,
    mut v_ctx_8049_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8051_: *mut LeanObject = core::ptr::null_mut();
    v___x_8050_ = lean_apply_1(v_x_8048_, v_ctx_8049_);
    v___x_8051_ = lean_apply_2(v_f_8047_, lean_box(0), v___x_8050_);
    return v___x_8051_;
}
pub unsafe fn l_ReaderT_instMonadFunctor(
    mut v_00_u03c1_8053_: *mut LeanObject,
    mut v_m_8054_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_8055_: *mut LeanObject = core::ptr::null_mut();
    v___f_8055_ = l_ReaderT_instMonadFunctor___closed__0;
    return v___f_8055_;
}
pub unsafe fn l_ReaderT_adapt___redArg(
    mut v_f_8056_: *mut LeanObject,
    mut v_x_8057_: *mut LeanObject,
    mut v_r_8058_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8060_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_r_8058_);
    v___x_8059_ = lean_apply_1(v_f_8056_, v_r_8058_);
    v___x_8060_ = lean_apply_1(v_x_8057_, v___x_8059_);
    return v___x_8060_;
}
pub unsafe fn l_ReaderT_adapt___redArg___boxed(
    mut v_f_8061_: *mut LeanObject,
    mut v_x_8062_: *mut LeanObject,
    mut v_r_8063_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8064_: *mut LeanObject = core::ptr::null_mut();
    v_res_8064_ = l_ReaderT_adapt___redArg(v_f_8061_, v_x_8062_, v_r_8063_);
    lean_dec(v_r_8063_);
    return v_res_8064_;
}
pub unsafe fn l_ReaderT_adapt(
    mut v_00_u03c1_8065_: *mut LeanObject,
    mut v_m_8066_: *mut LeanObject,
    mut v_00_u03c1_x27_8067_: *mut LeanObject,
    mut v_00_u03b1_8068_: *mut LeanObject,
    mut v_f_8069_: *mut LeanObject,
    mut v_x_8070_: *mut LeanObject,
    mut v_r_8071_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8073_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_r_8071_);
    v___x_8072_ = lean_apply_1(v_f_8069_, v_r_8071_);
    v___x_8073_ = lean_apply_1(v_x_8070_, v___x_8072_);
    return v___x_8073_;
}
pub unsafe fn l_ReaderT_adapt___boxed(
    mut v_00_u03c1_8074_: *mut LeanObject,
    mut v_m_8075_: *mut LeanObject,
    mut v_00_u03c1_x27_8076_: *mut LeanObject,
    mut v_00_u03b1_8077_: *mut LeanObject,
    mut v_f_8078_: *mut LeanObject,
    mut v_x_8079_: *mut LeanObject,
    mut v_r_8080_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8081_: *mut LeanObject = core::ptr::null_mut();
    v_res_8081_ = l_ReaderT_adapt(
        v_00_u03c1_8074_,
        v_m_8075_,
        v_00_u03c1_x27_8076_,
        v_00_u03b1_8077_,
        v_f_8078_,
        v_x_8079_,
        v_r_8080_,
    );
    lean_dec(v_r_8080_);
    return v_res_8081_;
}
pub unsafe fn l_readThe___redArg(mut v_inst_8082_: *mut LeanObject) -> *mut LeanObject {
    lean_inc(v_inst_8082_);
    return v_inst_8082_;
}
pub unsafe fn l_readThe___redArg___boxed(mut v_inst_8083_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_8084_: *mut LeanObject = core::ptr::null_mut();
    v_res_8084_ = l_readThe___redArg(v_inst_8083_);
    lean_dec(v_inst_8083_);
    return v_res_8084_;
}
pub unsafe fn l_readThe(
    mut v_00_u03c1_8085_: *mut LeanObject,
    mut v_m_8086_: *mut LeanObject,
    mut v_inst_8087_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_inst_8087_);
    return v_inst_8087_;
}
pub unsafe fn l_readThe___boxed(
    mut v_00_u03c1_8088_: *mut LeanObject,
    mut v_m_8089_: *mut LeanObject,
    mut v_inst_8090_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8091_: *mut LeanObject = core::ptr::null_mut();
    v_res_8091_ = l_readThe(v_00_u03c1_8088_, v_m_8089_, v_inst_8090_);
    lean_dec(v_inst_8090_);
    return v_res_8091_;
}
pub unsafe fn l_instMonadReaderOfMonadReaderOf___redArg(
    mut v_inst_8092_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_inst_8092_);
    return v_inst_8092_;
}
pub unsafe fn l_instMonadReaderOfMonadReaderOf___redArg___boxed(
    mut v_inst_8093_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8094_: *mut LeanObject = core::ptr::null_mut();
    v_res_8094_ = l_instMonadReaderOfMonadReaderOf___redArg(v_inst_8093_);
    lean_dec(v_inst_8093_);
    return v_res_8094_;
}
pub unsafe fn l_instMonadReaderOfMonadReaderOf(
    mut v_00_u03c1_8095_: *mut LeanObject,
    mut v_m_8096_: *mut LeanObject,
    mut v_inst_8097_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_inst_8097_);
    return v_inst_8097_;
}
pub unsafe fn l_instMonadReaderOfMonadReaderOf___boxed(
    mut v_00_u03c1_8098_: *mut LeanObject,
    mut v_m_8099_: *mut LeanObject,
    mut v_inst_8100_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8101_: *mut LeanObject = core::ptr::null_mut();
    v_res_8101_ = l_instMonadReaderOfMonadReaderOf(v_00_u03c1_8098_, v_m_8099_, v_inst_8100_);
    lean_dec(v_inst_8100_);
    return v_res_8101_;
}
pub unsafe fn l_instMonadReaderOfOfMonadLift___redArg(
    mut v_inst_8102_: *mut LeanObject,
    mut v_inst_8103_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8104_: *mut LeanObject = core::ptr::null_mut();
    v___x_8104_ = lean_apply_2(v_inst_8102_, lean_box(0), v_inst_8103_);
    return v___x_8104_;
}
pub unsafe fn l_instMonadReaderOfOfMonadLift(
    mut v_00_u03c1_8105_: *mut LeanObject,
    mut v_m_8106_: *mut LeanObject,
    mut v_n_8107_: *mut LeanObject,
    mut v_inst_8108_: *mut LeanObject,
    mut v_inst_8109_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8110_: *mut LeanObject = core::ptr::null_mut();
    v___x_8110_ = lean_apply_2(v_inst_8108_, lean_box(0), v_inst_8109_);
    return v___x_8110_;
}
pub unsafe fn l_instMonadReaderOfReaderTOfMonad___redArg(
    mut v_inst_8111_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8112_: *mut LeanObject = core::ptr::null_mut();
    v___x_8112_ = lean_alloc_closure(l_ReaderT_read___boxed as *mut core::ffi::c_void, 4, 3);
    lean_closure_set(v___x_8112_, 0, lean_box(0));
    lean_closure_set(v___x_8112_, 1, lean_box(0));
    lean_closure_set(v___x_8112_, 2, v_inst_8111_);
    return v___x_8112_;
}
pub unsafe fn l_instMonadReaderOfReaderTOfMonad(
    mut v_00_u03c1_8113_: *mut LeanObject,
    mut v_m_8114_: *mut LeanObject,
    mut v_inst_8115_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8116_: *mut LeanObject = core::ptr::null_mut();
    v___x_8116_ = lean_alloc_closure(l_ReaderT_read___boxed as *mut core::ffi::c_void, 4, 3);
    lean_closure_set(v___x_8116_, 0, lean_box(0));
    lean_closure_set(v___x_8116_, 1, lean_box(0));
    lean_closure_set(v___x_8116_, 2, v_inst_8115_);
    return v___x_8116_;
}
pub unsafe fn l_withTheReader___redArg(
    mut v_inst_8117_: *mut LeanObject,
    mut v_f_8118_: *mut LeanObject,
    mut v_x_8119_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8120_: *mut LeanObject = core::ptr::null_mut();
    v___x_8120_ = lean_apply_3(v_inst_8117_, lean_box(0), v_f_8118_, v_x_8119_);
    return v___x_8120_;
}
pub unsafe fn l_withTheReader(
    mut v_00_u03c1_8121_: *mut LeanObject,
    mut v_m_8122_: *mut LeanObject,
    mut v_inst_8123_: *mut LeanObject,
    mut v_00_u03b1_8124_: *mut LeanObject,
    mut v_f_8125_: *mut LeanObject,
    mut v_x_8126_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8127_: *mut LeanObject = core::ptr::null_mut();
    v___x_8127_ = lean_apply_3(v_inst_8123_, lean_box(0), v_f_8125_, v_x_8126_);
    return v___x_8127_;
}
pub unsafe fn l_instMonadWithReaderOfMonadWithReaderOf___redArg(
    mut v_inst_8128_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8129_: *mut LeanObject = core::ptr::null_mut();
    v___x_8129_ = lean_alloc_closure(l_withTheReader as *mut core::ffi::c_void, 6, 3);
    lean_closure_set(v___x_8129_, 0, lean_box(0));
    lean_closure_set(v___x_8129_, 1, lean_box(0));
    lean_closure_set(v___x_8129_, 2, v_inst_8128_);
    return v___x_8129_;
}
pub unsafe fn l_instMonadWithReaderOfMonadWithReaderOf(
    mut v_00_u03c1_8130_: *mut LeanObject,
    mut v_m_8131_: *mut LeanObject,
    mut v_inst_8132_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8133_: *mut LeanObject = core::ptr::null_mut();
    v___x_8133_ = lean_alloc_closure(l_withTheReader as *mut core::ffi::c_void, 6, 3);
    lean_closure_set(v___x_8133_, 0, lean_box(0));
    lean_closure_set(v___x_8133_, 1, lean_box(0));
    lean_closure_set(v___x_8133_, 2, v_inst_8132_);
    return v___x_8133_;
}
pub unsafe fn l_instMonadWithReaderOfOfMonadFunctor___redArg___lam__0(
    mut v_inst_8134_: *mut LeanObject,
    mut v_f_8135_: *mut LeanObject,
    mut v_00_u03b2_8136_: *mut LeanObject,
    mut v___y_8137_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8138_: *mut LeanObject = core::ptr::null_mut();
    v___x_8138_ = lean_apply_3(v_inst_8134_, lean_box(0), v_f_8135_, v___y_8137_);
    return v___x_8138_;
}
pub unsafe fn l_instMonadWithReaderOfOfMonadFunctor___redArg___lam__1(
    mut v_inst_8139_: *mut LeanObject,
    mut v_inst_8140_: *mut LeanObject,
    mut v_00_u03b1_8141_: *mut LeanObject,
    mut v_f_8142_: *mut LeanObject,
    mut v___y_8143_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_8144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8145_: *mut LeanObject = core::ptr::null_mut();
    v___f_8144_ = lean_alloc_closure(
        l_instMonadWithReaderOfOfMonadFunctor___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_8144_, 0, v_inst_8139_);
    lean_closure_set(v___f_8144_, 1, v_f_8142_);
    v___x_8145_ = lean_apply_3(v_inst_8140_, lean_box(0), v___f_8144_, v___y_8143_);
    return v___x_8145_;
}
pub unsafe fn l_instMonadWithReaderOfOfMonadFunctor___redArg(
    mut v_inst_8146_: *mut LeanObject,
    mut v_inst_8147_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_8148_: *mut LeanObject = core::ptr::null_mut();
    v___f_8148_ = lean_alloc_closure(
        l_instMonadWithReaderOfOfMonadFunctor___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        2,
    );
    lean_closure_set(v___f_8148_, 0, v_inst_8147_);
    lean_closure_set(v___f_8148_, 1, v_inst_8146_);
    return v___f_8148_;
}
pub unsafe fn l_instMonadWithReaderOfOfMonadFunctor(
    mut v_00_u03c1_8149_: *mut LeanObject,
    mut v_m_8150_: *mut LeanObject,
    mut v_n_8151_: *mut LeanObject,
    mut v_inst_8152_: *mut LeanObject,
    mut v_inst_8153_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_8154_: *mut LeanObject = core::ptr::null_mut();
    v___f_8154_ = lean_alloc_closure(
        l_instMonadWithReaderOfOfMonadFunctor___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        2,
    );
    lean_closure_set(v___f_8154_, 0, v_inst_8153_);
    lean_closure_set(v___f_8154_, 1, v_inst_8152_);
    return v___f_8154_;
}
pub unsafe fn l_instMonadWithReaderOfReaderT___lam__0(
    mut v_00_u03b1_8155_: *mut LeanObject,
    mut v_f_8156_: *mut LeanObject,
    mut v_x_8157_: *mut LeanObject,
    mut v_ctx_8158_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8160_: *mut LeanObject = core::ptr::null_mut();
    v___x_8159_ = lean_apply_1(v_f_8156_, v_ctx_8158_);
    v___x_8160_ = lean_apply_1(v_x_8157_, v___x_8159_);
    return v___x_8160_;
}
pub unsafe fn l_instMonadWithReaderOfReaderT(
    mut v_00_u03c1_8162_: *mut LeanObject,
    mut v_m_8163_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_8164_: *mut LeanObject = core::ptr::null_mut();
    v___f_8164_ = l_instMonadWithReaderOfReaderT___closed__0;
    return v___f_8164_;
}
pub unsafe fn l_getThe___redArg(mut v_inst_8165_: *mut LeanObject) -> *mut LeanObject {
    let mut v_get_8166_: *mut LeanObject = core::ptr::null_mut();
    v_get_8166_ = lean_ctor_get(v_inst_8165_, 0);
    lean_inc(v_get_8166_);
    return v_get_8166_;
}
pub unsafe fn l_getThe___redArg___boxed(mut v_inst_8167_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_8168_: *mut LeanObject = core::ptr::null_mut();
    v_res_8168_ = l_getThe___redArg(v_inst_8167_);
    lean_dec_ref(v_inst_8167_);
    return v_res_8168_;
}
pub unsafe fn l_getThe(
    mut v_00_u03c3_8169_: *mut LeanObject,
    mut v_m_8170_: *mut LeanObject,
    mut v_inst_8171_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_get_8172_: *mut LeanObject = core::ptr::null_mut();
    v_get_8172_ = lean_ctor_get(v_inst_8171_, 0);
    lean_inc(v_get_8172_);
    return v_get_8172_;
}
pub unsafe fn l_getThe___boxed(
    mut v_00_u03c3_8173_: *mut LeanObject,
    mut v_m_8174_: *mut LeanObject,
    mut v_inst_8175_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8176_: *mut LeanObject = core::ptr::null_mut();
    v_res_8176_ = l_getThe(v_00_u03c3_8173_, v_m_8174_, v_inst_8175_);
    lean_dec_ref(v_inst_8175_);
    return v_res_8176_;
}
pub unsafe fn l_modifyThe___redArg___lam__0(
    mut v_f_8177_: *mut LeanObject,
    mut v_s_8178_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8181_: *mut LeanObject = core::ptr::null_mut();
    v___x_8179_ = lean_box(0);
    v___x_8180_ = lean_apply_1(v_f_8177_, v_s_8178_);
    v___x_8181_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_8181_, 0, v___x_8179_);
    lean_ctor_set(v___x_8181_, 1, v___x_8180_);
    return v___x_8181_;
}
pub unsafe fn l_modifyThe___redArg(
    mut v_inst_8182_: *mut LeanObject,
    mut v_f_8183_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_modifyGet_8184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8186_: *mut LeanObject = core::ptr::null_mut();
    v_modifyGet_8184_ = lean_ctor_get(v_inst_8182_, 2);
    lean_inc(v_modifyGet_8184_);
    lean_dec_ref(v_inst_8182_);
    v___f_8185_ = lean_alloc_closure(
        l_modifyThe___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_8185_, 0, v_f_8183_);
    v___x_8186_ = lean_apply_2(v_modifyGet_8184_, lean_box(0), v___f_8185_);
    return v___x_8186_;
}
pub unsafe fn l_modifyThe(
    mut v_00_u03c3_8187_: *mut LeanObject,
    mut v_m_8188_: *mut LeanObject,
    mut v_inst_8189_: *mut LeanObject,
    mut v_f_8190_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_modifyGet_8191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8193_: *mut LeanObject = core::ptr::null_mut();
    v_modifyGet_8191_ = lean_ctor_get(v_inst_8189_, 2);
    lean_inc(v_modifyGet_8191_);
    lean_dec_ref(v_inst_8189_);
    v___f_8192_ = lean_alloc_closure(
        l_modifyThe___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_8192_, 0, v_f_8190_);
    v___x_8193_ = lean_apply_2(v_modifyGet_8191_, lean_box(0), v___f_8192_);
    return v___x_8193_;
}
pub unsafe fn l_modifyGetThe___redArg(
    mut v_inst_8194_: *mut LeanObject,
    mut v_f_8195_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_modifyGet_8196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8197_: *mut LeanObject = core::ptr::null_mut();
    v_modifyGet_8196_ = lean_ctor_get(v_inst_8194_, 2);
    lean_inc(v_modifyGet_8196_);
    lean_dec_ref(v_inst_8194_);
    v___x_8197_ = lean_apply_2(v_modifyGet_8196_, lean_box(0), v_f_8195_);
    return v___x_8197_;
}
pub unsafe fn l_modifyGetThe(
    mut v_00_u03b1_8198_: *mut LeanObject,
    mut v_00_u03c3_8199_: *mut LeanObject,
    mut v_m_8200_: *mut LeanObject,
    mut v_inst_8201_: *mut LeanObject,
    mut v_f_8202_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_modifyGet_8203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8204_: *mut LeanObject = core::ptr::null_mut();
    v_modifyGet_8203_ = lean_ctor_get(v_inst_8201_, 2);
    lean_inc(v_modifyGet_8203_);
    lean_dec_ref(v_inst_8201_);
    v___x_8204_ = lean_apply_2(v_modifyGet_8203_, lean_box(0), v_f_8202_);
    return v___x_8204_;
}
pub unsafe fn l_instMonadStateOfMonadStateOf___redArg___lam__0(
    mut v_modifyGet_8205_: *mut LeanObject,
    mut v_00_u03b1_8206_: *mut LeanObject,
    mut v_f_8207_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8208_: *mut LeanObject = core::ptr::null_mut();
    v___x_8208_ = lean_apply_2(v_modifyGet_8205_, lean_box(0), v_f_8207_);
    return v___x_8208_;
}
pub unsafe fn l_instMonadStateOfMonadStateOf___redArg(
    mut v_inst_8209_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_get_8210_: *mut LeanObject = core::ptr::null_mut();
    let mut v_set_8211_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modifyGet_8212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8214_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8215_: u8 = 0;
    let mut v___f_8216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8219_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8220_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_get_8210_ = lean_ctor_get(v_inst_8209_, 0);
                v_set_8211_ = lean_ctor_get(v_inst_8209_, 1);
                v_modifyGet_8212_ = lean_ctor_get(v_inst_8209_, 2);
                v_isSharedCheck_8220_ = (!lean_is_exclusive(v_inst_8209_)) as u8;
                if v_isSharedCheck_8220_ == 0 {
                    v___x_8214_ = v_inst_8209_;
                    v_isShared_8215_ = v_isSharedCheck_8220_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_modifyGet_8212_);
                    lean_inc(v_set_8211_);
                    lean_inc(v_get_8210_);
                    lean_dec(v_inst_8209_);
                    v___x_8214_ = lean_box(0);
                    v_isShared_8215_ = v_isSharedCheck_8220_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_8216_ = lean_alloc_closure(
                    l_instMonadStateOfMonadStateOf___redArg___lam__0 as *mut core::ffi::c_void,
                    3,
                    1,
                );
                lean_closure_set(v___f_8216_, 0, v_modifyGet_8212_);
                if v_isShared_8215_ == 0 {
                    lean_ctor_set(v___x_8214_, 2, v___f_8216_);
                    v___x_8218_ = v___x_8214_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8219_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8219_, 0, v_get_8210_);
                    lean_ctor_set(v_reuseFailAlloc_8219_, 1, v_set_8211_);
                    lean_ctor_set(v_reuseFailAlloc_8219_, 2, v___f_8216_);
                    v___x_8218_ = v_reuseFailAlloc_8219_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_8218_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_instMonadStateOfMonadStateOf(
    mut v_00_u03c3_8221_: *mut LeanObject,
    mut v_m_8222_: *mut LeanObject,
    mut v_inst_8223_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8224_: *mut LeanObject = core::ptr::null_mut();
    v___x_8224_ = l_instMonadStateOfMonadStateOf___redArg(v_inst_8223_);
    return v___x_8224_;
}
pub unsafe fn l_modify___redArg(
    mut v_inst_8225_: *mut LeanObject,
    mut v_f_8226_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_modifyGet_8227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8229_: *mut LeanObject = core::ptr::null_mut();
    v_modifyGet_8227_ = lean_ctor_get(v_inst_8225_, 2);
    lean_inc(v_modifyGet_8227_);
    lean_dec_ref(v_inst_8225_);
    v___f_8228_ = lean_alloc_closure(
        l_modifyThe___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_8228_, 0, v_f_8226_);
    v___x_8229_ = lean_apply_2(v_modifyGet_8227_, lean_box(0), v___f_8228_);
    return v___x_8229_;
}
pub unsafe fn l_modify(
    mut v_00_u03c3_8230_: *mut LeanObject,
    mut v_m_8231_: *mut LeanObject,
    mut v_inst_8232_: *mut LeanObject,
    mut v_f_8233_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_modifyGet_8234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8236_: *mut LeanObject = core::ptr::null_mut();
    v_modifyGet_8234_ = lean_ctor_get(v_inst_8232_, 2);
    lean_inc(v_modifyGet_8234_);
    lean_dec_ref(v_inst_8232_);
    v___f_8235_ = lean_alloc_closure(
        l_modifyThe___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_8235_, 0, v_f_8233_);
    v___x_8236_ = lean_apply_2(v_modifyGet_8234_, lean_box(0), v___f_8235_);
    return v___x_8236_;
}
pub unsafe fn l_getModify___redArg___lam__0(
    mut v_f_8237_: *mut LeanObject,
    mut v_s_8238_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8240_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_s_8238_);
    v___x_8239_ = lean_apply_1(v_f_8237_, v_s_8238_);
    v___x_8240_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_8240_, 0, v_s_8238_);
    lean_ctor_set(v___x_8240_, 1, v___x_8239_);
    return v___x_8240_;
}
pub unsafe fn l_getModify___redArg(
    mut v_inst_8241_: *mut LeanObject,
    mut v_f_8242_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_modifyGet_8243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8245_: *mut LeanObject = core::ptr::null_mut();
    v_modifyGet_8243_ = lean_ctor_get(v_inst_8241_, 2);
    lean_inc(v_modifyGet_8243_);
    lean_dec_ref(v_inst_8241_);
    v___f_8244_ = lean_alloc_closure(
        l_getModify___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_8244_, 0, v_f_8242_);
    v___x_8245_ = lean_apply_2(v_modifyGet_8243_, lean_box(0), v___f_8244_);
    return v___x_8245_;
}
pub unsafe fn l_getModify(
    mut v_00_u03c3_8246_: *mut LeanObject,
    mut v_m_8247_: *mut LeanObject,
    mut v_inst_8248_: *mut LeanObject,
    mut v_f_8249_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_modifyGet_8250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8252_: *mut LeanObject = core::ptr::null_mut();
    v_modifyGet_8250_ = lean_ctor_get(v_inst_8248_, 2);
    lean_inc(v_modifyGet_8250_);
    lean_dec_ref(v_inst_8248_);
    v___f_8251_ = lean_alloc_closure(
        l_getModify___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_8251_, 0, v_f_8249_);
    v___x_8252_ = lean_apply_2(v_modifyGet_8250_, lean_box(0), v___f_8251_);
    return v___x_8252_;
}
pub unsafe fn l_instMonadStateOfOfMonadLift___redArg___lam__0(
    mut v_set_8253_: *mut LeanObject,
    mut v_inst_8254_: *mut LeanObject,
    mut v_s_8255_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8257_: *mut LeanObject = core::ptr::null_mut();
    v___x_8256_ = lean_apply_1(v_set_8253_, v_s_8255_);
    v___x_8257_ = lean_apply_2(v_inst_8254_, lean_box(0), v___x_8256_);
    return v___x_8257_;
}
pub unsafe fn l_instMonadStateOfOfMonadLift___redArg___lam__1(
    mut v_modifyGet_8258_: *mut LeanObject,
    mut v_inst_8259_: *mut LeanObject,
    mut v_00_u03b1_8260_: *mut LeanObject,
    mut v_f_8261_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8263_: *mut LeanObject = core::ptr::null_mut();
    v___x_8262_ = lean_apply_2(v_modifyGet_8258_, lean_box(0), v_f_8261_);
    v___x_8263_ = lean_apply_2(v_inst_8259_, lean_box(0), v___x_8262_);
    return v___x_8263_;
}
pub unsafe fn l_instMonadStateOfOfMonadLift___redArg(
    mut v_inst_8264_: *mut LeanObject,
    mut v_inst_8265_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_get_8266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_set_8267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modifyGet_8268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8270_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8271_: u8 = 0;
    let mut v___f_8272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8276_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8277_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8278_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_get_8266_ = lean_ctor_get(v_inst_8265_, 0);
                v_set_8267_ = lean_ctor_get(v_inst_8265_, 1);
                v_modifyGet_8268_ = lean_ctor_get(v_inst_8265_, 2);
                v_isSharedCheck_8278_ = (!lean_is_exclusive(v_inst_8265_)) as u8;
                if v_isSharedCheck_8278_ == 0 {
                    v___x_8270_ = v_inst_8265_;
                    v_isShared_8271_ = v_isSharedCheck_8278_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_modifyGet_8268_);
                    lean_inc(v_set_8267_);
                    lean_inc(v_get_8266_);
                    lean_dec(v_inst_8265_);
                    v___x_8270_ = lean_box(0);
                    v_isShared_8271_ = v_isSharedCheck_8278_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc_n(v_inst_8264_, 2);
                v___f_8272_ = lean_alloc_closure(
                    l_instMonadStateOfOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
                    3,
                    2,
                );
                lean_closure_set(v___f_8272_, 0, v_set_8267_);
                lean_closure_set(v___f_8272_, 1, v_inst_8264_);
                v___f_8273_ = lean_alloc_closure(
                    l_instMonadStateOfOfMonadLift___redArg___lam__1 as *mut core::ffi::c_void,
                    4,
                    2,
                );
                lean_closure_set(v___f_8273_, 0, v_modifyGet_8268_);
                lean_closure_set(v___f_8273_, 1, v_inst_8264_);
                v___x_8274_ = lean_apply_2(v_inst_8264_, lean_box(0), v_get_8266_);
                if v_isShared_8271_ == 0 {
                    lean_ctor_set(v___x_8270_, 2, v___f_8273_);
                    lean_ctor_set(v___x_8270_, 1, v___f_8272_);
                    lean_ctor_set(v___x_8270_, 0, v___x_8274_);
                    v___x_8276_ = v___x_8270_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8277_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8277_, 0, v___x_8274_);
                    lean_ctor_set(v_reuseFailAlloc_8277_, 1, v___f_8272_);
                    lean_ctor_set(v_reuseFailAlloc_8277_, 2, v___f_8273_);
                    v___x_8276_ = v_reuseFailAlloc_8277_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_8276_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_instMonadStateOfOfMonadLift(
    mut v_00_u03c3_8279_: *mut LeanObject,
    mut v_m_8280_: *mut LeanObject,
    mut v_n_8281_: *mut LeanObject,
    mut v_inst_8282_: *mut LeanObject,
    mut v_inst_8283_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_get_8284_: *mut LeanObject = core::ptr::null_mut();
    let mut v_set_8285_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modifyGet_8286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8289_: u8 = 0;
    let mut v___f_8290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8296_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_get_8284_ = lean_ctor_get(v_inst_8283_, 0);
                v_set_8285_ = lean_ctor_get(v_inst_8283_, 1);
                v_modifyGet_8286_ = lean_ctor_get(v_inst_8283_, 2);
                v_isSharedCheck_8296_ = (!lean_is_exclusive(v_inst_8283_)) as u8;
                if v_isSharedCheck_8296_ == 0 {
                    v___x_8288_ = v_inst_8283_;
                    v_isShared_8289_ = v_isSharedCheck_8296_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_modifyGet_8286_);
                    lean_inc(v_set_8285_);
                    lean_inc(v_get_8284_);
                    lean_dec(v_inst_8283_);
                    v___x_8288_ = lean_box(0);
                    v_isShared_8289_ = v_isSharedCheck_8296_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc_n(v_inst_8282_, 2);
                v___f_8290_ = lean_alloc_closure(
                    l_instMonadStateOfOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
                    3,
                    2,
                );
                lean_closure_set(v___f_8290_, 0, v_set_8285_);
                lean_closure_set(v___f_8290_, 1, v_inst_8282_);
                v___f_8291_ = lean_alloc_closure(
                    l_instMonadStateOfOfMonadLift___redArg___lam__1 as *mut core::ffi::c_void,
                    4,
                    2,
                );
                lean_closure_set(v___f_8291_, 0, v_modifyGet_8286_);
                lean_closure_set(v___f_8291_, 1, v_inst_8282_);
                v___x_8292_ = lean_apply_2(v_inst_8282_, lean_box(0), v_get_8284_);
                if v_isShared_8289_ == 0 {
                    lean_ctor_set(v___x_8288_, 2, v___f_8291_);
                    lean_ctor_set(v___x_8288_, 1, v___f_8290_);
                    lean_ctor_set(v___x_8288_, 0, v___x_8292_);
                    v___x_8294_ = v___x_8288_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8295_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8295_, 0, v___x_8292_);
                    lean_ctor_set(v_reuseFailAlloc_8295_, 1, v___f_8290_);
                    lean_ctor_set(v_reuseFailAlloc_8295_, 2, v___f_8291_);
                    v___x_8294_ = v_reuseFailAlloc_8295_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_8294_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_EStateM_Result_ctorIdx___redArg(mut v_x_8297_: *mut LeanObject) -> *mut LeanObject {
    if lean_obj_tag(v_x_8297_) == 0 {
        let mut v___x_8298_: *mut LeanObject = core::ptr::null_mut();
        v___x_8298_ = lean_unsigned_to_nat(0);
        return v___x_8298_;
    } else {
        let mut v___x_8299_: *mut LeanObject = core::ptr::null_mut();
        v___x_8299_ = lean_unsigned_to_nat(1);
        return v___x_8299_;
    }
}
pub unsafe fn l_EStateM_Result_ctorIdx___redArg___boxed(
    mut v_x_8300_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8301_: *mut LeanObject = core::ptr::null_mut();
    v_res_8301_ = l_EStateM_Result_ctorIdx___redArg(v_x_8300_);
    lean_dec_ref(v_x_8300_);
    return v_res_8301_;
}
pub unsafe fn l_EStateM_Result_ctorIdx(
    mut v_00_u03b5_8302_: *mut LeanObject,
    mut v_00_u03c3_8303_: *mut LeanObject,
    mut v_00_u03b1_8304_: *mut LeanObject,
    mut v_x_8305_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8306_: *mut LeanObject = core::ptr::null_mut();
    v___x_8306_ = l_EStateM_Result_ctorIdx___redArg(v_x_8305_);
    return v___x_8306_;
}
pub unsafe fn l_EStateM_Result_ctorIdx___boxed(
    mut v_00_u03b5_8307_: *mut LeanObject,
    mut v_00_u03c3_8308_: *mut LeanObject,
    mut v_00_u03b1_8309_: *mut LeanObject,
    mut v_x_8310_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8311_: *mut LeanObject = core::ptr::null_mut();
    v_res_8311_ = l_EStateM_Result_ctorIdx(
        v_00_u03b5_8307_,
        v_00_u03c3_8308_,
        v_00_u03b1_8309_,
        v_x_8310_,
    );
    lean_dec_ref(v_x_8310_);
    return v_res_8311_;
}
pub unsafe fn l_EStateM_Result_ctorElim___redArg(
    mut v_t_8312_: *mut LeanObject,
    mut v_k_8313_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_8314_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8316_: *mut LeanObject = core::ptr::null_mut();
    v_a_8314_ = lean_ctor_get(v_t_8312_, 0);
    lean_inc(v_a_8314_);
    v_a_8315_ = lean_ctor_get(v_t_8312_, 1);
    lean_inc(v_a_8315_);
    lean_dec_ref(v_t_8312_);
    v___x_8316_ = lean_apply_2(v_k_8313_, v_a_8314_, v_a_8315_);
    return v___x_8316_;
}
pub unsafe fn l_EStateM_Result_ctorElim(
    mut v_00_u03b5_8317_: *mut LeanObject,
    mut v_00_u03c3_8318_: *mut LeanObject,
    mut v_00_u03b1_8319_: *mut LeanObject,
    mut v_motive_8320_: *mut LeanObject,
    mut v_ctorIdx_8321_: *mut LeanObject,
    mut v_t_8322_: *mut LeanObject,
    mut v_h_8323_: *mut LeanObject,
    mut v_k_8324_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8325_: *mut LeanObject = core::ptr::null_mut();
    v___x_8325_ = l_EStateM_Result_ctorElim___redArg(v_t_8322_, v_k_8324_);
    return v___x_8325_;
}
pub unsafe fn l_EStateM_Result_ctorElim___boxed(
    mut v_00_u03b5_8326_: *mut LeanObject,
    mut v_00_u03c3_8327_: *mut LeanObject,
    mut v_00_u03b1_8328_: *mut LeanObject,
    mut v_motive_8329_: *mut LeanObject,
    mut v_ctorIdx_8330_: *mut LeanObject,
    mut v_t_8331_: *mut LeanObject,
    mut v_h_8332_: *mut LeanObject,
    mut v_k_8333_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8334_: *mut LeanObject = core::ptr::null_mut();
    v_res_8334_ = l_EStateM_Result_ctorElim(
        v_00_u03b5_8326_,
        v_00_u03c3_8327_,
        v_00_u03b1_8328_,
        v_motive_8329_,
        v_ctorIdx_8330_,
        v_t_8331_,
        v_h_8332_,
        v_k_8333_,
    );
    lean_dec(v_ctorIdx_8330_);
    return v_res_8334_;
}
pub unsafe fn l_EStateM_Result_ok_elim___redArg(
    mut v_t_8335_: *mut LeanObject,
    mut v_ok_8336_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8337_: *mut LeanObject = core::ptr::null_mut();
    v___x_8337_ = l_EStateM_Result_ctorElim___redArg(v_t_8335_, v_ok_8336_);
    return v___x_8337_;
}
pub unsafe fn l_EStateM_Result_ok_elim(
    mut v_00_u03b5_8338_: *mut LeanObject,
    mut v_00_u03c3_8339_: *mut LeanObject,
    mut v_00_u03b1_8340_: *mut LeanObject,
    mut v_motive_8341_: *mut LeanObject,
    mut v_t_8342_: *mut LeanObject,
    mut v_h_8343_: *mut LeanObject,
    mut v_ok_8344_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8345_: *mut LeanObject = core::ptr::null_mut();
    v___x_8345_ = l_EStateM_Result_ctorElim___redArg(v_t_8342_, v_ok_8344_);
    return v___x_8345_;
}
pub unsafe fn l_EStateM_Result_error_elim___redArg(
    mut v_t_8346_: *mut LeanObject,
    mut v_error_8347_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8348_: *mut LeanObject = core::ptr::null_mut();
    v___x_8348_ = l_EStateM_Result_ctorElim___redArg(v_t_8346_, v_error_8347_);
    return v___x_8348_;
}
pub unsafe fn l_EStateM_Result_error_elim(
    mut v_00_u03b5_8349_: *mut LeanObject,
    mut v_00_u03c3_8350_: *mut LeanObject,
    mut v_00_u03b1_8351_: *mut LeanObject,
    mut v_motive_8352_: *mut LeanObject,
    mut v_t_8353_: *mut LeanObject,
    mut v_h_8354_: *mut LeanObject,
    mut v_error_8355_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8356_: *mut LeanObject = core::ptr::null_mut();
    v___x_8356_ = l_EStateM_Result_ctorElim___redArg(v_t_8353_, v_error_8355_);
    return v___x_8356_;
}
pub unsafe fn l_EStateM_instInhabitedResult___redArg(
    mut v_inst_8357_: *mut LeanObject,
    mut v_inst_8358_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8359_: *mut LeanObject = core::ptr::null_mut();
    v___x_8359_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_8359_, 0, v_inst_8357_);
    lean_ctor_set(v___x_8359_, 1, v_inst_8358_);
    return v___x_8359_;
}
pub unsafe fn l_EStateM_instInhabitedResult(
    mut v_00_u03b5_8360_: *mut LeanObject,
    mut v_00_u03c3_8361_: *mut LeanObject,
    mut v_00_u03b1_8362_: *mut LeanObject,
    mut v_inst_8363_: *mut LeanObject,
    mut v_inst_8364_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8365_: *mut LeanObject = core::ptr::null_mut();
    v___x_8365_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_8365_, 0, v_inst_8363_);
    lean_ctor_set(v___x_8365_, 1, v_inst_8364_);
    return v___x_8365_;
}
pub unsafe fn l_EStateM_instInhabited___redArg___lam__0(
    mut v_inst_8366_: *mut LeanObject,
    mut v_s_8367_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8368_: *mut LeanObject = core::ptr::null_mut();
    v___x_8368_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_8368_, 0, v_inst_8366_);
    lean_ctor_set(v___x_8368_, 1, v_s_8367_);
    return v___x_8368_;
}
pub unsafe fn l_EStateM_instInhabited___redArg(
    mut v_inst_8369_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_8370_: *mut LeanObject = core::ptr::null_mut();
    v___f_8370_ = lean_alloc_closure(
        l_EStateM_instInhabited___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_8370_, 0, v_inst_8369_);
    return v___f_8370_;
}
pub unsafe fn l_EStateM_instInhabited(
    mut v_00_u03b5_8371_: *mut LeanObject,
    mut v_00_u03c3_8372_: *mut LeanObject,
    mut v_00_u03b1_8373_: *mut LeanObject,
    mut v_inst_8374_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_8375_: *mut LeanObject = core::ptr::null_mut();
    v___f_8375_ = lean_alloc_closure(
        l_EStateM_instInhabited___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_8375_, 0, v_inst_8374_);
    return v___f_8375_;
}
pub unsafe fn l_EStateM_pure___redArg(
    mut v_a_8376_: *mut LeanObject,
    mut v_s_8377_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8378_: *mut LeanObject = core::ptr::null_mut();
    v___x_8378_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_8378_, 0, v_a_8376_);
    lean_ctor_set(v___x_8378_, 1, v_s_8377_);
    return v___x_8378_;
}
pub unsafe fn l_EStateM_pure(
    mut v_00_u03b5_8379_: *mut LeanObject,
    mut v_00_u03c3_8380_: *mut LeanObject,
    mut v_00_u03b1_8381_: *mut LeanObject,
    mut v_a_8382_: *mut LeanObject,
    mut v_s_8383_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8384_: *mut LeanObject = core::ptr::null_mut();
    v___x_8384_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_8384_, 0, v_a_8382_);
    lean_ctor_set(v___x_8384_, 1, v_s_8383_);
    return v___x_8384_;
}
pub unsafe fn l_EStateM_set___redArg(mut v_s_8385_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_8386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8387_: *mut LeanObject = core::ptr::null_mut();
    v___x_8386_ = lean_box(0);
    v___x_8387_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_8387_, 0, v___x_8386_);
    lean_ctor_set(v___x_8387_, 1, v_s_8385_);
    return v___x_8387_;
}
pub unsafe fn l_EStateM_set(
    mut v_00_u03b5_8388_: *mut LeanObject,
    mut v_00_u03c3_8389_: *mut LeanObject,
    mut v_s_8390_: *mut LeanObject,
    mut v_x_8391_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8393_: *mut LeanObject = core::ptr::null_mut();
    v___x_8392_ = lean_box(0);
    v___x_8393_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_8393_, 0, v___x_8392_);
    lean_ctor_set(v___x_8393_, 1, v_s_8390_);
    return v___x_8393_;
}
pub unsafe fn l_EStateM_set___boxed(
    mut v_00_u03b5_8394_: *mut LeanObject,
    mut v_00_u03c3_8395_: *mut LeanObject,
    mut v_s_8396_: *mut LeanObject,
    mut v_x_8397_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8398_: *mut LeanObject = core::ptr::null_mut();
    v_res_8398_ = l_EStateM_set(v_00_u03b5_8394_, v_00_u03c3_8395_, v_s_8396_, v_x_8397_);
    lean_dec(v_x_8397_);
    return v_res_8398_;
}
pub unsafe fn l_EStateM_get___redArg(mut v_s_8399_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_8400_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_s_8399_);
    v___x_8400_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_8400_, 0, v_s_8399_);
    lean_ctor_set(v___x_8400_, 1, v_s_8399_);
    return v___x_8400_;
}
pub unsafe fn l_EStateM_get(
    mut v_00_u03b5_8401_: *mut LeanObject,
    mut v_00_u03c3_8402_: *mut LeanObject,
    mut v_s_8403_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8404_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_s_8403_);
    v___x_8404_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_8404_, 0, v_s_8403_);
    lean_ctor_set(v___x_8404_, 1, v_s_8403_);
    return v___x_8404_;
}
pub unsafe fn l_EStateM_modifyGet___redArg(
    mut v_f_8405_: *mut LeanObject,
    mut v_s_8406_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8407_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_8408_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_8409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8411_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8412_: u8 = 0;
    let mut v___x_8414_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8416_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8407_ = lean_apply_1(v_f_8405_, v_s_8406_);
                v_fst_8408_ = lean_ctor_get(v___x_8407_, 0);
                v_snd_8409_ = lean_ctor_get(v___x_8407_, 1);
                v_isSharedCheck_8416_ = (!lean_is_exclusive(v___x_8407_)) as u8;
                if v_isSharedCheck_8416_ == 0 {
                    v___x_8411_ = v___x_8407_;
                    v_isShared_8412_ = v_isSharedCheck_8416_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_8409_);
                    lean_inc(v_fst_8408_);
                    lean_dec(v___x_8407_);
                    v___x_8411_ = lean_box(0);
                    v_isShared_8412_ = v_isSharedCheck_8416_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_8412_ == 0 {
                    v___x_8414_ = v___x_8411_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8415_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8415_, 0, v_fst_8408_);
                    lean_ctor_set(v_reuseFailAlloc_8415_, 1, v_snd_8409_);
                    v___x_8414_ = v_reuseFailAlloc_8415_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_8414_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_EStateM_modifyGet(
    mut v_00_u03b5_8417_: *mut LeanObject,
    mut v_00_u03c3_8418_: *mut LeanObject,
    mut v_00_u03b1_8419_: *mut LeanObject,
    mut v_f_8420_: *mut LeanObject,
    mut v_s_8421_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8422_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_8423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_8424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8427_: u8 = 0;
    let mut v___x_8429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8430_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8431_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8422_ = lean_apply_1(v_f_8420_, v_s_8421_);
                v_fst_8423_ = lean_ctor_get(v___x_8422_, 0);
                v_snd_8424_ = lean_ctor_get(v___x_8422_, 1);
                v_isSharedCheck_8431_ = (!lean_is_exclusive(v___x_8422_)) as u8;
                if v_isSharedCheck_8431_ == 0 {
                    v___x_8426_ = v___x_8422_;
                    v_isShared_8427_ = v_isSharedCheck_8431_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_8424_);
                    lean_inc(v_fst_8423_);
                    lean_dec(v___x_8422_);
                    v___x_8426_ = lean_box(0);
                    v_isShared_8427_ = v_isSharedCheck_8431_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_8427_ == 0 {
                    v___x_8429_ = v___x_8426_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8430_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8430_, 0, v_fst_8423_);
                    lean_ctor_set(v_reuseFailAlloc_8430_, 1, v_snd_8424_);
                    v___x_8429_ = v_reuseFailAlloc_8430_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_8429_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_EStateM_throw___redArg(
    mut v_e_8432_: *mut LeanObject,
    mut v_s_8433_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8434_: *mut LeanObject = core::ptr::null_mut();
    v___x_8434_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_8434_, 0, v_e_8432_);
    lean_ctor_set(v___x_8434_, 1, v_s_8433_);
    return v___x_8434_;
}
pub unsafe fn l_EStateM_throw(
    mut v_00_u03b5_8435_: *mut LeanObject,
    mut v_00_u03c3_8436_: *mut LeanObject,
    mut v_00_u03b1_8437_: *mut LeanObject,
    mut v_e_8438_: *mut LeanObject,
    mut v_s_8439_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8440_: *mut LeanObject = core::ptr::null_mut();
    v___x_8440_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_8440_, 0, v_e_8438_);
    lean_ctor_set(v___x_8440_, 1, v_s_8439_);
    return v___x_8440_;
}
pub unsafe fn l_EStateM_tryCatch___redArg(
    mut v_inst_8441_: *mut LeanObject,
    mut v_x_8442_: *mut LeanObject,
    mut v_handle_8443_: *mut LeanObject,
    mut v_s_8444_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_save_8445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_restore_8446_: *mut LeanObject = core::ptr::null_mut();
    let mut v_d_8447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8448_: *mut LeanObject = core::ptr::null_mut();
    v_save_8445_ = lean_ctor_get(v_inst_8441_, 0);
    lean_inc(v_save_8445_);
    v_restore_8446_ = lean_ctor_get(v_inst_8441_, 1);
    lean_inc(v_restore_8446_);
    lean_dec_ref(v_inst_8441_);
    lean_inc(v_s_8444_);
    v_d_8447_ = lean_apply_1(v_save_8445_, v_s_8444_);
    v___x_8448_ = lean_apply_1(v_x_8442_, v_s_8444_);
    if lean_obj_tag(v___x_8448_) == 0 {
        lean_dec(v_d_8447_);
        lean_dec(v_restore_8446_);
        lean_dec_ref(v_handle_8443_);
        return v___x_8448_;
    } else {
        let mut v_a_8449_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_8450_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_8451_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_8452_: *mut LeanObject = core::ptr::null_mut();
        v_a_8449_ = lean_ctor_get(v___x_8448_, 0);
        lean_inc(v_a_8449_);
        v_a_8450_ = lean_ctor_get(v___x_8448_, 1);
        lean_inc(v_a_8450_);
        lean_dec_ref_known(v___x_8448_, 2);
        v___x_8451_ = lean_apply_2(v_restore_8446_, v_a_8450_, v_d_8447_);
        v___x_8452_ = lean_apply_2(v_handle_8443_, v_a_8449_, v___x_8451_);
        return v___x_8452_;
    }
}
pub unsafe fn l_EStateM_tryCatch(
    mut v_00_u03b5_8453_: *mut LeanObject,
    mut v_00_u03c3_8454_: *mut LeanObject,
    mut v_00_u03b4_8455_: *mut LeanObject,
    mut v_inst_8456_: *mut LeanObject,
    mut v_00_u03b1_8457_: *mut LeanObject,
    mut v_x_8458_: *mut LeanObject,
    mut v_handle_8459_: *mut LeanObject,
    mut v_s_8460_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_save_8461_: *mut LeanObject = core::ptr::null_mut();
    let mut v_restore_8462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_d_8463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8464_: *mut LeanObject = core::ptr::null_mut();
    v_save_8461_ = lean_ctor_get(v_inst_8456_, 0);
    lean_inc(v_save_8461_);
    v_restore_8462_ = lean_ctor_get(v_inst_8456_, 1);
    lean_inc(v_restore_8462_);
    lean_dec_ref(v_inst_8456_);
    lean_inc(v_s_8460_);
    v_d_8463_ = lean_apply_1(v_save_8461_, v_s_8460_);
    v___x_8464_ = lean_apply_1(v_x_8458_, v_s_8460_);
    if lean_obj_tag(v___x_8464_) == 0 {
        lean_dec(v_d_8463_);
        lean_dec(v_restore_8462_);
        lean_dec_ref(v_handle_8459_);
        return v___x_8464_;
    } else {
        let mut v_a_8465_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_8466_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_8467_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_8468_: *mut LeanObject = core::ptr::null_mut();
        v_a_8465_ = lean_ctor_get(v___x_8464_, 0);
        lean_inc(v_a_8465_);
        v_a_8466_ = lean_ctor_get(v___x_8464_, 1);
        lean_inc(v_a_8466_);
        lean_dec_ref_known(v___x_8464_, 2);
        v___x_8467_ = lean_apply_2(v_restore_8462_, v_a_8466_, v_d_8463_);
        v___x_8468_ = lean_apply_2(v_handle_8459_, v_a_8465_, v___x_8467_);
        return v___x_8468_;
    }
}
pub unsafe fn l_EStateM_orElse___redArg(
    mut v_inst_8469_: *mut LeanObject,
    mut v_x_u2081_8470_: *mut LeanObject,
    mut v_x_u2082_8471_: *mut LeanObject,
    mut v_s_8472_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_save_8473_: *mut LeanObject = core::ptr::null_mut();
    let mut v_restore_8474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_d_8475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8476_: *mut LeanObject = core::ptr::null_mut();
    v_save_8473_ = lean_ctor_get(v_inst_8469_, 0);
    lean_inc(v_save_8473_);
    v_restore_8474_ = lean_ctor_get(v_inst_8469_, 1);
    lean_inc(v_restore_8474_);
    lean_dec_ref(v_inst_8469_);
    lean_inc(v_s_8472_);
    v_d_8475_ = lean_apply_1(v_save_8473_, v_s_8472_);
    v___x_8476_ = lean_apply_1(v_x_u2081_8470_, v_s_8472_);
    if lean_obj_tag(v___x_8476_) == 0 {
        lean_dec(v_d_8475_);
        lean_dec(v_restore_8474_);
        lean_dec_ref(v_x_u2082_8471_);
        return v___x_8476_;
    } else {
        let mut v_a_8477_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_8478_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_8479_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_8480_: *mut LeanObject = core::ptr::null_mut();
        v_a_8477_ = lean_ctor_get(v___x_8476_, 1);
        lean_inc(v_a_8477_);
        lean_dec_ref_known(v___x_8476_, 2);
        v___x_8478_ = lean_box(0);
        v___x_8479_ = lean_apply_2(v_restore_8474_, v_a_8477_, v_d_8475_);
        v___x_8480_ = lean_apply_2(v_x_u2082_8471_, v___x_8478_, v___x_8479_);
        return v___x_8480_;
    }
}
pub unsafe fn l_EStateM_orElse(
    mut v_00_u03b5_8481_: *mut LeanObject,
    mut v_00_u03c3_8482_: *mut LeanObject,
    mut v_00_u03b1_8483_: *mut LeanObject,
    mut v_00_u03b4_8484_: *mut LeanObject,
    mut v_inst_8485_: *mut LeanObject,
    mut v_x_u2081_8486_: *mut LeanObject,
    mut v_x_u2082_8487_: *mut LeanObject,
    mut v_s_8488_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_save_8489_: *mut LeanObject = core::ptr::null_mut();
    let mut v_restore_8490_: *mut LeanObject = core::ptr::null_mut();
    let mut v_d_8491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8492_: *mut LeanObject = core::ptr::null_mut();
    v_save_8489_ = lean_ctor_get(v_inst_8485_, 0);
    lean_inc(v_save_8489_);
    v_restore_8490_ = lean_ctor_get(v_inst_8485_, 1);
    lean_inc(v_restore_8490_);
    lean_dec_ref(v_inst_8485_);
    lean_inc(v_s_8488_);
    v_d_8491_ = lean_apply_1(v_save_8489_, v_s_8488_);
    v___x_8492_ = lean_apply_1(v_x_u2081_8486_, v_s_8488_);
    if lean_obj_tag(v___x_8492_) == 0 {
        lean_dec(v_d_8491_);
        lean_dec(v_restore_8490_);
        lean_dec_ref(v_x_u2082_8487_);
        return v___x_8492_;
    } else {
        let mut v_a_8493_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_8494_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_8495_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_8496_: *mut LeanObject = core::ptr::null_mut();
        v_a_8493_ = lean_ctor_get(v___x_8492_, 1);
        lean_inc(v_a_8493_);
        lean_dec_ref_known(v___x_8492_, 2);
        v___x_8494_ = lean_box(0);
        v___x_8495_ = lean_apply_2(v_restore_8490_, v_a_8493_, v_d_8491_);
        v___x_8496_ = lean_apply_2(v_x_u2082_8487_, v___x_8494_, v___x_8495_);
        return v___x_8496_;
    }
}
pub unsafe fn l_EStateM_adaptExcept___redArg(
    mut v_f_8497_: *mut LeanObject,
    mut v_x_8498_: *mut LeanObject,
    mut v_s_8499_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8500_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8505_: u8 = 0;
    let mut v___x_8507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8508_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8509_: u8 = 0;
    let mut v_a_8510_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8513_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8514_: u8 = 0;
    let mut v___x_8515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8519_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8500_ = lean_apply_1(v_x_8498_, v_s_8499_);
                if lean_obj_tag(v___x_8500_) == 0 {
                    lean_dec(v_f_8497_);
                    v_a_8501_ = lean_ctor_get(v___x_8500_, 0);
                    v_a_8502_ = lean_ctor_get(v___x_8500_, 1);
                    v_isSharedCheck_8509_ = (!lean_is_exclusive(v___x_8500_)) as u8;
                    if v_isSharedCheck_8509_ == 0 {
                        v___x_8504_ = v___x_8500_;
                        v_isShared_8505_ = v_isSharedCheck_8509_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_8502_);
                        lean_inc(v_a_8501_);
                        lean_dec(v___x_8500_);
                        v___x_8504_ = lean_box(0);
                        v_isShared_8505_ = v_isSharedCheck_8509_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_8510_ = lean_ctor_get(v___x_8500_, 0);
                    v_a_8511_ = lean_ctor_get(v___x_8500_, 1);
                    v_isSharedCheck_8519_ = (!lean_is_exclusive(v___x_8500_)) as u8;
                    if v_isSharedCheck_8519_ == 0 {
                        v___x_8513_ = v___x_8500_;
                        v_isShared_8514_ = v_isSharedCheck_8519_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_8511_);
                        lean_inc(v_a_8510_);
                        lean_dec(v___x_8500_);
                        v___x_8513_ = lean_box(0);
                        v_isShared_8514_ = v_isSharedCheck_8519_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_8505_ == 0 {
                    v___x_8507_ = v___x_8504_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8508_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8508_, 0, v_a_8501_);
                    lean_ctor_set(v_reuseFailAlloc_8508_, 1, v_a_8502_);
                    v___x_8507_ = v_reuseFailAlloc_8508_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_8507_;
            }
            3 => {
                v___x_8515_ = lean_apply_1(v_f_8497_, v_a_8510_);
                if v_isShared_8514_ == 0 {
                    lean_ctor_set(v___x_8513_, 0, v___x_8515_);
                    v___x_8517_ = v___x_8513_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_8518_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8518_, 0, v___x_8515_);
                    lean_ctor_set(v_reuseFailAlloc_8518_, 1, v_a_8511_);
                    v___x_8517_ = v_reuseFailAlloc_8518_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_8517_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_EStateM_adaptExcept(
    mut v_00_u03b5_8520_: *mut LeanObject,
    mut v_00_u03c3_8521_: *mut LeanObject,
    mut v_00_u03b1_8522_: *mut LeanObject,
    mut v_00_u03b5_x27_8523_: *mut LeanObject,
    mut v_f_8524_: *mut LeanObject,
    mut v_x_8525_: *mut LeanObject,
    mut v_s_8526_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8527_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8528_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8532_: u8 = 0;
    let mut v___x_8534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8536_: u8 = 0;
    let mut v_a_8537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8541_: u8 = 0;
    let mut v___x_8542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8545_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8546_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8527_ = lean_apply_1(v_x_8525_, v_s_8526_);
                if lean_obj_tag(v___x_8527_) == 0 {
                    lean_dec(v_f_8524_);
                    v_a_8528_ = lean_ctor_get(v___x_8527_, 0);
                    v_a_8529_ = lean_ctor_get(v___x_8527_, 1);
                    v_isSharedCheck_8536_ = (!lean_is_exclusive(v___x_8527_)) as u8;
                    if v_isSharedCheck_8536_ == 0 {
                        v___x_8531_ = v___x_8527_;
                        v_isShared_8532_ = v_isSharedCheck_8536_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_8529_);
                        lean_inc(v_a_8528_);
                        lean_dec(v___x_8527_);
                        v___x_8531_ = lean_box(0);
                        v_isShared_8532_ = v_isSharedCheck_8536_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_8537_ = lean_ctor_get(v___x_8527_, 0);
                    v_a_8538_ = lean_ctor_get(v___x_8527_, 1);
                    v_isSharedCheck_8546_ = (!lean_is_exclusive(v___x_8527_)) as u8;
                    if v_isSharedCheck_8546_ == 0 {
                        v___x_8540_ = v___x_8527_;
                        v_isShared_8541_ = v_isSharedCheck_8546_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_8538_);
                        lean_inc(v_a_8537_);
                        lean_dec(v___x_8527_);
                        v___x_8540_ = lean_box(0);
                        v_isShared_8541_ = v_isSharedCheck_8546_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_8532_ == 0 {
                    v___x_8534_ = v___x_8531_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8535_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8535_, 0, v_a_8528_);
                    lean_ctor_set(v_reuseFailAlloc_8535_, 1, v_a_8529_);
                    v___x_8534_ = v_reuseFailAlloc_8535_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_8534_;
            }
            3 => {
                v___x_8542_ = lean_apply_1(v_f_8524_, v_a_8537_);
                if v_isShared_8541_ == 0 {
                    lean_ctor_set(v___x_8540_, 0, v___x_8542_);
                    v___x_8544_ = v___x_8540_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_8545_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8545_, 0, v___x_8542_);
                    lean_ctor_set(v_reuseFailAlloc_8545_, 1, v_a_8538_);
                    v___x_8544_ = v_reuseFailAlloc_8545_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_8544_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_EStateM_bind___redArg(
    mut v_x_8547_: *mut LeanObject,
    mut v_f_8548_: *mut LeanObject,
    mut v_s_8549_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8550_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8551_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8554_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8558_: u8 = 0;
    let mut v___x_8560_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8561_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8562_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8550_ = lean_apply_1(v_x_8547_, v_s_8549_);
                if lean_obj_tag(v___x_8550_) == 0 {
                    v_a_8551_ = lean_ctor_get(v___x_8550_, 0);
                    lean_inc(v_a_8551_);
                    v_a_8552_ = lean_ctor_get(v___x_8550_, 1);
                    lean_inc(v_a_8552_);
                    lean_dec_ref_known(v___x_8550_, 2);
                    v___x_8553_ = lean_apply_2(v_f_8548_, v_a_8551_, v_a_8552_);
                    return v___x_8553_;
                } else {
                    lean_dec_ref(v_f_8548_);
                    v_a_8554_ = lean_ctor_get(v___x_8550_, 0);
                    v_a_8555_ = lean_ctor_get(v___x_8550_, 1);
                    v_isSharedCheck_8562_ = (!lean_is_exclusive(v___x_8550_)) as u8;
                    if v_isSharedCheck_8562_ == 0 {
                        v___x_8557_ = v___x_8550_;
                        v_isShared_8558_ = v_isSharedCheck_8562_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_8555_);
                        lean_inc(v_a_8554_);
                        lean_dec(v___x_8550_);
                        v___x_8557_ = lean_box(0);
                        v_isShared_8558_ = v_isSharedCheck_8562_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_8558_ == 0 {
                    v___x_8560_ = v___x_8557_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8561_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8561_, 0, v_a_8554_);
                    lean_ctor_set(v_reuseFailAlloc_8561_, 1, v_a_8555_);
                    v___x_8560_ = v_reuseFailAlloc_8561_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_8560_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_EStateM_bind(
    mut v_00_u03b5_8563_: *mut LeanObject,
    mut v_00_u03c3_8564_: *mut LeanObject,
    mut v_00_u03b1_8565_: *mut LeanObject,
    mut v_00_u03b2_8566_: *mut LeanObject,
    mut v_x_8567_: *mut LeanObject,
    mut v_f_8568_: *mut LeanObject,
    mut v_s_8569_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8570_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8578_: u8 = 0;
    let mut v___x_8580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8582_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8570_ = lean_apply_1(v_x_8567_, v_s_8569_);
                if lean_obj_tag(v___x_8570_) == 0 {
                    v_a_8571_ = lean_ctor_get(v___x_8570_, 0);
                    lean_inc(v_a_8571_);
                    v_a_8572_ = lean_ctor_get(v___x_8570_, 1);
                    lean_inc(v_a_8572_);
                    lean_dec_ref_known(v___x_8570_, 2);
                    v___x_8573_ = lean_apply_2(v_f_8568_, v_a_8571_, v_a_8572_);
                    return v___x_8573_;
                } else {
                    lean_dec_ref(v_f_8568_);
                    v_a_8574_ = lean_ctor_get(v___x_8570_, 0);
                    v_a_8575_ = lean_ctor_get(v___x_8570_, 1);
                    v_isSharedCheck_8582_ = (!lean_is_exclusive(v___x_8570_)) as u8;
                    if v_isSharedCheck_8582_ == 0 {
                        v___x_8577_ = v___x_8570_;
                        v_isShared_8578_ = v_isSharedCheck_8582_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_8575_);
                        lean_inc(v_a_8574_);
                        lean_dec(v___x_8570_);
                        v___x_8577_ = lean_box(0);
                        v_isShared_8578_ = v_isSharedCheck_8582_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_8578_ == 0 {
                    v___x_8580_ = v___x_8577_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8581_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8581_, 0, v_a_8574_);
                    lean_ctor_set(v_reuseFailAlloc_8581_, 1, v_a_8575_);
                    v___x_8580_ = v_reuseFailAlloc_8581_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_8580_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_EStateM_map___redArg(
    mut v_f_8583_: *mut LeanObject,
    mut v_x_8584_: *mut LeanObject,
    mut v_s_8585_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8587_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8591_: u8 = 0;
    let mut v___x_8592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8594_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8595_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8596_: u8 = 0;
    let mut v_a_8597_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8600_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8601_: u8 = 0;
    let mut v___x_8603_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8604_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8605_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8586_ = lean_apply_1(v_x_8584_, v_s_8585_);
                if lean_obj_tag(v___x_8586_) == 0 {
                    v_a_8587_ = lean_ctor_get(v___x_8586_, 0);
                    v_a_8588_ = lean_ctor_get(v___x_8586_, 1);
                    v_isSharedCheck_8596_ = (!lean_is_exclusive(v___x_8586_)) as u8;
                    if v_isSharedCheck_8596_ == 0 {
                        v___x_8590_ = v___x_8586_;
                        v_isShared_8591_ = v_isSharedCheck_8596_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_8588_);
                        lean_inc(v_a_8587_);
                        lean_dec(v___x_8586_);
                        v___x_8590_ = lean_box(0);
                        v_isShared_8591_ = v_isSharedCheck_8596_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_f_8583_);
                    v_a_8597_ = lean_ctor_get(v___x_8586_, 0);
                    v_a_8598_ = lean_ctor_get(v___x_8586_, 1);
                    v_isSharedCheck_8605_ = (!lean_is_exclusive(v___x_8586_)) as u8;
                    if v_isSharedCheck_8605_ == 0 {
                        v___x_8600_ = v___x_8586_;
                        v_isShared_8601_ = v_isSharedCheck_8605_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_8598_);
                        lean_inc(v_a_8597_);
                        lean_dec(v___x_8586_);
                        v___x_8600_ = lean_box(0);
                        v_isShared_8601_ = v_isSharedCheck_8605_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_8592_ = lean_apply_1(v_f_8583_, v_a_8587_);
                if v_isShared_8591_ == 0 {
                    lean_ctor_set(v___x_8590_, 0, v___x_8592_);
                    v___x_8594_ = v___x_8590_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8595_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8595_, 0, v___x_8592_);
                    lean_ctor_set(v_reuseFailAlloc_8595_, 1, v_a_8588_);
                    v___x_8594_ = v_reuseFailAlloc_8595_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_8594_;
            }
            3 => {
                if v_isShared_8601_ == 0 {
                    v___x_8603_ = v___x_8600_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_8604_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8604_, 0, v_a_8597_);
                    lean_ctor_set(v_reuseFailAlloc_8604_, 1, v_a_8598_);
                    v___x_8603_ = v_reuseFailAlloc_8604_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_8603_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_EStateM_map(
    mut v_00_u03b5_8606_: *mut LeanObject,
    mut v_00_u03c3_8607_: *mut LeanObject,
    mut v_00_u03b1_8608_: *mut LeanObject,
    mut v_00_u03b2_8609_: *mut LeanObject,
    mut v_f_8610_: *mut LeanObject,
    mut v_x_8611_: *mut LeanObject,
    mut v_s_8612_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8614_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8618_: u8 = 0;
    let mut v___x_8619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8621_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8622_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8623_: u8 = 0;
    let mut v_a_8624_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8628_: u8 = 0;
    let mut v___x_8630_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8631_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8632_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8613_ = lean_apply_1(v_x_8611_, v_s_8612_);
                if lean_obj_tag(v___x_8613_) == 0 {
                    v_a_8614_ = lean_ctor_get(v___x_8613_, 0);
                    v_a_8615_ = lean_ctor_get(v___x_8613_, 1);
                    v_isSharedCheck_8623_ = (!lean_is_exclusive(v___x_8613_)) as u8;
                    if v_isSharedCheck_8623_ == 0 {
                        v___x_8617_ = v___x_8613_;
                        v_isShared_8618_ = v_isSharedCheck_8623_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_8615_);
                        lean_inc(v_a_8614_);
                        lean_dec(v___x_8613_);
                        v___x_8617_ = lean_box(0);
                        v_isShared_8618_ = v_isSharedCheck_8623_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_f_8610_);
                    v_a_8624_ = lean_ctor_get(v___x_8613_, 0);
                    v_a_8625_ = lean_ctor_get(v___x_8613_, 1);
                    v_isSharedCheck_8632_ = (!lean_is_exclusive(v___x_8613_)) as u8;
                    if v_isSharedCheck_8632_ == 0 {
                        v___x_8627_ = v___x_8613_;
                        v_isShared_8628_ = v_isSharedCheck_8632_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_8625_);
                        lean_inc(v_a_8624_);
                        lean_dec(v___x_8613_);
                        v___x_8627_ = lean_box(0);
                        v_isShared_8628_ = v_isSharedCheck_8632_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_8619_ = lean_apply_1(v_f_8610_, v_a_8614_);
                if v_isShared_8618_ == 0 {
                    lean_ctor_set(v___x_8617_, 0, v___x_8619_);
                    v___x_8621_ = v___x_8617_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8622_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8622_, 0, v___x_8619_);
                    lean_ctor_set(v_reuseFailAlloc_8622_, 1, v_a_8615_);
                    v___x_8621_ = v_reuseFailAlloc_8622_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_8621_;
            }
            3 => {
                if v_isShared_8628_ == 0 {
                    v___x_8630_ = v___x_8627_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_8631_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8631_, 0, v_a_8624_);
                    lean_ctor_set(v_reuseFailAlloc_8631_, 1, v_a_8625_);
                    v___x_8630_ = v_reuseFailAlloc_8631_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_8630_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_EStateM_seqRight___redArg(
    mut v_x_8633_: *mut LeanObject,
    mut v_y_8634_: *mut LeanObject,
    mut v_s_8635_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8636_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8640_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8644_: u8 = 0;
    let mut v___x_8646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8648_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8636_ = lean_apply_1(v_x_8633_, v_s_8635_);
                if lean_obj_tag(v___x_8636_) == 0 {
                    v_a_8637_ = lean_ctor_get(v___x_8636_, 1);
                    lean_inc(v_a_8637_);
                    lean_dec_ref_known(v___x_8636_, 2);
                    v___x_8638_ = lean_box(0);
                    v___x_8639_ = lean_apply_2(v_y_8634_, v___x_8638_, v_a_8637_);
                    return v___x_8639_;
                } else {
                    lean_dec_ref(v_y_8634_);
                    v_a_8640_ = lean_ctor_get(v___x_8636_, 0);
                    v_a_8641_ = lean_ctor_get(v___x_8636_, 1);
                    v_isSharedCheck_8648_ = (!lean_is_exclusive(v___x_8636_)) as u8;
                    if v_isSharedCheck_8648_ == 0 {
                        v___x_8643_ = v___x_8636_;
                        v_isShared_8644_ = v_isSharedCheck_8648_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_8641_);
                        lean_inc(v_a_8640_);
                        lean_dec(v___x_8636_);
                        v___x_8643_ = lean_box(0);
                        v_isShared_8644_ = v_isSharedCheck_8648_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_8644_ == 0 {
                    v___x_8646_ = v___x_8643_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8647_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8647_, 0, v_a_8640_);
                    lean_ctor_set(v_reuseFailAlloc_8647_, 1, v_a_8641_);
                    v___x_8646_ = v_reuseFailAlloc_8647_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_8646_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_EStateM_seqRight(
    mut v_00_u03b5_8649_: *mut LeanObject,
    mut v_00_u03c3_8650_: *mut LeanObject,
    mut v_00_u03b1_8651_: *mut LeanObject,
    mut v_00_u03b2_8652_: *mut LeanObject,
    mut v_x_8653_: *mut LeanObject,
    mut v_y_8654_: *mut LeanObject,
    mut v_s_8655_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8656_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8664_: u8 = 0;
    let mut v___x_8666_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8667_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8668_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8656_ = lean_apply_1(v_x_8653_, v_s_8655_);
                if lean_obj_tag(v___x_8656_) == 0 {
                    v_a_8657_ = lean_ctor_get(v___x_8656_, 1);
                    lean_inc(v_a_8657_);
                    lean_dec_ref_known(v___x_8656_, 2);
                    v___x_8658_ = lean_box(0);
                    v___x_8659_ = lean_apply_2(v_y_8654_, v___x_8658_, v_a_8657_);
                    return v___x_8659_;
                } else {
                    lean_dec_ref(v_y_8654_);
                    v_a_8660_ = lean_ctor_get(v___x_8656_, 0);
                    v_a_8661_ = lean_ctor_get(v___x_8656_, 1);
                    v_isSharedCheck_8668_ = (!lean_is_exclusive(v___x_8656_)) as u8;
                    if v_isSharedCheck_8668_ == 0 {
                        v___x_8663_ = v___x_8656_;
                        v_isShared_8664_ = v_isSharedCheck_8668_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_8661_);
                        lean_inc(v_a_8660_);
                        lean_dec(v___x_8656_);
                        v___x_8663_ = lean_box(0);
                        v_isShared_8664_ = v_isSharedCheck_8668_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_8664_ == 0 {
                    v___x_8666_ = v___x_8663_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8667_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8667_, 0, v_a_8660_);
                    lean_ctor_set(v_reuseFailAlloc_8667_, 1, v_a_8661_);
                    v___x_8666_ = v_reuseFailAlloc_8667_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_8666_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_EStateM_instMonad___lam__0(
    mut v_00_u03b1_8669_: *mut LeanObject,
    mut v_00_u03b2_8670_: *mut LeanObject,
    mut v___y_8671_: *mut LeanObject,
    mut v___y_8672_: *mut LeanObject,
    mut v___y_8673_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8678_: u8 = 0;
    let mut v___x_8680_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8682_: u8 = 0;
    let mut v_unused_8683_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8684_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8687_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8688_: u8 = 0;
    let mut v___x_8690_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8691_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8692_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8674_ = lean_apply_1(v___y_8672_, v___y_8673_);
                if lean_obj_tag(v___x_8674_) == 0 {
                    v_a_8675_ = lean_ctor_get(v___x_8674_, 1);
                    v_isSharedCheck_8682_ = (!lean_is_exclusive(v___x_8674_)) as u8;
                    if v_isSharedCheck_8682_ == 0 {
                        v_unused_8683_ = lean_ctor_get(v___x_8674_, 0);
                        lean_dec(v_unused_8683_);
                        v___x_8677_ = v___x_8674_;
                        v_isShared_8678_ = v_isSharedCheck_8682_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_8675_);
                        lean_dec(v___x_8674_);
                        v___x_8677_ = lean_box(0);
                        v_isShared_8678_ = v_isSharedCheck_8682_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___y_8671_);
                    v_a_8684_ = lean_ctor_get(v___x_8674_, 0);
                    v_a_8685_ = lean_ctor_get(v___x_8674_, 1);
                    v_isSharedCheck_8692_ = (!lean_is_exclusive(v___x_8674_)) as u8;
                    if v_isSharedCheck_8692_ == 0 {
                        v___x_8687_ = v___x_8674_;
                        v_isShared_8688_ = v_isSharedCheck_8692_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_8685_);
                        lean_inc(v_a_8684_);
                        lean_dec(v___x_8674_);
                        v___x_8687_ = lean_box(0);
                        v_isShared_8688_ = v_isSharedCheck_8692_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_8678_ == 0 {
                    lean_ctor_set(v___x_8677_, 0, v___y_8671_);
                    v___x_8680_ = v___x_8677_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8681_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8681_, 0, v___y_8671_);
                    lean_ctor_set(v_reuseFailAlloc_8681_, 1, v_a_8675_);
                    v___x_8680_ = v_reuseFailAlloc_8681_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_8680_;
            }
            3 => {
                if v_isShared_8688_ == 0 {
                    v___x_8690_ = v___x_8687_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_8691_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8691_, 0, v_a_8684_);
                    lean_ctor_set(v_reuseFailAlloc_8691_, 1, v_a_8685_);
                    v___x_8690_ = v_reuseFailAlloc_8691_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_8690_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_EStateM_instMonad___lam__1(
    mut v_00_u03b1_8693_: *mut LeanObject,
    mut v_00_u03b2_8694_: *mut LeanObject,
    mut v_f_8695_: *mut LeanObject,
    mut v_x_8696_: *mut LeanObject,
    mut v___y_8697_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8698_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8699_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8702_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8703_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8706_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8707_: u8 = 0;
    let mut v___x_8708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8710_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8712_: u8 = 0;
    let mut v_a_8713_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8716_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8717_: u8 = 0;
    let mut v___x_8719_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8720_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8721_: u8 = 0;
    let mut v_a_8722_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8725_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8726_: u8 = 0;
    let mut v___x_8728_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8730_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8698_ = lean_apply_1(v_f_8695_, v___y_8697_);
                if lean_obj_tag(v___x_8698_) == 0 {
                    v_a_8699_ = lean_ctor_get(v___x_8698_, 0);
                    lean_inc(v_a_8699_);
                    v_a_8700_ = lean_ctor_get(v___x_8698_, 1);
                    lean_inc(v_a_8700_);
                    lean_dec_ref_known(v___x_8698_, 2);
                    v___x_8701_ = lean_box(0);
                    v___x_8702_ = lean_apply_2(v_x_8696_, v___x_8701_, v_a_8700_);
                    if lean_obj_tag(v___x_8702_) == 0 {
                        v_a_8703_ = lean_ctor_get(v___x_8702_, 0);
                        v_a_8704_ = lean_ctor_get(v___x_8702_, 1);
                        v_isSharedCheck_8712_ = (!lean_is_exclusive(v___x_8702_)) as u8;
                        if v_isSharedCheck_8712_ == 0 {
                            v___x_8706_ = v___x_8702_;
                            v_isShared_8707_ = v_isSharedCheck_8712_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_8704_);
                            lean_inc(v_a_8703_);
                            lean_dec(v___x_8702_);
                            v___x_8706_ = lean_box(0);
                            v_isShared_8707_ = v_isSharedCheck_8712_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_8699_);
                        v_a_8713_ = lean_ctor_get(v___x_8702_, 0);
                        v_a_8714_ = lean_ctor_get(v___x_8702_, 1);
                        v_isSharedCheck_8721_ = (!lean_is_exclusive(v___x_8702_)) as u8;
                        if v_isSharedCheck_8721_ == 0 {
                            v___x_8716_ = v___x_8702_;
                            v_isShared_8717_ = v_isSharedCheck_8721_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_8714_);
                            lean_inc(v_a_8713_);
                            lean_dec(v___x_8702_);
                            v___x_8716_ = lean_box(0);
                            v_isShared_8717_ = v_isSharedCheck_8721_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_x_8696_);
                    v_a_8722_ = lean_ctor_get(v___x_8698_, 0);
                    v_a_8723_ = lean_ctor_get(v___x_8698_, 1);
                    v_isSharedCheck_8730_ = (!lean_is_exclusive(v___x_8698_)) as u8;
                    if v_isSharedCheck_8730_ == 0 {
                        v___x_8725_ = v___x_8698_;
                        v_isShared_8726_ = v_isSharedCheck_8730_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_8723_);
                        lean_inc(v_a_8722_);
                        lean_dec(v___x_8698_);
                        v___x_8725_ = lean_box(0);
                        v_isShared_8726_ = v_isSharedCheck_8730_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_8708_ = lean_apply_1(v_a_8699_, v_a_8703_);
                if v_isShared_8707_ == 0 {
                    lean_ctor_set(v___x_8706_, 0, v___x_8708_);
                    v___x_8710_ = v___x_8706_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8711_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8711_, 0, v___x_8708_);
                    lean_ctor_set(v_reuseFailAlloc_8711_, 1, v_a_8704_);
                    v___x_8710_ = v_reuseFailAlloc_8711_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_8710_;
            }
            3 => {
                if v_isShared_8717_ == 0 {
                    v___x_8719_ = v___x_8716_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_8720_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8720_, 0, v_a_8713_);
                    lean_ctor_set(v_reuseFailAlloc_8720_, 1, v_a_8714_);
                    v___x_8719_ = v_reuseFailAlloc_8720_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_8719_;
            }
            5 => {
                if v_isShared_8726_ == 0 {
                    v___x_8728_ = v___x_8725_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_8729_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8729_, 0, v_a_8722_);
                    lean_ctor_set(v_reuseFailAlloc_8729_, 1, v_a_8723_);
                    v___x_8728_ = v_reuseFailAlloc_8729_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_8728_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_EStateM_instMonad___lam__2(
    mut v_00_u03b1_8731_: *mut LeanObject,
    mut v_00_u03b2_8732_: *mut LeanObject,
    mut v_x_8733_: *mut LeanObject,
    mut v_y_8734_: *mut LeanObject,
    mut v___y_8735_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8736_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8737_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8744_: u8 = 0;
    let mut v___x_8746_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8748_: u8 = 0;
    let mut v_unused_8749_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8750_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8753_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8754_: u8 = 0;
    let mut v___x_8756_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8758_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8736_ = lean_apply_1(v_x_8733_, v___y_8735_);
                if lean_obj_tag(v___x_8736_) == 0 {
                    v_a_8737_ = lean_ctor_get(v___x_8736_, 0);
                    lean_inc(v_a_8737_);
                    v_a_8738_ = lean_ctor_get(v___x_8736_, 1);
                    lean_inc(v_a_8738_);
                    lean_dec_ref_known(v___x_8736_, 2);
                    v___x_8739_ = lean_box(0);
                    v___x_8740_ = lean_apply_2(v_y_8734_, v___x_8739_, v_a_8738_);
                    if lean_obj_tag(v___x_8740_) == 0 {
                        v_a_8741_ = lean_ctor_get(v___x_8740_, 1);
                        v_isSharedCheck_8748_ = (!lean_is_exclusive(v___x_8740_)) as u8;
                        if v_isSharedCheck_8748_ == 0 {
                            v_unused_8749_ = lean_ctor_get(v___x_8740_, 0);
                            lean_dec(v_unused_8749_);
                            v___x_8743_ = v___x_8740_;
                            v_isShared_8744_ = v_isSharedCheck_8748_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_8741_);
                            lean_dec(v___x_8740_);
                            v___x_8743_ = lean_box(0);
                            v_isShared_8744_ = v_isSharedCheck_8748_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_8737_);
                        v_a_8750_ = lean_ctor_get(v___x_8740_, 0);
                        v_a_8751_ = lean_ctor_get(v___x_8740_, 1);
                        v_isSharedCheck_8758_ = (!lean_is_exclusive(v___x_8740_)) as u8;
                        if v_isSharedCheck_8758_ == 0 {
                            v___x_8753_ = v___x_8740_;
                            v_isShared_8754_ = v_isSharedCheck_8758_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_8751_);
                            lean_inc(v_a_8750_);
                            lean_dec(v___x_8740_);
                            v___x_8753_ = lean_box(0);
                            v_isShared_8754_ = v_isSharedCheck_8758_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_y_8734_);
                    return v___x_8736_;
                }
            }
            1 => {
                if v_isShared_8744_ == 0 {
                    lean_ctor_set(v___x_8743_, 0, v_a_8737_);
                    v___x_8746_ = v___x_8743_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8747_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8747_, 0, v_a_8737_);
                    lean_ctor_set(v_reuseFailAlloc_8747_, 1, v_a_8741_);
                    v___x_8746_ = v_reuseFailAlloc_8747_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_8746_;
            }
            3 => {
                if v_isShared_8754_ == 0 {
                    v___x_8756_ = v___x_8753_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_8757_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8757_, 0, v_a_8750_);
                    lean_ctor_set(v_reuseFailAlloc_8757_, 1, v_a_8751_);
                    v___x_8756_ = v_reuseFailAlloc_8757_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_8756_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_EStateM_instMonad(
    mut v_00_u03b5_8778_: *mut LeanObject,
    mut v_00_u03c3_8779_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8780_: *mut LeanObject = core::ptr::null_mut();
    v___x_8780_ = l_EStateM_instMonad___closed__9;
    return v___x_8780_;
}
pub unsafe fn l_EStateM_instOrElseOfBacktrackable___redArg(
    mut v_inst_8781_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8782_: *mut LeanObject = core::ptr::null_mut();
    v___x_8782_ = lean_alloc_closure(l_EStateM_orElse as *mut core::ffi::c_void, 8, 5);
    lean_closure_set(v___x_8782_, 0, lean_box(0));
    lean_closure_set(v___x_8782_, 1, lean_box(0));
    lean_closure_set(v___x_8782_, 2, lean_box(0));
    lean_closure_set(v___x_8782_, 3, lean_box(0));
    lean_closure_set(v___x_8782_, 4, v_inst_8781_);
    return v___x_8782_;
}
pub unsafe fn l_EStateM_instOrElseOfBacktrackable(
    mut v_00_u03b5_8783_: *mut LeanObject,
    mut v_00_u03c3_8784_: *mut LeanObject,
    mut v_00_u03b1_8785_: *mut LeanObject,
    mut v_00_u03b4_8786_: *mut LeanObject,
    mut v_inst_8787_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8788_: *mut LeanObject = core::ptr::null_mut();
    v___x_8788_ = lean_alloc_closure(l_EStateM_orElse as *mut core::ffi::c_void, 8, 5);
    lean_closure_set(v___x_8788_, 0, lean_box(0));
    lean_closure_set(v___x_8788_, 1, lean_box(0));
    lean_closure_set(v___x_8788_, 2, lean_box(0));
    lean_closure_set(v___x_8788_, 3, lean_box(0));
    lean_closure_set(v___x_8788_, 4, v_inst_8787_);
    return v___x_8788_;
}
pub unsafe fn l_EStateM_instMonadStateOf(
    mut v_00_u03b5_8796_: *mut LeanObject,
    mut v_00_u03c3_8797_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8798_: *mut LeanObject = core::ptr::null_mut();
    v___x_8798_ = l_EStateM_instMonadStateOf___closed__3;
    return v___x_8798_;
}
pub unsafe fn l_EStateM_instMonadExceptOfOfBacktrackable___redArg(
    mut v_inst_8800_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8803_: *mut LeanObject = core::ptr::null_mut();
    v___x_8801_ = l_EStateM_instMonadExceptOfOfBacktrackable___redArg___closed__0;
    v___x_8802_ = lean_alloc_closure(l_EStateM_tryCatch as *mut core::ffi::c_void, 8, 4);
    lean_closure_set(v___x_8802_, 0, lean_box(0));
    lean_closure_set(v___x_8802_, 1, lean_box(0));
    lean_closure_set(v___x_8802_, 2, lean_box(0));
    lean_closure_set(v___x_8802_, 3, v_inst_8800_);
    v___x_8803_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_8803_, 0, v___x_8801_);
    lean_ctor_set(v___x_8803_, 1, v___x_8802_);
    return v___x_8803_;
}
pub unsafe fn l_EStateM_instMonadExceptOfOfBacktrackable(
    mut v_00_u03b5_8804_: *mut LeanObject,
    mut v_00_u03c3_8805_: *mut LeanObject,
    mut v_00_u03b4_8806_: *mut LeanObject,
    mut v_inst_8807_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8808_: *mut LeanObject = core::ptr::null_mut();
    v___x_8808_ = l_EStateM_instMonadExceptOfOfBacktrackable___redArg(v_inst_8807_);
    return v___x_8808_;
}
pub unsafe fn l_EStateM_run___redArg(
    mut v_x_8809_: *mut LeanObject,
    mut v_s_8810_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8811_: *mut LeanObject = core::ptr::null_mut();
    v___x_8811_ = lean_apply_1(v_x_8809_, v_s_8810_);
    return v___x_8811_;
}
pub unsafe fn l_EStateM_run(
    mut v_00_u03b5_8812_: *mut LeanObject,
    mut v_00_u03c3_8813_: *mut LeanObject,
    mut v_00_u03b1_8814_: *mut LeanObject,
    mut v_x_8815_: *mut LeanObject,
    mut v_s_8816_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8817_: *mut LeanObject = core::ptr::null_mut();
    v___x_8817_ = lean_apply_1(v_x_8815_, v_s_8816_);
    return v___x_8817_;
}
pub unsafe fn l_EStateM_run_x27___redArg(
    mut v_x_8818_: *mut LeanObject,
    mut v_s_8819_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8820_: *mut LeanObject = core::ptr::null_mut();
    v___x_8820_ = lean_apply_1(v_x_8818_, v_s_8819_);
    if lean_obj_tag(v___x_8820_) == 0 {
        let mut v_a_8821_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_8822_: *mut LeanObject = core::ptr::null_mut();
        v_a_8821_ = lean_ctor_get(v___x_8820_, 0);
        lean_inc(v_a_8821_);
        lean_dec_ref_known(v___x_8820_, 2);
        v___x_8822_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_8822_, 0, v_a_8821_);
        return v___x_8822_;
    } else {
        let mut v___x_8823_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref_known(v___x_8820_, 2);
        v___x_8823_ = lean_box(0);
        return v___x_8823_;
    }
}
pub unsafe fn l_EStateM_run_x27(
    mut v_00_u03b5_8824_: *mut LeanObject,
    mut v_00_u03c3_8825_: *mut LeanObject,
    mut v_00_u03b1_8826_: *mut LeanObject,
    mut v_x_8827_: *mut LeanObject,
    mut v_s_8828_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8829_: *mut LeanObject = core::ptr::null_mut();
    v___x_8829_ = lean_apply_1(v_x_8827_, v_s_8828_);
    if lean_obj_tag(v___x_8829_) == 0 {
        let mut v_a_8830_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_8831_: *mut LeanObject = core::ptr::null_mut();
        v_a_8830_ = lean_ctor_get(v___x_8829_, 0);
        lean_inc(v_a_8830_);
        lean_dec_ref_known(v___x_8829_, 2);
        v___x_8831_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_8831_, 0, v_a_8830_);
        return v___x_8831_;
    } else {
        let mut v___x_8832_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref_known(v___x_8829_, 2);
        v___x_8832_ = lean_box(0);
        return v___x_8832_;
    }
}
pub unsafe fn l_EStateM_dummySave(
    mut v_00_u03c3_8833_: *mut LeanObject,
    mut v_x_8834_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8835_: *mut LeanObject = core::ptr::null_mut();
    v___x_8835_ = lean_box(0);
    return v___x_8835_;
}
pub unsafe fn l_EStateM_dummySave___boxed(
    mut v_00_u03c3_8836_: *mut LeanObject,
    mut v_x_8837_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8838_: *mut LeanObject = core::ptr::null_mut();
    v_res_8838_ = l_EStateM_dummySave(v_00_u03c3_8836_, v_x_8837_);
    lean_dec(v_x_8837_);
    return v_res_8838_;
}
pub unsafe fn l_EStateM_dummyRestore___redArg(mut v_s_8839_: *mut LeanObject) -> *mut LeanObject {
    lean_inc(v_s_8839_);
    return v_s_8839_;
}
pub unsafe fn l_EStateM_dummyRestore___redArg___boxed(
    mut v_s_8840_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8841_: *mut LeanObject = core::ptr::null_mut();
    v_res_8841_ = l_EStateM_dummyRestore___redArg(v_s_8840_);
    lean_dec(v_s_8840_);
    return v_res_8841_;
}
pub unsafe fn l_EStateM_dummyRestore(
    mut v_00_u03c3_8842_: *mut LeanObject,
    mut v_s_8843_: *mut LeanObject,
    mut v_x_8844_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_s_8843_);
    return v_s_8843_;
}
pub unsafe fn l_EStateM_dummyRestore___boxed(
    mut v_00_u03c3_8845_: *mut LeanObject,
    mut v_s_8846_: *mut LeanObject,
    mut v_x_8847_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8848_: *mut LeanObject = core::ptr::null_mut();
    v_res_8848_ = l_EStateM_dummyRestore(v_00_u03c3_8845_, v_s_8846_, v_x_8847_);
    lean_dec(v_s_8846_);
    return v_res_8848_;
}
pub unsafe fn l_EStateM_nonBacktrackable(mut v_00_u03c3_8854_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_8855_: *mut LeanObject = core::ptr::null_mut();
    v___x_8855_ = l_EStateM_nonBacktrackable___closed__2;
    return v___x_8855_;
}
pub unsafe fn l_mixHash___boxed(
    mut v_u_u2081_8858_: *mut LeanObject,
    mut v_u_u2082_8859_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_u_u2081_boxed_8860_: u64 = 0;
    let mut v_u_u2082_boxed_8861_: u64 = 0;
    let mut v_res_8862_: u64 = 0;
    let mut v_r_8863_: *mut LeanObject = core::ptr::null_mut();
    v_u_u2081_boxed_8860_ = lean_unbox_uint64(v_u_u2081_8858_);
    lean_dec_ref(v_u_u2081_8858_);
    v_u_u2082_boxed_8861_ = lean_unbox_uint64(v_u_u2082_8859_);
    lean_dec_ref(v_u_u2082_8859_);
    v_res_8862_ = lean_uint64_mix_hash(v_u_u2081_boxed_8860_, v_u_u2082_boxed_8861_);
    v_r_8863_ = lean_box_uint64(v_res_8862_);
    return v_r_8863_;
}
pub unsafe fn l_instHashableSubtype___redArg___lam__0(
    mut v_inst_8864_: *mut LeanObject,
    mut v_a_8865_: *mut LeanObject,
) -> u64 {
    let mut v___x_8866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8867_: u64 = 0;
    v___x_8866_ = lean_apply_1(v_inst_8864_, v_a_8865_);
    v___x_8867_ = lean_unbox_uint64(v___x_8866_);
    lean_dec_ref(v___x_8866_);
    return v___x_8867_;
}
pub unsafe fn l_instHashableSubtype___redArg___lam__0___boxed(
    mut v_inst_8868_: *mut LeanObject,
    mut v_a_8869_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8870_: u64 = 0;
    let mut v_r_8871_: *mut LeanObject = core::ptr::null_mut();
    v_res_8870_ = l_instHashableSubtype___redArg___lam__0(v_inst_8868_, v_a_8869_);
    v_r_8871_ = lean_box_uint64(v_res_8870_);
    return v_r_8871_;
}
pub unsafe fn l_instHashableSubtype___redArg(mut v_inst_8872_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_8873_: *mut LeanObject = core::ptr::null_mut();
    v___f_8873_ = lean_alloc_closure(
        l_instHashableSubtype___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_8873_, 0, v_inst_8872_);
    return v___f_8873_;
}
pub unsafe fn l_instHashableSubtype(
    mut v_00_u03b1_8874_: *mut LeanObject,
    mut v_inst_8875_: *mut LeanObject,
    mut v_p_8876_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_8877_: *mut LeanObject = core::ptr::null_mut();
    v___f_8877_ = lean_alloc_closure(
        l_instHashableSubtype___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_8877_, 0, v_inst_8875_);
    return v___f_8877_;
}
pub unsafe fn l_String_hash___boxed(mut v_s_8879_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_8880_: u64 = 0;
    let mut v_r_8881_: *mut LeanObject = core::ptr::null_mut();
    v_res_8880_ = lean_string_hash(v_s_8879_);
    lean_dec_ref(v_s_8879_);
    v_r_8881_ = lean_box_uint64(v_res_8880_);
    return v_r_8881_;
}
pub unsafe fn l_Lean_Name_ctorIdx(mut v_x_8884_: *mut LeanObject) -> *mut LeanObject {
    match lean_obj_tag(v_x_8884_) {
        0 => {
            let mut v___x_8885_: *mut LeanObject = core::ptr::null_mut();
            v___x_8885_ = lean_unsigned_to_nat(0);
            return v___x_8885_;
        }
        1 => {
            let mut v___x_8886_: *mut LeanObject = core::ptr::null_mut();
            v___x_8886_ = lean_unsigned_to_nat(1);
            return v___x_8886_;
        }
        _ => {
            let mut v___x_8887_: *mut LeanObject = core::ptr::null_mut();
            v___x_8887_ = lean_unsigned_to_nat(2);
            return v___x_8887_;
        }
    }
}
pub unsafe fn l_Lean_Name_ctorIdx___boxed(mut v_x_8888_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_8889_: *mut LeanObject = core::ptr::null_mut();
    v_res_8889_ = l_Lean_Name_ctorIdx(v_x_8888_);
    lean_dec(v_x_8888_);
    return v_res_8889_;
}
pub unsafe fn l_Lean_Name_ctorElim___redArg(
    mut v_t_8890_: *mut LeanObject,
    mut v_k_8891_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_t_8890_) {
        0 => {
            return v_k_8891_;
        }
        1 => {
            let mut v_pre_8892_: *mut LeanObject = core::ptr::null_mut();
            let mut v_str_8893_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_8894_: *mut LeanObject = core::ptr::null_mut();
            v_pre_8892_ = lean_ctor_get(v_t_8890_, 0);
            lean_inc(v_pre_8892_);
            v_str_8893_ = lean_ctor_get(v_t_8890_, 1);
            lean_inc_ref(v_str_8893_);
            lean_dec_ref_known(v_t_8890_, 2);
            v___x_8894_ = lean_apply_2(v_k_8891_, v_pre_8892_, v_str_8893_);
            return v___x_8894_;
        }
        _ => {
            let mut v_pre_8895_: *mut LeanObject = core::ptr::null_mut();
            let mut v_i_8896_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_8897_: *mut LeanObject = core::ptr::null_mut();
            v_pre_8895_ = lean_ctor_get(v_t_8890_, 0);
            lean_inc(v_pre_8895_);
            v_i_8896_ = lean_ctor_get(v_t_8890_, 1);
            lean_inc(v_i_8896_);
            lean_dec_ref_known(v_t_8890_, 2);
            v___x_8897_ = lean_apply_2(v_k_8891_, v_pre_8895_, v_i_8896_);
            return v___x_8897_;
        }
    }
}
pub unsafe fn l_Lean_Name_ctorElim(
    mut v_motive_8898_: *mut LeanObject,
    mut v_ctorIdx_8899_: *mut LeanObject,
    mut v_t_8900_: *mut LeanObject,
    mut v_h_8901_: *mut LeanObject,
    mut v_k_8902_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8903_: *mut LeanObject = core::ptr::null_mut();
    v___x_8903_ = l_Lean_Name_ctorElim___redArg(v_t_8900_, v_k_8902_);
    return v___x_8903_;
}
pub unsafe fn l_Lean_Name_ctorElim___boxed(
    mut v_motive_8904_: *mut LeanObject,
    mut v_ctorIdx_8905_: *mut LeanObject,
    mut v_t_8906_: *mut LeanObject,
    mut v_h_8907_: *mut LeanObject,
    mut v_k_8908_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8909_: *mut LeanObject = core::ptr::null_mut();
    v_res_8909_ = l_Lean_Name_ctorElim(
        v_motive_8904_,
        v_ctorIdx_8905_,
        v_t_8906_,
        v_h_8907_,
        v_k_8908_,
    );
    lean_dec(v_ctorIdx_8905_);
    return v_res_8909_;
}
pub unsafe fn l_Lean_Name_anonymous_elim___redArg(
    mut v_t_8910_: *mut LeanObject,
    mut v_anonymous_8911_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8912_: *mut LeanObject = core::ptr::null_mut();
    v___x_8912_ = l_Lean_Name_ctorElim___redArg(v_t_8910_, v_anonymous_8911_);
    return v___x_8912_;
}
pub unsafe fn l_Lean_Name_anonymous_elim(
    mut v_motive_8913_: *mut LeanObject,
    mut v_t_8914_: *mut LeanObject,
    mut v_h_8915_: *mut LeanObject,
    mut v_anonymous_8916_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8917_: *mut LeanObject = core::ptr::null_mut();
    v___x_8917_ = l_Lean_Name_ctorElim___redArg(v_t_8914_, v_anonymous_8916_);
    return v___x_8917_;
}
pub unsafe fn l_Lean_Name_str_elim___redArg(
    mut v_t_8918_: *mut LeanObject,
    mut v_str_8919_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8920_: *mut LeanObject = core::ptr::null_mut();
    v___x_8920_ = l_Lean_Name_ctorElim___redArg(v_t_8918_, v_str_8919_);
    return v___x_8920_;
}
pub unsafe fn l_Lean_Name_str_elim(
    mut v_motive_8921_: *mut LeanObject,
    mut v_t_8922_: *mut LeanObject,
    mut v_h_8923_: *mut LeanObject,
    mut v_str_8924_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8925_: *mut LeanObject = core::ptr::null_mut();
    v___x_8925_ = l_Lean_Name_ctorElim___redArg(v_t_8922_, v_str_8924_);
    return v___x_8925_;
}
pub unsafe fn l_Lean_Name_num_elim___redArg(
    mut v_t_8926_: *mut LeanObject,
    mut v_num_8927_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8928_: *mut LeanObject = core::ptr::null_mut();
    v___x_8928_ = l_Lean_Name_ctorElim___redArg(v_t_8926_, v_num_8927_);
    return v___x_8928_;
}
pub unsafe fn l_Lean_Name_num_elim(
    mut v_motive_8929_: *mut LeanObject,
    mut v_t_8930_: *mut LeanObject,
    mut v_h_8931_: *mut LeanObject,
    mut v_num_8932_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8933_: *mut LeanObject = core::ptr::null_mut();
    v___x_8933_ = l_Lean_Name_ctorElim___redArg(v_t_8930_, v_num_8932_);
    return v___x_8933_;
}
pub unsafe fn l_Lean_Name_casesOn___override___redArg(
    mut v_t_8934_: *mut LeanObject,
    mut v_anonymous_8935_: *mut LeanObject,
    mut v_str_8936_: *mut LeanObject,
    mut v_num_8937_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_t_8934_) {
        0 => {
            lean_dec(v_num_8937_);
            lean_dec(v_str_8936_);
            lean_inc(v_anonymous_8935_);
            return v_anonymous_8935_;
        }
        1 => {
            let mut v_pre_8938_: *mut LeanObject = core::ptr::null_mut();
            let mut v_str_8939_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_8940_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_num_8937_);
            v_pre_8938_ = lean_ctor_get(v_t_8934_, 0);
            lean_inc(v_pre_8938_);
            v_str_8939_ = lean_ctor_get(v_t_8934_, 1);
            lean_inc_ref(v_str_8939_);
            lean_dec_ref_known(v_t_8934_, 2);
            v___x_8940_ = lean_apply_2(v_str_8936_, v_pre_8938_, v_str_8939_);
            return v___x_8940_;
        }
        _ => {
            let mut v_pre_8941_: *mut LeanObject = core::ptr::null_mut();
            let mut v_i_8942_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_8943_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_str_8936_);
            v_pre_8941_ = lean_ctor_get(v_t_8934_, 0);
            lean_inc(v_pre_8941_);
            v_i_8942_ = lean_ctor_get(v_t_8934_, 1);
            lean_inc(v_i_8942_);
            lean_dec_ref_known(v_t_8934_, 2);
            v___x_8943_ = lean_apply_2(v_num_8937_, v_pre_8941_, v_i_8942_);
            return v___x_8943_;
        }
    }
}
pub unsafe fn l_Lean_Name_casesOn___override___redArg___boxed(
    mut v_t_8944_: *mut LeanObject,
    mut v_anonymous_8945_: *mut LeanObject,
    mut v_str_8946_: *mut LeanObject,
    mut v_num_8947_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8948_: *mut LeanObject = core::ptr::null_mut();
    v_res_8948_ = l_Lean_Name_casesOn___override___redArg(
        v_t_8944_,
        v_anonymous_8945_,
        v_str_8946_,
        v_num_8947_,
    );
    lean_dec(v_anonymous_8945_);
    return v_res_8948_;
}
pub unsafe fn l_Lean_Name_casesOn___override(
    mut v_motive_8949_: *mut LeanObject,
    mut v_t_8950_: *mut LeanObject,
    mut v_anonymous_8951_: *mut LeanObject,
    mut v_str_8952_: *mut LeanObject,
    mut v_num_8953_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_t_8950_) {
        0 => {
            lean_dec(v_num_8953_);
            lean_dec(v_str_8952_);
            lean_inc(v_anonymous_8951_);
            return v_anonymous_8951_;
        }
        1 => {
            let mut v_pre_8954_: *mut LeanObject = core::ptr::null_mut();
            let mut v_str_8955_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_8956_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_num_8953_);
            v_pre_8954_ = lean_ctor_get(v_t_8950_, 0);
            lean_inc(v_pre_8954_);
            v_str_8955_ = lean_ctor_get(v_t_8950_, 1);
            lean_inc_ref(v_str_8955_);
            lean_dec_ref_known(v_t_8950_, 2);
            v___x_8956_ = lean_apply_2(v_str_8952_, v_pre_8954_, v_str_8955_);
            return v___x_8956_;
        }
        _ => {
            let mut v_pre_8957_: *mut LeanObject = core::ptr::null_mut();
            let mut v_i_8958_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_8959_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_str_8952_);
            v_pre_8957_ = lean_ctor_get(v_t_8950_, 0);
            lean_inc(v_pre_8957_);
            v_i_8958_ = lean_ctor_get(v_t_8950_, 1);
            lean_inc(v_i_8958_);
            lean_dec_ref_known(v_t_8950_, 2);
            v___x_8959_ = lean_apply_2(v_num_8953_, v_pre_8957_, v_i_8958_);
            return v___x_8959_;
        }
    }
}
pub unsafe fn l_Lean_Name_casesOn___override___boxed(
    mut v_motive_8960_: *mut LeanObject,
    mut v_t_8961_: *mut LeanObject,
    mut v_anonymous_8962_: *mut LeanObject,
    mut v_str_8963_: *mut LeanObject,
    mut v_num_8964_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8965_: *mut LeanObject = core::ptr::null_mut();
    v_res_8965_ = l_Lean_Name_casesOn___override(
        v_motive_8960_,
        v_t_8961_,
        v_anonymous_8962_,
        v_str_8963_,
        v_num_8964_,
    );
    lean_dec(v_anonymous_8962_);
    return v_res_8965_;
}
pub unsafe fn _init_l_Lean_Name_anonymous___override() -> *mut LeanObject {
    let mut v___x_8966_: *mut LeanObject = core::ptr::null_mut();
    v___x_8966_ = lean_box(0);
    return v___x_8966_;
}
pub unsafe fn _init_l_Lean_Name_str___override___closed__0() -> u64 {
    let mut v___x_8967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8968_: u64 = 0;
    v___x_8967_ = lean_unsigned_to_nat(1723);
    v___x_8968_ = lean_uint64_of_nat(v___x_8967_);
    return v___x_8968_;
}
pub unsafe fn l_Lean_Name_str___override(
    mut v_pre_8969_: *mut LeanObject,
    mut v_str_8970_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_8972_: u64 = 0;
    let mut v___x_8973_: u64 = 0;
    let mut v___x_8974_: u64 = 0;
    let mut v___x_8975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8976_: u64 = 0;
    let mut v_hash_8977_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_pre_8969_) == 0 {
                    v___x_8976_ = lean_uint64_once(
                        core::ptr::addr_of_mut!(l_Lean_Name_str___override___closed__0),
                        core::ptr::addr_of_mut!(l_Lean_Name_str___override___closed__0_once),
                        _init_l_Lean_Name_str___override___closed__0,
                    );
                    v___y_8972_ = v___x_8976_;
                    state = 1;
                    continue;
                } else {
                    v_hash_8977_ = lean_ctor_get_uint64(
                        v_pre_8969_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v___y_8972_ = v_hash_8977_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_8973_ = lean_string_hash(v_str_8970_);
                v___x_8974_ = lean_uint64_mix_hash(v___y_8972_, v___x_8973_);
                v___x_8975_ = lean_alloc_ctor(1, 2, (8) as u32);
                lean_ctor_set(v___x_8975_, 0, v_pre_8969_);
                lean_ctor_set(v___x_8975_, 1, v_str_8970_);
                lean_ctor_set_uint64(
                    v___x_8975_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    v___x_8974_,
                );
                return v___x_8975_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Name_num___override___closed__0() -> u64 {
    let mut v___x_8978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8979_: u64 = 0;
    v___x_8978_ = lean_unsigned_to_nat(17);
    v___x_8979_ = lean_uint64_of_nat(v___x_8978_);
    return v___x_8979_;
}
pub unsafe fn l_Lean_Name_num___override(
    mut v_pre_8980_: *mut LeanObject,
    mut v_i_8981_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_8983_: u64 = 0;
    let mut v___y_8984_: u64 = 0;
    let mut v___x_8985_: u64 = 0;
    let mut v___x_8986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8988_: u64 = 0;
    let mut v___x_8989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8990_: u8 = 0;
    let mut v___x_8991_: u64 = 0;
    let mut v___x_8992_: u64 = 0;
    let mut v___x_8993_: u64 = 0;
    let mut v_hash_8994_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_pre_8980_) == 0 {
                    v___x_8993_ = lean_uint64_once(
                        core::ptr::addr_of_mut!(l_Lean_Name_str___override___closed__0),
                        core::ptr::addr_of_mut!(l_Lean_Name_str___override___closed__0_once),
                        _init_l_Lean_Name_str___override___closed__0,
                    );
                    v___y_8988_ = v___x_8993_;
                    state = 2;
                    continue;
                } else {
                    v_hash_8994_ = lean_ctor_get_uint64(
                        v_pre_8980_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v___y_8988_ = v_hash_8994_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_8985_ = lean_uint64_mix_hash(v___y_8983_, v___y_8984_);
                v___x_8986_ = lean_alloc_ctor(2, 2, (8) as u32);
                lean_ctor_set(v___x_8986_, 0, v_pre_8980_);
                lean_ctor_set(v___x_8986_, 1, v_i_8981_);
                lean_ctor_set_uint64(
                    v___x_8986_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    v___x_8985_,
                );
                return v___x_8986_;
            }
            2 => {
                v___x_8989_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_UInt64_size___closed__0),
                    core::ptr::addr_of_mut!(l_UInt64_size___closed__0_once),
                    _init_l_UInt64_size___closed__0,
                );
                v___x_8990_ = lean_nat_dec_lt(v_i_8981_, v___x_8989_);
                if v___x_8990_ == 0 {
                    v___x_8991_ = lean_uint64_once(
                        core::ptr::addr_of_mut!(l_Lean_Name_num___override___closed__0),
                        core::ptr::addr_of_mut!(l_Lean_Name_num___override___closed__0_once),
                        _init_l_Lean_Name_num___override___closed__0,
                    );
                    v___y_8983_ = v___y_8988_;
                    v___y_8984_ = v___x_8991_;
                    state = 1;
                    continue;
                } else {
                    v___x_8992_ = lean_uint64_of_nat(v_i_8981_);
                    v___y_8983_ = v___y_8988_;
                    v___y_8984_ = v___x_8992_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Name_hash___override(mut v_x_8995_: *mut LeanObject) -> u64 {
    if lean_obj_tag(v_x_8995_) == 0 {
        let mut v___x_8996_: u64 = 0;
        v___x_8996_ = lean_uint64_once(
            core::ptr::addr_of_mut!(l_Lean_Name_str___override___closed__0),
            core::ptr::addr_of_mut!(l_Lean_Name_str___override___closed__0_once),
            _init_l_Lean_Name_str___override___closed__0,
        );
        return v___x_8996_;
    } else {
        let mut v_hash_8997_: u64 = 0;
        v_hash_8997_ = lean_ctor_get_uint64(
            v_x_8995_,
            (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
        );
        return v_hash_8997_;
    }
}
pub unsafe fn l_Lean_Name_hash___override___boxed(
    mut v_x_8998_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8999_: u64 = 0;
    let mut v_r_9000_: *mut LeanObject = core::ptr::null_mut();
    v_res_8999_ = l_Lean_Name_hash___override(v_x_8998_);
    lean_dec(v_x_8998_);
    v_r_9000_ = lean_box_uint64(v_res_8999_);
    return v_r_9000_;
}
pub unsafe fn _init_l_Lean_instInhabitedName() -> *mut LeanObject {
    let mut v___x_9001_: *mut LeanObject = core::ptr::null_mut();
    v___x_9001_ = lean_box(0);
    return v___x_9001_;
}
pub unsafe fn lean_name_mk_string(
    mut v_p_9004_: *mut LeanObject,
    mut v_s_9005_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9006_: *mut LeanObject = core::ptr::null_mut();
    v___x_9006_ = l_Lean_Name_str___override(v_p_9004_, v_s_9005_);
    return v___x_9006_;
}
pub unsafe fn lean_name_mk_numeral(
    mut v_p_9007_: *mut LeanObject,
    mut v_v_9008_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9009_: *mut LeanObject = core::ptr::null_mut();
    v___x_9009_ = l_Lean_Name_num___override(v_p_9007_, v_v_9008_);
    return v___x_9009_;
}
pub unsafe fn l_Lean_Name_mkSimple(mut v_s_9010_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_9011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9012_: *mut LeanObject = core::ptr::null_mut();
    v___x_9011_ = lean_box(0);
    v___x_9012_ = l_Lean_Name_str___override(v___x_9011_, v_s_9010_);
    return v___x_9012_;
}
pub unsafe fn l_Lean_Name_mkStr1(mut v_s_u2081_9013_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_9014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9015_: *mut LeanObject = core::ptr::null_mut();
    v___x_9014_ = lean_box(0);
    v___x_9015_ = l_Lean_Name_str___override(v___x_9014_, v_s_u2081_9013_);
    return v___x_9015_;
}
pub unsafe fn l_Lean_Name_mkStr2(
    mut v_s_u2081_9016_: *mut LeanObject,
    mut v_s_u2082_9017_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9020_: *mut LeanObject = core::ptr::null_mut();
    v___x_9018_ = lean_box(0);
    v___x_9019_ = l_Lean_Name_str___override(v___x_9018_, v_s_u2081_9016_);
    v___x_9020_ = l_Lean_Name_str___override(v___x_9019_, v_s_u2082_9017_);
    return v___x_9020_;
}
pub unsafe fn l_Lean_Name_mkStr3(
    mut v_s_u2081_9021_: *mut LeanObject,
    mut v_s_u2082_9022_: *mut LeanObject,
    mut v_s_u2083_9023_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9027_: *mut LeanObject = core::ptr::null_mut();
    v___x_9024_ = lean_box(0);
    v___x_9025_ = l_Lean_Name_str___override(v___x_9024_, v_s_u2081_9021_);
    v___x_9026_ = l_Lean_Name_str___override(v___x_9025_, v_s_u2082_9022_);
    v___x_9027_ = l_Lean_Name_str___override(v___x_9026_, v_s_u2083_9023_);
    return v___x_9027_;
}
pub unsafe fn l_Lean_Name_mkStr4(
    mut v_s_u2081_9028_: *mut LeanObject,
    mut v_s_u2082_9029_: *mut LeanObject,
    mut v_s_u2083_9030_: *mut LeanObject,
    mut v_s_u2084_9031_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9036_: *mut LeanObject = core::ptr::null_mut();
    v___x_9032_ = lean_box(0);
    v___x_9033_ = l_Lean_Name_str___override(v___x_9032_, v_s_u2081_9028_);
    v___x_9034_ = l_Lean_Name_str___override(v___x_9033_, v_s_u2082_9029_);
    v___x_9035_ = l_Lean_Name_str___override(v___x_9034_, v_s_u2083_9030_);
    v___x_9036_ = l_Lean_Name_str___override(v___x_9035_, v_s_u2084_9031_);
    return v___x_9036_;
}
pub unsafe fn l_Lean_Name_mkStr5(
    mut v_s_u2081_9037_: *mut LeanObject,
    mut v_s_u2082_9038_: *mut LeanObject,
    mut v_s_u2083_9039_: *mut LeanObject,
    mut v_s_u2084_9040_: *mut LeanObject,
    mut v_s_u2085_9041_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9047_: *mut LeanObject = core::ptr::null_mut();
    v___x_9042_ = lean_box(0);
    v___x_9043_ = l_Lean_Name_str___override(v___x_9042_, v_s_u2081_9037_);
    v___x_9044_ = l_Lean_Name_str___override(v___x_9043_, v_s_u2082_9038_);
    v___x_9045_ = l_Lean_Name_str___override(v___x_9044_, v_s_u2083_9039_);
    v___x_9046_ = l_Lean_Name_str___override(v___x_9045_, v_s_u2084_9040_);
    v___x_9047_ = l_Lean_Name_str___override(v___x_9046_, v_s_u2085_9041_);
    return v___x_9047_;
}
pub unsafe fn l_Lean_Name_mkStr6(
    mut v_s_u2081_9048_: *mut LeanObject,
    mut v_s_u2082_9049_: *mut LeanObject,
    mut v_s_u2083_9050_: *mut LeanObject,
    mut v_s_u2084_9051_: *mut LeanObject,
    mut v_s_u2085_9052_: *mut LeanObject,
    mut v_s_u2086_9053_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9060_: *mut LeanObject = core::ptr::null_mut();
    v___x_9054_ = lean_box(0);
    v___x_9055_ = l_Lean_Name_str___override(v___x_9054_, v_s_u2081_9048_);
    v___x_9056_ = l_Lean_Name_str___override(v___x_9055_, v_s_u2082_9049_);
    v___x_9057_ = l_Lean_Name_str___override(v___x_9056_, v_s_u2083_9050_);
    v___x_9058_ = l_Lean_Name_str___override(v___x_9057_, v_s_u2084_9051_);
    v___x_9059_ = l_Lean_Name_str___override(v___x_9058_, v_s_u2085_9052_);
    v___x_9060_ = l_Lean_Name_str___override(v___x_9059_, v_s_u2086_9053_);
    return v___x_9060_;
}
pub unsafe fn l_Lean_Name_mkStr7(
    mut v_s_u2081_9061_: *mut LeanObject,
    mut v_s_u2082_9062_: *mut LeanObject,
    mut v_s_u2083_9063_: *mut LeanObject,
    mut v_s_u2084_9064_: *mut LeanObject,
    mut v_s_u2085_9065_: *mut LeanObject,
    mut v_s_u2086_9066_: *mut LeanObject,
    mut v_s_u2087_9067_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9075_: *mut LeanObject = core::ptr::null_mut();
    v___x_9068_ = lean_box(0);
    v___x_9069_ = l_Lean_Name_str___override(v___x_9068_, v_s_u2081_9061_);
    v___x_9070_ = l_Lean_Name_str___override(v___x_9069_, v_s_u2082_9062_);
    v___x_9071_ = l_Lean_Name_str___override(v___x_9070_, v_s_u2083_9063_);
    v___x_9072_ = l_Lean_Name_str___override(v___x_9071_, v_s_u2084_9064_);
    v___x_9073_ = l_Lean_Name_str___override(v___x_9072_, v_s_u2085_9065_);
    v___x_9074_ = l_Lean_Name_str___override(v___x_9073_, v_s_u2086_9066_);
    v___x_9075_ = l_Lean_Name_str___override(v___x_9074_, v_s_u2087_9067_);
    return v___x_9075_;
}
pub unsafe fn l_Lean_Name_mkStr8(
    mut v_s_u2081_9076_: *mut LeanObject,
    mut v_s_u2082_9077_: *mut LeanObject,
    mut v_s_u2083_9078_: *mut LeanObject,
    mut v_s_u2084_9079_: *mut LeanObject,
    mut v_s_u2085_9080_: *mut LeanObject,
    mut v_s_u2086_9081_: *mut LeanObject,
    mut v_s_u2087_9082_: *mut LeanObject,
    mut v_s_u2088_9083_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9092_: *mut LeanObject = core::ptr::null_mut();
    v___x_9084_ = lean_box(0);
    v___x_9085_ = l_Lean_Name_str___override(v___x_9084_, v_s_u2081_9076_);
    v___x_9086_ = l_Lean_Name_str___override(v___x_9085_, v_s_u2082_9077_);
    v___x_9087_ = l_Lean_Name_str___override(v___x_9086_, v_s_u2083_9078_);
    v___x_9088_ = l_Lean_Name_str___override(v___x_9087_, v_s_u2084_9079_);
    v___x_9089_ = l_Lean_Name_str___override(v___x_9088_, v_s_u2085_9080_);
    v___x_9090_ = l_Lean_Name_str___override(v___x_9089_, v_s_u2086_9081_);
    v___x_9091_ = l_Lean_Name_str___override(v___x_9090_, v_s_u2087_9082_);
    v___x_9092_ = l_Lean_Name_str___override(v___x_9091_, v_s_u2088_9083_);
    return v___x_9092_;
}
pub unsafe fn l_Lean_Name_beq___boxed(
    mut v_a_00___x40___internal___hyg_9095_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_9096_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9097_: u8 = 0;
    let mut v_r_9098_: *mut LeanObject = core::ptr::null_mut();
    v_res_9097_ = lean_name_eq(
        v_a_00___x40___internal___hyg_9095_,
        v_a_00___x40___internal___hyg_9096_,
    );
    lean_dec(v_a_00___x40___internal___hyg_9096_);
    lean_dec(v_a_00___x40___internal___hyg_9095_);
    v_r_9098_ = lean_box((v_res_9097_) as usize);
    return v_r_9098_;
}
pub unsafe fn l_Lean_Name_appendCore(
    mut v_x_9101_: *mut LeanObject,
    mut v_x_9102_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_9102_) {
        0 => {
            lean_inc(v_x_9101_);
            return v_x_9101_;
        }
        1 => {
            let mut v_pre_9103_: *mut LeanObject = core::ptr::null_mut();
            let mut v_str_9104_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_9105_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_9106_: *mut LeanObject = core::ptr::null_mut();
            v_pre_9103_ = lean_ctor_get(v_x_9102_, 0);
            lean_inc(v_pre_9103_);
            v_str_9104_ = lean_ctor_get(v_x_9102_, 1);
            lean_inc_ref(v_str_9104_);
            lean_dec_ref_known(v_x_9102_, 2);
            v___x_9105_ = l_Lean_Name_appendCore(v_x_9101_, v_pre_9103_);
            v___x_9106_ = l_Lean_Name_str___override(v___x_9105_, v_str_9104_);
            return v___x_9106_;
        }
        _ => {
            let mut v_pre_9107_: *mut LeanObject = core::ptr::null_mut();
            let mut v_i_9108_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_9109_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_9110_: *mut LeanObject = core::ptr::null_mut();
            v_pre_9107_ = lean_ctor_get(v_x_9102_, 0);
            lean_inc(v_pre_9107_);
            v_i_9108_ = lean_ctor_get(v_x_9102_, 1);
            lean_inc(v_i_9108_);
            lean_dec_ref_known(v_x_9102_, 2);
            v___x_9109_ = l_Lean_Name_appendCore(v_x_9101_, v_pre_9107_);
            v___x_9110_ = l_Lean_Name_num___override(v___x_9109_, v_i_9108_);
            return v___x_9110_;
        }
    }
}
pub unsafe fn l_Lean_Name_appendCore___boxed(
    mut v_x_9111_: *mut LeanObject,
    mut v_x_9112_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9113_: *mut LeanObject = core::ptr::null_mut();
    v_res_9113_ = l_Lean_Name_appendCore(v_x_9111_, v_x_9112_);
    lean_dec(v_x_9111_);
    return v_res_9113_;
}
pub unsafe fn _init_l_Lean_defaultMaxRecDepth() -> *mut LeanObject {
    let mut v___x_9114_: *mut LeanObject = core::ptr::null_mut();
    v___x_9114_ = lean_unsigned_to_nat(512);
    return v___x_9114_;
}
pub unsafe fn l_Lean_SourceInfo_ctorIdx(mut v_x_9117_: *mut LeanObject) -> *mut LeanObject {
    match lean_obj_tag(v_x_9117_) {
        0 => {
            let mut v___x_9118_: *mut LeanObject = core::ptr::null_mut();
            v___x_9118_ = lean_unsigned_to_nat(0);
            return v___x_9118_;
        }
        1 => {
            let mut v___x_9119_: *mut LeanObject = core::ptr::null_mut();
            v___x_9119_ = lean_unsigned_to_nat(1);
            return v___x_9119_;
        }
        _ => {
            let mut v___x_9120_: *mut LeanObject = core::ptr::null_mut();
            v___x_9120_ = lean_unsigned_to_nat(2);
            return v___x_9120_;
        }
    }
}
pub unsafe fn l_Lean_SourceInfo_ctorIdx___boxed(mut v_x_9121_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_9122_: *mut LeanObject = core::ptr::null_mut();
    v_res_9122_ = l_Lean_SourceInfo_ctorIdx(v_x_9121_);
    lean_dec(v_x_9121_);
    return v_res_9122_;
}
pub unsafe fn l_Lean_SourceInfo_ctorElim___redArg(
    mut v_t_9123_: *mut LeanObject,
    mut v_k_9124_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_t_9123_) {
        0 => {
            let mut v_leading_9125_: *mut LeanObject = core::ptr::null_mut();
            let mut v_pos_9126_: *mut LeanObject = core::ptr::null_mut();
            let mut v_trailing_9127_: *mut LeanObject = core::ptr::null_mut();
            let mut v_endPos_9128_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_9129_: *mut LeanObject = core::ptr::null_mut();
            v_leading_9125_ = lean_ctor_get(v_t_9123_, 0);
            lean_inc_ref(v_leading_9125_);
            v_pos_9126_ = lean_ctor_get(v_t_9123_, 1);
            lean_inc(v_pos_9126_);
            v_trailing_9127_ = lean_ctor_get(v_t_9123_, 2);
            lean_inc_ref(v_trailing_9127_);
            v_endPos_9128_ = lean_ctor_get(v_t_9123_, 3);
            lean_inc(v_endPos_9128_);
            lean_dec_ref_known(v_t_9123_, 4);
            v___x_9129_ = lean_apply_4(
                v_k_9124_,
                v_leading_9125_,
                v_pos_9126_,
                v_trailing_9127_,
                v_endPos_9128_,
            );
            return v___x_9129_;
        }
        1 => {
            let mut v_pos_9130_: *mut LeanObject = core::ptr::null_mut();
            let mut v_endPos_9131_: *mut LeanObject = core::ptr::null_mut();
            let mut v_canonical_9132_: u8 = 0;
            let mut v___x_9133_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_9134_: *mut LeanObject = core::ptr::null_mut();
            v_pos_9130_ = lean_ctor_get(v_t_9123_, 0);
            lean_inc(v_pos_9130_);
            v_endPos_9131_ = lean_ctor_get(v_t_9123_, 1);
            lean_inc(v_endPos_9131_);
            v_canonical_9132_ = lean_ctor_get_uint8(
                v_t_9123_,
                (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
            );
            lean_dec_ref_known(v_t_9123_, 2);
            v___x_9133_ = lean_box((v_canonical_9132_) as usize);
            v___x_9134_ = lean_apply_3(v_k_9124_, v_pos_9130_, v_endPos_9131_, v___x_9133_);
            return v___x_9134_;
        }
        _ => {
            return v_k_9124_;
        }
    }
}
pub unsafe fn l_Lean_SourceInfo_ctorElim(
    mut v_motive_9135_: *mut LeanObject,
    mut v_ctorIdx_9136_: *mut LeanObject,
    mut v_t_9137_: *mut LeanObject,
    mut v_h_9138_: *mut LeanObject,
    mut v_k_9139_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9140_: *mut LeanObject = core::ptr::null_mut();
    v___x_9140_ = l_Lean_SourceInfo_ctorElim___redArg(v_t_9137_, v_k_9139_);
    return v___x_9140_;
}
pub unsafe fn l_Lean_SourceInfo_ctorElim___boxed(
    mut v_motive_9141_: *mut LeanObject,
    mut v_ctorIdx_9142_: *mut LeanObject,
    mut v_t_9143_: *mut LeanObject,
    mut v_h_9144_: *mut LeanObject,
    mut v_k_9145_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9146_: *mut LeanObject = core::ptr::null_mut();
    v_res_9146_ = l_Lean_SourceInfo_ctorElim(
        v_motive_9141_,
        v_ctorIdx_9142_,
        v_t_9143_,
        v_h_9144_,
        v_k_9145_,
    );
    lean_dec(v_ctorIdx_9142_);
    return v_res_9146_;
}
pub unsafe fn l_Lean_SourceInfo_original_elim___redArg(
    mut v_t_9147_: *mut LeanObject,
    mut v_original_9148_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9149_: *mut LeanObject = core::ptr::null_mut();
    v___x_9149_ = l_Lean_SourceInfo_ctorElim___redArg(v_t_9147_, v_original_9148_);
    return v___x_9149_;
}
pub unsafe fn l_Lean_SourceInfo_original_elim(
    mut v_motive_9150_: *mut LeanObject,
    mut v_t_9151_: *mut LeanObject,
    mut v_h_9152_: *mut LeanObject,
    mut v_original_9153_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9154_: *mut LeanObject = core::ptr::null_mut();
    v___x_9154_ = l_Lean_SourceInfo_ctorElim___redArg(v_t_9151_, v_original_9153_);
    return v___x_9154_;
}
pub unsafe fn l_Lean_SourceInfo_synthetic_elim___redArg(
    mut v_t_9155_: *mut LeanObject,
    mut v_synthetic_9156_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9157_: *mut LeanObject = core::ptr::null_mut();
    v___x_9157_ = l_Lean_SourceInfo_ctorElim___redArg(v_t_9155_, v_synthetic_9156_);
    return v___x_9157_;
}
pub unsafe fn l_Lean_SourceInfo_synthetic_elim(
    mut v_motive_9158_: *mut LeanObject,
    mut v_t_9159_: *mut LeanObject,
    mut v_h_9160_: *mut LeanObject,
    mut v_synthetic_9161_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9162_: *mut LeanObject = core::ptr::null_mut();
    v___x_9162_ = l_Lean_SourceInfo_ctorElim___redArg(v_t_9159_, v_synthetic_9161_);
    return v___x_9162_;
}
pub unsafe fn l_Lean_SourceInfo_none_elim___redArg(
    mut v_t_9163_: *mut LeanObject,
    mut v_none_9164_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9165_: *mut LeanObject = core::ptr::null_mut();
    v___x_9165_ = l_Lean_SourceInfo_ctorElim___redArg(v_t_9163_, v_none_9164_);
    return v___x_9165_;
}
pub unsafe fn l_Lean_SourceInfo_none_elim(
    mut v_motive_9166_: *mut LeanObject,
    mut v_t_9167_: *mut LeanObject,
    mut v_h_9168_: *mut LeanObject,
    mut v_none_9169_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9170_: *mut LeanObject = core::ptr::null_mut();
    v___x_9170_ = l_Lean_SourceInfo_ctorElim___redArg(v_t_9167_, v_none_9169_);
    return v___x_9170_;
}
pub unsafe fn _init_l_Lean_instInhabitedSourceInfo() -> *mut LeanObject {
    let mut v___x_9171_: *mut LeanObject = core::ptr::null_mut();
    v___x_9171_ = lean_box(2);
    return v___x_9171_;
}
pub unsafe fn l_Lean_SourceInfo_getPos_x3f(
    mut v_info_9172_: *mut LeanObject,
    mut v_canonicalOnly_9173_: u8,
) -> *mut LeanObject {
    match lean_obj_tag(v_info_9172_) {
        0 => {
            let mut v_pos_9174_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_9175_: *mut LeanObject = core::ptr::null_mut();
            v_pos_9174_ = lean_ctor_get(v_info_9172_, 1);
            lean_inc(v_pos_9174_);
            v___x_9175_ = lean_alloc_ctor(1, 1, (0) as u32);
            lean_ctor_set(v___x_9175_, 0, v_pos_9174_);
            return v___x_9175_;
        }
        1 => {
            let mut v_canonical_9176_: u8 = 0;
            v_canonical_9176_ = lean_ctor_get_uint8(
                v_info_9172_,
                (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
            );
            if v_canonical_9176_ == 0 {
                if v_canonicalOnly_9173_ == 0 {
                    let mut v_pos_9177_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_9178_: *mut LeanObject = core::ptr::null_mut();
                    v_pos_9177_ = lean_ctor_get(v_info_9172_, 0);
                    lean_inc(v_pos_9177_);
                    v___x_9178_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_9178_, 0, v_pos_9177_);
                    return v___x_9178_;
                } else {
                    let mut v___x_9179_: *mut LeanObject = core::ptr::null_mut();
                    v___x_9179_ = lean_box(0);
                    return v___x_9179_;
                }
            } else {
                let mut v_pos_9180_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_9181_: *mut LeanObject = core::ptr::null_mut();
                v_pos_9180_ = lean_ctor_get(v_info_9172_, 0);
                lean_inc(v_pos_9180_);
                v___x_9181_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_9181_, 0, v_pos_9180_);
                return v___x_9181_;
            }
        }
        _ => {
            let mut v___x_9182_: *mut LeanObject = core::ptr::null_mut();
            v___x_9182_ = lean_box(0);
            return v___x_9182_;
        }
    }
}
pub unsafe fn l_Lean_SourceInfo_getPos_x3f___boxed(
    mut v_info_9183_: *mut LeanObject,
    mut v_canonicalOnly_9184_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_canonicalOnly_boxed_9185_: u8 = 0;
    let mut v_res_9186_: *mut LeanObject = core::ptr::null_mut();
    v_canonicalOnly_boxed_9185_ = (lean_unbox(v_canonicalOnly_9184_) as u8);
    v_res_9186_ = l_Lean_SourceInfo_getPos_x3f(v_info_9183_, v_canonicalOnly_boxed_9185_);
    lean_dec(v_info_9183_);
    return v_res_9186_;
}
pub unsafe fn l_Lean_SourceInfo_getTailPos_x3f(
    mut v_info_9187_: *mut LeanObject,
    mut v_canonicalOnly_9188_: u8,
) -> *mut LeanObject {
    match lean_obj_tag(v_info_9187_) {
        0 => {
            let mut v_endPos_9189_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_9190_: *mut LeanObject = core::ptr::null_mut();
            v_endPos_9189_ = lean_ctor_get(v_info_9187_, 3);
            lean_inc(v_endPos_9189_);
            v___x_9190_ = lean_alloc_ctor(1, 1, (0) as u32);
            lean_ctor_set(v___x_9190_, 0, v_endPos_9189_);
            return v___x_9190_;
        }
        1 => {
            let mut v_canonical_9191_: u8 = 0;
            v_canonical_9191_ = lean_ctor_get_uint8(
                v_info_9187_,
                (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
            );
            if v_canonical_9191_ == 0 {
                if v_canonicalOnly_9188_ == 0 {
                    let mut v_endPos_9192_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_9193_: *mut LeanObject = core::ptr::null_mut();
                    v_endPos_9192_ = lean_ctor_get(v_info_9187_, 1);
                    lean_inc(v_endPos_9192_);
                    v___x_9193_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_9193_, 0, v_endPos_9192_);
                    return v___x_9193_;
                } else {
                    let mut v___x_9194_: *mut LeanObject = core::ptr::null_mut();
                    v___x_9194_ = lean_box(0);
                    return v___x_9194_;
                }
            } else {
                let mut v_endPos_9195_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_9196_: *mut LeanObject = core::ptr::null_mut();
                v_endPos_9195_ = lean_ctor_get(v_info_9187_, 1);
                lean_inc(v_endPos_9195_);
                v___x_9196_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_9196_, 0, v_endPos_9195_);
                return v___x_9196_;
            }
        }
        _ => {
            let mut v___x_9197_: *mut LeanObject = core::ptr::null_mut();
            v___x_9197_ = lean_box(0);
            return v___x_9197_;
        }
    }
}
pub unsafe fn l_Lean_SourceInfo_getTailPos_x3f___boxed(
    mut v_info_9198_: *mut LeanObject,
    mut v_canonicalOnly_9199_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_canonicalOnly_boxed_9200_: u8 = 0;
    let mut v_res_9201_: *mut LeanObject = core::ptr::null_mut();
    v_canonicalOnly_boxed_9200_ = (lean_unbox(v_canonicalOnly_9199_) as u8);
    v_res_9201_ = l_Lean_SourceInfo_getTailPos_x3f(v_info_9198_, v_canonicalOnly_boxed_9200_);
    lean_dec(v_info_9198_);
    return v_res_9201_;
}
pub unsafe fn l_Lean_SourceInfo_getTrailing_x3f(
    mut v_info_9202_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_info_9202_) == 0 {
        let mut v_trailing_9203_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_9204_: *mut LeanObject = core::ptr::null_mut();
        v_trailing_9203_ = lean_ctor_get(v_info_9202_, 2);
        lean_inc_ref(v_trailing_9203_);
        v___x_9204_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_9204_, 0, v_trailing_9203_);
        return v___x_9204_;
    } else {
        let mut v___x_9205_: *mut LeanObject = core::ptr::null_mut();
        v___x_9205_ = lean_box(0);
        return v___x_9205_;
    }
}
pub unsafe fn l_Lean_SourceInfo_getTrailing_x3f___boxed(
    mut v_info_9206_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9207_: *mut LeanObject = core::ptr::null_mut();
    v_res_9207_ = l_Lean_SourceInfo_getTrailing_x3f(v_info_9206_);
    lean_dec(v_info_9206_);
    return v_res_9207_;
}
pub unsafe fn l_Lean_SourceInfo_getTrailingTailPos_x3f(
    mut v_info_9208_: *mut LeanObject,
    mut v_canonicalOnly_9209_: u8,
) -> *mut LeanObject {
    let mut v___x_9210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9211_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_9212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9214_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9215_: u8 = 0;
    let mut v_stopPos_9216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9219_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9220_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_9210_ = l_Lean_SourceInfo_getTrailing_x3f(v_info_9208_);
                if lean_obj_tag(v___x_9210_) == 0 {
                    v___x_9211_ =
                        l_Lean_SourceInfo_getTailPos_x3f(v_info_9208_, v_canonicalOnly_9209_);
                    return v___x_9211_;
                } else {
                    v_val_9212_ = lean_ctor_get(v___x_9210_, 0);
                    v_isSharedCheck_9220_ = (!lean_is_exclusive(v___x_9210_)) as u8;
                    if v_isSharedCheck_9220_ == 0 {
                        v___x_9214_ = v___x_9210_;
                        v_isShared_9215_ = v_isSharedCheck_9220_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_9212_);
                        lean_dec(v___x_9210_);
                        v___x_9214_ = lean_box(0);
                        v_isShared_9215_ = v_isSharedCheck_9220_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_stopPos_9216_ = lean_ctor_get(v_val_9212_, 2);
                lean_inc(v_stopPos_9216_);
                lean_dec(v_val_9212_);
                if v_isShared_9215_ == 0 {
                    lean_ctor_set(v___x_9214_, 0, v_stopPos_9216_);
                    v___x_9218_ = v___x_9214_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_9219_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9219_, 0, v_stopPos_9216_);
                    v___x_9218_ = v_reuseFailAlloc_9219_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_9218_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_SourceInfo_getTrailingTailPos_x3f___boxed(
    mut v_info_9221_: *mut LeanObject,
    mut v_canonicalOnly_9222_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_canonicalOnly_boxed_9223_: u8 = 0;
    let mut v_res_9224_: *mut LeanObject = core::ptr::null_mut();
    v_canonicalOnly_boxed_9223_ = (lean_unbox(v_canonicalOnly_9222_) as u8);
    v_res_9224_ =
        l_Lean_SourceInfo_getTrailingTailPos_x3f(v_info_9221_, v_canonicalOnly_boxed_9223_);
    lean_dec(v_info_9221_);
    return v_res_9224_;
}
pub unsafe fn l_Lean_Syntax_Preresolved_ctorIdx(mut v_x_9225_: *mut LeanObject) -> *mut LeanObject {
    if lean_obj_tag(v_x_9225_) == 0 {
        let mut v___x_9226_: *mut LeanObject = core::ptr::null_mut();
        v___x_9226_ = lean_unsigned_to_nat(0);
        return v___x_9226_;
    } else {
        let mut v___x_9227_: *mut LeanObject = core::ptr::null_mut();
        v___x_9227_ = lean_unsigned_to_nat(1);
        return v___x_9227_;
    }
}
pub unsafe fn l_Lean_Syntax_Preresolved_ctorIdx___boxed(
    mut v_x_9228_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9229_: *mut LeanObject = core::ptr::null_mut();
    v_res_9229_ = l_Lean_Syntax_Preresolved_ctorIdx(v_x_9228_);
    lean_dec_ref(v_x_9228_);
    return v_res_9229_;
}
pub unsafe fn l_Lean_Syntax_Preresolved_ctorElim___redArg(
    mut v_t_9230_: *mut LeanObject,
    mut v_k_9231_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_t_9230_) == 0 {
        let mut v_ns_9232_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_9233_: *mut LeanObject = core::ptr::null_mut();
        v_ns_9232_ = lean_ctor_get(v_t_9230_, 0);
        lean_inc(v_ns_9232_);
        lean_dec_ref_known(v_t_9230_, 1);
        v___x_9233_ = lean_apply_1(v_k_9231_, v_ns_9232_);
        return v___x_9233_;
    } else {
        let mut v_n_9234_: *mut LeanObject = core::ptr::null_mut();
        let mut v_fields_9235_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_9236_: *mut LeanObject = core::ptr::null_mut();
        v_n_9234_ = lean_ctor_get(v_t_9230_, 0);
        lean_inc(v_n_9234_);
        v_fields_9235_ = lean_ctor_get(v_t_9230_, 1);
        lean_inc(v_fields_9235_);
        lean_dec_ref_known(v_t_9230_, 2);
        v___x_9236_ = lean_apply_2(v_k_9231_, v_n_9234_, v_fields_9235_);
        return v___x_9236_;
    }
}
pub unsafe fn l_Lean_Syntax_Preresolved_ctorElim(
    mut v_motive_9237_: *mut LeanObject,
    mut v_ctorIdx_9238_: *mut LeanObject,
    mut v_t_9239_: *mut LeanObject,
    mut v_h_9240_: *mut LeanObject,
    mut v_k_9241_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9242_: *mut LeanObject = core::ptr::null_mut();
    v___x_9242_ = l_Lean_Syntax_Preresolved_ctorElim___redArg(v_t_9239_, v_k_9241_);
    return v___x_9242_;
}
pub unsafe fn l_Lean_Syntax_Preresolved_ctorElim___boxed(
    mut v_motive_9243_: *mut LeanObject,
    mut v_ctorIdx_9244_: *mut LeanObject,
    mut v_t_9245_: *mut LeanObject,
    mut v_h_9246_: *mut LeanObject,
    mut v_k_9247_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9248_: *mut LeanObject = core::ptr::null_mut();
    v_res_9248_ = l_Lean_Syntax_Preresolved_ctorElim(
        v_motive_9243_,
        v_ctorIdx_9244_,
        v_t_9245_,
        v_h_9246_,
        v_k_9247_,
    );
    lean_dec(v_ctorIdx_9244_);
    return v_res_9248_;
}
pub unsafe fn l_Lean_Syntax_Preresolved_namespace_elim___redArg(
    mut v_t_9249_: *mut LeanObject,
    mut v_namespace_9250_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9251_: *mut LeanObject = core::ptr::null_mut();
    v___x_9251_ = l_Lean_Syntax_Preresolved_ctorElim___redArg(v_t_9249_, v_namespace_9250_);
    return v___x_9251_;
}
pub unsafe fn l_Lean_Syntax_Preresolved_namespace_elim(
    mut v_motive_9252_: *mut LeanObject,
    mut v_t_9253_: *mut LeanObject,
    mut v_h_9254_: *mut LeanObject,
    mut v_namespace_9255_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9256_: *mut LeanObject = core::ptr::null_mut();
    v___x_9256_ = l_Lean_Syntax_Preresolved_ctorElim___redArg(v_t_9253_, v_namespace_9255_);
    return v___x_9256_;
}
pub unsafe fn l_Lean_Syntax_Preresolved_decl_elim___redArg(
    mut v_t_9257_: *mut LeanObject,
    mut v_decl_9258_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9259_: *mut LeanObject = core::ptr::null_mut();
    v___x_9259_ = l_Lean_Syntax_Preresolved_ctorElim___redArg(v_t_9257_, v_decl_9258_);
    return v___x_9259_;
}
pub unsafe fn l_Lean_Syntax_Preresolved_decl_elim(
    mut v_motive_9260_: *mut LeanObject,
    mut v_t_9261_: *mut LeanObject,
    mut v_h_9262_: *mut LeanObject,
    mut v_decl_9263_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9264_: *mut LeanObject = core::ptr::null_mut();
    v___x_9264_ = l_Lean_Syntax_Preresolved_ctorElim___redArg(v_t_9261_, v_decl_9263_);
    return v___x_9264_;
}
pub unsafe fn l_Lean_Syntax_ctorIdx(mut v_x_9265_: *mut LeanObject) -> *mut LeanObject {
    match lean_obj_tag(v_x_9265_) {
        0 => {
            let mut v___x_9266_: *mut LeanObject = core::ptr::null_mut();
            v___x_9266_ = lean_unsigned_to_nat(0);
            return v___x_9266_;
        }
        1 => {
            let mut v___x_9267_: *mut LeanObject = core::ptr::null_mut();
            v___x_9267_ = lean_unsigned_to_nat(1);
            return v___x_9267_;
        }
        2 => {
            let mut v___x_9268_: *mut LeanObject = core::ptr::null_mut();
            v___x_9268_ = lean_unsigned_to_nat(2);
            return v___x_9268_;
        }
        _ => {
            let mut v___x_9269_: *mut LeanObject = core::ptr::null_mut();
            v___x_9269_ = lean_unsigned_to_nat(3);
            return v___x_9269_;
        }
    }
}
pub unsafe fn l_Lean_Syntax_ctorIdx___boxed(mut v_x_9270_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_9271_: *mut LeanObject = core::ptr::null_mut();
    v_res_9271_ = l_Lean_Syntax_ctorIdx(v_x_9270_);
    lean_dec(v_x_9270_);
    return v_res_9271_;
}
pub unsafe fn l_Lean_Syntax_ctorElim___redArg(
    mut v_t_9272_: *mut LeanObject,
    mut v_k_9273_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_t_9272_) {
        0 => {
            return v_k_9273_;
        }
        1 => {
            let mut v_info_9274_: *mut LeanObject = core::ptr::null_mut();
            let mut v_kind_9275_: *mut LeanObject = core::ptr::null_mut();
            let mut v_args_9276_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_9277_: *mut LeanObject = core::ptr::null_mut();
            v_info_9274_ = lean_ctor_get(v_t_9272_, 0);
            lean_inc(v_info_9274_);
            v_kind_9275_ = lean_ctor_get(v_t_9272_, 1);
            lean_inc(v_kind_9275_);
            v_args_9276_ = lean_ctor_get(v_t_9272_, 2);
            lean_inc_ref(v_args_9276_);
            lean_dec_ref_known(v_t_9272_, 3);
            v___x_9277_ = lean_apply_3(v_k_9273_, v_info_9274_, v_kind_9275_, v_args_9276_);
            return v___x_9277_;
        }
        2 => {
            let mut v_info_9278_: *mut LeanObject = core::ptr::null_mut();
            let mut v_val_9279_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_9280_: *mut LeanObject = core::ptr::null_mut();
            v_info_9278_ = lean_ctor_get(v_t_9272_, 0);
            lean_inc(v_info_9278_);
            v_val_9279_ = lean_ctor_get(v_t_9272_, 1);
            lean_inc_ref(v_val_9279_);
            lean_dec_ref_known(v_t_9272_, 2);
            v___x_9280_ = lean_apply_2(v_k_9273_, v_info_9278_, v_val_9279_);
            return v___x_9280_;
        }
        _ => {
            let mut v_info_9281_: *mut LeanObject = core::ptr::null_mut();
            let mut v_rawVal_9282_: *mut LeanObject = core::ptr::null_mut();
            let mut v_val_9283_: *mut LeanObject = core::ptr::null_mut();
            let mut v_preresolved_9284_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_9285_: *mut LeanObject = core::ptr::null_mut();
            v_info_9281_ = lean_ctor_get(v_t_9272_, 0);
            lean_inc(v_info_9281_);
            v_rawVal_9282_ = lean_ctor_get(v_t_9272_, 1);
            lean_inc_ref(v_rawVal_9282_);
            v_val_9283_ = lean_ctor_get(v_t_9272_, 2);
            lean_inc(v_val_9283_);
            v_preresolved_9284_ = lean_ctor_get(v_t_9272_, 3);
            lean_inc(v_preresolved_9284_);
            lean_dec_ref_known(v_t_9272_, 4);
            v___x_9285_ = lean_apply_4(
                v_k_9273_,
                v_info_9281_,
                v_rawVal_9282_,
                v_val_9283_,
                v_preresolved_9284_,
            );
            return v___x_9285_;
        }
    }
}
pub unsafe fn l_Lean_Syntax_ctorElim(
    mut v_motive__1_9286_: *mut LeanObject,
    mut v_ctorIdx_9287_: *mut LeanObject,
    mut v_t_9288_: *mut LeanObject,
    mut v_h_9289_: *mut LeanObject,
    mut v_k_9290_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9291_: *mut LeanObject = core::ptr::null_mut();
    v___x_9291_ = l_Lean_Syntax_ctorElim___redArg(v_t_9288_, v_k_9290_);
    return v___x_9291_;
}
pub unsafe fn l_Lean_Syntax_ctorElim___boxed(
    mut v_motive__1_9292_: *mut LeanObject,
    mut v_ctorIdx_9293_: *mut LeanObject,
    mut v_t_9294_: *mut LeanObject,
    mut v_h_9295_: *mut LeanObject,
    mut v_k_9296_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9297_: *mut LeanObject = core::ptr::null_mut();
    v_res_9297_ = l_Lean_Syntax_ctorElim(
        v_motive__1_9292_,
        v_ctorIdx_9293_,
        v_t_9294_,
        v_h_9295_,
        v_k_9296_,
    );
    lean_dec(v_ctorIdx_9293_);
    return v_res_9297_;
}
pub unsafe fn l_Lean_Syntax_missing_elim___redArg(
    mut v_t_9298_: *mut LeanObject,
    mut v_missing_9299_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9300_: *mut LeanObject = core::ptr::null_mut();
    v___x_9300_ = l_Lean_Syntax_ctorElim___redArg(v_t_9298_, v_missing_9299_);
    return v___x_9300_;
}
pub unsafe fn l_Lean_Syntax_missing_elim(
    mut v_motive__1_9301_: *mut LeanObject,
    mut v_t_9302_: *mut LeanObject,
    mut v_h_9303_: *mut LeanObject,
    mut v_missing_9304_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9305_: *mut LeanObject = core::ptr::null_mut();
    v___x_9305_ = l_Lean_Syntax_ctorElim___redArg(v_t_9302_, v_missing_9304_);
    return v___x_9305_;
}
pub unsafe fn l_Lean_Syntax_node_elim___redArg(
    mut v_t_9306_: *mut LeanObject,
    mut v_node_9307_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9308_: *mut LeanObject = core::ptr::null_mut();
    v___x_9308_ = l_Lean_Syntax_ctorElim___redArg(v_t_9306_, v_node_9307_);
    return v___x_9308_;
}
pub unsafe fn l_Lean_Syntax_node_elim(
    mut v_motive__1_9309_: *mut LeanObject,
    mut v_t_9310_: *mut LeanObject,
    mut v_h_9311_: *mut LeanObject,
    mut v_node_9312_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9313_: *mut LeanObject = core::ptr::null_mut();
    v___x_9313_ = l_Lean_Syntax_ctorElim___redArg(v_t_9310_, v_node_9312_);
    return v___x_9313_;
}
pub unsafe fn l_Lean_Syntax_atom_elim___redArg(
    mut v_t_9314_: *mut LeanObject,
    mut v_atom_9315_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9316_: *mut LeanObject = core::ptr::null_mut();
    v___x_9316_ = l_Lean_Syntax_ctorElim___redArg(v_t_9314_, v_atom_9315_);
    return v___x_9316_;
}
pub unsafe fn l_Lean_Syntax_atom_elim(
    mut v_motive__1_9317_: *mut LeanObject,
    mut v_t_9318_: *mut LeanObject,
    mut v_h_9319_: *mut LeanObject,
    mut v_atom_9320_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9321_: *mut LeanObject = core::ptr::null_mut();
    v___x_9321_ = l_Lean_Syntax_ctorElim___redArg(v_t_9318_, v_atom_9320_);
    return v___x_9321_;
}
pub unsafe fn l_Lean_Syntax_ident_elim___redArg(
    mut v_t_9322_: *mut LeanObject,
    mut v_ident_9323_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9324_: *mut LeanObject = core::ptr::null_mut();
    v___x_9324_ = l_Lean_Syntax_ctorElim___redArg(v_t_9322_, v_ident_9323_);
    return v___x_9324_;
}
pub unsafe fn l_Lean_Syntax_ident_elim(
    mut v_motive__1_9325_: *mut LeanObject,
    mut v_t_9326_: *mut LeanObject,
    mut v_h_9327_: *mut LeanObject,
    mut v_ident_9328_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9329_: *mut LeanObject = core::ptr::null_mut();
    v___x_9329_ = l_Lean_Syntax_ctorElim___redArg(v_t_9326_, v_ident_9328_);
    return v___x_9329_;
}
pub unsafe fn l_Lean_Syntax_node1(
    mut v_info_9330_: *mut LeanObject,
    mut v_kind_9331_: *mut LeanObject,
    mut v_a_u2081_9332_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9334_: *mut LeanObject = core::ptr::null_mut();
    v___x_9333_ = l_Array_mkArray1___redArg(v_a_u2081_9332_);
    v___x_9334_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_9334_, 0, v_info_9330_);
    lean_ctor_set(v___x_9334_, 1, v_kind_9331_);
    lean_ctor_set(v___x_9334_, 2, v___x_9333_);
    return v___x_9334_;
}
pub unsafe fn l_Lean_Syntax_node2(
    mut v_info_9335_: *mut LeanObject,
    mut v_kind_9336_: *mut LeanObject,
    mut v_a_u2081_9337_: *mut LeanObject,
    mut v_a_u2082_9338_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9340_: *mut LeanObject = core::ptr::null_mut();
    v___x_9339_ = l_Array_mkArray2___redArg(v_a_u2081_9337_, v_a_u2082_9338_);
    v___x_9340_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_9340_, 0, v_info_9335_);
    lean_ctor_set(v___x_9340_, 1, v_kind_9336_);
    lean_ctor_set(v___x_9340_, 2, v___x_9339_);
    return v___x_9340_;
}
pub unsafe fn l_Lean_Syntax_node3(
    mut v_info_9341_: *mut LeanObject,
    mut v_kind_9342_: *mut LeanObject,
    mut v_a_u2081_9343_: *mut LeanObject,
    mut v_a_u2082_9344_: *mut LeanObject,
    mut v_a_u2083_9345_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9347_: *mut LeanObject = core::ptr::null_mut();
    v___x_9346_ = l_Array_mkArray3___redArg(v_a_u2081_9343_, v_a_u2082_9344_, v_a_u2083_9345_);
    v___x_9347_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_9347_, 0, v_info_9341_);
    lean_ctor_set(v___x_9347_, 1, v_kind_9342_);
    lean_ctor_set(v___x_9347_, 2, v___x_9346_);
    return v___x_9347_;
}
pub unsafe fn l_Lean_Syntax_node4(
    mut v_info_9348_: *mut LeanObject,
    mut v_kind_9349_: *mut LeanObject,
    mut v_a_u2081_9350_: *mut LeanObject,
    mut v_a_u2082_9351_: *mut LeanObject,
    mut v_a_u2083_9352_: *mut LeanObject,
    mut v_a_u2084_9353_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9355_: *mut LeanObject = core::ptr::null_mut();
    v___x_9354_ = l_Array_mkArray4___redArg(
        v_a_u2081_9350_,
        v_a_u2082_9351_,
        v_a_u2083_9352_,
        v_a_u2084_9353_,
    );
    v___x_9355_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_9355_, 0, v_info_9348_);
    lean_ctor_set(v___x_9355_, 1, v_kind_9349_);
    lean_ctor_set(v___x_9355_, 2, v___x_9354_);
    return v___x_9355_;
}
pub unsafe fn l_Lean_Syntax_node5(
    mut v_info_9356_: *mut LeanObject,
    mut v_kind_9357_: *mut LeanObject,
    mut v_a_u2081_9358_: *mut LeanObject,
    mut v_a_u2082_9359_: *mut LeanObject,
    mut v_a_u2083_9360_: *mut LeanObject,
    mut v_a_u2084_9361_: *mut LeanObject,
    mut v_a_u2085_9362_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9364_: *mut LeanObject = core::ptr::null_mut();
    v___x_9363_ = l_Array_mkArray5___redArg(
        v_a_u2081_9358_,
        v_a_u2082_9359_,
        v_a_u2083_9360_,
        v_a_u2084_9361_,
        v_a_u2085_9362_,
    );
    v___x_9364_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_9364_, 0, v_info_9356_);
    lean_ctor_set(v___x_9364_, 1, v_kind_9357_);
    lean_ctor_set(v___x_9364_, 2, v___x_9363_);
    return v___x_9364_;
}
pub unsafe fn l_Lean_Syntax_node6(
    mut v_info_9365_: *mut LeanObject,
    mut v_kind_9366_: *mut LeanObject,
    mut v_a_u2081_9367_: *mut LeanObject,
    mut v_a_u2082_9368_: *mut LeanObject,
    mut v_a_u2083_9369_: *mut LeanObject,
    mut v_a_u2084_9370_: *mut LeanObject,
    mut v_a_u2085_9371_: *mut LeanObject,
    mut v_a_u2086_9372_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9374_: *mut LeanObject = core::ptr::null_mut();
    v___x_9373_ = l_Array_mkArray6___redArg(
        v_a_u2081_9367_,
        v_a_u2082_9368_,
        v_a_u2083_9369_,
        v_a_u2084_9370_,
        v_a_u2085_9371_,
        v_a_u2086_9372_,
    );
    v___x_9374_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_9374_, 0, v_info_9365_);
    lean_ctor_set(v___x_9374_, 1, v_kind_9366_);
    lean_ctor_set(v___x_9374_, 2, v___x_9373_);
    return v___x_9374_;
}
pub unsafe fn l_Lean_Syntax_node7(
    mut v_info_9375_: *mut LeanObject,
    mut v_kind_9376_: *mut LeanObject,
    mut v_a_u2081_9377_: *mut LeanObject,
    mut v_a_u2082_9378_: *mut LeanObject,
    mut v_a_u2083_9379_: *mut LeanObject,
    mut v_a_u2084_9380_: *mut LeanObject,
    mut v_a_u2085_9381_: *mut LeanObject,
    mut v_a_u2086_9382_: *mut LeanObject,
    mut v_a_u2087_9383_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9385_: *mut LeanObject = core::ptr::null_mut();
    v___x_9384_ = l_Array_mkArray7___redArg(
        v_a_u2081_9377_,
        v_a_u2082_9378_,
        v_a_u2083_9379_,
        v_a_u2084_9380_,
        v_a_u2085_9381_,
        v_a_u2086_9382_,
        v_a_u2087_9383_,
    );
    v___x_9385_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_9385_, 0, v_info_9375_);
    lean_ctor_set(v___x_9385_, 1, v_kind_9376_);
    lean_ctor_set(v___x_9385_, 2, v___x_9384_);
    return v___x_9385_;
}
pub unsafe fn l_Lean_Syntax_node8(
    mut v_info_9386_: *mut LeanObject,
    mut v_kind_9387_: *mut LeanObject,
    mut v_a_u2081_9388_: *mut LeanObject,
    mut v_a_u2082_9389_: *mut LeanObject,
    mut v_a_u2083_9390_: *mut LeanObject,
    mut v_a_u2084_9391_: *mut LeanObject,
    mut v_a_u2085_9392_: *mut LeanObject,
    mut v_a_u2086_9393_: *mut LeanObject,
    mut v_a_u2087_9394_: *mut LeanObject,
    mut v_a_u2088_9395_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9397_: *mut LeanObject = core::ptr::null_mut();
    v___x_9396_ = l_Array_mkArray8___redArg(
        v_a_u2081_9388_,
        v_a_u2082_9389_,
        v_a_u2083_9390_,
        v_a_u2084_9391_,
        v_a_u2085_9392_,
        v_a_u2086_9393_,
        v_a_u2087_9394_,
        v_a_u2088_9395_,
    );
    v___x_9397_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_9397_, 0, v_info_9386_);
    lean_ctor_set(v___x_9397_, 1, v_kind_9387_);
    lean_ctor_set(v___x_9397_, 2, v___x_9396_);
    return v___x_9397_;
}
pub unsafe fn _init_l_Lean_instInhabitedSyntax() -> *mut LeanObject {
    let mut v___x_9398_: *mut LeanObject = core::ptr::null_mut();
    v___x_9398_ = lean_box(0);
    return v___x_9398_;
}
pub unsafe fn l_Lean_instInhabitedTSyntax(mut v_ks_9399_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_9400_: *mut LeanObject = core::ptr::null_mut();
    v___x_9400_ = lean_box(0);
    return v___x_9400_;
}
pub unsafe fn l_Lean_instInhabitedTSyntax___boxed(
    mut v_ks_9401_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9402_: *mut LeanObject = core::ptr::null_mut();
    v_res_9402_ = l_Lean_instInhabitedTSyntax(v_ks_9401_);
    lean_dec(v_ks_9401_);
    return v_res_9402_;
}
pub unsafe fn l_Lean_mkNode(
    mut v_k_9459_: *mut LeanObject,
    mut v_args_9460_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9462_: *mut LeanObject = core::ptr::null_mut();
    v___x_9461_ = lean_box(2);
    v___x_9462_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_9462_, 0, v___x_9461_);
    lean_ctor_set(v___x_9462_, 1, v_k_9459_);
    lean_ctor_set(v___x_9462_, 2, v_args_9460_);
    return v___x_9462_;
}
pub unsafe fn l_Lean_mkNullNode(mut v_args_9463_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_9464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9466_: *mut LeanObject = core::ptr::null_mut();
    v___x_9464_ = l_Lean_nullKind___closed__1;
    v___x_9465_ = lean_box(2);
    v___x_9466_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_9466_, 0, v___x_9465_);
    lean_ctor_set(v___x_9466_, 1, v___x_9464_);
    lean_ctor_set(v___x_9466_, 2, v_args_9463_);
    return v___x_9466_;
}
pub unsafe fn l_Lean_Syntax_getKind(mut v_stx_9470_: *mut LeanObject) -> *mut LeanObject {
    match lean_obj_tag(v_stx_9470_) {
        0 => {
            let mut v___x_9471_: *mut LeanObject = core::ptr::null_mut();
            v___x_9471_ = l_Lean_Syntax_getKind___closed__1;
            return v___x_9471_;
        }
        1 => {
            let mut v_kind_9472_: *mut LeanObject = core::ptr::null_mut();
            v_kind_9472_ = lean_ctor_get(v_stx_9470_, 1);
            lean_inc(v_kind_9472_);
            lean_dec_ref_known(v_stx_9470_, 3);
            return v_kind_9472_;
        }
        2 => {
            let mut v_val_9473_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_9474_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_9475_: *mut LeanObject = core::ptr::null_mut();
            v_val_9473_ = lean_ctor_get(v_stx_9470_, 1);
            lean_inc_ref(v_val_9473_);
            lean_dec_ref_known(v_stx_9470_, 2);
            v___x_9474_ = lean_box(0);
            v___x_9475_ = l_Lean_Name_str___override(v___x_9474_, v_val_9473_);
            return v___x_9475_;
        }
        _ => {
            let mut v___x_9476_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref_known(v_stx_9470_, 4);
            v___x_9476_ = l_Lean_identKind___closed__1;
            return v___x_9476_;
        }
    }
}
pub unsafe fn l_Lean_Syntax_setKind(
    mut v_stx_9477_: *mut LeanObject,
    mut v_k_9478_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_info_9479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_9480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9482_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9483_: u8 = 0;
    let mut v___x_9485_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9487_: u8 = 0;
    let mut v_unused_9488_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_stx_9477_) == 1 {
                    v_info_9479_ = lean_ctor_get(v_stx_9477_, 0);
                    v_args_9480_ = lean_ctor_get(v_stx_9477_, 2);
                    v_isSharedCheck_9487_ = (!lean_is_exclusive(v_stx_9477_)) as u8;
                    if v_isSharedCheck_9487_ == 0 {
                        v_unused_9488_ = lean_ctor_get(v_stx_9477_, 1);
                        lean_dec(v_unused_9488_);
                        v___x_9482_ = v_stx_9477_;
                        v_isShared_9483_ = v_isSharedCheck_9487_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_args_9480_);
                        lean_inc(v_info_9479_);
                        lean_dec(v_stx_9477_);
                        v___x_9482_ = lean_box(0);
                        v_isShared_9483_ = v_isSharedCheck_9487_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_k_9478_);
                    return v_stx_9477_;
                }
            }
            1 => {
                if v_isShared_9483_ == 0 {
                    lean_ctor_set(v___x_9482_, 1, v_k_9478_);
                    v___x_9485_ = v___x_9482_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_9486_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9486_, 0, v_info_9479_);
                    lean_ctor_set(v_reuseFailAlloc_9486_, 1, v_k_9478_);
                    lean_ctor_set(v_reuseFailAlloc_9486_, 2, v_args_9480_);
                    v___x_9485_ = v_reuseFailAlloc_9486_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_9485_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Syntax_isOfKind(
    mut v_stx_9489_: *mut LeanObject,
    mut v_k_9490_: *mut LeanObject,
) -> u8 {
    let mut v___x_9491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9492_: u8 = 0;
    v___x_9491_ = l_Lean_Syntax_getKind(v_stx_9489_);
    v___x_9492_ = lean_name_eq(v___x_9491_, v_k_9490_);
    lean_dec(v___x_9491_);
    return v___x_9492_;
}
pub unsafe fn l_Lean_Syntax_isOfKind___boxed(
    mut v_stx_9493_: *mut LeanObject,
    mut v_k_9494_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9495_: u8 = 0;
    let mut v_r_9496_: *mut LeanObject = core::ptr::null_mut();
    v_res_9495_ = l_Lean_Syntax_isOfKind(v_stx_9493_, v_k_9494_);
    lean_dec(v_k_9494_);
    v_r_9496_ = lean_box((v_res_9495_) as usize);
    return v_r_9496_;
}
pub unsafe fn l_Lean_Syntax_getArg(
    mut v_stx_9497_: *mut LeanObject,
    mut v_i_9498_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_stx_9497_) {
        0 => {
            return v_stx_9497_;
        }
        1 => {
            let mut v_args_9499_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_9500_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_9501_: u8 = 0;
            v_args_9499_ = lean_ctor_get(v_stx_9497_, 2);
            v___x_9500_ = lean_array_get_size(v_args_9499_);
            v___x_9501_ = lean_nat_dec_lt(v_i_9498_, v___x_9500_);
            if v___x_9501_ == 0 {
                let mut v___x_9502_: *mut LeanObject = core::ptr::null_mut();
                v___x_9502_ = lean_box(0);
                return v___x_9502_;
            } else {
                let mut v___x_9503_: *mut LeanObject = core::ptr::null_mut();
                v___x_9503_ = lean_array_fget_borrowed(v_args_9499_, v_i_9498_);
                lean_inc(v___x_9503_);
                return v___x_9503_;
            }
        }
        _ => {
            let mut v___x_9504_: *mut LeanObject = core::ptr::null_mut();
            v___x_9504_ = lean_box(0);
            return v___x_9504_;
        }
    }
}
pub unsafe fn l_Lean_Syntax_getArg___boxed(
    mut v_stx_9505_: *mut LeanObject,
    mut v_i_9506_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9507_: *mut LeanObject = core::ptr::null_mut();
    v_res_9507_ = l_Lean_Syntax_getArg(v_stx_9505_, v_i_9506_);
    lean_dec(v_i_9506_);
    lean_dec(v_stx_9505_);
    return v_res_9507_;
}
pub unsafe fn l_Lean_Syntax_getArgs(mut v_stx_9510_: *mut LeanObject) -> *mut LeanObject {
    if lean_obj_tag(v_stx_9510_) == 1 {
        let mut v_args_9511_: *mut LeanObject = core::ptr::null_mut();
        v_args_9511_ = lean_ctor_get(v_stx_9510_, 2);
        lean_inc_ref(v_args_9511_);
        return v_args_9511_;
    } else {
        let mut v___x_9512_: *mut LeanObject = core::ptr::null_mut();
        v___x_9512_ = l_Lean_Syntax_getArgs___closed__0;
        return v___x_9512_;
    }
}
pub unsafe fn l_Lean_Syntax_getArgs___boxed(mut v_stx_9513_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_9514_: *mut LeanObject = core::ptr::null_mut();
    v_res_9514_ = l_Lean_Syntax_getArgs(v_stx_9513_);
    lean_dec(v_stx_9513_);
    return v_res_9514_;
}
pub unsafe fn l_Lean_Syntax_getNumArgs(mut v_stx_9515_: *mut LeanObject) -> *mut LeanObject {
    if lean_obj_tag(v_stx_9515_) == 1 {
        let mut v_args_9516_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_9517_: *mut LeanObject = core::ptr::null_mut();
        v_args_9516_ = lean_ctor_get(v_stx_9515_, 2);
        v___x_9517_ = lean_array_get_size(v_args_9516_);
        return v___x_9517_;
    } else {
        let mut v___x_9518_: *mut LeanObject = core::ptr::null_mut();
        v___x_9518_ = lean_unsigned_to_nat(0);
        return v___x_9518_;
    }
}
pub unsafe fn l_Lean_Syntax_getNumArgs___boxed(
    mut v_stx_9519_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9520_: *mut LeanObject = core::ptr::null_mut();
    v_res_9520_ = l_Lean_Syntax_getNumArgs(v_stx_9519_);
    lean_dec(v_stx_9519_);
    return v_res_9520_;
}
pub unsafe fn l_Lean_Syntax_getOptional_x3f(mut v_stx_9521_: *mut LeanObject) -> *mut LeanObject {
    let mut v_kind_9522_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_9523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_9526_: u8 = 0;
    let mut v___x_9527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9532_: u8 = 0;
    let mut v___x_9533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9535_: u8 = 0;
    let mut v___x_9536_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_stx_9521_) == 1 {
                    v_kind_9522_ = lean_ctor_get(v_stx_9521_, 1);
                    v_args_9523_ = lean_ctor_get(v_stx_9521_, 2);
                    v___x_9524_ = lean_box(0);
                    v___x_9531_ = l_Lean_nullKind___closed__1;
                    v___x_9532_ = lean_name_eq(v_kind_9522_, v___x_9531_);
                    if v___x_9532_ == 0 {
                        v___y_9526_ = v___x_9532_;
                        state = 1;
                        continue;
                    } else {
                        v___x_9533_ = lean_array_get_size(v_args_9523_);
                        v___x_9534_ = lean_unsigned_to_nat(1);
                        v___x_9535_ = lean_nat_dec_eq(v___x_9533_, v___x_9534_);
                        v___y_9526_ = v___x_9535_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_9536_ = lean_box(0);
                    return v___x_9536_;
                }
            }
            1 => {
                if v___y_9526_ == 0 {
                    v___x_9527_ = lean_box(0);
                    return v___x_9527_;
                } else {
                    v___x_9528_ = lean_unsigned_to_nat(0);
                    v___x_9529_ = lean_array_get_borrowed(v___x_9524_, v_args_9523_, v___x_9528_);
                    lean_inc(v___x_9529_);
                    v___x_9530_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_9530_, 0, v___x_9529_);
                    return v___x_9530_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Syntax_getOptional_x3f___boxed(
    mut v_stx_9537_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9538_: *mut LeanObject = core::ptr::null_mut();
    v_res_9538_ = l_Lean_Syntax_getOptional_x3f(v_stx_9537_);
    lean_dec(v_stx_9537_);
    return v_res_9538_;
}
pub unsafe fn l_Lean_Syntax_isMissing(mut v_x_9539_: *mut LeanObject) -> u8 {
    if lean_obj_tag(v_x_9539_) == 0 {
        let mut v___x_9540_: u8 = 0;
        v___x_9540_ = 1;
        return v___x_9540_;
    } else {
        let mut v___x_9541_: u8 = 0;
        v___x_9541_ = 0;
        return v___x_9541_;
    }
}
pub unsafe fn l_Lean_Syntax_isMissing___boxed(mut v_x_9542_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_9543_: u8 = 0;
    let mut v_r_9544_: *mut LeanObject = core::ptr::null_mut();
    v_res_9543_ = l_Lean_Syntax_isMissing(v_x_9542_);
    lean_dec(v_x_9542_);
    v_r_9544_ = lean_box((v_res_9543_) as usize);
    return v_r_9544_;
}
pub unsafe fn l_Lean_Syntax_isNodeOf(
    mut v_stx_9545_: *mut LeanObject,
    mut v_k_9546_: *mut LeanObject,
    mut v_n_9547_: *mut LeanObject,
) -> u8 {
    let mut v___x_9548_: u8 = 0;
    lean_inc(v_stx_9545_);
    v___x_9548_ = l_Lean_Syntax_isOfKind(v_stx_9545_, v_k_9546_);
    if v___x_9548_ == 0 {
        lean_dec(v_stx_9545_);
        return v___x_9548_;
    } else {
        let mut v___x_9549_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_9550_: u8 = 0;
        v___x_9549_ = l_Lean_Syntax_getNumArgs(v_stx_9545_);
        lean_dec(v_stx_9545_);
        v___x_9550_ = lean_nat_dec_eq(v___x_9549_, v_n_9547_);
        lean_dec(v___x_9549_);
        return v___x_9550_;
    }
}
pub unsafe fn l_Lean_Syntax_isNodeOf___boxed(
    mut v_stx_9551_: *mut LeanObject,
    mut v_k_9552_: *mut LeanObject,
    mut v_n_9553_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9554_: u8 = 0;
    let mut v_r_9555_: *mut LeanObject = core::ptr::null_mut();
    v_res_9554_ = l_Lean_Syntax_isNodeOf(v_stx_9551_, v_k_9552_, v_n_9553_);
    lean_dec(v_n_9553_);
    lean_dec(v_k_9552_);
    v_r_9555_ = lean_box((v_res_9554_) as usize);
    return v_r_9555_;
}
pub unsafe fn l_Lean_Syntax_isIdent(mut v_x_9556_: *mut LeanObject) -> u8 {
    if lean_obj_tag(v_x_9556_) == 3 {
        let mut v___x_9557_: u8 = 0;
        v___x_9557_ = 1;
        return v___x_9557_;
    } else {
        let mut v___x_9558_: u8 = 0;
        v___x_9558_ = 0;
        return v___x_9558_;
    }
}
pub unsafe fn l_Lean_Syntax_isIdent___boxed(mut v_x_9559_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_9560_: u8 = 0;
    let mut v_r_9561_: *mut LeanObject = core::ptr::null_mut();
    v_res_9560_ = l_Lean_Syntax_isIdent(v_x_9559_);
    lean_dec(v_x_9559_);
    v_r_9561_ = lean_box((v_res_9560_) as usize);
    return v_r_9561_;
}
pub unsafe fn l_Lean_Syntax_getId(mut v_x_9562_: *mut LeanObject) -> *mut LeanObject {
    if lean_obj_tag(v_x_9562_) == 3 {
        let mut v_val_9563_: *mut LeanObject = core::ptr::null_mut();
        v_val_9563_ = lean_ctor_get(v_x_9562_, 2);
        lean_inc(v_val_9563_);
        return v_val_9563_;
    } else {
        let mut v___x_9564_: *mut LeanObject = core::ptr::null_mut();
        v___x_9564_ = lean_box(0);
        return v___x_9564_;
    }
}
pub unsafe fn l_Lean_Syntax_getId___boxed(mut v_x_9565_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_9566_: *mut LeanObject = core::ptr::null_mut();
    v_res_9566_ = l_Lean_Syntax_getId(v_x_9565_);
    lean_dec(v_x_9565_);
    return v_res_9566_;
}
pub unsafe fn l_Lean_Syntax_getInfo_x3f(mut v_x_9567_: *mut LeanObject) -> *mut LeanObject {
    if lean_obj_tag(v_x_9567_) == 0 {
        let mut v___x_9568_: *mut LeanObject = core::ptr::null_mut();
        v___x_9568_ = lean_box(0);
        return v___x_9568_;
    } else {
        let mut v_info_9569_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_9570_: *mut LeanObject = core::ptr::null_mut();
        v_info_9569_ = lean_ctor_get(v_x_9567_, 0);
        lean_inc(v_info_9569_);
        v___x_9570_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_9570_, 0, v_info_9569_);
        return v___x_9570_;
    }
}
pub unsafe fn l_Lean_Syntax_getInfo_x3f___boxed(mut v_x_9571_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_9572_: *mut LeanObject = core::ptr::null_mut();
    v_res_9572_ = l_Lean_Syntax_getInfo_x3f(v_x_9571_);
    lean_dec(v_x_9571_);
    return v_res_9572_;
}
pub unsafe fn l___private_Init_Prelude_0__Lean_Syntax_getHeadInfo_x3f_loop(
    mut v_args_9573_: *mut LeanObject,
    mut v_i_9574_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9576_: u8 = 0;
    let mut v___x_9577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9582_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_9575_ = lean_array_get_size(v_args_9573_);
                v___x_9576_ = lean_nat_dec_lt(v_i_9574_, v___x_9575_);
                if v___x_9576_ == 0 {
                    lean_dec(v_i_9574_);
                    v___x_9577_ = lean_box(0);
                    return v___x_9577_;
                } else {
                    v___x_9578_ = lean_box(0);
                    v___x_9579_ = lean_array_get_borrowed(v___x_9578_, v_args_9573_, v_i_9574_);
                    v___x_9580_ = l_Lean_Syntax_getHeadInfo_x3f(v___x_9579_);
                    if lean_obj_tag(v___x_9580_) == 0 {
                        v___x_9581_ = lean_unsigned_to_nat(1);
                        v___x_9582_ = lean_nat_add(v_i_9574_, v___x_9581_);
                        lean_dec(v_i_9574_);
                        v_i_9574_ = v___x_9582_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_i_9574_);
                        return v___x_9580_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Syntax_getHeadInfo_x3f(mut v_x_9584_: *mut LeanObject) -> *mut LeanObject {
    match lean_obj_tag(v_x_9584_) {
        0 => {
            let mut v___x_9585_: *mut LeanObject = core::ptr::null_mut();
            v___x_9585_ = lean_box(0);
            return v___x_9585_;
        }
        1 => {
            let mut v_info_9586_: *mut LeanObject = core::ptr::null_mut();
            v_info_9586_ = lean_ctor_get(v_x_9584_, 0);
            if lean_obj_tag(v_info_9586_) == 2 {
                let mut v_args_9587_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_9588_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_9589_: *mut LeanObject = core::ptr::null_mut();
                v_args_9587_ = lean_ctor_get(v_x_9584_, 2);
                v___x_9588_ = lean_unsigned_to_nat(0);
                v___x_9589_ = l___private_Init_Prelude_0__Lean_Syntax_getHeadInfo_x3f_loop(
                    v_args_9587_,
                    v___x_9588_,
                );
                return v___x_9589_;
            } else {
                let mut v___x_9590_: *mut LeanObject = core::ptr::null_mut();
                lean_inc(v_info_9586_);
                v___x_9590_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_9590_, 0, v_info_9586_);
                return v___x_9590_;
            }
        }
        _ => {
            let mut v_info_9591_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_9592_: *mut LeanObject = core::ptr::null_mut();
            v_info_9591_ = lean_ctor_get(v_x_9584_, 0);
            lean_inc(v_info_9591_);
            v___x_9592_ = lean_alloc_ctor(1, 1, (0) as u32);
            lean_ctor_set(v___x_9592_, 0, v_info_9591_);
            return v___x_9592_;
        }
    }
}
pub unsafe fn l_Lean_Syntax_getHeadInfo_x3f___boxed(
    mut v_x_9593_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9594_: *mut LeanObject = core::ptr::null_mut();
    v_res_9594_ = l_Lean_Syntax_getHeadInfo_x3f(v_x_9593_);
    lean_dec(v_x_9593_);
    return v_res_9594_;
}
pub unsafe fn l___private_Init_Prelude_0__Lean_Syntax_getHeadInfo_x3f_loop___boxed(
    mut v_args_9595_: *mut LeanObject,
    mut v_i_9596_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9597_: *mut LeanObject = core::ptr::null_mut();
    v_res_9597_ =
        l___private_Init_Prelude_0__Lean_Syntax_getHeadInfo_x3f_loop(v_args_9595_, v_i_9596_);
    lean_dec_ref(v_args_9595_);
    return v_res_9597_;
}
pub unsafe fn l_Lean_Syntax_getHeadInfo(mut v_stx_9598_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_9599_: *mut LeanObject = core::ptr::null_mut();
    v___x_9599_ = l_Lean_Syntax_getHeadInfo_x3f(v_stx_9598_);
    if lean_obj_tag(v___x_9599_) == 0 {
        let mut v___x_9600_: *mut LeanObject = core::ptr::null_mut();
        v___x_9600_ = lean_box(2);
        return v___x_9600_;
    } else {
        let mut v_val_9601_: *mut LeanObject = core::ptr::null_mut();
        v_val_9601_ = lean_ctor_get(v___x_9599_, 0);
        lean_inc(v_val_9601_);
        lean_dec_ref_known(v___x_9599_, 1);
        return v_val_9601_;
    }
}
pub unsafe fn l_Lean_Syntax_getHeadInfo___boxed(
    mut v_stx_9602_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9603_: *mut LeanObject = core::ptr::null_mut();
    v_res_9603_ = l_Lean_Syntax_getHeadInfo(v_stx_9602_);
    lean_dec(v_stx_9602_);
    return v_res_9603_;
}
pub unsafe fn l_Lean_Syntax_getPos_x3f(
    mut v_stx_9604_: *mut LeanObject,
    mut v_canonicalOnly_9605_: u8,
) -> *mut LeanObject {
    let mut v___x_9606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9607_: *mut LeanObject = core::ptr::null_mut();
    v___x_9606_ = l_Lean_Syntax_getHeadInfo(v_stx_9604_);
    v___x_9607_ = l_Lean_SourceInfo_getPos_x3f(v___x_9606_, v_canonicalOnly_9605_);
    lean_dec(v___x_9606_);
    return v___x_9607_;
}
pub unsafe fn l_Lean_Syntax_getPos_x3f___boxed(
    mut v_stx_9608_: *mut LeanObject,
    mut v_canonicalOnly_9609_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_canonicalOnly_boxed_9610_: u8 = 0;
    let mut v_res_9611_: *mut LeanObject = core::ptr::null_mut();
    v_canonicalOnly_boxed_9610_ = (lean_unbox(v_canonicalOnly_9609_) as u8);
    v_res_9611_ = l_Lean_Syntax_getPos_x3f(v_stx_9608_, v_canonicalOnly_boxed_9610_);
    lean_dec(v_stx_9608_);
    return v_res_9611_;
}
pub unsafe fn l_Lean_Syntax_getTailPos_x3f(
    mut v_stx_9612_: *mut LeanObject,
    mut v_canonicalOnly_9613_: u8,
) -> *mut LeanObject {
    let mut v___x_9614_: *mut LeanObject = core::ptr::null_mut();
    let mut v_info_9615_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_9616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endPos_9620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9621_: *mut LeanObject = core::ptr::null_mut();
    let mut v_canonical_9622_: u8 = 0;
    let mut v_endPos_9623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9624_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endPos_9625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_info_9627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endPos_9628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9629_: *mut LeanObject = core::ptr::null_mut();
    let mut v_canonical_9630_: u8 = 0;
    let mut v_endPos_9631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endPos_9634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9636_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_stx_9612_) {
                0 => {
                    v___x_9614_ = lean_box(0);
                    return v___x_9614_;
                }
                1 => {
                    v_info_9615_ = lean_ctor_get(v_stx_9612_, 0);
                    v_args_9616_ = lean_ctor_get(v_stx_9612_, 2);
                    match lean_obj_tag(v_info_9615_) {
                        0 => {
                            v_endPos_9620_ = lean_ctor_get(v_info_9615_, 3);
                            lean_inc(v_endPos_9620_);
                            v___x_9621_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v___x_9621_, 0, v_endPos_9620_);
                            return v___x_9621_;
                        }
                        1 => {
                            v_canonical_9622_ = lean_ctor_get_uint8(
                                v_info_9615_,
                                (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                            );
                            if v_canonical_9622_ == 0 {
                                if v_canonicalOnly_9613_ == 0 {
                                    v_endPos_9623_ = lean_ctor_get(v_info_9615_, 1);
                                    lean_inc(v_endPos_9623_);
                                    v___x_9624_ = lean_alloc_ctor(1, 1, (0) as u32);
                                    lean_ctor_set(v___x_9624_, 0, v_endPos_9623_);
                                    return v___x_9624_;
                                } else {
                                    state = 1;
                                    continue;
                                }
                            } else {
                                v_endPos_9625_ = lean_ctor_get(v_info_9615_, 1);
                                lean_inc(v_endPos_9625_);
                                v___x_9626_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v___x_9626_, 0, v_endPos_9625_);
                                return v___x_9626_;
                            }
                        }
                        _ => {
                            state = 1;
                            continue;
                        }
                    }
                }
                _ => {
                    v_info_9627_ = lean_ctor_get(v_stx_9612_, 0);
                    match lean_obj_tag(v_info_9627_) {
                        0 => {
                            v_endPos_9628_ = lean_ctor_get(v_info_9627_, 3);
                            lean_inc(v_endPos_9628_);
                            v___x_9629_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v___x_9629_, 0, v_endPos_9628_);
                            return v___x_9629_;
                        }
                        1 => {
                            v_canonical_9630_ = lean_ctor_get_uint8(
                                v_info_9627_,
                                (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                            );
                            if v_canonical_9630_ == 0 {
                                if v_canonicalOnly_9613_ == 0 {
                                    v_endPos_9631_ = lean_ctor_get(v_info_9627_, 1);
                                    lean_inc(v_endPos_9631_);
                                    v___x_9632_ = lean_alloc_ctor(1, 1, (0) as u32);
                                    lean_ctor_set(v___x_9632_, 0, v_endPos_9631_);
                                    return v___x_9632_;
                                } else {
                                    v___x_9633_ = lean_box(0);
                                    return v___x_9633_;
                                }
                            } else {
                                v_endPos_9634_ = lean_ctor_get(v_info_9627_, 1);
                                lean_inc(v_endPos_9634_);
                                v___x_9635_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v___x_9635_, 0, v_endPos_9634_);
                                return v___x_9635_;
                            }
                        }
                        _ => {
                            v___x_9636_ = lean_box(0);
                            return v___x_9636_;
                        }
                    }
                }
            },
            1 => {
                v___x_9618_ = lean_unsigned_to_nat(0);
                v___x_9619_ = l___private_Init_Prelude_0__Lean_Syntax_getTailPos_x3f_loop(
                    v_canonicalOnly_9613_,
                    v_args_9616_,
                    v___x_9618_,
                );
                return v___x_9619_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Prelude_0__Lean_Syntax_getTailPos_x3f_loop(
    mut v_canonicalOnly_9637_: u8,
    mut v_args_9638_: *mut LeanObject,
    mut v_i_9639_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9641_: u8 = 0;
    let mut v___x_9642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9649_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_9640_ = lean_array_get_size(v_args_9638_);
                v___x_9641_ = lean_nat_dec_lt(v_i_9639_, v___x_9640_);
                if v___x_9641_ == 0 {
                    lean_dec(v_i_9639_);
                    v___x_9642_ = lean_box(0);
                    return v___x_9642_;
                } else {
                    v___x_9643_ = lean_box(0);
                    v___x_9644_ = lean_nat_sub(v___x_9640_, v_i_9639_);
                    v___x_9645_ = lean_unsigned_to_nat(1);
                    v___x_9646_ = lean_nat_sub(v___x_9644_, v___x_9645_);
                    lean_dec(v___x_9644_);
                    v___x_9647_ = lean_array_get_borrowed(v___x_9643_, v_args_9638_, v___x_9646_);
                    lean_dec(v___x_9646_);
                    v___x_9648_ = l_Lean_Syntax_getTailPos_x3f(v___x_9647_, v_canonicalOnly_9637_);
                    if lean_obj_tag(v___x_9648_) == 0 {
                        v___x_9649_ = lean_nat_add(v_i_9639_, v___x_9645_);
                        lean_dec(v_i_9639_);
                        v_i_9639_ = v___x_9649_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_i_9639_);
                        return v___x_9648_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Prelude_0__Lean_Syntax_getTailPos_x3f_loop___boxed(
    mut v_canonicalOnly_9651_: *mut LeanObject,
    mut v_args_9652_: *mut LeanObject,
    mut v_i_9653_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_canonicalOnly_boxed_9654_: u8 = 0;
    let mut v_res_9655_: *mut LeanObject = core::ptr::null_mut();
    v_canonicalOnly_boxed_9654_ = (lean_unbox(v_canonicalOnly_9651_) as u8);
    v_res_9655_ = l___private_Init_Prelude_0__Lean_Syntax_getTailPos_x3f_loop(
        v_canonicalOnly_boxed_9654_,
        v_args_9652_,
        v_i_9653_,
    );
    lean_dec_ref(v_args_9652_);
    return v_res_9655_;
}
pub unsafe fn l_Lean_Syntax_getTailPos_x3f___boxed(
    mut v_stx_9656_: *mut LeanObject,
    mut v_canonicalOnly_9657_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_canonicalOnly_boxed_9658_: u8 = 0;
    let mut v_res_9659_: *mut LeanObject = core::ptr::null_mut();
    v_canonicalOnly_boxed_9658_ = (lean_unbox(v_canonicalOnly_9657_) as u8);
    v_res_9659_ = l_Lean_Syntax_getTailPos_x3f(v_stx_9656_, v_canonicalOnly_boxed_9658_);
    lean_dec(v_stx_9656_);
    return v_res_9659_;
}
pub unsafe fn l_Lean_TSyntaxArray_rawImpl___redArg(
    mut v_a_9660_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc_ref(v_a_9660_);
    return v_a_9660_;
}
pub unsafe fn l_Lean_TSyntaxArray_rawImpl___redArg___boxed(
    mut v_a_9661_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9662_: *mut LeanObject = core::ptr::null_mut();
    v_res_9662_ = l_Lean_TSyntaxArray_rawImpl___redArg(v_a_9661_);
    lean_dec_ref(v_a_9661_);
    return v_res_9662_;
}
pub unsafe fn l_Lean_TSyntaxArray_rawImpl(
    mut v_ks_9663_: *mut LeanObject,
    mut v_a_9664_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc_ref(v_a_9664_);
    return v_a_9664_;
}
pub unsafe fn l_Lean_TSyntaxArray_rawImpl___boxed(
    mut v_ks_9665_: *mut LeanObject,
    mut v_a_9666_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9667_: *mut LeanObject = core::ptr::null_mut();
    v_res_9667_ = l_Lean_TSyntaxArray_rawImpl(v_ks_9665_, v_a_9666_);
    lean_dec_ref(v_a_9666_);
    lean_dec(v_ks_9665_);
    return v_res_9667_;
}
pub unsafe fn l_Lean_TSyntaxArray_mkImpl___redArg(
    mut v_a_9668_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc_ref(v_a_9668_);
    return v_a_9668_;
}
pub unsafe fn l_Lean_TSyntaxArray_mkImpl___redArg___boxed(
    mut v_a_9669_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9670_: *mut LeanObject = core::ptr::null_mut();
    v_res_9670_ = l_Lean_TSyntaxArray_mkImpl___redArg(v_a_9669_);
    lean_dec_ref(v_a_9669_);
    return v_res_9670_;
}
pub unsafe fn l_Lean_TSyntaxArray_mkImpl(
    mut v_ks_9671_: *mut LeanObject,
    mut v_a_9672_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc_ref(v_a_9672_);
    return v_a_9672_;
}
pub unsafe fn l_Lean_TSyntaxArray_mkImpl___boxed(
    mut v_ks_9673_: *mut LeanObject,
    mut v_a_9674_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9675_: *mut LeanObject = core::ptr::null_mut();
    v_res_9675_ = l_Lean_TSyntaxArray_mkImpl(v_ks_9673_, v_a_9674_);
    lean_dec_ref(v_a_9674_);
    lean_dec(v_ks_9673_);
    return v_res_9675_;
}
pub unsafe fn l_Lean_SourceInfo_fromRef(
    mut v_ref_9676_: *mut LeanObject,
    mut v_canonical_9677_: u8,
) -> *mut LeanObject {
    let mut v_ref_9679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9680_: u8 = 0;
    let mut v___x_9681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_9683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9685_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_9686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9688_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_9689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9690_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_9691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9692_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_canonical_9677_ == 0 {
                    v_ref_9679_ = v_ref_9676_;
                    state = 1;
                    continue;
                } else {
                    v___x_9688_ = l_Lean_Syntax_getPos_x3f(v_ref_9676_, v_canonical_9677_);
                    if lean_obj_tag(v___x_9688_) == 0 {
                        v_ref_9679_ = v_ref_9676_;
                        state = 1;
                        continue;
                    } else {
                        v_val_9689_ = lean_ctor_get(v___x_9688_, 0);
                        lean_inc(v_val_9689_);
                        lean_dec_ref_known(v___x_9688_, 1);
                        v___x_9690_ = l_Lean_Syntax_getTailPos_x3f(v_ref_9676_, v_canonical_9677_);
                        if lean_obj_tag(v___x_9690_) == 0 {
                            lean_dec(v_val_9689_);
                            v_ref_9679_ = v_ref_9676_;
                            state = 1;
                            continue;
                        } else {
                            v_val_9691_ = lean_ctor_get(v___x_9690_, 0);
                            lean_inc(v_val_9691_);
                            lean_dec_ref_known(v___x_9690_, 1);
                            v___x_9692_ = lean_alloc_ctor(1, 2, (1) as u32);
                            lean_ctor_set(v___x_9692_, 0, v_val_9689_);
                            lean_ctor_set(v___x_9692_, 1, v_val_9691_);
                            lean_ctor_set_uint8(
                                v___x_9692_,
                                (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                                v_canonical_9677_,
                            );
                            return v___x_9692_;
                        }
                    }
                }
            }
            1 => {
                v___x_9680_ = 0;
                v___x_9681_ = l_Lean_Syntax_getPos_x3f(v_ref_9679_, v___x_9680_);
                if lean_obj_tag(v___x_9681_) == 0 {
                    v___x_9682_ = lean_box(2);
                    return v___x_9682_;
                } else {
                    v_val_9683_ = lean_ctor_get(v___x_9681_, 0);
                    lean_inc(v_val_9683_);
                    lean_dec_ref_known(v___x_9681_, 1);
                    v___x_9684_ = l_Lean_Syntax_getTailPos_x3f(v_ref_9679_, v___x_9680_);
                    if lean_obj_tag(v___x_9684_) == 0 {
                        lean_dec(v_val_9683_);
                        v___x_9685_ = lean_box(2);
                        return v___x_9685_;
                    } else {
                        v_val_9686_ = lean_ctor_get(v___x_9684_, 0);
                        lean_inc(v_val_9686_);
                        lean_dec_ref_known(v___x_9684_, 1);
                        v___x_9687_ = lean_alloc_ctor(1, 2, (1) as u32);
                        lean_ctor_set(v___x_9687_, 0, v_val_9683_);
                        lean_ctor_set(v___x_9687_, 1, v_val_9686_);
                        lean_ctor_set_uint8(
                            v___x_9687_,
                            (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                            v___x_9680_,
                        );
                        return v___x_9687_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_SourceInfo_fromRef___boxed(
    mut v_ref_9693_: *mut LeanObject,
    mut v_canonical_9694_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_canonical_boxed_9695_: u8 = 0;
    let mut v_res_9696_: *mut LeanObject = core::ptr::null_mut();
    v_canonical_boxed_9695_ = (lean_unbox(v_canonical_9694_) as u8);
    v_res_9696_ = l_Lean_SourceInfo_fromRef(v_ref_9693_, v_canonical_boxed_9695_);
    lean_dec(v_ref_9693_);
    return v_res_9696_;
}
pub unsafe fn l_Lean_mkAtom(mut v_val_9697_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_9698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9699_: *mut LeanObject = core::ptr::null_mut();
    v___x_9698_ = lean_box(2);
    v___x_9699_ = lean_alloc_ctor(2, 2, (0) as u32);
    lean_ctor_set(v___x_9699_, 0, v___x_9698_);
    lean_ctor_set(v___x_9699_, 1, v_val_9697_);
    return v___x_9699_;
}
pub unsafe fn l_Lean_mkAtomFrom(
    mut v_src_9700_: *mut LeanObject,
    mut v_val_9701_: *mut LeanObject,
    mut v_canonical_9702_: u8,
) -> *mut LeanObject {
    let mut v___x_9703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9704_: *mut LeanObject = core::ptr::null_mut();
    v___x_9703_ = l_Lean_SourceInfo_fromRef(v_src_9700_, v_canonical_9702_);
    v___x_9704_ = lean_alloc_ctor(2, 2, (0) as u32);
    lean_ctor_set(v___x_9704_, 0, v___x_9703_);
    lean_ctor_set(v___x_9704_, 1, v_val_9701_);
    return v___x_9704_;
}
pub unsafe fn l_Lean_mkAtomFrom___boxed(
    mut v_src_9705_: *mut LeanObject,
    mut v_val_9706_: *mut LeanObject,
    mut v_canonical_9707_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_canonical_boxed_9708_: u8 = 0;
    let mut v_res_9709_: *mut LeanObject = core::ptr::null_mut();
    v_canonical_boxed_9708_ = (lean_unbox(v_canonical_9707_) as u8);
    v_res_9709_ = l_Lean_mkAtomFrom(v_src_9705_, v_val_9706_, v_canonical_boxed_9708_);
    lean_dec(v_src_9705_);
    return v_res_9709_;
}
pub unsafe fn l_Lean_ParserDescr_ctorIdx(mut v_x_9710_: *mut LeanObject) -> *mut LeanObject {
    match lean_obj_tag(v_x_9710_) {
        0 => {
            let mut v___x_9711_: *mut LeanObject = core::ptr::null_mut();
            v___x_9711_ = lean_unsigned_to_nat(0);
            return v___x_9711_;
        }
        1 => {
            let mut v___x_9712_: *mut LeanObject = core::ptr::null_mut();
            v___x_9712_ = lean_unsigned_to_nat(1);
            return v___x_9712_;
        }
        2 => {
            let mut v___x_9713_: *mut LeanObject = core::ptr::null_mut();
            v___x_9713_ = lean_unsigned_to_nat(2);
            return v___x_9713_;
        }
        3 => {
            let mut v___x_9714_: *mut LeanObject = core::ptr::null_mut();
            v___x_9714_ = lean_unsigned_to_nat(3);
            return v___x_9714_;
        }
        4 => {
            let mut v___x_9715_: *mut LeanObject = core::ptr::null_mut();
            v___x_9715_ = lean_unsigned_to_nat(4);
            return v___x_9715_;
        }
        5 => {
            let mut v___x_9716_: *mut LeanObject = core::ptr::null_mut();
            v___x_9716_ = lean_unsigned_to_nat(5);
            return v___x_9716_;
        }
        6 => {
            let mut v___x_9717_: *mut LeanObject = core::ptr::null_mut();
            v___x_9717_ = lean_unsigned_to_nat(6);
            return v___x_9717_;
        }
        7 => {
            let mut v___x_9718_: *mut LeanObject = core::ptr::null_mut();
            v___x_9718_ = lean_unsigned_to_nat(7);
            return v___x_9718_;
        }
        8 => {
            let mut v___x_9719_: *mut LeanObject = core::ptr::null_mut();
            v___x_9719_ = lean_unsigned_to_nat(8);
            return v___x_9719_;
        }
        9 => {
            let mut v___x_9720_: *mut LeanObject = core::ptr::null_mut();
            v___x_9720_ = lean_unsigned_to_nat(9);
            return v___x_9720_;
        }
        10 => {
            let mut v___x_9721_: *mut LeanObject = core::ptr::null_mut();
            v___x_9721_ = lean_unsigned_to_nat(10);
            return v___x_9721_;
        }
        11 => {
            let mut v___x_9722_: *mut LeanObject = core::ptr::null_mut();
            v___x_9722_ = lean_unsigned_to_nat(11);
            return v___x_9722_;
        }
        _ => {
            let mut v___x_9723_: *mut LeanObject = core::ptr::null_mut();
            v___x_9723_ = lean_unsigned_to_nat(12);
            return v___x_9723_;
        }
    }
}
pub unsafe fn l_Lean_ParserDescr_ctorIdx___boxed(
    mut v_x_9724_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9725_: *mut LeanObject = core::ptr::null_mut();
    v_res_9725_ = l_Lean_ParserDescr_ctorIdx(v_x_9724_);
    lean_dec_ref(v_x_9724_);
    return v_res_9725_;
}
pub unsafe fn l_Lean_ParserDescr_ctorElim___redArg(
    mut v_t_9726_: *mut LeanObject,
    mut v_k_9727_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_t_9726_) {
        1 => {
            let mut v_name_9728_: *mut LeanObject = core::ptr::null_mut();
            let mut v_p_9729_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_9730_: *mut LeanObject = core::ptr::null_mut();
            v_name_9728_ = lean_ctor_get(v_t_9726_, 0);
            lean_inc(v_name_9728_);
            v_p_9729_ = lean_ctor_get(v_t_9726_, 1);
            lean_inc_ref(v_p_9729_);
            lean_dec_ref_known(v_t_9726_, 2);
            v___x_9730_ = lean_apply_2(v_k_9727_, v_name_9728_, v_p_9729_);
            return v___x_9730_;
        }
        2 => {
            let mut v_name_9731_: *mut LeanObject = core::ptr::null_mut();
            let mut v_p_u2081_9732_: *mut LeanObject = core::ptr::null_mut();
            let mut v_p_u2082_9733_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_9734_: *mut LeanObject = core::ptr::null_mut();
            v_name_9731_ = lean_ctor_get(v_t_9726_, 0);
            lean_inc(v_name_9731_);
            v_p_u2081_9732_ = lean_ctor_get(v_t_9726_, 1);
            lean_inc_ref(v_p_u2081_9732_);
            v_p_u2082_9733_ = lean_ctor_get(v_t_9726_, 2);
            lean_inc_ref(v_p_u2082_9733_);
            lean_dec_ref_known(v_t_9726_, 3);
            v___x_9734_ = lean_apply_3(v_k_9727_, v_name_9731_, v_p_u2081_9732_, v_p_u2082_9733_);
            return v___x_9734_;
        }
        3 => {
            let mut v_kind_9735_: *mut LeanObject = core::ptr::null_mut();
            let mut v_prec_9736_: *mut LeanObject = core::ptr::null_mut();
            let mut v_p_9737_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_9738_: *mut LeanObject = core::ptr::null_mut();
            v_kind_9735_ = lean_ctor_get(v_t_9726_, 0);
            lean_inc(v_kind_9735_);
            v_prec_9736_ = lean_ctor_get(v_t_9726_, 1);
            lean_inc(v_prec_9736_);
            v_p_9737_ = lean_ctor_get(v_t_9726_, 2);
            lean_inc_ref(v_p_9737_);
            lean_dec_ref_known(v_t_9726_, 3);
            v___x_9738_ = lean_apply_3(v_k_9727_, v_kind_9735_, v_prec_9736_, v_p_9737_);
            return v___x_9738_;
        }
        4 => {
            let mut v_kind_9739_: *mut LeanObject = core::ptr::null_mut();
            let mut v_prec_9740_: *mut LeanObject = core::ptr::null_mut();
            let mut v_lhsPrec_9741_: *mut LeanObject = core::ptr::null_mut();
            let mut v_p_9742_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_9743_: *mut LeanObject = core::ptr::null_mut();
            v_kind_9739_ = lean_ctor_get(v_t_9726_, 0);
            lean_inc(v_kind_9739_);
            v_prec_9740_ = lean_ctor_get(v_t_9726_, 1);
            lean_inc(v_prec_9740_);
            v_lhsPrec_9741_ = lean_ctor_get(v_t_9726_, 2);
            lean_inc(v_lhsPrec_9741_);
            v_p_9742_ = lean_ctor_get(v_t_9726_, 3);
            lean_inc_ref(v_p_9742_);
            lean_dec_ref_known(v_t_9726_, 4);
            v___x_9743_ = lean_apply_4(
                v_k_9727_,
                v_kind_9739_,
                v_prec_9740_,
                v_lhsPrec_9741_,
                v_p_9742_,
            );
            return v___x_9743_;
        }
        5 => {
            let mut v_val_9744_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_9745_: *mut LeanObject = core::ptr::null_mut();
            v_val_9744_ = lean_ctor_get(v_t_9726_, 0);
            lean_inc_ref(v_val_9744_);
            lean_dec_ref_known(v_t_9726_, 1);
            v___x_9745_ = lean_apply_1(v_k_9727_, v_val_9744_);
            return v___x_9745_;
        }
        6 => {
            let mut v_val_9746_: *mut LeanObject = core::ptr::null_mut();
            let mut v_includeIdent_9747_: u8 = 0;
            let mut v___x_9748_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_9749_: *mut LeanObject = core::ptr::null_mut();
            v_val_9746_ = lean_ctor_get(v_t_9726_, 0);
            lean_inc_ref(v_val_9746_);
            v_includeIdent_9747_ = lean_ctor_get_uint8(
                v_t_9726_,
                (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
            );
            lean_dec_ref_known(v_t_9726_, 1);
            v___x_9748_ = lean_box((v_includeIdent_9747_) as usize);
            v___x_9749_ = lean_apply_2(v_k_9727_, v_val_9746_, v___x_9748_);
            return v___x_9749_;
        }
        7 => {
            let mut v_catName_9750_: *mut LeanObject = core::ptr::null_mut();
            let mut v_rbp_9751_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_9752_: *mut LeanObject = core::ptr::null_mut();
            v_catName_9750_ = lean_ctor_get(v_t_9726_, 0);
            lean_inc(v_catName_9750_);
            v_rbp_9751_ = lean_ctor_get(v_t_9726_, 1);
            lean_inc(v_rbp_9751_);
            lean_dec_ref_known(v_t_9726_, 2);
            v___x_9752_ = lean_apply_2(v_k_9727_, v_catName_9750_, v_rbp_9751_);
            return v___x_9752_;
        }
        9 => {
            let mut v_name_9753_: *mut LeanObject = core::ptr::null_mut();
            let mut v_kind_9754_: *mut LeanObject = core::ptr::null_mut();
            let mut v_p_9755_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_9756_: *mut LeanObject = core::ptr::null_mut();
            v_name_9753_ = lean_ctor_get(v_t_9726_, 0);
            lean_inc_ref(v_name_9753_);
            v_kind_9754_ = lean_ctor_get(v_t_9726_, 1);
            lean_inc(v_kind_9754_);
            v_p_9755_ = lean_ctor_get(v_t_9726_, 2);
            lean_inc_ref(v_p_9755_);
            lean_dec_ref_known(v_t_9726_, 3);
            v___x_9756_ = lean_apply_3(v_k_9727_, v_name_9753_, v_kind_9754_, v_p_9755_);
            return v___x_9756_;
        }
        10 => {
            let mut v_p_9757_: *mut LeanObject = core::ptr::null_mut();
            let mut v_sep_9758_: *mut LeanObject = core::ptr::null_mut();
            let mut v_psep_9759_: *mut LeanObject = core::ptr::null_mut();
            let mut v_allowTrailingSep_9760_: u8 = 0;
            let mut v___x_9761_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_9762_: *mut LeanObject = core::ptr::null_mut();
            v_p_9757_ = lean_ctor_get(v_t_9726_, 0);
            lean_inc_ref(v_p_9757_);
            v_sep_9758_ = lean_ctor_get(v_t_9726_, 1);
            lean_inc_ref(v_sep_9758_);
            v_psep_9759_ = lean_ctor_get(v_t_9726_, 2);
            lean_inc_ref(v_psep_9759_);
            v_allowTrailingSep_9760_ = lean_ctor_get_uint8(
                v_t_9726_,
                (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
            );
            lean_dec_ref_known(v_t_9726_, 3);
            v___x_9761_ = lean_box((v_allowTrailingSep_9760_) as usize);
            v___x_9762_ =
                lean_apply_4(v_k_9727_, v_p_9757_, v_sep_9758_, v_psep_9759_, v___x_9761_);
            return v___x_9762_;
        }
        11 => {
            let mut v_p_9763_: *mut LeanObject = core::ptr::null_mut();
            let mut v_sep_9764_: *mut LeanObject = core::ptr::null_mut();
            let mut v_psep_9765_: *mut LeanObject = core::ptr::null_mut();
            let mut v_allowTrailingSep_9766_: u8 = 0;
            let mut v___x_9767_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_9768_: *mut LeanObject = core::ptr::null_mut();
            v_p_9763_ = lean_ctor_get(v_t_9726_, 0);
            lean_inc_ref(v_p_9763_);
            v_sep_9764_ = lean_ctor_get(v_t_9726_, 1);
            lean_inc_ref(v_sep_9764_);
            v_psep_9765_ = lean_ctor_get(v_t_9726_, 2);
            lean_inc_ref(v_psep_9765_);
            v_allowTrailingSep_9766_ = lean_ctor_get_uint8(
                v_t_9726_,
                (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
            );
            lean_dec_ref_known(v_t_9726_, 3);
            v___x_9767_ = lean_box((v_allowTrailingSep_9766_) as usize);
            v___x_9768_ =
                lean_apply_4(v_k_9727_, v_p_9763_, v_sep_9764_, v_psep_9765_, v___x_9767_);
            return v___x_9768_;
        }
        12 => {
            let mut v_val_9769_: *mut LeanObject = core::ptr::null_mut();
            let mut v_asciiVal_9770_: *mut LeanObject = core::ptr::null_mut();
            let mut v_preserveForPP_9771_: u8 = 0;
            let mut v___x_9772_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_9773_: *mut LeanObject = core::ptr::null_mut();
            v_val_9769_ = lean_ctor_get(v_t_9726_, 0);
            lean_inc_ref(v_val_9769_);
            v_asciiVal_9770_ = lean_ctor_get(v_t_9726_, 1);
            lean_inc_ref(v_asciiVal_9770_);
            v_preserveForPP_9771_ = lean_ctor_get_uint8(
                v_t_9726_,
                (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
            );
            lean_dec_ref_known(v_t_9726_, 2);
            v___x_9772_ = lean_box((v_preserveForPP_9771_) as usize);
            v___x_9773_ = lean_apply_3(v_k_9727_, v_val_9769_, v_asciiVal_9770_, v___x_9772_);
            return v___x_9773_;
        }
        _ => {
            let mut v_name_9774_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_9775_: *mut LeanObject = core::ptr::null_mut();
            v_name_9774_ = lean_ctor_get(v_t_9726_, 0);
            lean_inc(v_name_9774_);
            lean_dec_ref(v_t_9726_);
            v___x_9775_ = lean_apply_1(v_k_9727_, v_name_9774_);
            return v___x_9775_;
        }
    }
}
pub unsafe fn l_Lean_ParserDescr_ctorElim(
    mut v_motive_9776_: *mut LeanObject,
    mut v_ctorIdx_9777_: *mut LeanObject,
    mut v_t_9778_: *mut LeanObject,
    mut v_h_9779_: *mut LeanObject,
    mut v_k_9780_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9781_: *mut LeanObject = core::ptr::null_mut();
    v___x_9781_ = l_Lean_ParserDescr_ctorElim___redArg(v_t_9778_, v_k_9780_);
    return v___x_9781_;
}
pub unsafe fn l_Lean_ParserDescr_ctorElim___boxed(
    mut v_motive_9782_: *mut LeanObject,
    mut v_ctorIdx_9783_: *mut LeanObject,
    mut v_t_9784_: *mut LeanObject,
    mut v_h_9785_: *mut LeanObject,
    mut v_k_9786_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9787_: *mut LeanObject = core::ptr::null_mut();
    v_res_9787_ = l_Lean_ParserDescr_ctorElim(
        v_motive_9782_,
        v_ctorIdx_9783_,
        v_t_9784_,
        v_h_9785_,
        v_k_9786_,
    );
    lean_dec(v_ctorIdx_9783_);
    return v_res_9787_;
}
pub unsafe fn l_Lean_ParserDescr_const_elim___redArg(
    mut v_t_9788_: *mut LeanObject,
    mut v_const_9789_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9790_: *mut LeanObject = core::ptr::null_mut();
    v___x_9790_ = l_Lean_ParserDescr_ctorElim___redArg(v_t_9788_, v_const_9789_);
    return v___x_9790_;
}
pub unsafe fn l_Lean_ParserDescr_const_elim(
    mut v_motive_9791_: *mut LeanObject,
    mut v_t_9792_: *mut LeanObject,
    mut v_h_9793_: *mut LeanObject,
    mut v_const_9794_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9795_: *mut LeanObject = core::ptr::null_mut();
    v___x_9795_ = l_Lean_ParserDescr_ctorElim___redArg(v_t_9792_, v_const_9794_);
    return v___x_9795_;
}
pub unsafe fn l_Lean_ParserDescr_unary_elim___redArg(
    mut v_t_9796_: *mut LeanObject,
    mut v_unary_9797_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9798_: *mut LeanObject = core::ptr::null_mut();
    v___x_9798_ = l_Lean_ParserDescr_ctorElim___redArg(v_t_9796_, v_unary_9797_);
    return v___x_9798_;
}
pub unsafe fn l_Lean_ParserDescr_unary_elim(
    mut v_motive_9799_: *mut LeanObject,
    mut v_t_9800_: *mut LeanObject,
    mut v_h_9801_: *mut LeanObject,
    mut v_unary_9802_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9803_: *mut LeanObject = core::ptr::null_mut();
    v___x_9803_ = l_Lean_ParserDescr_ctorElim___redArg(v_t_9800_, v_unary_9802_);
    return v___x_9803_;
}
pub unsafe fn l_Lean_ParserDescr_binary_elim___redArg(
    mut v_t_9804_: *mut LeanObject,
    mut v_binary_9805_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9806_: *mut LeanObject = core::ptr::null_mut();
    v___x_9806_ = l_Lean_ParserDescr_ctorElim___redArg(v_t_9804_, v_binary_9805_);
    return v___x_9806_;
}
pub unsafe fn l_Lean_ParserDescr_binary_elim(
    mut v_motive_9807_: *mut LeanObject,
    mut v_t_9808_: *mut LeanObject,
    mut v_h_9809_: *mut LeanObject,
    mut v_binary_9810_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9811_: *mut LeanObject = core::ptr::null_mut();
    v___x_9811_ = l_Lean_ParserDescr_ctorElim___redArg(v_t_9808_, v_binary_9810_);
    return v___x_9811_;
}
pub unsafe fn l_Lean_ParserDescr_node_elim___redArg(
    mut v_t_9812_: *mut LeanObject,
    mut v_node_9813_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9814_: *mut LeanObject = core::ptr::null_mut();
    v___x_9814_ = l_Lean_ParserDescr_ctorElim___redArg(v_t_9812_, v_node_9813_);
    return v___x_9814_;
}
pub unsafe fn l_Lean_ParserDescr_node_elim(
    mut v_motive_9815_: *mut LeanObject,
    mut v_t_9816_: *mut LeanObject,
    mut v_h_9817_: *mut LeanObject,
    mut v_node_9818_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9819_: *mut LeanObject = core::ptr::null_mut();
    v___x_9819_ = l_Lean_ParserDescr_ctorElim___redArg(v_t_9816_, v_node_9818_);
    return v___x_9819_;
}
pub unsafe fn l_Lean_ParserDescr_trailingNode_elim___redArg(
    mut v_t_9820_: *mut LeanObject,
    mut v_trailingNode_9821_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9822_: *mut LeanObject = core::ptr::null_mut();
    v___x_9822_ = l_Lean_ParserDescr_ctorElim___redArg(v_t_9820_, v_trailingNode_9821_);
    return v___x_9822_;
}
pub unsafe fn l_Lean_ParserDescr_trailingNode_elim(
    mut v_motive_9823_: *mut LeanObject,
    mut v_t_9824_: *mut LeanObject,
    mut v_h_9825_: *mut LeanObject,
    mut v_trailingNode_9826_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9827_: *mut LeanObject = core::ptr::null_mut();
    v___x_9827_ = l_Lean_ParserDescr_ctorElim___redArg(v_t_9824_, v_trailingNode_9826_);
    return v___x_9827_;
}
pub unsafe fn l_Lean_ParserDescr_symbol_elim___redArg(
    mut v_t_9828_: *mut LeanObject,
    mut v_symbol_9829_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9830_: *mut LeanObject = core::ptr::null_mut();
    v___x_9830_ = l_Lean_ParserDescr_ctorElim___redArg(v_t_9828_, v_symbol_9829_);
    return v___x_9830_;
}
pub unsafe fn l_Lean_ParserDescr_symbol_elim(
    mut v_motive_9831_: *mut LeanObject,
    mut v_t_9832_: *mut LeanObject,
    mut v_h_9833_: *mut LeanObject,
    mut v_symbol_9834_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9835_: *mut LeanObject = core::ptr::null_mut();
    v___x_9835_ = l_Lean_ParserDescr_ctorElim___redArg(v_t_9832_, v_symbol_9834_);
    return v___x_9835_;
}
pub unsafe fn l_Lean_ParserDescr_nonReservedSymbol_elim___redArg(
    mut v_t_9836_: *mut LeanObject,
    mut v_nonReservedSymbol_9837_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9838_: *mut LeanObject = core::ptr::null_mut();
    v___x_9838_ = l_Lean_ParserDescr_ctorElim___redArg(v_t_9836_, v_nonReservedSymbol_9837_);
    return v___x_9838_;
}
pub unsafe fn l_Lean_ParserDescr_nonReservedSymbol_elim(
    mut v_motive_9839_: *mut LeanObject,
    mut v_t_9840_: *mut LeanObject,
    mut v_h_9841_: *mut LeanObject,
    mut v_nonReservedSymbol_9842_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9843_: *mut LeanObject = core::ptr::null_mut();
    v___x_9843_ = l_Lean_ParserDescr_ctorElim___redArg(v_t_9840_, v_nonReservedSymbol_9842_);
    return v___x_9843_;
}
pub unsafe fn l_Lean_ParserDescr_cat_elim___redArg(
    mut v_t_9844_: *mut LeanObject,
    mut v_cat_9845_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9846_: *mut LeanObject = core::ptr::null_mut();
    v___x_9846_ = l_Lean_ParserDescr_ctorElim___redArg(v_t_9844_, v_cat_9845_);
    return v___x_9846_;
}
pub unsafe fn l_Lean_ParserDescr_cat_elim(
    mut v_motive_9847_: *mut LeanObject,
    mut v_t_9848_: *mut LeanObject,
    mut v_h_9849_: *mut LeanObject,
    mut v_cat_9850_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9851_: *mut LeanObject = core::ptr::null_mut();
    v___x_9851_ = l_Lean_ParserDescr_ctorElim___redArg(v_t_9848_, v_cat_9850_);
    return v___x_9851_;
}
pub unsafe fn l_Lean_ParserDescr_parser_elim___redArg(
    mut v_t_9852_: *mut LeanObject,
    mut v_parser_9853_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9854_: *mut LeanObject = core::ptr::null_mut();
    v___x_9854_ = l_Lean_ParserDescr_ctorElim___redArg(v_t_9852_, v_parser_9853_);
    return v___x_9854_;
}
pub unsafe fn l_Lean_ParserDescr_parser_elim(
    mut v_motive_9855_: *mut LeanObject,
    mut v_t_9856_: *mut LeanObject,
    mut v_h_9857_: *mut LeanObject,
    mut v_parser_9858_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9859_: *mut LeanObject = core::ptr::null_mut();
    v___x_9859_ = l_Lean_ParserDescr_ctorElim___redArg(v_t_9856_, v_parser_9858_);
    return v___x_9859_;
}
pub unsafe fn l_Lean_ParserDescr_nodeWithAntiquot_elim___redArg(
    mut v_t_9860_: *mut LeanObject,
    mut v_nodeWithAntiquot_9861_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9862_: *mut LeanObject = core::ptr::null_mut();
    v___x_9862_ = l_Lean_ParserDescr_ctorElim___redArg(v_t_9860_, v_nodeWithAntiquot_9861_);
    return v___x_9862_;
}
pub unsafe fn l_Lean_ParserDescr_nodeWithAntiquot_elim(
    mut v_motive_9863_: *mut LeanObject,
    mut v_t_9864_: *mut LeanObject,
    mut v_h_9865_: *mut LeanObject,
    mut v_nodeWithAntiquot_9866_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9867_: *mut LeanObject = core::ptr::null_mut();
    v___x_9867_ = l_Lean_ParserDescr_ctorElim___redArg(v_t_9864_, v_nodeWithAntiquot_9866_);
    return v___x_9867_;
}
pub unsafe fn l_Lean_ParserDescr_sepBy_elim___redArg(
    mut v_t_9868_: *mut LeanObject,
    mut v_sepBy_9869_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9870_: *mut LeanObject = core::ptr::null_mut();
    v___x_9870_ = l_Lean_ParserDescr_ctorElim___redArg(v_t_9868_, v_sepBy_9869_);
    return v___x_9870_;
}
pub unsafe fn l_Lean_ParserDescr_sepBy_elim(
    mut v_motive_9871_: *mut LeanObject,
    mut v_t_9872_: *mut LeanObject,
    mut v_h_9873_: *mut LeanObject,
    mut v_sepBy_9874_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9875_: *mut LeanObject = core::ptr::null_mut();
    v___x_9875_ = l_Lean_ParserDescr_ctorElim___redArg(v_t_9872_, v_sepBy_9874_);
    return v___x_9875_;
}
pub unsafe fn l_Lean_ParserDescr_sepBy1_elim___redArg(
    mut v_t_9876_: *mut LeanObject,
    mut v_sepBy1_9877_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9878_: *mut LeanObject = core::ptr::null_mut();
    v___x_9878_ = l_Lean_ParserDescr_ctorElim___redArg(v_t_9876_, v_sepBy1_9877_);
    return v___x_9878_;
}
pub unsafe fn l_Lean_ParserDescr_sepBy1_elim(
    mut v_motive_9879_: *mut LeanObject,
    mut v_t_9880_: *mut LeanObject,
    mut v_h_9881_: *mut LeanObject,
    mut v_sepBy1_9882_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9883_: *mut LeanObject = core::ptr::null_mut();
    v___x_9883_ = l_Lean_ParserDescr_ctorElim___redArg(v_t_9880_, v_sepBy1_9882_);
    return v___x_9883_;
}
pub unsafe fn l_Lean_ParserDescr_unicodeSymbol_elim___redArg(
    mut v_t_9884_: *mut LeanObject,
    mut v_unicodeSymbol_9885_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9886_: *mut LeanObject = core::ptr::null_mut();
    v___x_9886_ = l_Lean_ParserDescr_ctorElim___redArg(v_t_9884_, v_unicodeSymbol_9885_);
    return v___x_9886_;
}
pub unsafe fn l_Lean_ParserDescr_unicodeSymbol_elim(
    mut v_motive_9887_: *mut LeanObject,
    mut v_t_9888_: *mut LeanObject,
    mut v_h_9889_: *mut LeanObject,
    mut v_unicodeSymbol_9890_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9891_: *mut LeanObject = core::ptr::null_mut();
    v___x_9891_ = l_Lean_ParserDescr_ctorElim___redArg(v_t_9888_, v_unicodeSymbol_9890_);
    return v___x_9891_;
}
pub unsafe fn _init_l_Lean_reservedMacroScope() -> *mut LeanObject {
    let mut v___x_9895_: *mut LeanObject = core::ptr::null_mut();
    v___x_9895_ = lean_unsigned_to_nat(0);
    return v___x_9895_;
}
pub unsafe fn _init_l_Lean_firstFrontendMacroScope() -> *mut LeanObject {
    let mut v___x_9896_: *mut LeanObject = core::ptr::null_mut();
    v___x_9896_ = lean_unsigned_to_nat(1);
    return v___x_9896_;
}
pub unsafe fn l_Lean_instMonadRefOfMonadLiftOfMonadFunctor___redArg___lam__0(
    mut v_withRef_9897_: *mut LeanObject,
    mut v_ref_9898_: *mut LeanObject,
    mut v_00_u03b2_9899_: *mut LeanObject,
    mut v___y_9900_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9901_: *mut LeanObject = core::ptr::null_mut();
    v___x_9901_ = lean_apply_3(v_withRef_9897_, lean_box(0), v_ref_9898_, v___y_9900_);
    return v___x_9901_;
}
pub unsafe fn l_Lean_instMonadRefOfMonadLiftOfMonadFunctor___redArg___lam__1(
    mut v_withRef_9902_: *mut LeanObject,
    mut v_inst_9903_: *mut LeanObject,
    mut v_00_u03b1_9904_: *mut LeanObject,
    mut v_ref_9905_: *mut LeanObject,
    mut v_x_9906_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_9907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9908_: *mut LeanObject = core::ptr::null_mut();
    v___f_9907_ = lean_alloc_closure(
        l_Lean_instMonadRefOfMonadLiftOfMonadFunctor___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_9907_, 0, v_withRef_9902_);
    lean_closure_set(v___f_9907_, 1, v_ref_9905_);
    v___x_9908_ = lean_apply_3(v_inst_9903_, lean_box(0), v___f_9907_, v_x_9906_);
    return v___x_9908_;
}
pub unsafe fn l_Lean_instMonadRefOfMonadLiftOfMonadFunctor___redArg(
    mut v_inst_9909_: *mut LeanObject,
    mut v_inst_9910_: *mut LeanObject,
    mut v_inst_9911_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_getRef_9912_: *mut LeanObject = core::ptr::null_mut();
    let mut v_withRef_9913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9915_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9916_: u8 = 0;
    let mut v___f_9917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9920_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9922_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_getRef_9912_ = lean_ctor_get(v_inst_9911_, 0);
                v_withRef_9913_ = lean_ctor_get(v_inst_9911_, 1);
                v_isSharedCheck_9922_ = (!lean_is_exclusive(v_inst_9911_)) as u8;
                if v_isSharedCheck_9922_ == 0 {
                    v___x_9915_ = v_inst_9911_;
                    v_isShared_9916_ = v_isSharedCheck_9922_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_withRef_9913_);
                    lean_inc(v_getRef_9912_);
                    lean_dec(v_inst_9911_);
                    v___x_9915_ = lean_box(0);
                    v_isShared_9916_ = v_isSharedCheck_9922_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_9917_ = lean_alloc_closure(
                    l_Lean_instMonadRefOfMonadLiftOfMonadFunctor___redArg___lam__1
                        as *mut core::ffi::c_void,
                    5,
                    2,
                );
                lean_closure_set(v___f_9917_, 0, v_withRef_9913_);
                lean_closure_set(v___f_9917_, 1, v_inst_9910_);
                v___x_9918_ = lean_apply_2(v_inst_9909_, lean_box(0), v_getRef_9912_);
                if v_isShared_9916_ == 0 {
                    lean_ctor_set(v___x_9915_, 1, v___f_9917_);
                    lean_ctor_set(v___x_9915_, 0, v___x_9918_);
                    v___x_9920_ = v___x_9915_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_9921_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9921_, 0, v___x_9918_);
                    lean_ctor_set(v_reuseFailAlloc_9921_, 1, v___f_9917_);
                    v___x_9920_ = v_reuseFailAlloc_9921_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_9920_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instMonadRefOfMonadLiftOfMonadFunctor(
    mut v_m_9923_: *mut LeanObject,
    mut v_n_9924_: *mut LeanObject,
    mut v_inst_9925_: *mut LeanObject,
    mut v_inst_9926_: *mut LeanObject,
    mut v_inst_9927_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9928_: *mut LeanObject = core::ptr::null_mut();
    v___x_9928_ = l_Lean_instMonadRefOfMonadLiftOfMonadFunctor___redArg(
        v_inst_9925_,
        v_inst_9926_,
        v_inst_9927_,
    );
    return v___x_9928_;
}
pub unsafe fn l_Lean_replaceRef(
    mut v_ref_9929_: *mut LeanObject,
    mut v_oldRef_9930_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9931_: u8 = 0;
    let mut v___x_9932_: *mut LeanObject = core::ptr::null_mut();
    v___x_9931_ = 0;
    v___x_9932_ = l_Lean_Syntax_getPos_x3f(v_ref_9929_, v___x_9931_);
    if lean_obj_tag(v___x_9932_) == 0 {
        lean_inc(v_oldRef_9930_);
        return v_oldRef_9930_;
    } else {
        lean_dec_ref_known(v___x_9932_, 1);
        lean_inc(v_ref_9929_);
        return v_ref_9929_;
    }
}
pub unsafe fn l_Lean_replaceRef___boxed(
    mut v_ref_9933_: *mut LeanObject,
    mut v_oldRef_9934_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9935_: *mut LeanObject = core::ptr::null_mut();
    v_res_9935_ = l_Lean_replaceRef(v_ref_9933_, v_oldRef_9934_);
    lean_dec(v_oldRef_9934_);
    lean_dec(v_ref_9933_);
    return v_res_9935_;
}
pub unsafe fn l_Lean_withRef___redArg___lam__0(
    mut v_ref_9936_: *mut LeanObject,
    mut v_withRef_9937_: *mut LeanObject,
    mut v_x_9938_: *mut LeanObject,
    mut v_oldRef_9939_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_9940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9941_: *mut LeanObject = core::ptr::null_mut();
    v_ref_9940_ = l_Lean_replaceRef(v_ref_9936_, v_oldRef_9939_);
    v___x_9941_ = lean_apply_3(v_withRef_9937_, lean_box(0), v_ref_9940_, v_x_9938_);
    return v___x_9941_;
}
pub unsafe fn l_Lean_withRef___redArg___lam__0___boxed(
    mut v_ref_9942_: *mut LeanObject,
    mut v_withRef_9943_: *mut LeanObject,
    mut v_x_9944_: *mut LeanObject,
    mut v_oldRef_9945_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9946_: *mut LeanObject = core::ptr::null_mut();
    v_res_9946_ =
        l_Lean_withRef___redArg___lam__0(v_ref_9942_, v_withRef_9943_, v_x_9944_, v_oldRef_9945_);
    lean_dec(v_oldRef_9945_);
    lean_dec(v_ref_9942_);
    return v_res_9946_;
}
pub unsafe fn l_Lean_withRef___redArg(
    mut v_inst_9947_: *mut LeanObject,
    mut v_inst_9948_: *mut LeanObject,
    mut v_ref_9949_: *mut LeanObject,
    mut v_x_9950_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toBind_9951_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getRef_9952_: *mut LeanObject = core::ptr::null_mut();
    let mut v_withRef_9953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_9954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9955_: *mut LeanObject = core::ptr::null_mut();
    v_toBind_9951_ = lean_ctor_get(v_inst_9947_, 1);
    lean_inc(v_toBind_9951_);
    lean_dec_ref(v_inst_9947_);
    v_getRef_9952_ = lean_ctor_get(v_inst_9948_, 0);
    lean_inc(v_getRef_9952_);
    v_withRef_9953_ = lean_ctor_get(v_inst_9948_, 1);
    lean_inc(v_withRef_9953_);
    lean_dec_ref(v_inst_9948_);
    v___f_9954_ = lean_alloc_closure(
        l_Lean_withRef___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_9954_, 0, v_ref_9949_);
    lean_closure_set(v___f_9954_, 1, v_withRef_9953_);
    lean_closure_set(v___f_9954_, 2, v_x_9950_);
    v___x_9955_ = lean_apply_4(
        v_toBind_9951_,
        lean_box(0),
        lean_box(0),
        v_getRef_9952_,
        v___f_9954_,
    );
    return v___x_9955_;
}
pub unsafe fn l_Lean_withRef(
    mut v_m_9956_: *mut LeanObject,
    mut v_inst_9957_: *mut LeanObject,
    mut v_inst_9958_: *mut LeanObject,
    mut v_00_u03b1_9959_: *mut LeanObject,
    mut v_ref_9960_: *mut LeanObject,
    mut v_x_9961_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toBind_9962_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getRef_9963_: *mut LeanObject = core::ptr::null_mut();
    let mut v_withRef_9964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_9965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9966_: *mut LeanObject = core::ptr::null_mut();
    v_toBind_9962_ = lean_ctor_get(v_inst_9957_, 1);
    lean_inc(v_toBind_9962_);
    lean_dec_ref(v_inst_9957_);
    v_getRef_9963_ = lean_ctor_get(v_inst_9958_, 0);
    lean_inc(v_getRef_9963_);
    v_withRef_9964_ = lean_ctor_get(v_inst_9958_, 1);
    lean_inc(v_withRef_9964_);
    lean_dec_ref(v_inst_9958_);
    v___f_9965_ = lean_alloc_closure(
        l_Lean_withRef___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_9965_, 0, v_ref_9960_);
    lean_closure_set(v___f_9965_, 1, v_withRef_9964_);
    lean_closure_set(v___f_9965_, 2, v_x_9961_);
    v___x_9966_ = lean_apply_4(
        v_toBind_9962_,
        lean_box(0),
        lean_box(0),
        v_getRef_9963_,
        v___f_9965_,
    );
    return v___x_9966_;
}
pub unsafe fn l_Lean_withRef_x3f___redArg___lam__0(
    mut v_val_9967_: *mut LeanObject,
    mut v_withRef_9968_: *mut LeanObject,
    mut v_x_9969_: *mut LeanObject,
    mut v_oldRef_9970_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_9971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9972_: *mut LeanObject = core::ptr::null_mut();
    v_ref_9971_ = l_Lean_replaceRef(v_val_9967_, v_oldRef_9970_);
    v___x_9972_ = lean_apply_3(v_withRef_9968_, lean_box(0), v_ref_9971_, v_x_9969_);
    return v___x_9972_;
}
pub unsafe fn l_Lean_withRef_x3f___redArg___lam__0___boxed(
    mut v_val_9973_: *mut LeanObject,
    mut v_withRef_9974_: *mut LeanObject,
    mut v_x_9975_: *mut LeanObject,
    mut v_oldRef_9976_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9977_: *mut LeanObject = core::ptr::null_mut();
    v_res_9977_ = l_Lean_withRef_x3f___redArg___lam__0(
        v_val_9973_,
        v_withRef_9974_,
        v_x_9975_,
        v_oldRef_9976_,
    );
    lean_dec(v_oldRef_9976_);
    lean_dec(v_val_9973_);
    return v_res_9977_;
}
pub unsafe fn l_Lean_withRef_x3f___redArg(
    mut v_inst_9978_: *mut LeanObject,
    mut v_inst_9979_: *mut LeanObject,
    mut v_ref_x3f_9980_: *mut LeanObject,
    mut v_x_9981_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_ref_x3f_9980_) == 0 {
        lean_dec_ref(v_inst_9979_);
        lean_dec_ref(v_inst_9978_);
        return v_x_9981_;
    } else {
        let mut v_val_9982_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toBind_9983_: *mut LeanObject = core::ptr::null_mut();
        let mut v_getRef_9984_: *mut LeanObject = core::ptr::null_mut();
        let mut v_withRef_9985_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_9986_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_9987_: *mut LeanObject = core::ptr::null_mut();
        v_val_9982_ = lean_ctor_get(v_ref_x3f_9980_, 0);
        lean_inc(v_val_9982_);
        lean_dec_ref_known(v_ref_x3f_9980_, 1);
        v_toBind_9983_ = lean_ctor_get(v_inst_9978_, 1);
        lean_inc(v_toBind_9983_);
        lean_dec_ref(v_inst_9978_);
        v_getRef_9984_ = lean_ctor_get(v_inst_9979_, 0);
        lean_inc(v_getRef_9984_);
        v_withRef_9985_ = lean_ctor_get(v_inst_9979_, 1);
        lean_inc(v_withRef_9985_);
        lean_dec_ref(v_inst_9979_);
        v___f_9986_ = lean_alloc_closure(
            l_Lean_withRef_x3f___redArg___lam__0___boxed as *mut core::ffi::c_void,
            4,
            3,
        );
        lean_closure_set(v___f_9986_, 0, v_val_9982_);
        lean_closure_set(v___f_9986_, 1, v_withRef_9985_);
        lean_closure_set(v___f_9986_, 2, v_x_9981_);
        v___x_9987_ = lean_apply_4(
            v_toBind_9983_,
            lean_box(0),
            lean_box(0),
            v_getRef_9984_,
            v___f_9986_,
        );
        return v___x_9987_;
    }
}
pub unsafe fn l_Lean_withRef_x3f(
    mut v_m_9988_: *mut LeanObject,
    mut v_inst_9989_: *mut LeanObject,
    mut v_inst_9990_: *mut LeanObject,
    mut v_00_u03b1_9991_: *mut LeanObject,
    mut v_ref_x3f_9992_: *mut LeanObject,
    mut v_x_9993_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_ref_x3f_9992_) == 0 {
        lean_dec_ref(v_inst_9990_);
        lean_dec_ref(v_inst_9989_);
        return v_x_9993_;
    } else {
        let mut v_val_9994_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toBind_9995_: *mut LeanObject = core::ptr::null_mut();
        let mut v_getRef_9996_: *mut LeanObject = core::ptr::null_mut();
        let mut v_withRef_9997_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_9998_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_9999_: *mut LeanObject = core::ptr::null_mut();
        v_val_9994_ = lean_ctor_get(v_ref_x3f_9992_, 0);
        lean_inc(v_val_9994_);
        lean_dec_ref_known(v_ref_x3f_9992_, 1);
        v_toBind_9995_ = lean_ctor_get(v_inst_9989_, 1);
        lean_inc(v_toBind_9995_);
        lean_dec_ref(v_inst_9989_);
        v_getRef_9996_ = lean_ctor_get(v_inst_9990_, 0);
        lean_inc(v_getRef_9996_);
        v_withRef_9997_ = lean_ctor_get(v_inst_9990_, 1);
        lean_inc(v_withRef_9997_);
        lean_dec_ref(v_inst_9990_);
        v___f_9998_ = lean_alloc_closure(
            l_Lean_withRef_x3f___redArg___lam__0___boxed as *mut core::ffi::c_void,
            4,
            3,
        );
        lean_closure_set(v___f_9998_, 0, v_val_9994_);
        lean_closure_set(v___f_9998_, 1, v_withRef_9997_);
        lean_closure_set(v___f_9998_, 2, v_x_9993_);
        v___x_9999_ = lean_apply_4(
            v_toBind_9995_,
            lean_box(0),
            lean_box(0),
            v_getRef_9996_,
            v___f_9998_,
        );
        return v___x_9999_;
    }
}
pub unsafe fn l_Lean_MonadQuotation_getMainModule___redArg(
    mut v_self_10000_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_getContext_10001_: *mut LeanObject = core::ptr::null_mut();
    v_getContext_10001_ = lean_ctor_get(v_self_10000_, 2);
    lean_inc(v_getContext_10001_);
    return v_getContext_10001_;
}
pub unsafe fn l_Lean_MonadQuotation_getMainModule___redArg___boxed(
    mut v_self_10002_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10003_: *mut LeanObject = core::ptr::null_mut();
    v_res_10003_ = l_Lean_MonadQuotation_getMainModule___redArg(v_self_10002_);
    lean_dec_ref(v_self_10002_);
    return v_res_10003_;
}
pub unsafe fn l_Lean_MonadQuotation_getMainModule(
    mut v_m_10004_: *mut LeanObject,
    mut v_self_10005_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_getContext_10006_: *mut LeanObject = core::ptr::null_mut();
    v_getContext_10006_ = lean_ctor_get(v_self_10005_, 2);
    lean_inc(v_getContext_10006_);
    return v_getContext_10006_;
}
pub unsafe fn l_Lean_MonadQuotation_getMainModule___boxed(
    mut v_m_10007_: *mut LeanObject,
    mut v_self_10008_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10009_: *mut LeanObject = core::ptr::null_mut();
    v_res_10009_ = l_Lean_MonadQuotation_getMainModule(v_m_10007_, v_self_10008_);
    lean_dec_ref(v_self_10008_);
    return v_res_10009_;
}
pub unsafe fn l_Lean_MonadRef_mkInfoFromRefPos___redArg___lam__0(
    mut v_toPure_10010_: *mut LeanObject,
    mut v_____do__lift_10011_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10012_: u8 = 0;
    let mut v___x_10013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10014_: *mut LeanObject = core::ptr::null_mut();
    v___x_10012_ = 0;
    v___x_10013_ = l_Lean_SourceInfo_fromRef(v_____do__lift_10011_, v___x_10012_);
    v___x_10014_ = lean_apply_2(v_toPure_10010_, lean_box(0), v___x_10013_);
    return v___x_10014_;
}
pub unsafe fn l_Lean_MonadRef_mkInfoFromRefPos___redArg___lam__0___boxed(
    mut v_toPure_10015_: *mut LeanObject,
    mut v_____do__lift_10016_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10017_: *mut LeanObject = core::ptr::null_mut();
    v_res_10017_ =
        l_Lean_MonadRef_mkInfoFromRefPos___redArg___lam__0(v_toPure_10015_, v_____do__lift_10016_);
    lean_dec(v_____do__lift_10016_);
    return v_res_10017_;
}
pub unsafe fn l_Lean_MonadRef_mkInfoFromRefPos___redArg(
    mut v_inst_10018_: *mut LeanObject,
    mut v_inst_10019_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_10020_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_10021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getRef_10022_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_10023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_10024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10025_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_10020_ = lean_ctor_get(v_inst_10018_, 0);
    lean_inc_ref(v_toApplicative_10020_);
    v_toBind_10021_ = lean_ctor_get(v_inst_10018_, 1);
    lean_inc(v_toBind_10021_);
    lean_dec_ref(v_inst_10018_);
    v_getRef_10022_ = lean_ctor_get(v_inst_10019_, 0);
    lean_inc(v_getRef_10022_);
    lean_dec_ref(v_inst_10019_);
    v_toPure_10023_ = lean_ctor_get(v_toApplicative_10020_, 1);
    lean_inc(v_toPure_10023_);
    lean_dec_ref(v_toApplicative_10020_);
    v___f_10024_ = lean_alloc_closure(
        l_Lean_MonadRef_mkInfoFromRefPos___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_10024_, 0, v_toPure_10023_);
    v___x_10025_ = lean_apply_4(
        v_toBind_10021_,
        lean_box(0),
        lean_box(0),
        v_getRef_10022_,
        v___f_10024_,
    );
    return v___x_10025_;
}
pub unsafe fn l_Lean_MonadRef_mkInfoFromRefPos(
    mut v_m_10026_: *mut LeanObject,
    mut v_inst_10027_: *mut LeanObject,
    mut v_inst_10028_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_10029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_10030_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getRef_10031_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_10032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_10033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10034_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_10029_ = lean_ctor_get(v_inst_10027_, 0);
    lean_inc_ref(v_toApplicative_10029_);
    v_toBind_10030_ = lean_ctor_get(v_inst_10027_, 1);
    lean_inc(v_toBind_10030_);
    lean_dec_ref(v_inst_10027_);
    v_getRef_10031_ = lean_ctor_get(v_inst_10028_, 0);
    lean_inc(v_getRef_10031_);
    lean_dec_ref(v_inst_10028_);
    v_toPure_10032_ = lean_ctor_get(v_toApplicative_10029_, 1);
    lean_inc(v_toPure_10032_);
    lean_dec_ref(v_toApplicative_10029_);
    v___f_10033_ = lean_alloc_closure(
        l_Lean_MonadRef_mkInfoFromRefPos___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_10033_, 0, v_toPure_10032_);
    v___x_10034_ = lean_apply_4(
        v_toBind_10030_,
        lean_box(0),
        lean_box(0),
        v_getRef_10031_,
        v___f_10033_,
    );
    return v___x_10034_;
}
pub unsafe fn l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg___lam__0(
    mut v_withFreshMacroScope_10035_: *mut LeanObject,
    mut v_00_u03b2_10036_: *mut LeanObject,
    mut v___y_10037_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10038_: *mut LeanObject = core::ptr::null_mut();
    v___x_10038_ = lean_apply_2(v_withFreshMacroScope_10035_, lean_box(0), v___y_10037_);
    return v___x_10038_;
}
pub unsafe fn l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg___lam__1(
    mut v_inst_10039_: *mut LeanObject,
    mut v___f_10040_: *mut LeanObject,
    mut v_00_u03b1_10041_: *mut LeanObject,
    mut v___y_10042_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10043_: *mut LeanObject = core::ptr::null_mut();
    v___x_10043_ = lean_apply_3(v_inst_10039_, lean_box(0), v___f_10040_, v___y_10042_);
    return v___x_10043_;
}
pub unsafe fn l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(
    mut v_inst_10044_: *mut LeanObject,
    mut v_inst_10045_: *mut LeanObject,
    mut v_inst_10046_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toMonadRef_10047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getCurrMacroScope_10048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getContext_10049_: *mut LeanObject = core::ptr::null_mut();
    let mut v_withFreshMacroScope_10050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10052_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_10053_: u8 = 0;
    let mut v___f_10054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_10055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10060_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10061_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_10062_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toMonadRef_10047_ = lean_ctor_get(v_inst_10046_, 0);
                v_getCurrMacroScope_10048_ = lean_ctor_get(v_inst_10046_, 1);
                v_getContext_10049_ = lean_ctor_get(v_inst_10046_, 2);
                v_withFreshMacroScope_10050_ = lean_ctor_get(v_inst_10046_, 3);
                v_isSharedCheck_10062_ = (!lean_is_exclusive(v_inst_10046_)) as u8;
                if v_isSharedCheck_10062_ == 0 {
                    v___x_10052_ = v_inst_10046_;
                    v_isShared_10053_ = v_isSharedCheck_10062_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_withFreshMacroScope_10050_);
                    lean_inc(v_getContext_10049_);
                    lean_inc(v_getCurrMacroScope_10048_);
                    lean_inc(v_toMonadRef_10047_);
                    lean_dec(v_inst_10046_);
                    v___x_10052_ = lean_box(0);
                    v_isShared_10053_ = v_isSharedCheck_10062_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_10054_ = lean_alloc_closure(
                    l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg___lam__0
                        as *mut core::ffi::c_void,
                    3,
                    1,
                );
                lean_closure_set(v___f_10054_, 0, v_withFreshMacroScope_10050_);
                lean_inc(v_inst_10044_);
                v___f_10055_ = lean_alloc_closure(
                    l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg___lam__1
                        as *mut core::ffi::c_void,
                    4,
                    2,
                );
                lean_closure_set(v___f_10055_, 0, v_inst_10044_);
                lean_closure_set(v___f_10055_, 1, v___f_10054_);
                lean_inc_n(v_inst_10045_, 2);
                v___x_10056_ = l_Lean_instMonadRefOfMonadLiftOfMonadFunctor___redArg(
                    v_inst_10045_,
                    v_inst_10044_,
                    v_toMonadRef_10047_,
                );
                v___x_10057_ = lean_apply_2(v_inst_10045_, lean_box(0), v_getCurrMacroScope_10048_);
                v___x_10058_ = lean_apply_2(v_inst_10045_, lean_box(0), v_getContext_10049_);
                if v_isShared_10053_ == 0 {
                    lean_ctor_set(v___x_10052_, 3, v___f_10055_);
                    lean_ctor_set(v___x_10052_, 2, v___x_10058_);
                    lean_ctor_set(v___x_10052_, 1, v___x_10057_);
                    lean_ctor_set(v___x_10052_, 0, v___x_10056_);
                    v___x_10060_ = v___x_10052_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_10061_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_10061_, 0, v___x_10056_);
                    lean_ctor_set(v_reuseFailAlloc_10061_, 1, v___x_10057_);
                    lean_ctor_set(v_reuseFailAlloc_10061_, 2, v___x_10058_);
                    lean_ctor_set(v_reuseFailAlloc_10061_, 3, v___f_10055_);
                    v___x_10060_ = v_reuseFailAlloc_10061_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_10060_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift(
    mut v_m_10063_: *mut LeanObject,
    mut v_n_10064_: *mut LeanObject,
    mut v_inst_10065_: *mut LeanObject,
    mut v_inst_10066_: *mut LeanObject,
    mut v_inst_10067_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10068_: *mut LeanObject = core::ptr::null_mut();
    v___x_10068_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(
        v_inst_10065_,
        v_inst_10066_,
        v_inst_10067_,
    );
    return v___x_10068_;
}
pub unsafe fn l_Lean_Name_hasMacroScopes(mut v_x_10070_: *mut LeanObject) -> u8 {
    let mut v___x_10071_: u8 = 0;
    let mut v_str_10072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10074_: u8 = 0;
    let mut v_pre_10075_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_x_10070_) {
                0 => {
                    v___x_10071_ = 0;
                    return v___x_10071_;
                }
                1 => {
                    v_str_10072_ = lean_ctor_get(v_x_10070_, 1);
                    v___x_10073_ = l_Lean_Name_hasMacroScopes___closed__0;
                    v___x_10074_ = lean_string_dec_eq(v_str_10072_, v___x_10073_);
                    return v___x_10074_;
                }
                _ => {
                    v_pre_10075_ = lean_ctor_get(v_x_10070_, 0);
                    v_x_10070_ = v_pre_10075_;
                    state = 0;
                    continue;
                }
            },
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Name_hasMacroScopes___boxed(
    mut v_x_10077_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10078_: u8 = 0;
    let mut v_r_10079_: *mut LeanObject = core::ptr::null_mut();
    v_res_10078_ = l_Lean_Name_hasMacroScopes(v_x_10077_);
    lean_dec(v_x_10077_);
    v_r_10079_ = lean_box((v_res_10078_) as usize);
    return v_r_10079_;
}
pub unsafe fn l___private_Init_Prelude_0__Lean_eraseMacroScopesAux(
    mut v_x_10081_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pre_10082_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_10083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10085_: u8 = 0;
    let mut v_pre_10087_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_x_10081_) {
                0 => {
                    return v_x_10081_;
                }
                1 => {
                    v_pre_10082_ = lean_ctor_get(v_x_10081_, 0);
                    v_str_10083_ = lean_ctor_get(v_x_10081_, 1);
                    v___x_10084_ = l___private_Init_Prelude_0__Lean_eraseMacroScopesAux___closed__0;
                    v___x_10085_ = lean_string_dec_eq(v_str_10083_, v___x_10084_);
                    if v___x_10085_ == 0 {
                        v_x_10081_ = v_pre_10082_;
                        state = 0;
                        continue;
                    } else {
                        lean_inc(v_pre_10082_);
                        return v_pre_10082_;
                    }
                }
                _ => {
                    v_pre_10087_ = lean_ctor_get(v_x_10081_, 0);
                    v_x_10081_ = v_pre_10087_;
                    state = 0;
                    continue;
                }
            },
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Prelude_0__Lean_eraseMacroScopesAux___boxed(
    mut v_x_10089_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10090_: *mut LeanObject = core::ptr::null_mut();
    v_res_10090_ = l___private_Init_Prelude_0__Lean_eraseMacroScopesAux(v_x_10089_);
    lean_dec(v_x_10089_);
    return v_res_10090_;
}
pub unsafe fn lean_erase_macro_scopes(mut v_n_10091_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_10092_: u8 = 0;
    v___x_10092_ = l_Lean_Name_hasMacroScopes(v_n_10091_);
    if v___x_10092_ == 0 {
        return v_n_10091_;
    } else {
        let mut v___x_10093_: *mut LeanObject = core::ptr::null_mut();
        v___x_10093_ = l___private_Init_Prelude_0__Lean_eraseMacroScopesAux(v_n_10091_);
        lean_dec(v_n_10091_);
        return v___x_10093_;
    }
}
pub unsafe fn l___private_Init_Prelude_0__Lean_simpMacroScopesAux(
    mut v_x_10094_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_10094_) == 2 {
        let mut v_pre_10095_: *mut LeanObject = core::ptr::null_mut();
        let mut v_i_10096_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_10097_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_10098_: *mut LeanObject = core::ptr::null_mut();
        v_pre_10095_ = lean_ctor_get(v_x_10094_, 0);
        lean_inc(v_pre_10095_);
        v_i_10096_ = lean_ctor_get(v_x_10094_, 1);
        lean_inc(v_i_10096_);
        lean_dec_ref_known(v_x_10094_, 2);
        v___x_10097_ = l___private_Init_Prelude_0__Lean_simpMacroScopesAux(v_pre_10095_);
        v___x_10098_ = l_Lean_Name_num___override(v___x_10097_, v_i_10096_);
        return v___x_10098_;
    } else {
        let mut v___x_10099_: *mut LeanObject = core::ptr::null_mut();
        v___x_10099_ = l___private_Init_Prelude_0__Lean_eraseMacroScopesAux(v_x_10094_);
        lean_dec(v_x_10094_);
        return v___x_10099_;
    }
}
pub unsafe fn lean_simp_macro_scopes(mut v_n_10100_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_10101_: u8 = 0;
    v___x_10101_ = l_Lean_Name_hasMacroScopes(v_n_10100_);
    if v___x_10101_ == 0 {
        return v_n_10100_;
    } else {
        let mut v___x_10102_: *mut LeanObject = core::ptr::null_mut();
        v___x_10102_ = l___private_Init_Prelude_0__Lean_simpMacroScopesAux(v_n_10100_);
        return v___x_10102_;
    }
}
pub unsafe fn l_List_foldl___at___00Lean_MacroScopesView_review_spec__0(
    mut v_x_10107_: *mut LeanObject,
    mut v_x_10108_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_10109_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_10110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10111_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_10108_) == 0 {
                    return v_x_10107_;
                } else {
                    v_head_10109_ = lean_ctor_get(v_x_10108_, 0);
                    lean_inc(v_head_10109_);
                    v_tail_10110_ = lean_ctor_get(v_x_10108_, 1);
                    lean_inc(v_tail_10110_);
                    lean_dec_ref_known(v_x_10108_, 2);
                    v___x_10111_ = l_Lean_Name_num___override(v_x_10107_, v_head_10109_);
                    v_x_10107_ = v___x_10111_;
                    v_x_10108_ = v_tail_10110_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MacroScopesView_review(mut v_view_10113_: *mut LeanObject) -> *mut LeanObject {
    let mut v_scopes_10114_: *mut LeanObject = core::ptr::null_mut();
    v_scopes_10114_ = lean_ctor_get(v_view_10113_, 3);
    if lean_obj_tag(v_scopes_10114_) == 0 {
        let mut v_name_10115_: *mut LeanObject = core::ptr::null_mut();
        v_name_10115_ = lean_ctor_get(v_view_10113_, 0);
        lean_inc(v_name_10115_);
        lean_dec_ref(v_view_10113_);
        return v_name_10115_;
    } else {
        let mut v_name_10116_: *mut LeanObject = core::ptr::null_mut();
        let mut v_imported_10117_: *mut LeanObject = core::ptr::null_mut();
        let mut v_ctx_10118_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_10119_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_10120_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_10121_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_10122_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_10123_: *mut LeanObject = core::ptr::null_mut();
        let mut v_base_10124_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_10125_: *mut LeanObject = core::ptr::null_mut();
        lean_inc_ref(v_scopes_10114_);
        v_name_10116_ = lean_ctor_get(v_view_10113_, 0);
        lean_inc(v_name_10116_);
        v_imported_10117_ = lean_ctor_get(v_view_10113_, 1);
        lean_inc(v_imported_10117_);
        v_ctx_10118_ = lean_ctor_get(v_view_10113_, 2);
        lean_inc(v_ctx_10118_);
        lean_dec_ref(v_view_10113_);
        v___x_10119_ = l___private_Init_Prelude_0__Lean_eraseMacroScopesAux___closed__0;
        v___x_10120_ = l_Lean_Name_str___override(v_name_10116_, v___x_10119_);
        v___x_10121_ = l_Lean_Name_appendCore(v___x_10120_, v_imported_10117_);
        lean_dec(v___x_10120_);
        v___x_10122_ = l_Lean_Name_appendCore(v___x_10121_, v_ctx_10118_);
        lean_dec(v___x_10121_);
        v___x_10123_ = l_Lean_Name_hasMacroScopes___closed__0;
        v_base_10124_ = l_Lean_Name_str___override(v___x_10122_, v___x_10123_);
        v___x_10125_ = l_List_foldl___at___00Lean_MacroScopesView_review_spec__0(
            v_base_10124_,
            v_scopes_10114_,
        );
        return v___x_10125_;
    }
}
pub unsafe fn l_panic___at___00__private_Init_Prelude_0__Lean_assembleParts_spec__0(
    mut v_msg_10126_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10128_: *mut LeanObject = core::ptr::null_mut();
    v___x_10127_ = lean_box(0);
    v___x_10128_ = lean_panic_fn_borrowed(v___x_10127_, v_msg_10126_);
    return v___x_10128_;
}
pub unsafe fn l___private_Init_Prelude_0__Lean_assembleParts(
    mut v_x_10130_: *mut LeanObject,
    mut v_x_10131_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_10132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10134_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_10135_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_10136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10137_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_10139_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_10140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10141_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_10130_) == 0 {
                    return v_x_10131_;
                } else {
                    v_head_10132_ = lean_ctor_get(v_x_10130_, 0);
                    lean_inc(v_head_10132_);
                    match lean_obj_tag(v_head_10132_) {
                        0 => {
                            lean_dec_ref_known(v_x_10130_, 2);
                            lean_dec(v_x_10131_);
                            v___x_10133_ =
                                l___private_Init_Prelude_0__Lean_assembleParts___closed__0;
                            v___x_10134_ = l_panic___at___00__private_Init_Prelude_0__Lean_assembleParts_spec__0(v___x_10133_);
                            return v___x_10134_;
                        }
                        1 => {
                            v_tail_10135_ = lean_ctor_get(v_x_10130_, 1);
                            lean_inc(v_tail_10135_);
                            lean_dec_ref_known(v_x_10130_, 2);
                            v_str_10136_ = lean_ctor_get(v_head_10132_, 1);
                            lean_inc_ref(v_str_10136_);
                            lean_dec_ref_known(v_head_10132_, 2);
                            v___x_10137_ = l_Lean_Name_str___override(v_x_10131_, v_str_10136_);
                            v_x_10130_ = v_tail_10135_;
                            v_x_10131_ = v___x_10137_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v_tail_10139_ = lean_ctor_get(v_x_10130_, 1);
                            lean_inc(v_tail_10139_);
                            lean_dec_ref_known(v_x_10130_, 2);
                            v_i_10140_ = lean_ctor_get(v_head_10132_, 1);
                            lean_inc(v_i_10140_);
                            lean_dec_ref_known(v_head_10132_, 2);
                            v___x_10141_ = l_Lean_Name_num___override(v_x_10131_, v_i_10140_);
                            v_x_10130_ = v_tail_10139_;
                            v_x_10131_ = v___x_10141_;
                            state = 0;
                            continue;
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00__private_Init_Prelude_0__Lean_extractImported_spec__0(
    mut v_msg_10143_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10145_: *mut LeanObject = core::ptr::null_mut();
    v___x_10144_ = l_Lean_instInhabitedMacroScopesView;
    v___x_10145_ = lean_panic_fn_borrowed(v___x_10144_, v_msg_10143_);
    return v___x_10145_;
}
pub unsafe fn l___private_Init_Prelude_0__Lean_extractImported(
    mut v_scps_10147_: *mut LeanObject,
    mut v_mainModule_10148_: *mut LeanObject,
    mut v_x_10149_: *mut LeanObject,
    mut v_x_10150_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10152_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_10153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_10154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10156_: u8 = 0;
    let mut v___x_10157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10161_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_10162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10163_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_x_10149_) {
                0 => {
                    lean_dec(v_x_10150_);
                    lean_dec(v_mainModule_10148_);
                    lean_dec(v_scps_10147_);
                    v___x_10151_ = l___private_Init_Prelude_0__Lean_extractImported___closed__0;
                    v___x_10152_ =
                        l_panic___at___00__private_Init_Prelude_0__Lean_extractImported_spec__0(
                            v___x_10151_,
                        );
                    return v___x_10152_;
                }
                1 => {
                    v_pre_10153_ = lean_ctor_get(v_x_10149_, 0);
                    lean_inc(v_pre_10153_);
                    v_str_10154_ = lean_ctor_get(v_x_10149_, 1);
                    v___x_10155_ = l___private_Init_Prelude_0__Lean_eraseMacroScopesAux___closed__0;
                    v___x_10156_ = lean_string_dec_eq(v_str_10154_, v___x_10155_);
                    if v___x_10156_ == 0 {
                        v___x_10157_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v___x_10157_, 0, v_x_10149_);
                        lean_ctor_set(v___x_10157_, 1, v_x_10150_);
                        v_x_10149_ = v_pre_10153_;
                        v_x_10150_ = v___x_10157_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref_known(v_x_10149_, 2);
                        v___x_10159_ = lean_box(0);
                        v___x_10160_ = l___private_Init_Prelude_0__Lean_assembleParts(
                            v_x_10150_,
                            v___x_10159_,
                        );
                        v___x_10161_ = lean_alloc_ctor(0, 4, (0) as u32);
                        lean_ctor_set(v___x_10161_, 0, v_pre_10153_);
                        lean_ctor_set(v___x_10161_, 1, v___x_10160_);
                        lean_ctor_set(v___x_10161_, 2, v_mainModule_10148_);
                        lean_ctor_set(v___x_10161_, 3, v_scps_10147_);
                        return v___x_10161_;
                    }
                }
                _ => {
                    v_pre_10162_ = lean_ctor_get(v_x_10149_, 0);
                    lean_inc(v_pre_10162_);
                    v___x_10163_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_10163_, 0, v_x_10149_);
                    lean_ctor_set(v___x_10163_, 1, v_x_10150_);
                    v_x_10149_ = v_pre_10162_;
                    v_x_10150_ = v___x_10163_;
                    state = 0;
                    continue;
                }
            },
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Prelude_0__Lean_extractMainModule(
    mut v_scps_10166_: *mut LeanObject,
    mut v_x_10167_: *mut LeanObject,
    mut v_x_10168_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10170_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_10171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_10172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10174_: u8 = 0;
    let mut v___x_10175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10183_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_x_10167_) {
                0 => {
                    lean_dec(v_x_10168_);
                    lean_dec(v_scps_10166_);
                    v___x_10169_ = l___private_Init_Prelude_0__Lean_extractMainModule___closed__0;
                    v___x_10170_ =
                        l_panic___at___00__private_Init_Prelude_0__Lean_extractImported_spec__0(
                            v___x_10169_,
                        );
                    return v___x_10170_;
                }
                1 => {
                    v_pre_10171_ = lean_ctor_get(v_x_10167_, 0);
                    lean_inc(v_pre_10171_);
                    v_str_10172_ = lean_ctor_get(v_x_10167_, 1);
                    v___x_10173_ = l___private_Init_Prelude_0__Lean_eraseMacroScopesAux___closed__0;
                    v___x_10174_ = lean_string_dec_eq(v_str_10172_, v___x_10173_);
                    if v___x_10174_ == 0 {
                        v___x_10175_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v___x_10175_, 0, v_x_10167_);
                        lean_ctor_set(v___x_10175_, 1, v_x_10168_);
                        v_x_10167_ = v_pre_10171_;
                        v_x_10168_ = v___x_10175_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref_known(v_x_10167_, 2);
                        v___x_10177_ = lean_box(0);
                        v___x_10178_ = l___private_Init_Prelude_0__Lean_assembleParts(
                            v_x_10168_,
                            v___x_10177_,
                        );
                        v___x_10179_ = lean_alloc_ctor(0, 4, (0) as u32);
                        lean_ctor_set(v___x_10179_, 0, v_pre_10171_);
                        lean_ctor_set(v___x_10179_, 1, v___x_10177_);
                        lean_ctor_set(v___x_10179_, 2, v___x_10178_);
                        lean_ctor_set(v___x_10179_, 3, v_scps_10166_);
                        return v___x_10179_;
                    }
                }
                _ => {
                    v___x_10180_ = lean_box(0);
                    v___x_10181_ =
                        l___private_Init_Prelude_0__Lean_assembleParts(v_x_10168_, v___x_10180_);
                    v___x_10182_ = lean_box(0);
                    v___x_10183_ = l___private_Init_Prelude_0__Lean_extractImported(
                        v_scps_10166_,
                        v___x_10181_,
                        v_x_10167_,
                        v___x_10182_,
                    );
                    return v___x_10183_;
                }
            },
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Prelude_0__Lean_extractMacroScopesAux(
    mut v_x_10185_: *mut LeanObject,
    mut v_x_10186_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10188_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_10189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10191_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_10192_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_10193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10194_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_x_10185_) {
                0 => {
                    lean_dec(v_x_10186_);
                    v___x_10187_ =
                        l___private_Init_Prelude_0__Lean_extractMacroScopesAux___closed__0;
                    v___x_10188_ =
                        l_panic___at___00__private_Init_Prelude_0__Lean_extractImported_spec__0(
                            v___x_10187_,
                        );
                    return v___x_10188_;
                }
                1 => {
                    v_pre_10189_ = lean_ctor_get(v_x_10185_, 0);
                    lean_inc(v_pre_10189_);
                    lean_dec_ref_known(v_x_10185_, 2);
                    v___x_10190_ = lean_box(0);
                    v___x_10191_ = l___private_Init_Prelude_0__Lean_extractMainModule(
                        v_x_10186_,
                        v_pre_10189_,
                        v___x_10190_,
                    );
                    return v___x_10191_;
                }
                _ => {
                    v_pre_10192_ = lean_ctor_get(v_x_10185_, 0);
                    lean_inc(v_pre_10192_);
                    v_i_10193_ = lean_ctor_get(v_x_10185_, 1);
                    lean_inc(v_i_10193_);
                    lean_dec_ref_known(v_x_10185_, 2);
                    v___x_10194_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_10194_, 0, v_i_10193_);
                    lean_ctor_set(v___x_10194_, 1, v_x_10186_);
                    v_x_10185_ = v_pre_10192_;
                    v_x_10186_ = v___x_10194_;
                    state = 0;
                    continue;
                }
            },
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_extractMacroScopes(mut v_n_10196_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_10197_: u8 = 0;
    v___x_10197_ = l_Lean_Name_hasMacroScopes(v_n_10196_);
    if v___x_10197_ == 0 {
        let mut v___x_10198_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_10199_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_10200_: *mut LeanObject = core::ptr::null_mut();
        v___x_10198_ = lean_box(0);
        v___x_10199_ = lean_box(0);
        v___x_10200_ = lean_alloc_ctor(0, 4, (0) as u32);
        lean_ctor_set(v___x_10200_, 0, v_n_10196_);
        lean_ctor_set(v___x_10200_, 1, v___x_10198_);
        lean_ctor_set(v___x_10200_, 2, v___x_10198_);
        lean_ctor_set(v___x_10200_, 3, v___x_10199_);
        return v___x_10200_;
    } else {
        let mut v___x_10201_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_10202_: *mut LeanObject = core::ptr::null_mut();
        v___x_10201_ = lean_box(0);
        v___x_10202_ =
            l___private_Init_Prelude_0__Lean_extractMacroScopesAux(v_n_10196_, v___x_10201_);
        return v___x_10202_;
    }
}
pub unsafe fn l_Lean_addMacroScope(
    mut v_ctx_10203_: *mut LeanObject,
    mut v_n_10204_: *mut LeanObject,
    mut v_scp_10205_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10206_: u8 = 0;
    let mut v___x_10207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_view_10213_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_10214_: *mut LeanObject = core::ptr::null_mut();
    let mut v_imported_10215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ctx_10216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_scopes_10217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10219_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_10220_: u8 = 0;
    let mut v___x_10221_: u8 = 0;
    let mut v___x_10222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_10231_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_10206_ = l_Lean_Name_hasMacroScopes(v_n_10204_);
                if v___x_10206_ == 0 {
                    v___x_10207_ = l___private_Init_Prelude_0__Lean_eraseMacroScopesAux___closed__0;
                    v___x_10208_ = l_Lean_Name_str___override(v_n_10204_, v___x_10207_);
                    v___x_10209_ = l_Lean_Name_appendCore(v___x_10208_, v_ctx_10203_);
                    lean_dec(v___x_10208_);
                    v___x_10210_ = l_Lean_Name_hasMacroScopes___closed__0;
                    v___x_10211_ = l_Lean_Name_str___override(v___x_10209_, v___x_10210_);
                    v___x_10212_ = l_Lean_Name_num___override(v___x_10211_, v_scp_10205_);
                    return v___x_10212_;
                } else {
                    lean_inc(v_n_10204_);
                    v_view_10213_ = l_Lean_extractMacroScopes(v_n_10204_);
                    v_name_10214_ = lean_ctor_get(v_view_10213_, 0);
                    v_imported_10215_ = lean_ctor_get(v_view_10213_, 1);
                    v_ctx_10216_ = lean_ctor_get(v_view_10213_, 2);
                    v_scopes_10217_ = lean_ctor_get(v_view_10213_, 3);
                    v_isSharedCheck_10231_ = (!lean_is_exclusive(v_view_10213_)) as u8;
                    if v_isSharedCheck_10231_ == 0 {
                        v___x_10219_ = v_view_10213_;
                        v_isShared_10220_ = v_isSharedCheck_10231_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_scopes_10217_);
                        lean_inc(v_ctx_10216_);
                        lean_inc(v_imported_10215_);
                        lean_inc(v_name_10214_);
                        lean_dec(v_view_10213_);
                        v___x_10219_ = lean_box(0);
                        v_isShared_10220_ = v_isSharedCheck_10231_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_10221_ = lean_name_eq(v_ctx_10216_, v_ctx_10203_);
                if v___x_10221_ == 0 {
                    lean_dec(v_n_10204_);
                    v___x_10222_ = l_Lean_Name_appendCore(v_imported_10215_, v_ctx_10216_);
                    lean_dec(v_imported_10215_);
                    v___x_10223_ = l_List_foldl___at___00Lean_MacroScopesView_review_spec__0(
                        v___x_10222_,
                        v_scopes_10217_,
                    );
                    v___x_10224_ = lean_box(0);
                    v___x_10225_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_10225_, 0, v_scp_10205_);
                    lean_ctor_set(v___x_10225_, 1, v___x_10224_);
                    if v_isShared_10220_ == 0 {
                        lean_ctor_set(v___x_10219_, 3, v___x_10225_);
                        lean_ctor_set(v___x_10219_, 2, v_ctx_10203_);
                        lean_ctor_set(v___x_10219_, 1, v___x_10223_);
                        v___x_10227_ = v___x_10219_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_10229_ = lean_alloc_ctor(0, 4, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_10229_, 0, v_name_10214_);
                        lean_ctor_set(v_reuseFailAlloc_10229_, 1, v___x_10223_);
                        lean_ctor_set(v_reuseFailAlloc_10229_, 2, v_ctx_10203_);
                        lean_ctor_set(v_reuseFailAlloc_10229_, 3, v___x_10225_);
                        v___x_10227_ = v_reuseFailAlloc_10229_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_10219_);
                    lean_dec(v_scopes_10217_);
                    lean_dec(v_ctx_10216_);
                    lean_dec(v_imported_10215_);
                    lean_dec(v_name_10214_);
                    lean_dec(v_ctx_10203_);
                    v___x_10230_ = l_Lean_Name_num___override(v_n_10204_, v_scp_10205_);
                    return v___x_10230_;
                }
            }
            2 => {
                v___x_10228_ = l_Lean_MacroScopesView_review(v___x_10227_);
                return v___x_10228_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Name_append(
    mut v_a_10233_: *mut LeanObject,
    mut v_b_10234_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10235_: u8 = 0;
    let mut v___x_10236_: u8 = 0;
    let mut v___x_10237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_view_10238_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_10239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_imported_10240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ctx_10241_: *mut LeanObject = core::ptr::null_mut();
    let mut v_scopes_10242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10244_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_10245_: u8 = 0;
    let mut v___x_10246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10249_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10250_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_10251_: u8 = 0;
    let mut v___x_10252_: u8 = 0;
    let mut v_view_10253_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_10254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_imported_10255_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ctx_10256_: *mut LeanObject = core::ptr::null_mut();
    let mut v_scopes_10257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10259_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_10260_: u8 = 0;
    let mut v___x_10261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10265_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_10266_: u8 = 0;
    let mut v___x_10267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10268_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_10235_ = l_Lean_Name_hasMacroScopes(v_a_10233_);
                if v___x_10235_ == 0 {
                    v___x_10236_ = l_Lean_Name_hasMacroScopes(v_b_10234_);
                    if v___x_10236_ == 0 {
                        v___x_10237_ = l_Lean_Name_appendCore(v_a_10233_, v_b_10234_);
                        lean_dec(v_a_10233_);
                        return v___x_10237_;
                    } else {
                        v_view_10238_ = l_Lean_extractMacroScopes(v_b_10234_);
                        v_name_10239_ = lean_ctor_get(v_view_10238_, 0);
                        v_imported_10240_ = lean_ctor_get(v_view_10238_, 1);
                        v_ctx_10241_ = lean_ctor_get(v_view_10238_, 2);
                        v_scopes_10242_ = lean_ctor_get(v_view_10238_, 3);
                        v_isSharedCheck_10251_ = (!lean_is_exclusive(v_view_10238_)) as u8;
                        if v_isSharedCheck_10251_ == 0 {
                            v___x_10244_ = v_view_10238_;
                            v_isShared_10245_ = v_isSharedCheck_10251_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_scopes_10242_);
                            lean_inc(v_ctx_10241_);
                            lean_inc(v_imported_10240_);
                            lean_inc(v_name_10239_);
                            lean_dec(v_view_10238_);
                            v___x_10244_ = lean_box(0);
                            v_isShared_10245_ = v_isSharedCheck_10251_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v___x_10252_ = l_Lean_Name_hasMacroScopes(v_b_10234_);
                    if v___x_10252_ == 0 {
                        v_view_10253_ = l_Lean_extractMacroScopes(v_a_10233_);
                        v_name_10254_ = lean_ctor_get(v_view_10253_, 0);
                        v_imported_10255_ = lean_ctor_get(v_view_10253_, 1);
                        v_ctx_10256_ = lean_ctor_get(v_view_10253_, 2);
                        v_scopes_10257_ = lean_ctor_get(v_view_10253_, 3);
                        v_isSharedCheck_10266_ = (!lean_is_exclusive(v_view_10253_)) as u8;
                        if v_isSharedCheck_10266_ == 0 {
                            v___x_10259_ = v_view_10253_;
                            v_isShared_10260_ = v_isSharedCheck_10266_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_scopes_10257_);
                            lean_inc(v_ctx_10256_);
                            lean_inc(v_imported_10255_);
                            lean_inc(v_name_10254_);
                            lean_dec(v_view_10253_);
                            v___x_10259_ = lean_box(0);
                            v_isShared_10260_ = v_isSharedCheck_10266_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_dec(v_b_10234_);
                        lean_dec(v_a_10233_);
                        v___x_10267_ = l_Lean_Name_append___closed__0;
                        v___x_10268_ =
                            l_panic___at___00__private_Init_Prelude_0__Lean_assembleParts_spec__0(
                                v___x_10267_,
                            );
                        return v___x_10268_;
                    }
                }
            }
            1 => {
                v___x_10246_ = l_Lean_Name_appendCore(v_a_10233_, v_name_10239_);
                lean_dec(v_a_10233_);
                if v_isShared_10245_ == 0 {
                    lean_ctor_set(v___x_10244_, 0, v___x_10246_);
                    v___x_10248_ = v___x_10244_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_10250_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_10250_, 0, v___x_10246_);
                    lean_ctor_set(v_reuseFailAlloc_10250_, 1, v_imported_10240_);
                    lean_ctor_set(v_reuseFailAlloc_10250_, 2, v_ctx_10241_);
                    lean_ctor_set(v_reuseFailAlloc_10250_, 3, v_scopes_10242_);
                    v___x_10248_ = v_reuseFailAlloc_10250_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_10249_ = l_Lean_MacroScopesView_review(v___x_10248_);
                return v___x_10249_;
            }
            3 => {
                v___x_10261_ = l_Lean_Name_appendCore(v_name_10254_, v_b_10234_);
                lean_dec(v_name_10254_);
                if v_isShared_10260_ == 0 {
                    lean_ctor_set(v___x_10259_, 0, v___x_10261_);
                    v___x_10263_ = v___x_10259_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_10265_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_10265_, 0, v___x_10261_);
                    lean_ctor_set(v_reuseFailAlloc_10265_, 1, v_imported_10255_);
                    lean_ctor_set(v_reuseFailAlloc_10265_, 2, v_ctx_10256_);
                    lean_ctor_set(v_reuseFailAlloc_10265_, 3, v_scopes_10257_);
                    v___x_10263_ = v_reuseFailAlloc_10265_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_10264_ = l_Lean_MacroScopesView_review(v___x_10263_);
                return v___x_10264_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MonadQuotation_addMacroScope___redArg___lam__0(
    mut v_ctx_10271_: *mut LeanObject,
    mut v_n_10272_: *mut LeanObject,
    mut v_toPure_10273_: *mut LeanObject,
    mut v_scp_10274_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10276_: *mut LeanObject = core::ptr::null_mut();
    v___x_10275_ = l_Lean_addMacroScope(v_ctx_10271_, v_n_10272_, v_scp_10274_);
    v___x_10276_ = lean_apply_2(v_toPure_10273_, lean_box(0), v___x_10275_);
    return v___x_10276_;
}
pub unsafe fn l_Lean_MonadQuotation_addMacroScope___redArg___lam__1(
    mut v_n_10277_: *mut LeanObject,
    mut v_toPure_10278_: *mut LeanObject,
    mut v_toBind_10279_: *mut LeanObject,
    mut v_getCurrMacroScope_10280_: *mut LeanObject,
    mut v_ctx_10281_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_10282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10283_: *mut LeanObject = core::ptr::null_mut();
    v___f_10282_ = lean_alloc_closure(
        l_Lean_MonadQuotation_addMacroScope___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_10282_, 0, v_ctx_10281_);
    lean_closure_set(v___f_10282_, 1, v_n_10277_);
    lean_closure_set(v___f_10282_, 2, v_toPure_10278_);
    v___x_10283_ = lean_apply_4(
        v_toBind_10279_,
        lean_box(0),
        lean_box(0),
        v_getCurrMacroScope_10280_,
        v___f_10282_,
    );
    return v___x_10283_;
}
pub unsafe fn l_Lean_MonadQuotation_addMacroScope___redArg(
    mut v_inst_10284_: *mut LeanObject,
    mut v_inst_10285_: *mut LeanObject,
    mut v_n_10286_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_10287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_10288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getCurrMacroScope_10289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getContext_10290_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_10291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_10292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10293_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_10287_ = lean_ctor_get(v_inst_10285_, 0);
    lean_inc_ref(v_toApplicative_10287_);
    v_toBind_10288_ = lean_ctor_get(v_inst_10285_, 1);
    lean_inc_n(v_toBind_10288_, 2);
    lean_dec_ref(v_inst_10285_);
    v_getCurrMacroScope_10289_ = lean_ctor_get(v_inst_10284_, 1);
    lean_inc(v_getCurrMacroScope_10289_);
    v_getContext_10290_ = lean_ctor_get(v_inst_10284_, 2);
    lean_inc(v_getContext_10290_);
    lean_dec_ref(v_inst_10284_);
    v_toPure_10291_ = lean_ctor_get(v_toApplicative_10287_, 1);
    lean_inc(v_toPure_10291_);
    lean_dec_ref(v_toApplicative_10287_);
    v___f_10292_ = lean_alloc_closure(
        l_Lean_MonadQuotation_addMacroScope___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_10292_, 0, v_n_10286_);
    lean_closure_set(v___f_10292_, 1, v_toPure_10291_);
    lean_closure_set(v___f_10292_, 2, v_toBind_10288_);
    lean_closure_set(v___f_10292_, 3, v_getCurrMacroScope_10289_);
    v___x_10293_ = lean_apply_4(
        v_toBind_10288_,
        lean_box(0),
        lean_box(0),
        v_getContext_10290_,
        v___f_10292_,
    );
    return v___x_10293_;
}
pub unsafe fn l_Lean_MonadQuotation_addMacroScope(
    mut v_m_10294_: *mut LeanObject,
    mut v_inst_10295_: *mut LeanObject,
    mut v_inst_10296_: *mut LeanObject,
    mut v_n_10297_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_10298_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_10299_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getCurrMacroScope_10300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getContext_10301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_10302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_10303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10304_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_10298_ = lean_ctor_get(v_inst_10296_, 0);
    lean_inc_ref(v_toApplicative_10298_);
    v_toBind_10299_ = lean_ctor_get(v_inst_10296_, 1);
    lean_inc_n(v_toBind_10299_, 2);
    lean_dec_ref(v_inst_10296_);
    v_getCurrMacroScope_10300_ = lean_ctor_get(v_inst_10295_, 1);
    lean_inc(v_getCurrMacroScope_10300_);
    v_getContext_10301_ = lean_ctor_get(v_inst_10295_, 2);
    lean_inc(v_getContext_10301_);
    lean_dec_ref(v_inst_10295_);
    v_toPure_10302_ = lean_ctor_get(v_toApplicative_10298_, 1);
    lean_inc(v_toPure_10302_);
    lean_dec_ref(v_toApplicative_10298_);
    v___f_10303_ = lean_alloc_closure(
        l_Lean_MonadQuotation_addMacroScope___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_10303_, 0, v_n_10297_);
    lean_closure_set(v___f_10303_, 1, v_toPure_10302_);
    lean_closure_set(v___f_10303_, 2, v_toBind_10299_);
    lean_closure_set(v___f_10303_, 3, v_getCurrMacroScope_10300_);
    v___x_10304_ = lean_apply_4(
        v_toBind_10299_,
        lean_box(0),
        lean_box(0),
        v_getContext_10301_,
        v___f_10303_,
    );
    return v___x_10304_;
}
pub unsafe fn l_Lean_Syntax_matchesNull(
    mut v_stx_10305_: *mut LeanObject,
    mut v_n_10306_: *mut LeanObject,
) -> u8 {
    let mut v___x_10307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10308_: u8 = 0;
    v___x_10307_ = l_Lean_nullKind___closed__1;
    v___x_10308_ = l_Lean_Syntax_isNodeOf(v_stx_10305_, v___x_10307_, v_n_10306_);
    return v___x_10308_;
}
pub unsafe fn l_Lean_Syntax_matchesNull___boxed(
    mut v_stx_10309_: *mut LeanObject,
    mut v_n_10310_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10311_: u8 = 0;
    let mut v_r_10312_: *mut LeanObject = core::ptr::null_mut();
    v_res_10311_ = l_Lean_Syntax_matchesNull(v_stx_10309_, v_n_10310_);
    lean_dec(v_n_10310_);
    v_r_10312_ = lean_box((v_res_10311_) as usize);
    return v_r_10312_;
}
pub unsafe fn l_Lean_Syntax_matchesIdent(
    mut v_stx_10313_: *mut LeanObject,
    mut v_id_10314_: *mut LeanObject,
) -> u8 {
    let mut v___x_10315_: u8 = 0;
    v___x_10315_ = l_Lean_Syntax_isIdent(v_stx_10313_);
    if v___x_10315_ == 0 {
        lean_dec(v_id_10314_);
        return v___x_10315_;
    } else {
        let mut v___x_10316_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_10317_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_10318_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_10319_: u8 = 0;
        v___x_10316_ = l_Lean_Syntax_getId(v_stx_10313_);
        v___x_10317_ = lean_erase_macro_scopes(v___x_10316_);
        v___x_10318_ = lean_erase_macro_scopes(v_id_10314_);
        v___x_10319_ = lean_name_eq(v___x_10317_, v___x_10318_);
        lean_dec(v___x_10318_);
        lean_dec(v___x_10317_);
        return v___x_10319_;
    }
}
pub unsafe fn l_Lean_Syntax_matchesIdent___boxed(
    mut v_stx_10320_: *mut LeanObject,
    mut v_id_10321_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10322_: u8 = 0;
    let mut v_r_10323_: *mut LeanObject = core::ptr::null_mut();
    v_res_10322_ = l_Lean_Syntax_matchesIdent(v_stx_10320_, v_id_10321_);
    lean_dec(v_stx_10320_);
    v_r_10323_ = lean_box((v_res_10322_) as usize);
    return v_r_10323_;
}
pub unsafe fn l_Lean_Syntax_matchesLit(
    mut v_stx_10324_: *mut LeanObject,
    mut v_k_10325_: *mut LeanObject,
    mut v_val_10326_: *mut LeanObject,
) -> u8 {
    if lean_obj_tag(v_stx_10324_) == 1 {
        let mut v_kind_10327_: *mut LeanObject = core::ptr::null_mut();
        let mut v_args_10328_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_10329_: u8 = 0;
        v_kind_10327_ = lean_ctor_get(v_stx_10324_, 1);
        v_args_10328_ = lean_ctor_get(v_stx_10324_, 2);
        v___x_10329_ = lean_name_eq(v_k_10325_, v_kind_10327_);
        if v___x_10329_ == 0 {
            return v___x_10329_;
        } else {
            let mut v___x_10330_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_10331_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_10332_: u8 = 0;
            v___x_10330_ = lean_unsigned_to_nat(0);
            v___x_10331_ = lean_array_get_size(v_args_10328_);
            v___x_10332_ = lean_nat_dec_lt(v___x_10330_, v___x_10331_);
            if v___x_10332_ == 0 {
                return v___x_10332_;
            } else {
                let mut v___x_10333_: *mut LeanObject = core::ptr::null_mut();
                v___x_10333_ = lean_array_fget_borrowed(v_args_10328_, v___x_10330_);
                if lean_obj_tag(v___x_10333_) == 2 {
                    let mut v_val_10334_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_10335_: u8 = 0;
                    v_val_10334_ = lean_ctor_get(v___x_10333_, 1);
                    v___x_10335_ = lean_string_dec_eq(v_val_10326_, v_val_10334_);
                    return v___x_10335_;
                } else {
                    let mut v___x_10336_: u8 = 0;
                    v___x_10336_ = 0;
                    return v___x_10336_;
                }
            }
        }
    } else {
        let mut v___x_10337_: u8 = 0;
        v___x_10337_ = 0;
        return v___x_10337_;
    }
}
pub unsafe fn l_Lean_Syntax_matchesLit___boxed(
    mut v_stx_10338_: *mut LeanObject,
    mut v_k_10339_: *mut LeanObject,
    mut v_val_10340_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10341_: u8 = 0;
    let mut v_r_10342_: *mut LeanObject = core::ptr::null_mut();
    v_res_10341_ = l_Lean_Syntax_matchesLit(v_stx_10338_, v_k_10339_, v_val_10340_);
    lean_dec_ref(v_val_10340_);
    lean_dec(v_k_10339_);
    lean_dec(v_stx_10338_);
    v_r_10342_ = lean_box((v_res_10341_) as usize);
    return v_r_10342_;
}
pub unsafe fn _init_l_Lean_Macro_MethodsRefPointed() -> *mut LeanObject {
    let mut v___x_10343_: *mut LeanObject = core::ptr::null_mut();
    v___x_10343_ = lean_box(0);
    return v___x_10343_;
}
pub unsafe fn l_Lean_Macro_Exception_ctorIdx(mut v_x_10344_: *mut LeanObject) -> *mut LeanObject {
    if lean_obj_tag(v_x_10344_) == 0 {
        let mut v___x_10345_: *mut LeanObject = core::ptr::null_mut();
        v___x_10345_ = lean_unsigned_to_nat(0);
        return v___x_10345_;
    } else {
        let mut v___x_10346_: *mut LeanObject = core::ptr::null_mut();
        v___x_10346_ = lean_unsigned_to_nat(1);
        return v___x_10346_;
    }
}
pub unsafe fn l_Lean_Macro_Exception_ctorIdx___boxed(
    mut v_x_10347_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10348_: *mut LeanObject = core::ptr::null_mut();
    v_res_10348_ = l_Lean_Macro_Exception_ctorIdx(v_x_10347_);
    lean_dec(v_x_10347_);
    return v_res_10348_;
}
pub unsafe fn l_Lean_Macro_Exception_ctorElim___redArg(
    mut v_t_10349_: *mut LeanObject,
    mut v_k_10350_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_t_10349_) == 0 {
        let mut v_a_10351_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_10352_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_10353_: *mut LeanObject = core::ptr::null_mut();
        v_a_10351_ = lean_ctor_get(v_t_10349_, 0);
        lean_inc(v_a_10351_);
        v_a_10352_ = lean_ctor_get(v_t_10349_, 1);
        lean_inc_ref(v_a_10352_);
        lean_dec_ref_known(v_t_10349_, 2);
        v___x_10353_ = lean_apply_2(v_k_10350_, v_a_10351_, v_a_10352_);
        return v___x_10353_;
    } else {
        return v_k_10350_;
    }
}
pub unsafe fn l_Lean_Macro_Exception_ctorElim(
    mut v_motive_10354_: *mut LeanObject,
    mut v_ctorIdx_10355_: *mut LeanObject,
    mut v_t_10356_: *mut LeanObject,
    mut v_h_10357_: *mut LeanObject,
    mut v_k_10358_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10359_: *mut LeanObject = core::ptr::null_mut();
    v___x_10359_ = l_Lean_Macro_Exception_ctorElim___redArg(v_t_10356_, v_k_10358_);
    return v___x_10359_;
}
pub unsafe fn l_Lean_Macro_Exception_ctorElim___boxed(
    mut v_motive_10360_: *mut LeanObject,
    mut v_ctorIdx_10361_: *mut LeanObject,
    mut v_t_10362_: *mut LeanObject,
    mut v_h_10363_: *mut LeanObject,
    mut v_k_10364_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10365_: *mut LeanObject = core::ptr::null_mut();
    v_res_10365_ = l_Lean_Macro_Exception_ctorElim(
        v_motive_10360_,
        v_ctorIdx_10361_,
        v_t_10362_,
        v_h_10363_,
        v_k_10364_,
    );
    lean_dec(v_ctorIdx_10361_);
    return v_res_10365_;
}
pub unsafe fn l_Lean_Macro_Exception_error_elim___redArg(
    mut v_t_10366_: *mut LeanObject,
    mut v_error_10367_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10368_: *mut LeanObject = core::ptr::null_mut();
    v___x_10368_ = l_Lean_Macro_Exception_ctorElim___redArg(v_t_10366_, v_error_10367_);
    return v___x_10368_;
}
pub unsafe fn l_Lean_Macro_Exception_error_elim(
    mut v_motive_10369_: *mut LeanObject,
    mut v_t_10370_: *mut LeanObject,
    mut v_h_10371_: *mut LeanObject,
    mut v_error_10372_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10373_: *mut LeanObject = core::ptr::null_mut();
    v___x_10373_ = l_Lean_Macro_Exception_ctorElim___redArg(v_t_10370_, v_error_10372_);
    return v___x_10373_;
}
pub unsafe fn l_Lean_Macro_Exception_unsupportedSyntax_elim___redArg(
    mut v_t_10374_: *mut LeanObject,
    mut v_unsupportedSyntax_10375_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10376_: *mut LeanObject = core::ptr::null_mut();
    v___x_10376_ = l_Lean_Macro_Exception_ctorElim___redArg(v_t_10374_, v_unsupportedSyntax_10375_);
    return v___x_10376_;
}
pub unsafe fn l_Lean_Macro_Exception_unsupportedSyntax_elim(
    mut v_motive_10377_: *mut LeanObject,
    mut v_t_10378_: *mut LeanObject,
    mut v_h_10379_: *mut LeanObject,
    mut v_unsupportedSyntax_10380_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10381_: *mut LeanObject = core::ptr::null_mut();
    v___x_10381_ = l_Lean_Macro_Exception_ctorElim___redArg(v_t_10378_, v_unsupportedSyntax_10380_);
    return v___x_10381_;
}
pub unsafe fn l_Lean_Macro_instMonadRefMacroM___lam__0(
    mut v_ctx_10387_: *mut LeanObject,
    mut v___y_10388_: *mut LeanObject,
    mut v___y_10389_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_10390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10391_: *mut LeanObject = core::ptr::null_mut();
    v_ref_10390_ = lean_ctor_get(v_ctx_10387_, 5);
    lean_inc(v_ref_10390_);
    v___x_10391_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_10391_, 0, v_ref_10390_);
    lean_ctor_set(v___x_10391_, 1, v___y_10389_);
    return v___x_10391_;
}
pub unsafe fn l_Lean_Macro_instMonadRefMacroM___lam__0___boxed(
    mut v_ctx_10392_: *mut LeanObject,
    mut v___y_10393_: *mut LeanObject,
    mut v___y_10394_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10395_: *mut LeanObject = core::ptr::null_mut();
    v_res_10395_ =
        l_Lean_Macro_instMonadRefMacroM___lam__0(v_ctx_10392_, v___y_10393_, v___y_10394_);
    lean_dec_ref(v___y_10393_);
    lean_dec_ref(v_ctx_10392_);
    return v_res_10395_;
}
pub unsafe fn l_Lean_Macro_instMonadRefMacroM___lam__1(
    mut v_00_u03b1_10396_: *mut LeanObject,
    mut v_ref_10397_: *mut LeanObject,
    mut v_x_10398_: *mut LeanObject,
    mut v___y_10399_: *mut LeanObject,
    mut v___y_10400_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_methods_10401_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_10402_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_10403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_10404_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_10405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10407_: *mut LeanObject = core::ptr::null_mut();
    v_methods_10401_ = lean_ctor_get(v___y_10399_, 0);
    v_quotContext_10402_ = lean_ctor_get(v___y_10399_, 1);
    v_currMacroScope_10403_ = lean_ctor_get(v___y_10399_, 2);
    v_currRecDepth_10404_ = lean_ctor_get(v___y_10399_, 3);
    v_maxRecDepth_10405_ = lean_ctor_get(v___y_10399_, 4);
    lean_inc(v_maxRecDepth_10405_);
    lean_inc(v_currRecDepth_10404_);
    lean_inc(v_currMacroScope_10403_);
    lean_inc(v_quotContext_10402_);
    lean_inc(v_methods_10401_);
    v___x_10406_ = lean_alloc_ctor(0, 6, (0) as u32);
    lean_ctor_set(v___x_10406_, 0, v_methods_10401_);
    lean_ctor_set(v___x_10406_, 1, v_quotContext_10402_);
    lean_ctor_set(v___x_10406_, 2, v_currMacroScope_10403_);
    lean_ctor_set(v___x_10406_, 3, v_currRecDepth_10404_);
    lean_ctor_set(v___x_10406_, 4, v_maxRecDepth_10405_);
    lean_ctor_set(v___x_10406_, 5, v_ref_10397_);
    v___x_10407_ = lean_apply_2(v_x_10398_, v___x_10406_, v___y_10400_);
    return v___x_10407_;
}
pub unsafe fn l_Lean_Macro_instMonadRefMacroM___lam__1___boxed(
    mut v_00_u03b1_10408_: *mut LeanObject,
    mut v_ref_10409_: *mut LeanObject,
    mut v_x_10410_: *mut LeanObject,
    mut v___y_10411_: *mut LeanObject,
    mut v___y_10412_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10413_: *mut LeanObject = core::ptr::null_mut();
    v_res_10413_ = l_Lean_Macro_instMonadRefMacroM___lam__1(
        v_00_u03b1_10408_,
        v_ref_10409_,
        v_x_10410_,
        v___y_10411_,
        v___y_10412_,
    );
    lean_dec_ref(v___y_10411_);
    return v_res_10413_;
}
pub unsafe fn l_Lean_Macro_throwUnsupported___redArg(
    mut v_a_10426_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10428_: *mut LeanObject = core::ptr::null_mut();
    v___x_10427_ = lean_box(1);
    v___x_10428_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_10428_, 0, v___x_10427_);
    lean_ctor_set(v___x_10428_, 1, v_a_10426_);
    return v___x_10428_;
}
pub unsafe fn l_Lean_Macro_throwUnsupported(
    mut v_00_u03b1_10429_: *mut LeanObject,
    mut v_a_10430_: *mut LeanObject,
    mut v_a_10431_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10432_: *mut LeanObject = core::ptr::null_mut();
    v___x_10432_ = l_Lean_Macro_throwUnsupported___redArg(v_a_10431_);
    return v___x_10432_;
}
pub unsafe fn l_Lean_Macro_throwUnsupported___boxed(
    mut v_00_u03b1_10433_: *mut LeanObject,
    mut v_a_10434_: *mut LeanObject,
    mut v_a_10435_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10436_: *mut LeanObject = core::ptr::null_mut();
    v_res_10436_ = l_Lean_Macro_throwUnsupported(v_00_u03b1_10433_, v_a_10434_, v_a_10435_);
    lean_dec_ref(v_a_10434_);
    return v_res_10436_;
}
pub unsafe fn l_Lean_Macro_throwError___redArg(
    mut v_msg_10437_: *mut LeanObject,
    mut v_a_10438_: *mut LeanObject,
    mut v_a_10439_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_10440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10442_: *mut LeanObject = core::ptr::null_mut();
    v_ref_10440_ = lean_ctor_get(v_a_10438_, 5);
    lean_inc(v_ref_10440_);
    v___x_10441_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_10441_, 0, v_ref_10440_);
    lean_ctor_set(v___x_10441_, 1, v_msg_10437_);
    v___x_10442_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_10442_, 0, v___x_10441_);
    lean_ctor_set(v___x_10442_, 1, v_a_10439_);
    return v___x_10442_;
}
pub unsafe fn l_Lean_Macro_throwError___redArg___boxed(
    mut v_msg_10443_: *mut LeanObject,
    mut v_a_10444_: *mut LeanObject,
    mut v_a_10445_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10446_: *mut LeanObject = core::ptr::null_mut();
    v_res_10446_ = l_Lean_Macro_throwError___redArg(v_msg_10443_, v_a_10444_, v_a_10445_);
    lean_dec_ref(v_a_10444_);
    return v_res_10446_;
}
pub unsafe fn l_Lean_Macro_throwError(
    mut v_00_u03b1_10447_: *mut LeanObject,
    mut v_msg_10448_: *mut LeanObject,
    mut v_a_10449_: *mut LeanObject,
    mut v_a_10450_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10451_: *mut LeanObject = core::ptr::null_mut();
    v___x_10451_ = l_Lean_Macro_throwError___redArg(v_msg_10448_, v_a_10449_, v_a_10450_);
    return v___x_10451_;
}
pub unsafe fn l_Lean_Macro_throwError___boxed(
    mut v_00_u03b1_10452_: *mut LeanObject,
    mut v_msg_10453_: *mut LeanObject,
    mut v_a_10454_: *mut LeanObject,
    mut v_a_10455_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10456_: *mut LeanObject = core::ptr::null_mut();
    v_res_10456_ = l_Lean_Macro_throwError(v_00_u03b1_10452_, v_msg_10453_, v_a_10454_, v_a_10455_);
    lean_dec_ref(v_a_10454_);
    return v_res_10456_;
}
pub unsafe fn l_Lean_Macro_throwErrorAt___redArg(
    mut v_ref_10457_: *mut LeanObject,
    mut v_msg_10458_: *mut LeanObject,
    mut v_a_10459_: *mut LeanObject,
    mut v_a_10460_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_methods_10461_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_10462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_10463_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_10464_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_10465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_10466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_10467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10469_: *mut LeanObject = core::ptr::null_mut();
    v_methods_10461_ = lean_ctor_get(v_a_10459_, 0);
    v_quotContext_10462_ = lean_ctor_get(v_a_10459_, 1);
    v_currMacroScope_10463_ = lean_ctor_get(v_a_10459_, 2);
    v_currRecDepth_10464_ = lean_ctor_get(v_a_10459_, 3);
    v_maxRecDepth_10465_ = lean_ctor_get(v_a_10459_, 4);
    v_ref_10466_ = lean_ctor_get(v_a_10459_, 5);
    v_ref_10467_ = l_Lean_replaceRef(v_ref_10457_, v_ref_10466_);
    lean_inc(v_maxRecDepth_10465_);
    lean_inc(v_currRecDepth_10464_);
    lean_inc(v_currMacroScope_10463_);
    lean_inc(v_quotContext_10462_);
    lean_inc(v_methods_10461_);
    v___x_10468_ = lean_alloc_ctor(0, 6, (0) as u32);
    lean_ctor_set(v___x_10468_, 0, v_methods_10461_);
    lean_ctor_set(v___x_10468_, 1, v_quotContext_10462_);
    lean_ctor_set(v___x_10468_, 2, v_currMacroScope_10463_);
    lean_ctor_set(v___x_10468_, 3, v_currRecDepth_10464_);
    lean_ctor_set(v___x_10468_, 4, v_maxRecDepth_10465_);
    lean_ctor_set(v___x_10468_, 5, v_ref_10467_);
    v___x_10469_ = l_Lean_Macro_throwError___redArg(v_msg_10458_, v___x_10468_, v_a_10460_);
    lean_dec_ref_known(v___x_10468_, 6);
    return v___x_10469_;
}
pub unsafe fn l_Lean_Macro_throwErrorAt___redArg___boxed(
    mut v_ref_10470_: *mut LeanObject,
    mut v_msg_10471_: *mut LeanObject,
    mut v_a_10472_: *mut LeanObject,
    mut v_a_10473_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10474_: *mut LeanObject = core::ptr::null_mut();
    v_res_10474_ =
        l_Lean_Macro_throwErrorAt___redArg(v_ref_10470_, v_msg_10471_, v_a_10472_, v_a_10473_);
    lean_dec_ref(v_a_10472_);
    lean_dec(v_ref_10470_);
    return v_res_10474_;
}
pub unsafe fn l_Lean_Macro_throwErrorAt(
    mut v_00_u03b1_10475_: *mut LeanObject,
    mut v_ref_10476_: *mut LeanObject,
    mut v_msg_10477_: *mut LeanObject,
    mut v_a_10478_: *mut LeanObject,
    mut v_a_10479_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10480_: *mut LeanObject = core::ptr::null_mut();
    v___x_10480_ =
        l_Lean_Macro_throwErrorAt___redArg(v_ref_10476_, v_msg_10477_, v_a_10478_, v_a_10479_);
    return v___x_10480_;
}
pub unsafe fn l_Lean_Macro_throwErrorAt___boxed(
    mut v_00_u03b1_10481_: *mut LeanObject,
    mut v_ref_10482_: *mut LeanObject,
    mut v_msg_10483_: *mut LeanObject,
    mut v_a_10484_: *mut LeanObject,
    mut v_a_10485_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10486_: *mut LeanObject = core::ptr::null_mut();
    v_res_10486_ = l_Lean_Macro_throwErrorAt(
        v_00_u03b1_10481_,
        v_ref_10482_,
        v_msg_10483_,
        v_a_10484_,
        v_a_10485_,
    );
    lean_dec_ref(v_a_10484_);
    lean_dec(v_ref_10482_);
    return v_res_10486_;
}
pub unsafe fn l_Lean_Macro_withFreshMacroScope___redArg(
    mut v_x_10487_: *mut LeanObject,
    mut v_a_10488_: *mut LeanObject,
    mut v_a_10489_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_macroScope_10490_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceMsgs_10491_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expandedMacroDecls_10492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_10495_: u8 = 0;
    let mut v_methods_10496_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_10497_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_10498_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_10499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_10500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10506_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_10508_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_macroScope_10490_ = lean_ctor_get(v_a_10489_, 0);
                v_traceMsgs_10491_ = lean_ctor_get(v_a_10489_, 1);
                v_expandedMacroDecls_10492_ = lean_ctor_get(v_a_10489_, 2);
                v_isSharedCheck_10508_ = (!lean_is_exclusive(v_a_10489_)) as u8;
                if v_isSharedCheck_10508_ == 0 {
                    v___x_10494_ = v_a_10489_;
                    v_isShared_10495_ = v_isSharedCheck_10508_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_expandedMacroDecls_10492_);
                    lean_inc(v_traceMsgs_10491_);
                    lean_inc(v_macroScope_10490_);
                    lean_dec(v_a_10489_);
                    v___x_10494_ = lean_box(0);
                    v_isShared_10495_ = v_isSharedCheck_10508_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_methods_10496_ = lean_ctor_get(v_a_10488_, 0);
                v_quotContext_10497_ = lean_ctor_get(v_a_10488_, 1);
                v_currRecDepth_10498_ = lean_ctor_get(v_a_10488_, 3);
                v_maxRecDepth_10499_ = lean_ctor_get(v_a_10488_, 4);
                v_ref_10500_ = lean_ctor_get(v_a_10488_, 5);
                v___x_10501_ = lean_unsigned_to_nat(1);
                v___x_10502_ = lean_nat_add(v_macroScope_10490_, v___x_10501_);
                if v_isShared_10495_ == 0 {
                    lean_ctor_set(v___x_10494_, 0, v___x_10502_);
                    v___x_10504_ = v___x_10494_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_10507_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_10507_, 0, v___x_10502_);
                    lean_ctor_set(v_reuseFailAlloc_10507_, 1, v_traceMsgs_10491_);
                    lean_ctor_set(v_reuseFailAlloc_10507_, 2, v_expandedMacroDecls_10492_);
                    v___x_10504_ = v_reuseFailAlloc_10507_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_inc(v_ref_10500_);
                lean_inc(v_maxRecDepth_10499_);
                lean_inc(v_currRecDepth_10498_);
                lean_inc(v_quotContext_10497_);
                lean_inc(v_methods_10496_);
                v___x_10505_ = lean_alloc_ctor(0, 6, (0) as u32);
                lean_ctor_set(v___x_10505_, 0, v_methods_10496_);
                lean_ctor_set(v___x_10505_, 1, v_quotContext_10497_);
                lean_ctor_set(v___x_10505_, 2, v_macroScope_10490_);
                lean_ctor_set(v___x_10505_, 3, v_currRecDepth_10498_);
                lean_ctor_set(v___x_10505_, 4, v_maxRecDepth_10499_);
                lean_ctor_set(v___x_10505_, 5, v_ref_10500_);
                v___x_10506_ = lean_apply_2(v_x_10487_, v___x_10505_, v___x_10504_);
                return v___x_10506_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Macro_withFreshMacroScope___redArg___boxed(
    mut v_x_10509_: *mut LeanObject,
    mut v_a_10510_: *mut LeanObject,
    mut v_a_10511_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10512_: *mut LeanObject = core::ptr::null_mut();
    v_res_10512_ = l_Lean_Macro_withFreshMacroScope___redArg(v_x_10509_, v_a_10510_, v_a_10511_);
    lean_dec_ref(v_a_10510_);
    return v_res_10512_;
}
pub unsafe fn l_Lean_Macro_withFreshMacroScope(
    mut v_00_u03b1_10513_: *mut LeanObject,
    mut v_x_10514_: *mut LeanObject,
    mut v_a_10515_: *mut LeanObject,
    mut v_a_10516_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_macroScope_10517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceMsgs_10518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expandedMacroDecls_10519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10521_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_10522_: u8 = 0;
    let mut v_methods_10523_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_10524_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_10525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_10526_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_10527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_10535_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_macroScope_10517_ = lean_ctor_get(v_a_10516_, 0);
                v_traceMsgs_10518_ = lean_ctor_get(v_a_10516_, 1);
                v_expandedMacroDecls_10519_ = lean_ctor_get(v_a_10516_, 2);
                v_isSharedCheck_10535_ = (!lean_is_exclusive(v_a_10516_)) as u8;
                if v_isSharedCheck_10535_ == 0 {
                    v___x_10521_ = v_a_10516_;
                    v_isShared_10522_ = v_isSharedCheck_10535_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_expandedMacroDecls_10519_);
                    lean_inc(v_traceMsgs_10518_);
                    lean_inc(v_macroScope_10517_);
                    lean_dec(v_a_10516_);
                    v___x_10521_ = lean_box(0);
                    v_isShared_10522_ = v_isSharedCheck_10535_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_methods_10523_ = lean_ctor_get(v_a_10515_, 0);
                v_quotContext_10524_ = lean_ctor_get(v_a_10515_, 1);
                v_currRecDepth_10525_ = lean_ctor_get(v_a_10515_, 3);
                v_maxRecDepth_10526_ = lean_ctor_get(v_a_10515_, 4);
                v_ref_10527_ = lean_ctor_get(v_a_10515_, 5);
                v___x_10528_ = lean_unsigned_to_nat(1);
                v___x_10529_ = lean_nat_add(v_macroScope_10517_, v___x_10528_);
                if v_isShared_10522_ == 0 {
                    lean_ctor_set(v___x_10521_, 0, v___x_10529_);
                    v___x_10531_ = v___x_10521_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_10534_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_10534_, 0, v___x_10529_);
                    lean_ctor_set(v_reuseFailAlloc_10534_, 1, v_traceMsgs_10518_);
                    lean_ctor_set(v_reuseFailAlloc_10534_, 2, v_expandedMacroDecls_10519_);
                    v___x_10531_ = v_reuseFailAlloc_10534_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_inc(v_ref_10527_);
                lean_inc(v_maxRecDepth_10526_);
                lean_inc(v_currRecDepth_10525_);
                lean_inc(v_quotContext_10524_);
                lean_inc(v_methods_10523_);
                v___x_10532_ = lean_alloc_ctor(0, 6, (0) as u32);
                lean_ctor_set(v___x_10532_, 0, v_methods_10523_);
                lean_ctor_set(v___x_10532_, 1, v_quotContext_10524_);
                lean_ctor_set(v___x_10532_, 2, v_macroScope_10517_);
                lean_ctor_set(v___x_10532_, 3, v_currRecDepth_10525_);
                lean_ctor_set(v___x_10532_, 4, v_maxRecDepth_10526_);
                lean_ctor_set(v___x_10532_, 5, v_ref_10527_);
                v___x_10533_ = lean_apply_2(v_x_10514_, v___x_10532_, v___x_10531_);
                return v___x_10533_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Macro_withFreshMacroScope___boxed(
    mut v_00_u03b1_10536_: *mut LeanObject,
    mut v_x_10537_: *mut LeanObject,
    mut v_a_10538_: *mut LeanObject,
    mut v_a_10539_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10540_: *mut LeanObject = core::ptr::null_mut();
    v_res_10540_ =
        l_Lean_Macro_withFreshMacroScope(v_00_u03b1_10536_, v_x_10537_, v_a_10538_, v_a_10539_);
    lean_dec_ref(v_a_10538_);
    return v_res_10540_;
}
pub unsafe fn l_Lean_Macro_withIncRecDepth___redArg(
    mut v_ref_10541_: *mut LeanObject,
    mut v_x_10542_: *mut LeanObject,
    mut v_a_10543_: *mut LeanObject,
    mut v_a_10544_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_methods_10545_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_10546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_10547_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_10548_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_10549_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_10550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10551_: u8 = 0;
    v_methods_10545_ = lean_ctor_get(v_a_10543_, 0);
    v_quotContext_10546_ = lean_ctor_get(v_a_10543_, 1);
    v_currMacroScope_10547_ = lean_ctor_get(v_a_10543_, 2);
    v_currRecDepth_10548_ = lean_ctor_get(v_a_10543_, 3);
    v_maxRecDepth_10549_ = lean_ctor_get(v_a_10543_, 4);
    v_ref_10550_ = lean_ctor_get(v_a_10543_, 5);
    v___x_10551_ = lean_nat_dec_eq(v_currRecDepth_10548_, v_maxRecDepth_10549_);
    if v___x_10551_ == 0 {
        let mut v___x_10552_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_10553_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_10554_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_10555_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_ref_10541_);
        v___x_10552_ = lean_unsigned_to_nat(1);
        v___x_10553_ = lean_nat_add(v_currRecDepth_10548_, v___x_10552_);
        lean_inc(v_ref_10550_);
        lean_inc(v_maxRecDepth_10549_);
        lean_inc(v_currMacroScope_10547_);
        lean_inc(v_quotContext_10546_);
        lean_inc(v_methods_10545_);
        v___x_10554_ = lean_alloc_ctor(0, 6, (0) as u32);
        lean_ctor_set(v___x_10554_, 0, v_methods_10545_);
        lean_ctor_set(v___x_10554_, 1, v_quotContext_10546_);
        lean_ctor_set(v___x_10554_, 2, v_currMacroScope_10547_);
        lean_ctor_set(v___x_10554_, 3, v___x_10553_);
        lean_ctor_set(v___x_10554_, 4, v_maxRecDepth_10549_);
        lean_ctor_set(v___x_10554_, 5, v_ref_10550_);
        v___x_10555_ = lean_apply_2(v_x_10542_, v___x_10554_, v_a_10544_);
        return v___x_10555_;
    } else {
        let mut v___x_10556_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_10557_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_10558_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_x_10542_);
        v___x_10556_ = l_Lean_maxRecDepthErrorMessage___closed__0;
        v___x_10557_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_10557_, 0, v_ref_10541_);
        lean_ctor_set(v___x_10557_, 1, v___x_10556_);
        v___x_10558_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_10558_, 0, v___x_10557_);
        lean_ctor_set(v___x_10558_, 1, v_a_10544_);
        return v___x_10558_;
    }
}
pub unsafe fn l_Lean_Macro_withIncRecDepth___redArg___boxed(
    mut v_ref_10559_: *mut LeanObject,
    mut v_x_10560_: *mut LeanObject,
    mut v_a_10561_: *mut LeanObject,
    mut v_a_10562_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10563_: *mut LeanObject = core::ptr::null_mut();
    v_res_10563_ =
        l_Lean_Macro_withIncRecDepth___redArg(v_ref_10559_, v_x_10560_, v_a_10561_, v_a_10562_);
    lean_dec_ref(v_a_10561_);
    return v_res_10563_;
}
pub unsafe fn l_Lean_Macro_withIncRecDepth(
    mut v_00_u03b1_10564_: *mut LeanObject,
    mut v_ref_10565_: *mut LeanObject,
    mut v_x_10566_: *mut LeanObject,
    mut v_a_10567_: *mut LeanObject,
    mut v_a_10568_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_methods_10569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_10570_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_10571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_10572_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_10573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_10574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10575_: u8 = 0;
    v_methods_10569_ = lean_ctor_get(v_a_10567_, 0);
    v_quotContext_10570_ = lean_ctor_get(v_a_10567_, 1);
    v_currMacroScope_10571_ = lean_ctor_get(v_a_10567_, 2);
    v_currRecDepth_10572_ = lean_ctor_get(v_a_10567_, 3);
    v_maxRecDepth_10573_ = lean_ctor_get(v_a_10567_, 4);
    v_ref_10574_ = lean_ctor_get(v_a_10567_, 5);
    v___x_10575_ = lean_nat_dec_eq(v_currRecDepth_10572_, v_maxRecDepth_10573_);
    if v___x_10575_ == 0 {
        let mut v___x_10576_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_10577_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_10578_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_10579_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_ref_10565_);
        v___x_10576_ = lean_unsigned_to_nat(1);
        v___x_10577_ = lean_nat_add(v_currRecDepth_10572_, v___x_10576_);
        lean_inc(v_ref_10574_);
        lean_inc(v_maxRecDepth_10573_);
        lean_inc(v_currMacroScope_10571_);
        lean_inc(v_quotContext_10570_);
        lean_inc(v_methods_10569_);
        v___x_10578_ = lean_alloc_ctor(0, 6, (0) as u32);
        lean_ctor_set(v___x_10578_, 0, v_methods_10569_);
        lean_ctor_set(v___x_10578_, 1, v_quotContext_10570_);
        lean_ctor_set(v___x_10578_, 2, v_currMacroScope_10571_);
        lean_ctor_set(v___x_10578_, 3, v___x_10577_);
        lean_ctor_set(v___x_10578_, 4, v_maxRecDepth_10573_);
        lean_ctor_set(v___x_10578_, 5, v_ref_10574_);
        v___x_10579_ = lean_apply_2(v_x_10566_, v___x_10578_, v_a_10568_);
        return v___x_10579_;
    } else {
        let mut v___x_10580_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_10581_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_10582_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_x_10566_);
        v___x_10580_ = l_Lean_maxRecDepthErrorMessage___closed__0;
        v___x_10581_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_10581_, 0, v_ref_10565_);
        lean_ctor_set(v___x_10581_, 1, v___x_10580_);
        v___x_10582_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_10582_, 0, v___x_10581_);
        lean_ctor_set(v___x_10582_, 1, v_a_10568_);
        return v___x_10582_;
    }
}
pub unsafe fn l_Lean_Macro_withIncRecDepth___boxed(
    mut v_00_u03b1_10583_: *mut LeanObject,
    mut v_ref_10584_: *mut LeanObject,
    mut v_x_10585_: *mut LeanObject,
    mut v_a_10586_: *mut LeanObject,
    mut v_a_10587_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10588_: *mut LeanObject = core::ptr::null_mut();
    v_res_10588_ = l_Lean_Macro_withIncRecDepth(
        v_00_u03b1_10583_,
        v_ref_10584_,
        v_x_10585_,
        v_a_10586_,
        v_a_10587_,
    );
    lean_dec_ref(v_a_10586_);
    return v_res_10588_;
}
pub unsafe fn l_Lean_Macro_instMonadQuotationMacroM___lam__0(
    mut v_ctx_10589_: *mut LeanObject,
    mut v___y_10590_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_currMacroScope_10591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10592_: *mut LeanObject = core::ptr::null_mut();
    v_currMacroScope_10591_ = lean_ctor_get(v_ctx_10589_, 2);
    lean_inc(v_currMacroScope_10591_);
    v___x_10592_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_10592_, 0, v_currMacroScope_10591_);
    lean_ctor_set(v___x_10592_, 1, v___y_10590_);
    return v___x_10592_;
}
pub unsafe fn l_Lean_Macro_instMonadQuotationMacroM___lam__0___boxed(
    mut v_ctx_10593_: *mut LeanObject,
    mut v___y_10594_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10595_: *mut LeanObject = core::ptr::null_mut();
    v_res_10595_ = l_Lean_Macro_instMonadQuotationMacroM___lam__0(v_ctx_10593_, v___y_10594_);
    lean_dec_ref(v_ctx_10593_);
    return v_res_10595_;
}
pub unsafe fn l_Lean_Macro_instMonadQuotationMacroM___lam__1(
    mut v_ctx_10596_: *mut LeanObject,
    mut v___y_10597_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_quotContext_10598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10599_: *mut LeanObject = core::ptr::null_mut();
    v_quotContext_10598_ = lean_ctor_get(v_ctx_10596_, 1);
    lean_inc(v_quotContext_10598_);
    v___x_10599_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_10599_, 0, v_quotContext_10598_);
    lean_ctor_set(v___x_10599_, 1, v___y_10597_);
    return v___x_10599_;
}
pub unsafe fn l_Lean_Macro_instMonadQuotationMacroM___lam__1___boxed(
    mut v_ctx_10600_: *mut LeanObject,
    mut v___y_10601_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10602_: *mut LeanObject = core::ptr::null_mut();
    v_res_10602_ = l_Lean_Macro_instMonadQuotationMacroM___lam__1(v_ctx_10600_, v___y_10601_);
    lean_dec_ref(v_ctx_10600_);
    return v_res_10602_;
}
pub unsafe fn l_Lean_Macro_addMacroScope(
    mut v_n_10612_: *mut LeanObject,
    mut v_a_10613_: *mut LeanObject,
    mut v_a_10614_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_quotContext_10615_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_10616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10618_: *mut LeanObject = core::ptr::null_mut();
    v_quotContext_10615_ = lean_ctor_get(v_a_10613_, 1);
    v_currMacroScope_10616_ = lean_ctor_get(v_a_10613_, 2);
    lean_inc(v_currMacroScope_10616_);
    lean_inc(v_quotContext_10615_);
    v___x_10617_ = l_Lean_addMacroScope(v_quotContext_10615_, v_n_10612_, v_currMacroScope_10616_);
    v___x_10618_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_10618_, 0, v___x_10617_);
    lean_ctor_set(v___x_10618_, 1, v_a_10614_);
    return v___x_10618_;
}
pub unsafe fn l_Lean_Macro_addMacroScope___boxed(
    mut v_n_10619_: *mut LeanObject,
    mut v_a_10620_: *mut LeanObject,
    mut v_a_10621_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10622_: *mut LeanObject = core::ptr::null_mut();
    v_res_10622_ = l_Lean_Macro_addMacroScope(v_n_10619_, v_a_10620_, v_a_10621_);
    lean_dec_ref(v_a_10620_);
    return v_res_10622_;
}
pub unsafe fn l_Lean_Macro_instInhabitedMethods_default___lam__0(
    mut v_x_10623_: *mut LeanObject,
    mut v___y_10624_: *mut LeanObject,
    mut v___y_10625_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10627_: *mut LeanObject = core::ptr::null_mut();
    v___x_10626_ = lean_box(0);
    v___x_10627_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_10627_, 0, v___x_10626_);
    lean_ctor_set(v___x_10627_, 1, v___y_10625_);
    return v___x_10627_;
}
pub unsafe fn l_Lean_Macro_instInhabitedMethods_default___lam__0___boxed(
    mut v_x_10628_: *mut LeanObject,
    mut v___y_10629_: *mut LeanObject,
    mut v___y_10630_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10631_: *mut LeanObject = core::ptr::null_mut();
    v_res_10631_ =
        l_Lean_Macro_instInhabitedMethods_default___lam__0(v_x_10628_, v___y_10629_, v___y_10630_);
    lean_dec_ref(v___y_10629_);
    lean_dec(v_x_10628_);
    return v_res_10631_;
}
pub unsafe fn l_Lean_Macro_instInhabitedMethods_default___lam__1(
    mut v_x_10632_: *mut LeanObject,
    mut v___y_10633_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10635_: *mut LeanObject = core::ptr::null_mut();
    v___x_10634_ = lean_box(0);
    v___x_10635_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_10635_, 0, v___x_10634_);
    lean_ctor_set(v___x_10635_, 1, v___y_10633_);
    return v___x_10635_;
}
pub unsafe fn l_Lean_Macro_instInhabitedMethods_default___lam__1___boxed(
    mut v_x_10636_: *mut LeanObject,
    mut v___y_10637_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10638_: *mut LeanObject = core::ptr::null_mut();
    v_res_10638_ = l_Lean_Macro_instInhabitedMethods_default___lam__1(v_x_10636_, v___y_10637_);
    lean_dec_ref(v_x_10636_);
    return v_res_10638_;
}
pub unsafe fn l_Lean_Macro_instInhabitedMethods_default___lam__2(
    mut v_x_10639_: *mut LeanObject,
    mut v___y_10640_: *mut LeanObject,
    mut v___y_10641_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10642_: u8 = 0;
    let mut v___x_10643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10644_: *mut LeanObject = core::ptr::null_mut();
    v___x_10642_ = 0;
    v___x_10643_ = lean_box((v___x_10642_) as usize);
    v___x_10644_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_10644_, 0, v___x_10643_);
    lean_ctor_set(v___x_10644_, 1, v___y_10641_);
    return v___x_10644_;
}
pub unsafe fn l_Lean_Macro_instInhabitedMethods_default___lam__2___boxed(
    mut v_x_10645_: *mut LeanObject,
    mut v___y_10646_: *mut LeanObject,
    mut v___y_10647_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10648_: *mut LeanObject = core::ptr::null_mut();
    v_res_10648_ =
        l_Lean_Macro_instInhabitedMethods_default___lam__2(v_x_10645_, v___y_10646_, v___y_10647_);
    lean_dec_ref(v___y_10646_);
    lean_dec(v_x_10645_);
    return v_res_10648_;
}
pub unsafe fn l_Lean_Macro_instInhabitedMethods_default___lam__3(
    mut v_x_10649_: *mut LeanObject,
    mut v___y_10650_: *mut LeanObject,
    mut v___y_10651_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10653_: *mut LeanObject = core::ptr::null_mut();
    v___x_10652_ = lean_box(0);
    v___x_10653_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_10653_, 0, v___x_10652_);
    lean_ctor_set(v___x_10653_, 1, v___y_10651_);
    return v___x_10653_;
}
pub unsafe fn l_Lean_Macro_instInhabitedMethods_default___lam__3___boxed(
    mut v_x_10654_: *mut LeanObject,
    mut v___y_10655_: *mut LeanObject,
    mut v___y_10656_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10657_: *mut LeanObject = core::ptr::null_mut();
    v_res_10657_ =
        l_Lean_Macro_instInhabitedMethods_default___lam__3(v_x_10654_, v___y_10655_, v___y_10656_);
    lean_dec_ref(v___y_10655_);
    lean_dec(v_x_10654_);
    return v_res_10657_;
}
pub unsafe fn l_Lean_Macro_instInhabitedMethods_default___lam__4(
    mut v_x_10658_: *mut LeanObject,
    mut v___y_10659_: *mut LeanObject,
    mut v___y_10660_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10662_: *mut LeanObject = core::ptr::null_mut();
    v___x_10661_ = lean_box(0);
    v___x_10662_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_10662_, 0, v___x_10661_);
    lean_ctor_set(v___x_10662_, 1, v___y_10660_);
    return v___x_10662_;
}
pub unsafe fn l_Lean_Macro_instInhabitedMethods_default___lam__4___boxed(
    mut v_x_10663_: *mut LeanObject,
    mut v___y_10664_: *mut LeanObject,
    mut v___y_10665_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10666_: *mut LeanObject = core::ptr::null_mut();
    v_res_10666_ =
        l_Lean_Macro_instInhabitedMethods_default___lam__4(v_x_10663_, v___y_10664_, v___y_10665_);
    lean_dec_ref(v___y_10664_);
    lean_dec(v_x_10663_);
    return v_res_10666_;
}
pub unsafe fn l_Lean_Macro_mkMethodsImp(mut v_methods_10680_: *mut LeanObject) -> *mut LeanObject {
    lean_inc_ref(v_methods_10680_);
    return v_methods_10680_;
}
pub unsafe fn l_Lean_Macro_mkMethodsImp___boxed(
    mut v_methods_10681_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10682_: *mut LeanObject = core::ptr::null_mut();
    v_res_10682_ = l_Lean_Macro_mkMethodsImp(v_methods_10681_);
    lean_dec_ref(v_methods_10681_);
    return v_res_10682_;
}
pub unsafe fn l_Lean_Macro_getMethodsImp(
    mut v_a_10684_: *mut LeanObject,
    mut v_a_10685_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_methods_10686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10687_: *mut LeanObject = core::ptr::null_mut();
    v_methods_10686_ = lean_ctor_get(v_a_10684_, 0);
    lean_inc(v_methods_10686_);
    v___x_10687_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_10687_, 0, v_methods_10686_);
    lean_ctor_set(v___x_10687_, 1, v_a_10685_);
    return v___x_10687_;
}
pub unsafe fn l_Lean_Macro_getMethodsImp___boxed(
    mut v_a_10688_: *mut LeanObject,
    mut v_a_10689_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10690_: *mut LeanObject = core::ptr::null_mut();
    v_res_10690_ = l_Lean_Macro_getMethodsImp(v_a_10688_, v_a_10689_);
    lean_dec_ref(v_a_10688_);
    return v_res_10690_;
}
pub unsafe fn l_Lean_Macro_expandMacro_x3f(
    mut v_stx_10691_: *mut LeanObject,
    mut v_a_10692_: *mut LeanObject,
    mut v_a_10693_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_10695_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_10696_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expandMacro_x3f_10697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10698_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_10699_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_10700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10702_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_10703_: u8 = 0;
    let mut v___x_10705_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10706_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_10707_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_10694_ = l_Lean_Macro_getMethodsImp(v_a_10692_, v_a_10693_);
                if lean_obj_tag(v___x_10694_) == 0 {
                    v_a_10695_ = lean_ctor_get(v___x_10694_, 0);
                    lean_inc(v_a_10695_);
                    v_a_10696_ = lean_ctor_get(v___x_10694_, 1);
                    lean_inc(v_a_10696_);
                    lean_dec_ref_known(v___x_10694_, 2);
                    v_expandMacro_x3f_10697_ = lean_ctor_get(v_a_10695_, 0);
                    lean_inc_ref(v_expandMacro_x3f_10697_);
                    lean_dec(v_a_10695_);
                    lean_inc_ref(v_a_10692_);
                    v___x_10698_ = lean_apply_3(
                        v_expandMacro_x3f_10697_,
                        v_stx_10691_,
                        v_a_10692_,
                        v_a_10696_,
                    );
                    return v___x_10698_;
                } else {
                    lean_dec(v_stx_10691_);
                    v_a_10699_ = lean_ctor_get(v___x_10694_, 0);
                    v_a_10700_ = lean_ctor_get(v___x_10694_, 1);
                    v_isSharedCheck_10707_ = (!lean_is_exclusive(v___x_10694_)) as u8;
                    if v_isSharedCheck_10707_ == 0 {
                        v___x_10702_ = v___x_10694_;
                        v_isShared_10703_ = v_isSharedCheck_10707_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_10700_);
                        lean_inc(v_a_10699_);
                        lean_dec(v___x_10694_);
                        v___x_10702_ = lean_box(0);
                        v_isShared_10703_ = v_isSharedCheck_10707_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_10703_ == 0 {
                    v___x_10705_ = v___x_10702_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_10706_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_10706_, 0, v_a_10699_);
                    lean_ctor_set(v_reuseFailAlloc_10706_, 1, v_a_10700_);
                    v___x_10705_ = v_reuseFailAlloc_10706_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_10705_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Macro_expandMacro_x3f___boxed(
    mut v_stx_10708_: *mut LeanObject,
    mut v_a_10709_: *mut LeanObject,
    mut v_a_10710_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10711_: *mut LeanObject = core::ptr::null_mut();
    v_res_10711_ = l_Lean_Macro_expandMacro_x3f(v_stx_10708_, v_a_10709_, v_a_10710_);
    lean_dec_ref(v_a_10709_);
    return v_res_10711_;
}
pub unsafe fn l_Lean_Macro_hasDecl(
    mut v_declName_10712_: *mut LeanObject,
    mut v_a_10713_: *mut LeanObject,
    mut v_a_10714_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10715_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_10716_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_10717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasDecl_10718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10719_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_10720_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_10721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_10724_: u8 = 0;
    let mut v___x_10726_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10727_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_10728_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_10715_ = l_Lean_Macro_getMethodsImp(v_a_10713_, v_a_10714_);
                if lean_obj_tag(v___x_10715_) == 0 {
                    v_a_10716_ = lean_ctor_get(v___x_10715_, 0);
                    lean_inc(v_a_10716_);
                    v_a_10717_ = lean_ctor_get(v___x_10715_, 1);
                    lean_inc(v_a_10717_);
                    lean_dec_ref_known(v___x_10715_, 2);
                    v_hasDecl_10718_ = lean_ctor_get(v_a_10716_, 2);
                    lean_inc_ref(v_hasDecl_10718_);
                    lean_dec(v_a_10716_);
                    lean_inc_ref(v_a_10713_);
                    v___x_10719_ =
                        lean_apply_3(v_hasDecl_10718_, v_declName_10712_, v_a_10713_, v_a_10717_);
                    return v___x_10719_;
                } else {
                    lean_dec(v_declName_10712_);
                    v_a_10720_ = lean_ctor_get(v___x_10715_, 0);
                    v_a_10721_ = lean_ctor_get(v___x_10715_, 1);
                    v_isSharedCheck_10728_ = (!lean_is_exclusive(v___x_10715_)) as u8;
                    if v_isSharedCheck_10728_ == 0 {
                        v___x_10723_ = v___x_10715_;
                        v_isShared_10724_ = v_isSharedCheck_10728_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_10721_);
                        lean_inc(v_a_10720_);
                        lean_dec(v___x_10715_);
                        v___x_10723_ = lean_box(0);
                        v_isShared_10724_ = v_isSharedCheck_10728_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_10724_ == 0 {
                    v___x_10726_ = v___x_10723_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_10727_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_10727_, 0, v_a_10720_);
                    lean_ctor_set(v_reuseFailAlloc_10727_, 1, v_a_10721_);
                    v___x_10726_ = v_reuseFailAlloc_10727_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_10726_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Macro_hasDecl___boxed(
    mut v_declName_10729_: *mut LeanObject,
    mut v_a_10730_: *mut LeanObject,
    mut v_a_10731_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10732_: *mut LeanObject = core::ptr::null_mut();
    v_res_10732_ = l_Lean_Macro_hasDecl(v_declName_10729_, v_a_10730_, v_a_10731_);
    lean_dec_ref(v_a_10730_);
    return v_res_10732_;
}
pub unsafe fn l_Lean_Macro_getCurrNamespace(
    mut v_a_10733_: *mut LeanObject,
    mut v_a_10734_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10735_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_10736_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_10737_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getCurrNamespace_10738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10739_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_10740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_10741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_10744_: u8 = 0;
    let mut v___x_10746_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_10748_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_10735_ = l_Lean_Macro_getMethodsImp(v_a_10733_, v_a_10734_);
                if lean_obj_tag(v___x_10735_) == 0 {
                    v_a_10736_ = lean_ctor_get(v___x_10735_, 0);
                    lean_inc(v_a_10736_);
                    v_a_10737_ = lean_ctor_get(v___x_10735_, 1);
                    lean_inc(v_a_10737_);
                    lean_dec_ref_known(v___x_10735_, 2);
                    v_getCurrNamespace_10738_ = lean_ctor_get(v_a_10736_, 1);
                    lean_inc_ref(v_getCurrNamespace_10738_);
                    lean_dec(v_a_10736_);
                    lean_inc_ref(v_a_10733_);
                    v___x_10739_ = lean_apply_2(v_getCurrNamespace_10738_, v_a_10733_, v_a_10737_);
                    return v___x_10739_;
                } else {
                    v_a_10740_ = lean_ctor_get(v___x_10735_, 0);
                    v_a_10741_ = lean_ctor_get(v___x_10735_, 1);
                    v_isSharedCheck_10748_ = (!lean_is_exclusive(v___x_10735_)) as u8;
                    if v_isSharedCheck_10748_ == 0 {
                        v___x_10743_ = v___x_10735_;
                        v_isShared_10744_ = v_isSharedCheck_10748_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_10741_);
                        lean_inc(v_a_10740_);
                        lean_dec(v___x_10735_);
                        v___x_10743_ = lean_box(0);
                        v_isShared_10744_ = v_isSharedCheck_10748_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_10744_ == 0 {
                    v___x_10746_ = v___x_10743_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_10747_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_10747_, 0, v_a_10740_);
                    lean_ctor_set(v_reuseFailAlloc_10747_, 1, v_a_10741_);
                    v___x_10746_ = v_reuseFailAlloc_10747_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_10746_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Macro_getCurrNamespace___boxed(
    mut v_a_10749_: *mut LeanObject,
    mut v_a_10750_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10751_: *mut LeanObject = core::ptr::null_mut();
    v_res_10751_ = l_Lean_Macro_getCurrNamespace(v_a_10749_, v_a_10750_);
    lean_dec_ref(v_a_10749_);
    return v_res_10751_;
}
pub unsafe fn l_Lean_Macro_resolveNamespace(
    mut v_n_10752_: *mut LeanObject,
    mut v_a_10753_: *mut LeanObject,
    mut v_a_10754_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10755_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_10756_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_10757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_resolveNamespace_10758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10759_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_10760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_10761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10763_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_10764_: u8 = 0;
    let mut v___x_10766_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10767_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_10768_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_10755_ = l_Lean_Macro_getMethodsImp(v_a_10753_, v_a_10754_);
                if lean_obj_tag(v___x_10755_) == 0 {
                    v_a_10756_ = lean_ctor_get(v___x_10755_, 0);
                    lean_inc(v_a_10756_);
                    v_a_10757_ = lean_ctor_get(v___x_10755_, 1);
                    lean_inc(v_a_10757_);
                    lean_dec_ref_known(v___x_10755_, 2);
                    v_resolveNamespace_10758_ = lean_ctor_get(v_a_10756_, 3);
                    lean_inc_ref(v_resolveNamespace_10758_);
                    lean_dec(v_a_10756_);
                    lean_inc_ref(v_a_10753_);
                    v___x_10759_ = lean_apply_3(
                        v_resolveNamespace_10758_,
                        v_n_10752_,
                        v_a_10753_,
                        v_a_10757_,
                    );
                    return v___x_10759_;
                } else {
                    lean_dec(v_n_10752_);
                    v_a_10760_ = lean_ctor_get(v___x_10755_, 0);
                    v_a_10761_ = lean_ctor_get(v___x_10755_, 1);
                    v_isSharedCheck_10768_ = (!lean_is_exclusive(v___x_10755_)) as u8;
                    if v_isSharedCheck_10768_ == 0 {
                        v___x_10763_ = v___x_10755_;
                        v_isShared_10764_ = v_isSharedCheck_10768_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_10761_);
                        lean_inc(v_a_10760_);
                        lean_dec(v___x_10755_);
                        v___x_10763_ = lean_box(0);
                        v_isShared_10764_ = v_isSharedCheck_10768_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_10764_ == 0 {
                    v___x_10766_ = v___x_10763_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_10767_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_10767_, 0, v_a_10760_);
                    lean_ctor_set(v_reuseFailAlloc_10767_, 1, v_a_10761_);
                    v___x_10766_ = v_reuseFailAlloc_10767_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_10766_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Macro_resolveNamespace___boxed(
    mut v_n_10769_: *mut LeanObject,
    mut v_a_10770_: *mut LeanObject,
    mut v_a_10771_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10772_: *mut LeanObject = core::ptr::null_mut();
    v_res_10772_ = l_Lean_Macro_resolveNamespace(v_n_10769_, v_a_10770_, v_a_10771_);
    lean_dec_ref(v_a_10770_);
    return v_res_10772_;
}
pub unsafe fn l_Lean_Macro_resolveGlobalName(
    mut v_n_10773_: *mut LeanObject,
    mut v_a_10774_: *mut LeanObject,
    mut v_a_10775_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10776_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_10777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_10778_: *mut LeanObject = core::ptr::null_mut();
    let mut v_resolveGlobalName_10779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10780_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_10781_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_10782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10784_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_10785_: u8 = 0;
    let mut v___x_10787_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10788_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_10789_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_10776_ = l_Lean_Macro_getMethodsImp(v_a_10774_, v_a_10775_);
                if lean_obj_tag(v___x_10776_) == 0 {
                    v_a_10777_ = lean_ctor_get(v___x_10776_, 0);
                    lean_inc(v_a_10777_);
                    v_a_10778_ = lean_ctor_get(v___x_10776_, 1);
                    lean_inc(v_a_10778_);
                    lean_dec_ref_known(v___x_10776_, 2);
                    v_resolveGlobalName_10779_ = lean_ctor_get(v_a_10777_, 4);
                    lean_inc_ref(v_resolveGlobalName_10779_);
                    lean_dec(v_a_10777_);
                    lean_inc_ref(v_a_10774_);
                    v___x_10780_ = lean_apply_3(
                        v_resolveGlobalName_10779_,
                        v_n_10773_,
                        v_a_10774_,
                        v_a_10778_,
                    );
                    return v___x_10780_;
                } else {
                    lean_dec(v_n_10773_);
                    v_a_10781_ = lean_ctor_get(v___x_10776_, 0);
                    v_a_10782_ = lean_ctor_get(v___x_10776_, 1);
                    v_isSharedCheck_10789_ = (!lean_is_exclusive(v___x_10776_)) as u8;
                    if v_isSharedCheck_10789_ == 0 {
                        v___x_10784_ = v___x_10776_;
                        v_isShared_10785_ = v_isSharedCheck_10789_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_10782_);
                        lean_inc(v_a_10781_);
                        lean_dec(v___x_10776_);
                        v___x_10784_ = lean_box(0);
                        v_isShared_10785_ = v_isSharedCheck_10789_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_10785_ == 0 {
                    v___x_10787_ = v___x_10784_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_10788_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_10788_, 0, v_a_10781_);
                    lean_ctor_set(v_reuseFailAlloc_10788_, 1, v_a_10782_);
                    v___x_10787_ = v_reuseFailAlloc_10788_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_10787_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Macro_resolveGlobalName___boxed(
    mut v_n_10790_: *mut LeanObject,
    mut v_a_10791_: *mut LeanObject,
    mut v_a_10792_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10793_: *mut LeanObject = core::ptr::null_mut();
    v_res_10793_ = l_Lean_Macro_resolveGlobalName(v_n_10790_, v_a_10791_, v_a_10792_);
    lean_dec_ref(v_a_10791_);
    return v_res_10793_;
}
pub unsafe fn l_Lean_Macro_trace___redArg(
    mut v_clsName_10794_: *mut LeanObject,
    mut v_msg_10795_: *mut LeanObject,
    mut v_a_10796_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_macroScope_10797_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceMsgs_10798_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expandedMacroDecls_10799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10801_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_10802_: u8 = 0;
    let mut v___x_10803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10808_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_10810_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_macroScope_10797_ = lean_ctor_get(v_a_10796_, 0);
                v_traceMsgs_10798_ = lean_ctor_get(v_a_10796_, 1);
                v_expandedMacroDecls_10799_ = lean_ctor_get(v_a_10796_, 2);
                v_isSharedCheck_10810_ = (!lean_is_exclusive(v_a_10796_)) as u8;
                if v_isSharedCheck_10810_ == 0 {
                    v___x_10801_ = v_a_10796_;
                    v_isShared_10802_ = v_isSharedCheck_10810_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_expandedMacroDecls_10799_);
                    lean_inc(v_traceMsgs_10798_);
                    lean_inc(v_macroScope_10797_);
                    lean_dec(v_a_10796_);
                    v___x_10801_ = lean_box(0);
                    v_isShared_10802_ = v_isSharedCheck_10810_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_10803_ = lean_box(0);
                v___x_10804_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_10804_, 0, v_clsName_10794_);
                lean_ctor_set(v___x_10804_, 1, v_msg_10795_);
                v___x_10805_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_10805_, 0, v___x_10804_);
                lean_ctor_set(v___x_10805_, 1, v_traceMsgs_10798_);
                if v_isShared_10802_ == 0 {
                    lean_ctor_set(v___x_10801_, 1, v___x_10805_);
                    v___x_10807_ = v___x_10801_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_10809_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_10809_, 0, v_macroScope_10797_);
                    lean_ctor_set(v_reuseFailAlloc_10809_, 1, v___x_10805_);
                    lean_ctor_set(v_reuseFailAlloc_10809_, 2, v_expandedMacroDecls_10799_);
                    v___x_10807_ = v_reuseFailAlloc_10809_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_10808_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_10808_, 0, v___x_10803_);
                lean_ctor_set(v___x_10808_, 1, v___x_10807_);
                return v___x_10808_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Macro_trace(
    mut v_clsName_10811_: *mut LeanObject,
    mut v_msg_10812_: *mut LeanObject,
    mut v_a_10813_: *mut LeanObject,
    mut v_a_10814_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10815_: *mut LeanObject = core::ptr::null_mut();
    v___x_10815_ = l_Lean_Macro_trace___redArg(v_clsName_10811_, v_msg_10812_, v_a_10814_);
    return v___x_10815_;
}
pub unsafe fn l_Lean_Macro_trace___boxed(
    mut v_clsName_10816_: *mut LeanObject,
    mut v_msg_10817_: *mut LeanObject,
    mut v_a_10818_: *mut LeanObject,
    mut v_a_10819_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10820_: *mut LeanObject = core::ptr::null_mut();
    v_res_10820_ = l_Lean_Macro_trace(v_clsName_10816_, v_msg_10817_, v_a_10818_, v_a_10819_);
    lean_dec_ref(v_a_10818_);
    return v_res_10820_;
}
pub unsafe fn l_Lean_PrettyPrinter_instMonadQuotationUnexpandM___lam__0(
    mut v_00_u03b1_10821_: *mut LeanObject,
    mut v_ref_10822_: *mut LeanObject,
    mut v_x_10823_: *mut LeanObject,
    mut v___y_10824_: *mut LeanObject,
    mut v___y_10825_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10826_: *mut LeanObject = core::ptr::null_mut();
    v___x_10826_ = lean_apply_2(v_x_10823_, v_ref_10822_, v___y_10825_);
    return v___x_10826_;
}
pub unsafe fn l_Lean_PrettyPrinter_instMonadQuotationUnexpandM___lam__0___boxed(
    mut v_00_u03b1_10827_: *mut LeanObject,
    mut v_ref_10828_: *mut LeanObject,
    mut v_x_10829_: *mut LeanObject,
    mut v___y_10830_: *mut LeanObject,
    mut v___y_10831_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10832_: *mut LeanObject = core::ptr::null_mut();
    v_res_10832_ = l_Lean_PrettyPrinter_instMonadQuotationUnexpandM___lam__0(
        v_00_u03b1_10827_,
        v_ref_10828_,
        v_x_10829_,
        v___y_10830_,
        v___y_10831_,
    );
    lean_dec(v___y_10830_);
    return v_res_10832_;
}
pub unsafe fn l_Lean_PrettyPrinter_instMonadQuotationUnexpandM___lam__1(
    mut v_00_u03b1_10833_: *mut LeanObject,
    mut v___y_10834_: *mut LeanObject,
    mut v___y_10835_: *mut LeanObject,
    mut v___y_10836_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10837_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___y_10835_);
    v___x_10837_ = lean_apply_2(v___y_10834_, v___y_10835_, v___y_10836_);
    return v___x_10837_;
}
pub unsafe fn l_Lean_PrettyPrinter_instMonadQuotationUnexpandM___lam__1___boxed(
    mut v_00_u03b1_10838_: *mut LeanObject,
    mut v___y_10839_: *mut LeanObject,
    mut v___y_10840_: *mut LeanObject,
    mut v___y_10841_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10842_: *mut LeanObject = core::ptr::null_mut();
    v_res_10842_ = l_Lean_PrettyPrinter_instMonadQuotationUnexpandM___lam__1(
        v_00_u03b1_10838_,
        v___y_10839_,
        v___y_10840_,
        v___y_10841_,
    );
    lean_dec(v___y_10840_);
    return v_res_10842_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Prelude(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    l_Unit_unit = _init_l_Unit_unit();
    lean_mark_persistent(l_Unit_unit);
    l_instInhabitedSort = _init_l_instInhabitedSort();
    l_instInhabitedBool_default = _init_l_instInhabitedBool_default();
    l_instInhabitedBool = _init_l_instInhabitedBool();
    l_instInhabitedNonemptyType = _init_l_instInhabitedNonemptyType();
    l_instInhabitedNat = _init_l_instInhabitedNat();
    lean_mark_persistent(l_instInhabitedNat);
    l_instLENat = _init_l_instLENat();
    lean_mark_persistent(l_instLENat);
    l_instLTNat = _init_l_instLTNat();
    lean_mark_persistent(l_instLTNat);
    l_System_Platform_numBits = _init_l_System_Platform_numBits();
    lean_mark_persistent(l_System_Platform_numBits);
    l_UInt8_size = _init_l_UInt8_size();
    lean_mark_persistent(l_UInt8_size);
    l_instInhabitedUInt8 = _init_l_instInhabitedUInt8();
    l_instLTUInt8 = _init_l_instLTUInt8();
    lean_mark_persistent(l_instLTUInt8);
    l_instLEUInt8 = _init_l_instLEUInt8();
    lean_mark_persistent(l_instLEUInt8);
    l_UInt16_size = _init_l_UInt16_size();
    lean_mark_persistent(l_UInt16_size);
    l_instInhabitedUInt16 = _init_l_instInhabitedUInt16();
    l_UInt32_size = _init_l_UInt32_size();
    lean_mark_persistent(l_UInt32_size);
    l_instInhabitedUInt32 = _init_l_instInhabitedUInt32();
    l_instLTUInt32 = _init_l_instLTUInt32();
    lean_mark_persistent(l_instLTUInt32);
    l_instLEUInt32 = _init_l_instLEUInt32();
    lean_mark_persistent(l_instLEUInt32);
    l_UInt64_size = _init_l_UInt64_size();
    lean_mark_persistent(l_UInt64_size);
    l_instInhabitedUInt64 = _init_l_instInhabitedUInt64();
    l_USize_size = _init_l_USize_size();
    lean_mark_persistent(l_USize_size);
    l_instInhabitedUSize = _init_l_instInhabitedUSize();
    l_ByteArray_empty = _init_l_ByteArray_empty();
    lean_mark_persistent(l_ByteArray_empty);
    l_instInhabitedRaw = _init_l_instInhabitedRaw();
    lean_mark_persistent(l_instInhabitedRaw);
    l_Lean_Name_anonymous___override = _init_l_Lean_Name_anonymous___override();
    lean_mark_persistent(l_Lean_Name_anonymous___override);
    l_Lean_instInhabitedName = _init_l_Lean_instInhabitedName();
    lean_mark_persistent(l_Lean_instInhabitedName);
    l_Lean_defaultMaxRecDepth = _init_l_Lean_defaultMaxRecDepth();
    lean_mark_persistent(l_Lean_defaultMaxRecDepth);
    l_Lean_instInhabitedSourceInfo = _init_l_Lean_instInhabitedSourceInfo();
    lean_mark_persistent(l_Lean_instInhabitedSourceInfo);
    l_Lean_instInhabitedSyntax = _init_l_Lean_instInhabitedSyntax();
    lean_mark_persistent(l_Lean_instInhabitedSyntax);
    l_Lean_reservedMacroScope = _init_l_Lean_reservedMacroScope();
    lean_mark_persistent(l_Lean_reservedMacroScope);
    l_Lean_firstFrontendMacroScope = _init_l_Lean_firstFrontendMacroScope();
    lean_mark_persistent(l_Lean_firstFrontendMacroScope);
    l_Lean_Macro_MethodsRefPointed = _init_l_Lean_Macro_MethodsRefPointed();
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Prelude(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Prelude(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = runtime_initialize_Init_Prelude(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Prelude(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Prelude(builtin);
}
