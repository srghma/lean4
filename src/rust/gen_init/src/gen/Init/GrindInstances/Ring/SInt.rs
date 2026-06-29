// Lean compiler output
// Module: Init.GrindInstances.Ring.SInt
// Imports: Init.Grind.ToInt Init.GrindInstances.ToInt Init.Data.BitVec.Basic Init.Data.SInt.Basic Init.Data.SInt.Lemmas Init.Grind.Ring.Basic Init.Data.Int.Pow Init.Data.Nat.Dvd Init.Grind.Ring.ToInt
use crate::ffi::{
    lean_int8_mul, lean_int8_of_int, lean_int8_of_nat, lean_int16_mul, lean_int16_of_int,
    lean_int16_of_nat, lean_int32_mul, lean_int32_of_int, lean_int32_of_nat, lean_int64_mul,
    lean_int64_of_int, lean_int64_of_nat, lean_isize_mul, lean_isize_of_int, lean_isize_of_nat,
};
use crate::r#gen::Init::Data::BitVec::Basic::{
    initialize_Init_Data_BitVec_Basic, runtime_initialize_Init_Data_BitVec_Basic,
};
use crate::r#gen::Init::Data::Int::Pow::{
    initialize_Init_Data_Int_Pow, runtime_initialize_Init_Data_Int_Pow,
};
use crate::r#gen::Init::Data::Nat::Dvd::{
    initialize_Init_Data_Nat_Dvd, runtime_initialize_Init_Data_Nat_Dvd,
};
use crate::r#gen::Init::Data::SInt::Basic::{
    initialize_Init_Data_SInt_Basic, l_ISize_add___boxed, l_ISize_instOfNat___boxed,
    l_ISize_mul___boxed, l_ISize_neg___boxed, l_ISize_ofInt___boxed, l_ISize_ofNat___boxed,
    l_ISize_pow___boxed, l_ISize_sub___boxed, l_Int8_add___boxed, l_Int8_instOfNat___boxed,
    l_Int8_mul___boxed, l_Int8_neg___boxed, l_Int8_ofInt___boxed, l_Int8_ofNat___boxed,
    l_Int8_pow___boxed, l_Int8_sub___boxed, l_Int16_add___boxed, l_Int16_instOfNat___boxed,
    l_Int16_mul___boxed, l_Int16_neg___boxed, l_Int16_ofInt___boxed, l_Int16_ofNat___boxed,
    l_Int16_pow___boxed, l_Int16_sub___boxed, l_Int32_add___boxed, l_Int32_instOfNat___boxed,
    l_Int32_mul___boxed, l_Int32_neg___boxed, l_Int32_ofInt___boxed, l_Int32_ofNat___boxed,
    l_Int32_pow___boxed, l_Int32_sub___boxed, l_Int64_add___boxed, l_Int64_instOfNat___boxed,
    l_Int64_mul___boxed, l_Int64_neg___boxed, l_Int64_ofInt___boxed, l_Int64_ofNat___boxed,
    l_Int64_pow___boxed, l_Int64_sub___boxed, runtime_initialize_Init_Data_SInt_Basic,
};
use crate::r#gen::Init::Data::SInt::Lemmas::{
    initialize_Init_Data_SInt_Lemmas, runtime_initialize_Init_Data_SInt_Lemmas,
};
use crate::r#gen::Init::Grind::Ring::Basic::{
    initialize_Init_Grind_Ring_Basic, runtime_initialize_Init_Grind_Ring_Basic,
};
use crate::r#gen::Init::Grind::Ring::ToInt::{
    initialize_Init_Grind_Ring_ToInt, runtime_initialize_Init_Grind_Ring_ToInt,
};
use crate::r#gen::Init::Grind::ToInt::{
    initialize_Init_Grind_ToInt, runtime_initialize_Init_Grind_ToInt,
};
use crate::r#gen::Init::GrindInstances::ToInt::{
    initialize_Init_GrindInstances_ToInt, runtime_initialize_Init_GrindInstances_ToInt,
};
use crate::r#gen::Init::Prelude::l_instHAdd___redArg___lam__0;
pub static l_Lean_Grind_Int8_natCast___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Int8_ofNat___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_Int8_natCast___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_Int8_natCast___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Grind_Int8_natCast: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_Int8_natCast___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_Int8_intCast___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Int8_ofInt___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_Int8_intCast___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_Int8_intCast___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Grind_Int8_intCast: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_Int8_intCast___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_instCommRingInt8___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Grind_instCommRingInt8___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_instCommRingInt8___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingInt8___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_instCommRingInt8___closed__1_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Grind_instCommRingInt8___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_instCommRingInt8___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingInt8___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_instCommRingInt8___closed__2_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Lean_Grind_instCommRingInt8___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingInt8___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_instCommRingInt8___closed__3_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Lean_Grind_instCommRingInt8___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingInt8___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_instCommRingInt8___closed__4_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Lean_Grind_instCommRingInt8___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingInt8___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_instCommRingInt8___closed__5_value: crate::leanh::LeanClosureObject<1> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_instHAdd___redArg___lam__0 as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Grind_instCommRingInt8___closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Grind_instCommRingInt8___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingInt8___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_instCommRingInt8___closed__6_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Lean_Grind_instCommRingInt8___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingInt8___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_instCommRingInt8___closed__7_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Lean_Grind_instCommRingInt8___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingInt8___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_instCommRingInt8___closed__8_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Int8_instOfNat___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_instCommRingInt8___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingInt8___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_instCommRingInt8___closed__9_value: crate::leanh::LeanCtorObject<6> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6
                + 0) as u16,
            other: 6,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Grind_instCommRingInt8___closed__2_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Grind_instCommRingInt8___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Grind_Int8_natCast___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Grind_instCommRingInt8___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Grind_instCommRingInt8___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Grind_instCommRingInt8___closed__5_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Grind_instCommRingInt8___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingInt8___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_instCommRingInt8___closed__10_value: crate::leanh::LeanCtorObject<5> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5
                + 0) as u16,
            other: 5,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Grind_instCommRingInt8___closed__9_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Grind_instCommRingInt8___closed__6_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Grind_instCommRingInt8___closed__7_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Grind_Int8_intCast___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Grind_instCommRingInt8___closed__1_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Grind_instCommRingInt8___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingInt8___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Grind_instCommRingInt8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingInt8___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_Int16_natCast___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Int16_ofNat___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_Int16_natCast___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_Int16_natCast___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Grind_Int16_natCast: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_Int16_natCast___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_Int16_intCast___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Int16_ofInt___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_Int16_intCast___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_Int16_intCast___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Grind_Int16_intCast: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_Int16_intCast___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_instCommRingInt16___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Grind_instCommRingInt16___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_instCommRingInt16___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingInt16___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_instCommRingInt16___closed__1_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Grind_instCommRingInt16___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_instCommRingInt16___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingInt16___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_instCommRingInt16___closed__2_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Lean_Grind_instCommRingInt16___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingInt16___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_instCommRingInt16___closed__3_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Lean_Grind_instCommRingInt16___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingInt16___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_instCommRingInt16___closed__4_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Lean_Grind_instCommRingInt16___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingInt16___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_instCommRingInt16___closed__5_value: crate::leanh::LeanClosureObject<1> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_instHAdd___redArg___lam__0 as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Grind_instCommRingInt16___closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Grind_instCommRingInt16___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingInt16___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_instCommRingInt16___closed__6_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Lean_Grind_instCommRingInt16___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingInt16___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_instCommRingInt16___closed__7_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Lean_Grind_instCommRingInt16___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingInt16___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_instCommRingInt16___closed__8_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Int16_instOfNat___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_instCommRingInt16___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingInt16___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_instCommRingInt16___closed__9_value: crate::leanh::LeanCtorObject<6> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6
                + 0) as u16,
            other: 6,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Grind_instCommRingInt16___closed__2_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Grind_instCommRingInt16___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Grind_Int16_natCast___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Grind_instCommRingInt16___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Grind_instCommRingInt16___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Grind_instCommRingInt16___closed__5_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Grind_instCommRingInt16___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingInt16___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_instCommRingInt16___closed__10_value: crate::leanh::LeanCtorObject<5> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5
                + 0) as u16,
            other: 5,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Grind_instCommRingInt16___closed__9_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Grind_instCommRingInt16___closed__6_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Grind_instCommRingInt16___closed__7_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Grind_Int16_intCast___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Grind_instCommRingInt16___closed__1_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Grind_instCommRingInt16___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingInt16___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Grind_instCommRingInt16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingInt16___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_Int32_natCast___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Int32_ofNat___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_Int32_natCast___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_Int32_natCast___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Grind_Int32_natCast: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_Int32_natCast___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_Int32_intCast___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Int32_ofInt___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_Int32_intCast___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_Int32_intCast___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Grind_Int32_intCast: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_Int32_intCast___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_instCommRingInt32___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Grind_instCommRingInt32___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_instCommRingInt32___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingInt32___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_instCommRingInt32___closed__1_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Grind_instCommRingInt32___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_instCommRingInt32___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingInt32___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_instCommRingInt32___closed__2_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Lean_Grind_instCommRingInt32___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingInt32___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_instCommRingInt32___closed__3_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Lean_Grind_instCommRingInt32___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingInt32___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_instCommRingInt32___closed__4_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Lean_Grind_instCommRingInt32___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingInt32___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_instCommRingInt32___closed__5_value: crate::leanh::LeanClosureObject<1> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_instHAdd___redArg___lam__0 as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Grind_instCommRingInt32___closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Grind_instCommRingInt32___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingInt32___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_instCommRingInt32___closed__6_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Lean_Grind_instCommRingInt32___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingInt32___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_instCommRingInt32___closed__7_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Lean_Grind_instCommRingInt32___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingInt32___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_instCommRingInt32___closed__8_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Int32_instOfNat___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_instCommRingInt32___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingInt32___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_instCommRingInt32___closed__9_value: crate::leanh::LeanCtorObject<6> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6
                + 0) as u16,
            other: 6,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Grind_instCommRingInt32___closed__2_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Grind_instCommRingInt32___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Grind_Int32_natCast___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Grind_instCommRingInt32___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Grind_instCommRingInt32___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Grind_instCommRingInt32___closed__5_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Grind_instCommRingInt32___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingInt32___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_instCommRingInt32___closed__10_value: crate::leanh::LeanCtorObject<5> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5
                + 0) as u16,
            other: 5,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Grind_instCommRingInt32___closed__9_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Grind_instCommRingInt32___closed__6_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Grind_instCommRingInt32___closed__7_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Grind_Int32_intCast___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Grind_instCommRingInt32___closed__1_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Grind_instCommRingInt32___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingInt32___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Grind_instCommRingInt32: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingInt32___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_Int64_natCast___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Int64_ofNat___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_Int64_natCast___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_Int64_natCast___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Grind_Int64_natCast: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_Int64_natCast___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_Int64_intCast___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Int64_ofInt___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_Int64_intCast___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_Int64_intCast___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Grind_Int64_intCast: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_Int64_intCast___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_instCommRingInt64___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Grind_instCommRingInt64___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_instCommRingInt64___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingInt64___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_instCommRingInt64___closed__1_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Grind_instCommRingInt64___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_instCommRingInt64___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingInt64___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_instCommRingInt64___closed__2_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Lean_Grind_instCommRingInt64___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingInt64___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_instCommRingInt64___closed__3_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Lean_Grind_instCommRingInt64___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingInt64___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_instCommRingInt64___closed__4_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Lean_Grind_instCommRingInt64___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingInt64___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_instCommRingInt64___closed__5_value: crate::leanh::LeanClosureObject<1> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_instHAdd___redArg___lam__0 as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Grind_instCommRingInt64___closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Grind_instCommRingInt64___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingInt64___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_instCommRingInt64___closed__6_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Lean_Grind_instCommRingInt64___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingInt64___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_instCommRingInt64___closed__7_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Lean_Grind_instCommRingInt64___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingInt64___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_instCommRingInt64___closed__8_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Int64_instOfNat___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_instCommRingInt64___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingInt64___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_instCommRingInt64___closed__9_value: crate::leanh::LeanCtorObject<6> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6
                + 0) as u16,
            other: 6,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Grind_instCommRingInt64___closed__2_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Grind_instCommRingInt64___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Grind_Int64_natCast___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Grind_instCommRingInt64___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Grind_instCommRingInt64___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Grind_instCommRingInt64___closed__5_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Grind_instCommRingInt64___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingInt64___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_instCommRingInt64___closed__10_value: crate::leanh::LeanCtorObject<5> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5
                + 0) as u16,
            other: 5,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Grind_instCommRingInt64___closed__9_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Grind_instCommRingInt64___closed__6_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Grind_instCommRingInt64___closed__7_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Grind_Int64_intCast___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Grind_instCommRingInt64___closed__1_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Grind_instCommRingInt64___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingInt64___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Grind_instCommRingInt64: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingInt64___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_ISize_natCast___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_ISize_ofNat___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_ISize_natCast___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_ISize_natCast___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Grind_ISize_natCast: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_ISize_natCast___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_ISize_intCast___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_ISize_ofInt___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_ISize_intCast___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_ISize_intCast___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Grind_ISize_intCast: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_ISize_intCast___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_instCommRingISize___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Grind_instCommRingISize___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_instCommRingISize___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingISize___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_instCommRingISize___closed__1_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Grind_instCommRingISize___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_instCommRingISize___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingISize___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_instCommRingISize___closed__2_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Lean_Grind_instCommRingISize___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingISize___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_instCommRingISize___closed__3_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Lean_Grind_instCommRingISize___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingISize___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_instCommRingISize___closed__4_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Lean_Grind_instCommRingISize___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingISize___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_instCommRingISize___closed__5_value: crate::leanh::LeanClosureObject<1> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_instHAdd___redArg___lam__0 as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Grind_instCommRingISize___closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Grind_instCommRingISize___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingISize___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_instCommRingISize___closed__6_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Lean_Grind_instCommRingISize___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingISize___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_instCommRingISize___closed__7_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Lean_Grind_instCommRingISize___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingISize___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_instCommRingISize___closed__8_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_ISize_instOfNat___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_instCommRingISize___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingISize___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_instCommRingISize___closed__9_value: crate::leanh::LeanCtorObject<6> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6
                + 0) as u16,
            other: 6,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Grind_instCommRingISize___closed__2_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Grind_instCommRingISize___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Grind_ISize_natCast___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Grind_instCommRingISize___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Grind_instCommRingISize___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Grind_instCommRingISize___closed__5_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Grind_instCommRingISize___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingISize___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_instCommRingISize___closed__10_value: crate::leanh::LeanCtorObject<5> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5
                + 0) as u16,
            other: 5,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Grind_instCommRingISize___closed__9_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Grind_instCommRingISize___closed__6_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Grind_instCommRingISize___closed__7_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Grind_ISize_intCast___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Grind_instCommRingISize___closed__1_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Grind_instCommRingISize___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingISize___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Grind_instCommRingISize: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingISize___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_Grind_instCommRingInt8___lam__0(
    mut v_x1_235_: *mut crate::leanh::LeanObject,
    mut v_x2_236_: u8,
) -> u8 {
    let mut v___x_237_: u8 = 0;
    let mut v___x_238_: u8 = 0;
    v___x_237_ = lean_int8_of_nat(v_x1_235_);
    v___x_238_ = lean_int8_mul(v___x_237_, v_x2_236_);
    return v___x_238_;
}
pub unsafe fn l_Lean_Grind_instCommRingInt8___lam__0___boxed(
    mut v_x1_239_: *mut crate::leanh::LeanObject,
    mut v_x2_240_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x2_64__boxed_241_: u8 = 0;
    let mut v_res_242_: u8 = 0;
    let mut v_r_243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x2_64__boxed_241_ = (crate::leanh::lean_unbox(v_x2_240_) as u8);
    v_res_242_ = l_Lean_Grind_instCommRingInt8___lam__0(v_x1_239_, v_x2_64__boxed_241_);
    crate::leanh::lean_dec(v_x1_239_);
    v_r_243_ = crate::leanh::lean_box((v_res_242_) as usize);
    return v_r_243_;
}
pub unsafe fn l_Lean_Grind_instCommRingInt8___lam__1(
    mut v_x1_244_: *mut crate::leanh::LeanObject,
    mut v_x2_245_: u8,
) -> u8 {
    let mut v___x_246_: u8 = 0;
    let mut v___x_247_: u8 = 0;
    v___x_246_ = lean_int8_of_int(v_x1_244_);
    v___x_247_ = lean_int8_mul(v___x_246_, v_x2_245_);
    return v___x_247_;
}
pub unsafe fn l_Lean_Grind_instCommRingInt8___lam__1___boxed(
    mut v_x1_248_: *mut crate::leanh::LeanObject,
    mut v_x2_249_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x2_74__boxed_250_: u8 = 0;
    let mut v_res_251_: u8 = 0;
    let mut v_r_252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x2_74__boxed_250_ = (crate::leanh::lean_unbox(v_x2_249_) as u8);
    v_res_251_ = l_Lean_Grind_instCommRingInt8___lam__1(v_x1_248_, v_x2_74__boxed_250_);
    crate::leanh::lean_dec(v_x1_248_);
    v_r_252_ = crate::leanh::lean_box((v_res_251_) as usize);
    return v_r_252_;
}
pub unsafe fn l_Lean_Grind_instCommRingInt16___lam__0(
    mut v_x1_281_: *mut crate::leanh::LeanObject,
    mut v_x2_282_: u16,
) -> u16 {
    let mut v___x_283_: u16 = 0;
    let mut v___x_284_: u16 = 0;
    v___x_283_ = lean_int16_of_nat(v_x1_281_);
    v___x_284_ = lean_int16_mul(v___x_283_, v_x2_282_);
    return v___x_284_;
}
pub unsafe fn l_Lean_Grind_instCommRingInt16___lam__0___boxed(
    mut v_x1_285_: *mut crate::leanh::LeanObject,
    mut v_x2_286_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x2_64__boxed_287_: u16 = 0;
    let mut v_res_288_: u16 = 0;
    let mut v_r_289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x2_64__boxed_287_ = (crate::leanh::lean_unbox(v_x2_286_) as u16);
    v_res_288_ = l_Lean_Grind_instCommRingInt16___lam__0(v_x1_285_, v_x2_64__boxed_287_);
    crate::leanh::lean_dec(v_x1_285_);
    v_r_289_ = crate::leanh::lean_box((v_res_288_) as usize);
    return v_r_289_;
}
pub unsafe fn l_Lean_Grind_instCommRingInt16___lam__1(
    mut v_x1_290_: *mut crate::leanh::LeanObject,
    mut v_x2_291_: u16,
) -> u16 {
    let mut v___x_292_: u16 = 0;
    let mut v___x_293_: u16 = 0;
    v___x_292_ = lean_int16_of_int(v_x1_290_);
    v___x_293_ = lean_int16_mul(v___x_292_, v_x2_291_);
    return v___x_293_;
}
pub unsafe fn l_Lean_Grind_instCommRingInt16___lam__1___boxed(
    mut v_x1_294_: *mut crate::leanh::LeanObject,
    mut v_x2_295_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x2_74__boxed_296_: u16 = 0;
    let mut v_res_297_: u16 = 0;
    let mut v_r_298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x2_74__boxed_296_ = (crate::leanh::lean_unbox(v_x2_295_) as u16);
    v_res_297_ = l_Lean_Grind_instCommRingInt16___lam__1(v_x1_294_, v_x2_74__boxed_296_);
    crate::leanh::lean_dec(v_x1_294_);
    v_r_298_ = crate::leanh::lean_box((v_res_297_) as usize);
    return v_r_298_;
}
pub unsafe fn l_Lean_Grind_instCommRingInt32___lam__0(
    mut v_x1_327_: *mut crate::leanh::LeanObject,
    mut v_x2_328_: u32,
) -> u32 {
    let mut v___x_329_: u32 = 0;
    let mut v___x_330_: u32 = 0;
    v___x_329_ = lean_int32_of_nat(v_x1_327_);
    v___x_330_ = lean_int32_mul(v___x_329_, v_x2_328_);
    return v___x_330_;
}
pub unsafe fn l_Lean_Grind_instCommRingInt32___lam__0___boxed(
    mut v_x1_331_: *mut crate::leanh::LeanObject,
    mut v_x2_332_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x2_64__boxed_333_: u32 = 0;
    let mut v_res_334_: u32 = 0;
    let mut v_r_335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x2_64__boxed_333_ = crate::leanh::lean_unbox_uint32(v_x2_332_);
    crate::leanh::lean_dec(v_x2_332_);
    v_res_334_ = l_Lean_Grind_instCommRingInt32___lam__0(v_x1_331_, v_x2_64__boxed_333_);
    crate::leanh::lean_dec(v_x1_331_);
    v_r_335_ = crate::leanh::lean_box_uint32(v_res_334_);
    return v_r_335_;
}
pub unsafe fn l_Lean_Grind_instCommRingInt32___lam__1(
    mut v_x1_336_: *mut crate::leanh::LeanObject,
    mut v_x2_337_: u32,
) -> u32 {
    let mut v___x_338_: u32 = 0;
    let mut v___x_339_: u32 = 0;
    v___x_338_ = lean_int32_of_int(v_x1_336_);
    v___x_339_ = lean_int32_mul(v___x_338_, v_x2_337_);
    return v___x_339_;
}
pub unsafe fn l_Lean_Grind_instCommRingInt32___lam__1___boxed(
    mut v_x1_340_: *mut crate::leanh::LeanObject,
    mut v_x2_341_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x2_74__boxed_342_: u32 = 0;
    let mut v_res_343_: u32 = 0;
    let mut v_r_344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x2_74__boxed_342_ = crate::leanh::lean_unbox_uint32(v_x2_341_);
    crate::leanh::lean_dec(v_x2_341_);
    v_res_343_ = l_Lean_Grind_instCommRingInt32___lam__1(v_x1_340_, v_x2_74__boxed_342_);
    crate::leanh::lean_dec(v_x1_340_);
    v_r_344_ = crate::leanh::lean_box_uint32(v_res_343_);
    return v_r_344_;
}
pub unsafe fn l_Lean_Grind_instCommRingInt64___lam__0(
    mut v_x1_373_: *mut crate::leanh::LeanObject,
    mut v_x2_374_: u64,
) -> u64 {
    let mut v___x_375_: u64 = 0;
    let mut v___x_376_: u64 = 0;
    v___x_375_ = lean_int64_of_nat(v_x1_373_);
    v___x_376_ = lean_int64_mul(v___x_375_, v_x2_374_);
    return v___x_376_;
}
pub unsafe fn l_Lean_Grind_instCommRingInt64___lam__0___boxed(
    mut v_x1_377_: *mut crate::leanh::LeanObject,
    mut v_x2_378_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x2_64__boxed_379_: u64 = 0;
    let mut v_res_380_: u64 = 0;
    let mut v_r_381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x2_64__boxed_379_ = crate::leanh::lean_unbox_uint64(v_x2_378_);
    crate::leanh::lean_dec_ref(v_x2_378_);
    v_res_380_ = l_Lean_Grind_instCommRingInt64___lam__0(v_x1_377_, v_x2_64__boxed_379_);
    crate::leanh::lean_dec(v_x1_377_);
    v_r_381_ = crate::leanh::lean_box_uint64(v_res_380_);
    return v_r_381_;
}
pub unsafe fn l_Lean_Grind_instCommRingInt64___lam__1(
    mut v_x1_382_: *mut crate::leanh::LeanObject,
    mut v_x2_383_: u64,
) -> u64 {
    let mut v___x_384_: u64 = 0;
    let mut v___x_385_: u64 = 0;
    v___x_384_ = lean_int64_of_int(v_x1_382_);
    v___x_385_ = lean_int64_mul(v___x_384_, v_x2_383_);
    return v___x_385_;
}
pub unsafe fn l_Lean_Grind_instCommRingInt64___lam__1___boxed(
    mut v_x1_386_: *mut crate::leanh::LeanObject,
    mut v_x2_387_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x2_74__boxed_388_: u64 = 0;
    let mut v_res_389_: u64 = 0;
    let mut v_r_390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x2_74__boxed_388_ = crate::leanh::lean_unbox_uint64(v_x2_387_);
    crate::leanh::lean_dec_ref(v_x2_387_);
    v_res_389_ = l_Lean_Grind_instCommRingInt64___lam__1(v_x1_386_, v_x2_74__boxed_388_);
    crate::leanh::lean_dec(v_x1_386_);
    v_r_390_ = crate::leanh::lean_box_uint64(v_res_389_);
    return v_r_390_;
}
pub unsafe fn l_Lean_Grind_instCommRingISize___lam__0(
    mut v_x1_419_: *mut crate::leanh::LeanObject,
    mut v_x2_420_: usize,
) -> usize {
    let mut v___x_421_: usize = 0;
    let mut v___x_422_: usize = 0;
    v___x_421_ = lean_isize_of_nat(v_x1_419_);
    v___x_422_ = lean_isize_mul(v___x_421_, v_x2_420_);
    return v___x_422_;
}
pub unsafe fn l_Lean_Grind_instCommRingISize___lam__0___boxed(
    mut v_x1_423_: *mut crate::leanh::LeanObject,
    mut v_x2_424_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x2_64__boxed_425_: usize = 0;
    let mut v_res_426_: usize = 0;
    let mut v_r_427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x2_64__boxed_425_ = crate::leanh::lean_unbox_usize(v_x2_424_);
    crate::leanh::lean_dec(v_x2_424_);
    v_res_426_ = l_Lean_Grind_instCommRingISize___lam__0(v_x1_423_, v_x2_64__boxed_425_);
    crate::leanh::lean_dec(v_x1_423_);
    v_r_427_ = crate::leanh::lean_box_usize(v_res_426_);
    return v_r_427_;
}
pub unsafe fn l_Lean_Grind_instCommRingISize___lam__1(
    mut v_x1_428_: *mut crate::leanh::LeanObject,
    mut v_x2_429_: usize,
) -> usize {
    let mut v___x_430_: usize = 0;
    let mut v___x_431_: usize = 0;
    v___x_430_ = lean_isize_of_int(v_x1_428_);
    v___x_431_ = lean_isize_mul(v___x_430_, v_x2_429_);
    return v___x_431_;
}
pub unsafe fn l_Lean_Grind_instCommRingISize___lam__1___boxed(
    mut v_x1_432_: *mut crate::leanh::LeanObject,
    mut v_x2_433_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x2_74__boxed_434_: usize = 0;
    let mut v_res_435_: usize = 0;
    let mut v_r_436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x2_74__boxed_434_ = crate::leanh::lean_unbox_usize(v_x2_433_);
    crate::leanh::lean_dec(v_x2_433_);
    v_res_435_ = l_Lean_Grind_instCommRingISize___lam__1(v_x1_432_, v_x2_74__boxed_434_);
    crate::leanh::lean_dec(v_x1_432_);
    v_r_436_ = crate::leanh::lean_box_usize(v_res_435_);
    return v_r_436_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_GrindInstances_Ring_SInt(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Grind_ToInt(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_GrindInstances_ToInt(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_BitVec_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_SInt_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_SInt_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_Ring_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Int_Pow(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Dvd(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_Ring_ToInt(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_GrindInstances_Ring_SInt(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_GrindInstances_Ring_SInt(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Grind_ToInt(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_GrindInstances_ToInt(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_BitVec_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_SInt_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_SInt_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Grind_Ring_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Int_Pow(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Dvd(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Grind_Ring_ToInt(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_GrindInstances_Ring_SInt(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_GrindInstances_Ring_SInt(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_GrindInstances_Ring_SInt(builtin);
}
