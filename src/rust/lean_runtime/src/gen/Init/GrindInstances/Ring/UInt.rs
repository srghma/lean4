// Lean compiler output
// Module: Init.GrindInstances.Ring.UInt
// Imports: Init.GrindInstances.ToInt Init.GrindInstances.ToInt Init.Data.UInt.Basic Init.Data.UInt.Lemmas Init.Grind.Ring.Basic Init.Grind.Ring.ToInt
use crate::r#gen::Init::Data::UInt::Basic::{
    initialize_Init_Data_UInt_Basic, l_UInt8_add___boxed, l_UInt8_mul___boxed, l_UInt8_neg___boxed,
    l_UInt8_ofInt, l_UInt8_ofInt___boxed, l_UInt8_pow___boxed, l_UInt8_sub___boxed,
    l_UInt16_add___boxed, l_UInt16_mul___boxed, l_UInt16_neg___boxed, l_UInt16_ofInt,
    l_UInt16_ofInt___boxed, l_UInt16_pow___boxed, l_UInt16_sub___boxed, l_UInt32_mul___boxed,
    l_UInt32_neg___boxed, l_UInt32_ofInt, l_UInt32_ofInt___boxed, l_UInt32_pow___boxed,
    l_UInt64_add___boxed, l_UInt64_mul___boxed, l_UInt64_neg___boxed, l_UInt64_ofInt,
    l_UInt64_ofInt___boxed, l_UInt64_pow___boxed, l_UInt64_sub___boxed, l_USize_mul___boxed,
    l_USize_neg___boxed, l_USize_ofInt, l_USize_ofInt___boxed, l_USize_pow___boxed,
    runtime_initialize_Init_Data_UInt_Basic,
};
use crate::r#gen::Init::Data::UInt::BasicAux::{
    l_UInt8_instOfNat___boxed, l_UInt16_instOfNat___boxed, l_UInt16_ofNat___boxed,
    l_UInt32_add___boxed, l_UInt32_instOfNat___boxed, l_UInt32_ofNat___boxed, l_UInt32_sub___boxed,
    l_UInt64_instOfNat___boxed, l_UInt64_ofNat___boxed, l_USize_add___boxed,
    l_USize_instOfNat___boxed, l_USize_ofNat___boxed, l_USize_sub___boxed,
};
use crate::r#gen::Init::Data::UInt::Lemmas::{
    initialize_Init_Data_UInt_Lemmas, runtime_initialize_Init_Data_UInt_Lemmas,
};
use crate::r#gen::Init::Grind::Ring::Basic::{
    initialize_Init_Grind_Ring_Basic, runtime_initialize_Init_Grind_Ring_Basic,
};
use crate::r#gen::Init::Grind::Ring::ToInt::{
    initialize_Init_Grind_Ring_ToInt, runtime_initialize_Init_Grind_Ring_ToInt,
};
use crate::r#gen::Init::GrindInstances::ToInt::{
    initialize_Init_GrindInstances_ToInt, runtime_initialize_Init_GrindInstances_ToInt,
};
use crate::r#gen::Init::Prelude::{l_UInt8_ofNat___boxed, l_instHAdd___redArg___lam__0};
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint8_mul, lean_uint16_mul, lean_uint32_mul, lean_uint64_mul, lean_usize_mul,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_uint16_of_nat, lean_uint32_of_nat, lean_uint64_of_nat, lean_usize_of_nat,
};
use crate::lean_imports_rs::Init::Prelude::lean_uint8_of_nat;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_box, lean_box_uint32, lean_box_uint64, lean_box_usize,
    lean_dec, lean_dec_ref, lean_io_result_is_error, lean_io_result_mk_ok, lean_unbox,
    lean_unbox_uint32, lean_unbox_uint64, lean_unbox_usize,
};
pub static l_UInt8_natCast___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_UInt8_ofNat___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_UInt8_natCast___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_UInt8_natCast___closed__0_value) as *mut LeanObject;
pub static mut l_UInt8_natCast: *mut LeanObject =
    core::ptr::addr_of!(l_UInt8_natCast___closed__0_value) as *mut LeanObject;
pub static l_UInt8_intCast___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_UInt8_ofInt___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_UInt8_intCast___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_UInt8_intCast___closed__0_value) as *mut LeanObject;
pub static mut l_UInt8_intCast: *mut LeanObject =
    core::ptr::addr_of!(l_UInt8_intCast___closed__0_value) as *mut LeanObject;
pub static l_UInt16_natCast___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_UInt16_ofNat___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_UInt16_natCast___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_UInt16_natCast___closed__0_value) as *mut LeanObject;
pub static mut l_UInt16_natCast: *mut LeanObject =
    core::ptr::addr_of!(l_UInt16_natCast___closed__0_value) as *mut LeanObject;
pub static l_UInt16_intCast___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_UInt16_ofInt___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_UInt16_intCast___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_UInt16_intCast___closed__0_value) as *mut LeanObject;
pub static mut l_UInt16_intCast: *mut LeanObject =
    core::ptr::addr_of!(l_UInt16_intCast___closed__0_value) as *mut LeanObject;
pub static l_UInt32_natCast___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_UInt32_ofNat___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_UInt32_natCast___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_UInt32_natCast___closed__0_value) as *mut LeanObject;
pub static mut l_UInt32_natCast: *mut LeanObject =
    core::ptr::addr_of!(l_UInt32_natCast___closed__0_value) as *mut LeanObject;
pub static l_UInt32_intCast___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_UInt32_ofInt___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_UInt32_intCast___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_UInt32_intCast___closed__0_value) as *mut LeanObject;
pub static mut l_UInt32_intCast: *mut LeanObject =
    core::ptr::addr_of!(l_UInt32_intCast___closed__0_value) as *mut LeanObject;
pub static l_UInt64_natCast___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_UInt64_ofNat___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_UInt64_natCast___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_UInt64_natCast___closed__0_value) as *mut LeanObject;
pub static mut l_UInt64_natCast: *mut LeanObject =
    core::ptr::addr_of!(l_UInt64_natCast___closed__0_value) as *mut LeanObject;
pub static l_UInt64_intCast___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_UInt64_ofInt___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_UInt64_intCast___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_UInt64_intCast___closed__0_value) as *mut LeanObject;
pub static mut l_UInt64_intCast: *mut LeanObject =
    core::ptr::addr_of!(l_UInt64_intCast___closed__0_value) as *mut LeanObject;
pub static l_USize_natCast___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_USize_ofNat___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_USize_natCast___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_USize_natCast___closed__0_value) as *mut LeanObject;
pub static mut l_USize_natCast: *mut LeanObject =
    core::ptr::addr_of!(l_USize_natCast___closed__0_value) as *mut LeanObject;
pub static l_USize_intCast___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_USize_ofInt___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_USize_intCast___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_USize_intCast___closed__0_value) as *mut LeanObject;
pub static mut l_USize_intCast: *mut LeanObject =
    core::ptr::addr_of!(l_USize_intCast___closed__0_value) as *mut LeanObject;
pub static l_Lean_Grind_instCommRingUInt8___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Grind_instCommRingUInt8___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_instCommRingUInt8___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingUInt8___closed__0_value) as *mut LeanObject;
pub static l_Lean_Grind_instCommRingUInt8___closed__1_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Grind_instCommRingUInt8___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_instCommRingUInt8___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingUInt8___closed__1_value) as *mut LeanObject;
pub static l_Lean_Grind_instCommRingUInt8___closed__2_value: LeanClosureObject<0> =
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
        m_fun: l_UInt8_add___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_instCommRingUInt8___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingUInt8___closed__2_value) as *mut LeanObject;
pub static l_Lean_Grind_instCommRingUInt8___closed__3_value: LeanClosureObject<0> =
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
        m_fun: l_UInt8_mul___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_instCommRingUInt8___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingUInt8___closed__3_value) as *mut LeanObject;
pub static l_Lean_Grind_instCommRingUInt8___closed__4_value: LeanClosureObject<0> =
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
        m_fun: l_UInt8_pow___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_instCommRingUInt8___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingUInt8___closed__4_value) as *mut LeanObject;
pub static l_Lean_Grind_instCommRingUInt8___closed__5_value: LeanClosureObject<1> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_instHAdd___redArg___lam__0 as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Grind_instCommRingUInt8___closed__4_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Grind_instCommRingUInt8___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingUInt8___closed__5_value) as *mut LeanObject;
pub static l_Lean_Grind_instCommRingUInt8___closed__6_value: LeanClosureObject<0> =
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
        m_fun: l_UInt8_neg___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_instCommRingUInt8___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingUInt8___closed__6_value) as *mut LeanObject;
pub static l_Lean_Grind_instCommRingUInt8___closed__7_value: LeanClosureObject<0> =
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
        m_fun: l_UInt8_sub___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_instCommRingUInt8___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingUInt8___closed__7_value) as *mut LeanObject;
pub static l_Lean_Grind_instCommRingUInt8___closed__8_value: LeanClosureObject<0> =
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
        m_fun: l_UInt8_instOfNat___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_instCommRingUInt8___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingUInt8___closed__8_value) as *mut LeanObject;
pub static l_Lean_Grind_instCommRingUInt8___closed__9_value: LeanCtorObject<6> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 6
            + 0) as u16,
        other: 6,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Grind_instCommRingUInt8___closed__2_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_instCommRingUInt8___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_UInt8_natCast___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_instCommRingUInt8___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_instCommRingUInt8___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_instCommRingUInt8___closed__5_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Grind_instCommRingUInt8___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingUInt8___closed__9_value) as *mut LeanObject;
pub static l_Lean_Grind_instCommRingUInt8___closed__10_value: LeanCtorObject<5> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Grind_instCommRingUInt8___closed__9_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_instCommRingUInt8___closed__6_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_instCommRingUInt8___closed__7_value) as *mut LeanObject,
        core::ptr::addr_of!(l_UInt8_intCast___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_instCommRingUInt8___closed__1_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Grind_instCommRingUInt8___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingUInt8___closed__10_value) as *mut LeanObject;
pub static mut l_Lean_Grind_instCommRingUInt8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingUInt8___closed__10_value) as *mut LeanObject;
pub static l_Lean_Grind_instCommRingUInt16___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Grind_instCommRingUInt16___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_instCommRingUInt16___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingUInt16___closed__0_value) as *mut LeanObject;
pub static l_Lean_Grind_instCommRingUInt16___closed__1_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Grind_instCommRingUInt16___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_instCommRingUInt16___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingUInt16___closed__1_value) as *mut LeanObject;
pub static l_Lean_Grind_instCommRingUInt16___closed__2_value: LeanClosureObject<0> =
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
        m_fun: l_UInt16_add___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_instCommRingUInt16___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingUInt16___closed__2_value) as *mut LeanObject;
pub static l_Lean_Grind_instCommRingUInt16___closed__3_value: LeanClosureObject<0> =
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
        m_fun: l_UInt16_mul___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_instCommRingUInt16___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingUInt16___closed__3_value) as *mut LeanObject;
pub static l_Lean_Grind_instCommRingUInt16___closed__4_value: LeanClosureObject<0> =
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
        m_fun: l_UInt16_pow___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_instCommRingUInt16___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingUInt16___closed__4_value) as *mut LeanObject;
pub static l_Lean_Grind_instCommRingUInt16___closed__5_value: LeanClosureObject<1> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_instHAdd___redArg___lam__0 as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Grind_instCommRingUInt16___closed__4_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Grind_instCommRingUInt16___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingUInt16___closed__5_value) as *mut LeanObject;
pub static l_Lean_Grind_instCommRingUInt16___closed__6_value: LeanClosureObject<0> =
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
        m_fun: l_UInt16_neg___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_instCommRingUInt16___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingUInt16___closed__6_value) as *mut LeanObject;
pub static l_Lean_Grind_instCommRingUInt16___closed__7_value: LeanClosureObject<0> =
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
        m_fun: l_UInt16_sub___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_instCommRingUInt16___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingUInt16___closed__7_value) as *mut LeanObject;
pub static l_Lean_Grind_instCommRingUInt16___closed__8_value: LeanClosureObject<0> =
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
        m_fun: l_UInt16_instOfNat___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_instCommRingUInt16___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingUInt16___closed__8_value) as *mut LeanObject;
pub static l_Lean_Grind_instCommRingUInt16___closed__9_value: LeanCtorObject<6> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 6
            + 0) as u16,
        other: 6,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Grind_instCommRingUInt16___closed__2_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_instCommRingUInt16___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_UInt16_natCast___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_instCommRingUInt16___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_instCommRingUInt16___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_instCommRingUInt16___closed__5_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Grind_instCommRingUInt16___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingUInt16___closed__9_value) as *mut LeanObject;
pub static l_Lean_Grind_instCommRingUInt16___closed__10_value: LeanCtorObject<5> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Grind_instCommRingUInt16___closed__9_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_instCommRingUInt16___closed__6_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_instCommRingUInt16___closed__7_value) as *mut LeanObject,
        core::ptr::addr_of!(l_UInt16_intCast___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_instCommRingUInt16___closed__1_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Grind_instCommRingUInt16___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingUInt16___closed__10_value) as *mut LeanObject;
pub static mut l_Lean_Grind_instCommRingUInt16: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingUInt16___closed__10_value) as *mut LeanObject;
pub static l_Lean_Grind_instCommRingUInt32___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Grind_instCommRingUInt32___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_instCommRingUInt32___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingUInt32___closed__0_value) as *mut LeanObject;
pub static l_Lean_Grind_instCommRingUInt32___closed__1_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Grind_instCommRingUInt32___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_instCommRingUInt32___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingUInt32___closed__1_value) as *mut LeanObject;
pub static l_Lean_Grind_instCommRingUInt32___closed__2_value: LeanClosureObject<0> =
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
        m_fun: l_UInt32_add___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_instCommRingUInt32___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingUInt32___closed__2_value) as *mut LeanObject;
pub static l_Lean_Grind_instCommRingUInt32___closed__3_value: LeanClosureObject<0> =
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
        m_fun: l_UInt32_mul___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_instCommRingUInt32___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingUInt32___closed__3_value) as *mut LeanObject;
pub static l_Lean_Grind_instCommRingUInt32___closed__4_value: LeanClosureObject<0> =
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
        m_fun: l_UInt32_pow___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_instCommRingUInt32___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingUInt32___closed__4_value) as *mut LeanObject;
pub static l_Lean_Grind_instCommRingUInt32___closed__5_value: LeanClosureObject<1> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_instHAdd___redArg___lam__0 as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Grind_instCommRingUInt32___closed__4_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Grind_instCommRingUInt32___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingUInt32___closed__5_value) as *mut LeanObject;
pub static l_Lean_Grind_instCommRingUInt32___closed__6_value: LeanClosureObject<0> =
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
        m_fun: l_UInt32_neg___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_instCommRingUInt32___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingUInt32___closed__6_value) as *mut LeanObject;
pub static l_Lean_Grind_instCommRingUInt32___closed__7_value: LeanClosureObject<0> =
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
        m_fun: l_UInt32_sub___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_instCommRingUInt32___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingUInt32___closed__7_value) as *mut LeanObject;
pub static l_Lean_Grind_instCommRingUInt32___closed__8_value: LeanClosureObject<0> =
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
        m_fun: l_UInt32_instOfNat___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_instCommRingUInt32___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingUInt32___closed__8_value) as *mut LeanObject;
pub static l_Lean_Grind_instCommRingUInt32___closed__9_value: LeanCtorObject<6> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 6
            + 0) as u16,
        other: 6,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Grind_instCommRingUInt32___closed__2_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_instCommRingUInt32___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_UInt32_natCast___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_instCommRingUInt32___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_instCommRingUInt32___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_instCommRingUInt32___closed__5_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Grind_instCommRingUInt32___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingUInt32___closed__9_value) as *mut LeanObject;
pub static l_Lean_Grind_instCommRingUInt32___closed__10_value: LeanCtorObject<5> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Grind_instCommRingUInt32___closed__9_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_instCommRingUInt32___closed__6_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_instCommRingUInt32___closed__7_value) as *mut LeanObject,
        core::ptr::addr_of!(l_UInt32_intCast___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_instCommRingUInt32___closed__1_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Grind_instCommRingUInt32___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingUInt32___closed__10_value) as *mut LeanObject;
pub static mut l_Lean_Grind_instCommRingUInt32: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingUInt32___closed__10_value) as *mut LeanObject;
pub static l_Lean_Grind_instCommRingUInt64___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Grind_instCommRingUInt64___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_instCommRingUInt64___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingUInt64___closed__0_value) as *mut LeanObject;
pub static l_Lean_Grind_instCommRingUInt64___closed__1_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Grind_instCommRingUInt64___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_instCommRingUInt64___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingUInt64___closed__1_value) as *mut LeanObject;
pub static l_Lean_Grind_instCommRingUInt64___closed__2_value: LeanClosureObject<0> =
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
        m_fun: l_UInt64_add___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_instCommRingUInt64___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingUInt64___closed__2_value) as *mut LeanObject;
pub static l_Lean_Grind_instCommRingUInt64___closed__3_value: LeanClosureObject<0> =
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
        m_fun: l_UInt64_mul___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_instCommRingUInt64___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingUInt64___closed__3_value) as *mut LeanObject;
pub static l_Lean_Grind_instCommRingUInt64___closed__4_value: LeanClosureObject<0> =
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
        m_fun: l_UInt64_pow___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_instCommRingUInt64___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingUInt64___closed__4_value) as *mut LeanObject;
pub static l_Lean_Grind_instCommRingUInt64___closed__5_value: LeanClosureObject<1> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_instHAdd___redArg___lam__0 as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Grind_instCommRingUInt64___closed__4_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Grind_instCommRingUInt64___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingUInt64___closed__5_value) as *mut LeanObject;
pub static l_Lean_Grind_instCommRingUInt64___closed__6_value: LeanClosureObject<0> =
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
        m_fun: l_UInt64_neg___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_instCommRingUInt64___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingUInt64___closed__6_value) as *mut LeanObject;
pub static l_Lean_Grind_instCommRingUInt64___closed__7_value: LeanClosureObject<0> =
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
        m_fun: l_UInt64_sub___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_instCommRingUInt64___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingUInt64___closed__7_value) as *mut LeanObject;
pub static l_Lean_Grind_instCommRingUInt64___closed__8_value: LeanClosureObject<0> =
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
        m_fun: l_UInt64_instOfNat___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_instCommRingUInt64___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingUInt64___closed__8_value) as *mut LeanObject;
pub static l_Lean_Grind_instCommRingUInt64___closed__9_value: LeanCtorObject<6> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 6
            + 0) as u16,
        other: 6,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Grind_instCommRingUInt64___closed__2_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_instCommRingUInt64___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_UInt64_natCast___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_instCommRingUInt64___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_instCommRingUInt64___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_instCommRingUInt64___closed__5_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Grind_instCommRingUInt64___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingUInt64___closed__9_value) as *mut LeanObject;
pub static l_Lean_Grind_instCommRingUInt64___closed__10_value: LeanCtorObject<5> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Grind_instCommRingUInt64___closed__9_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_instCommRingUInt64___closed__6_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_instCommRingUInt64___closed__7_value) as *mut LeanObject,
        core::ptr::addr_of!(l_UInt64_intCast___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_instCommRingUInt64___closed__1_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Grind_instCommRingUInt64___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingUInt64___closed__10_value) as *mut LeanObject;
pub static mut l_Lean_Grind_instCommRingUInt64: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingUInt64___closed__10_value) as *mut LeanObject;
pub static l_Lean_Grind_instCommRingUSize___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Grind_instCommRingUSize___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_instCommRingUSize___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingUSize___closed__0_value) as *mut LeanObject;
pub static l_Lean_Grind_instCommRingUSize___closed__1_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Grind_instCommRingUSize___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_instCommRingUSize___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingUSize___closed__1_value) as *mut LeanObject;
pub static l_Lean_Grind_instCommRingUSize___closed__2_value: LeanClosureObject<0> =
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
        m_fun: l_USize_add___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_instCommRingUSize___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingUSize___closed__2_value) as *mut LeanObject;
pub static l_Lean_Grind_instCommRingUSize___closed__3_value: LeanClosureObject<0> =
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
        m_fun: l_USize_mul___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_instCommRingUSize___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingUSize___closed__3_value) as *mut LeanObject;
pub static l_Lean_Grind_instCommRingUSize___closed__4_value: LeanClosureObject<0> =
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
        m_fun: l_USize_pow___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_instCommRingUSize___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingUSize___closed__4_value) as *mut LeanObject;
pub static l_Lean_Grind_instCommRingUSize___closed__5_value: LeanClosureObject<1> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_instHAdd___redArg___lam__0 as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Grind_instCommRingUSize___closed__4_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Grind_instCommRingUSize___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingUSize___closed__5_value) as *mut LeanObject;
pub static l_Lean_Grind_instCommRingUSize___closed__6_value: LeanClosureObject<0> =
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
        m_fun: l_USize_neg___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_instCommRingUSize___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingUSize___closed__6_value) as *mut LeanObject;
pub static l_Lean_Grind_instCommRingUSize___closed__7_value: LeanClosureObject<0> =
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
        m_fun: l_USize_sub___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_instCommRingUSize___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingUSize___closed__7_value) as *mut LeanObject;
pub static l_Lean_Grind_instCommRingUSize___closed__8_value: LeanClosureObject<0> =
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
        m_fun: l_USize_instOfNat___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_instCommRingUSize___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingUSize___closed__8_value) as *mut LeanObject;
pub static l_Lean_Grind_instCommRingUSize___closed__9_value: LeanCtorObject<6> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 6
            + 0) as u16,
        other: 6,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Grind_instCommRingUSize___closed__2_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_instCommRingUSize___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_USize_natCast___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_instCommRingUSize___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_instCommRingUSize___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_instCommRingUSize___closed__5_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Grind_instCommRingUSize___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingUSize___closed__9_value) as *mut LeanObject;
pub static l_Lean_Grind_instCommRingUSize___closed__10_value: LeanCtorObject<5> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Grind_instCommRingUSize___closed__9_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_instCommRingUSize___closed__6_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_instCommRingUSize___closed__7_value) as *mut LeanObject,
        core::ptr::addr_of!(l_USize_intCast___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_instCommRingUSize___closed__1_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Grind_instCommRingUSize___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingUSize___closed__10_value) as *mut LeanObject;
pub static mut l_Lean_Grind_instCommRingUSize: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingUSize___closed__10_value) as *mut LeanObject;
pub unsafe fn l_Lean_Grind_instCommRingUInt8___lam__0(
    mut v_x1_251_: *mut LeanObject,
    mut v_x2_252_: u8,
) -> u8 {
    let mut v___x_253_: u8 = 0;
    let mut v___x_254_: u8 = 0;
    v___x_253_ = lean_uint8_of_nat(v_x1_251_);
    v___x_254_ = lean_uint8_mul(v___x_253_, v_x2_252_);
    return v___x_254_;
}
pub unsafe fn l_Lean_Grind_instCommRingUInt8___lam__0___boxed(
    mut v_x1_255_: *mut LeanObject,
    mut v_x2_256_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x2_64__boxed_257_: u8 = 0;
    let mut v_res_258_: u8 = 0;
    let mut v_r_259_: *mut LeanObject = core::ptr::null_mut();
    v_x2_64__boxed_257_ = (lean_unbox(v_x2_256_) as u8);
    v_res_258_ = l_Lean_Grind_instCommRingUInt8___lam__0(v_x1_255_, v_x2_64__boxed_257_);
    lean_dec(v_x1_255_);
    v_r_259_ = lean_box((v_res_258_) as usize);
    return v_r_259_;
}
pub unsafe fn l_Lean_Grind_instCommRingUInt8___lam__1(
    mut v_x1_260_: *mut LeanObject,
    mut v_x2_261_: u8,
) -> u8 {
    let mut v___x_262_: u8 = 0;
    let mut v___x_263_: u8 = 0;
    v___x_262_ = l_UInt8_ofInt(v_x1_260_);
    v___x_263_ = lean_uint8_mul(v___x_262_, v_x2_261_);
    return v___x_263_;
}
pub unsafe fn l_Lean_Grind_instCommRingUInt8___lam__1___boxed(
    mut v_x1_264_: *mut LeanObject,
    mut v_x2_265_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x2_74__boxed_266_: u8 = 0;
    let mut v_res_267_: u8 = 0;
    let mut v_r_268_: *mut LeanObject = core::ptr::null_mut();
    v_x2_74__boxed_266_ = (lean_unbox(v_x2_265_) as u8);
    v_res_267_ = l_Lean_Grind_instCommRingUInt8___lam__1(v_x1_264_, v_x2_74__boxed_266_);
    lean_dec(v_x1_264_);
    v_r_268_ = lean_box((v_res_267_) as usize);
    return v_r_268_;
}
pub unsafe fn l_Lean_Grind_instCommRingUInt16___lam__0(
    mut v_x1_293_: *mut LeanObject,
    mut v_x2_294_: u16,
) -> u16 {
    let mut v___x_295_: u16 = 0;
    let mut v___x_296_: u16 = 0;
    v___x_295_ = lean_uint16_of_nat(v_x1_293_);
    v___x_296_ = lean_uint16_mul(v___x_295_, v_x2_294_);
    return v___x_296_;
}
pub unsafe fn l_Lean_Grind_instCommRingUInt16___lam__0___boxed(
    mut v_x1_297_: *mut LeanObject,
    mut v_x2_298_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x2_64__boxed_299_: u16 = 0;
    let mut v_res_300_: u16 = 0;
    let mut v_r_301_: *mut LeanObject = core::ptr::null_mut();
    v_x2_64__boxed_299_ = (lean_unbox(v_x2_298_) as u16);
    v_res_300_ = l_Lean_Grind_instCommRingUInt16___lam__0(v_x1_297_, v_x2_64__boxed_299_);
    lean_dec(v_x1_297_);
    v_r_301_ = lean_box((v_res_300_) as usize);
    return v_r_301_;
}
pub unsafe fn l_Lean_Grind_instCommRingUInt16___lam__1(
    mut v_x1_302_: *mut LeanObject,
    mut v_x2_303_: u16,
) -> u16 {
    let mut v___x_304_: u16 = 0;
    let mut v___x_305_: u16 = 0;
    v___x_304_ = l_UInt16_ofInt(v_x1_302_);
    v___x_305_ = lean_uint16_mul(v___x_304_, v_x2_303_);
    return v___x_305_;
}
pub unsafe fn l_Lean_Grind_instCommRingUInt16___lam__1___boxed(
    mut v_x1_306_: *mut LeanObject,
    mut v_x2_307_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x2_74__boxed_308_: u16 = 0;
    let mut v_res_309_: u16 = 0;
    let mut v_r_310_: *mut LeanObject = core::ptr::null_mut();
    v_x2_74__boxed_308_ = (lean_unbox(v_x2_307_) as u16);
    v_res_309_ = l_Lean_Grind_instCommRingUInt16___lam__1(v_x1_306_, v_x2_74__boxed_308_);
    lean_dec(v_x1_306_);
    v_r_310_ = lean_box((v_res_309_) as usize);
    return v_r_310_;
}
pub unsafe fn l_Lean_Grind_instCommRingUInt32___lam__0(
    mut v_x1_335_: *mut LeanObject,
    mut v_x2_336_: u32,
) -> u32 {
    let mut v___x_337_: u32 = 0;
    let mut v___x_338_: u32 = 0;
    v___x_337_ = lean_uint32_of_nat(v_x1_335_);
    v___x_338_ = lean_uint32_mul(v___x_337_, v_x2_336_);
    return v___x_338_;
}
pub unsafe fn l_Lean_Grind_instCommRingUInt32___lam__0___boxed(
    mut v_x1_339_: *mut LeanObject,
    mut v_x2_340_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x2_64__boxed_341_: u32 = 0;
    let mut v_res_342_: u32 = 0;
    let mut v_r_343_: *mut LeanObject = core::ptr::null_mut();
    v_x2_64__boxed_341_ = lean_unbox_uint32(v_x2_340_);
    lean_dec(v_x2_340_);
    v_res_342_ = l_Lean_Grind_instCommRingUInt32___lam__0(v_x1_339_, v_x2_64__boxed_341_);
    lean_dec(v_x1_339_);
    v_r_343_ = lean_box_uint32(v_res_342_);
    return v_r_343_;
}
pub unsafe fn l_Lean_Grind_instCommRingUInt32___lam__1(
    mut v_x1_344_: *mut LeanObject,
    mut v_x2_345_: u32,
) -> u32 {
    let mut v___x_346_: u32 = 0;
    let mut v___x_347_: u32 = 0;
    v___x_346_ = l_UInt32_ofInt(v_x1_344_);
    v___x_347_ = lean_uint32_mul(v___x_346_, v_x2_345_);
    return v___x_347_;
}
pub unsafe fn l_Lean_Grind_instCommRingUInt32___lam__1___boxed(
    mut v_x1_348_: *mut LeanObject,
    mut v_x2_349_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x2_74__boxed_350_: u32 = 0;
    let mut v_res_351_: u32 = 0;
    let mut v_r_352_: *mut LeanObject = core::ptr::null_mut();
    v_x2_74__boxed_350_ = lean_unbox_uint32(v_x2_349_);
    lean_dec(v_x2_349_);
    v_res_351_ = l_Lean_Grind_instCommRingUInt32___lam__1(v_x1_348_, v_x2_74__boxed_350_);
    lean_dec(v_x1_348_);
    v_r_352_ = lean_box_uint32(v_res_351_);
    return v_r_352_;
}
pub unsafe fn l_Lean_Grind_instCommRingUInt64___lam__0(
    mut v_x1_377_: *mut LeanObject,
    mut v_x2_378_: u64,
) -> u64 {
    let mut v___x_379_: u64 = 0;
    let mut v___x_380_: u64 = 0;
    v___x_379_ = lean_uint64_of_nat(v_x1_377_);
    v___x_380_ = lean_uint64_mul(v___x_379_, v_x2_378_);
    return v___x_380_;
}
pub unsafe fn l_Lean_Grind_instCommRingUInt64___lam__0___boxed(
    mut v_x1_381_: *mut LeanObject,
    mut v_x2_382_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x2_64__boxed_383_: u64 = 0;
    let mut v_res_384_: u64 = 0;
    let mut v_r_385_: *mut LeanObject = core::ptr::null_mut();
    v_x2_64__boxed_383_ = lean_unbox_uint64(v_x2_382_);
    lean_dec_ref(v_x2_382_);
    v_res_384_ = l_Lean_Grind_instCommRingUInt64___lam__0(v_x1_381_, v_x2_64__boxed_383_);
    lean_dec(v_x1_381_);
    v_r_385_ = lean_box_uint64(v_res_384_);
    return v_r_385_;
}
pub unsafe fn l_Lean_Grind_instCommRingUInt64___lam__1(
    mut v_x1_386_: *mut LeanObject,
    mut v_x2_387_: u64,
) -> u64 {
    let mut v___x_388_: u64 = 0;
    let mut v___x_389_: u64 = 0;
    v___x_388_ = l_UInt64_ofInt(v_x1_386_);
    v___x_389_ = lean_uint64_mul(v___x_388_, v_x2_387_);
    return v___x_389_;
}
pub unsafe fn l_Lean_Grind_instCommRingUInt64___lam__1___boxed(
    mut v_x1_390_: *mut LeanObject,
    mut v_x2_391_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x2_74__boxed_392_: u64 = 0;
    let mut v_res_393_: u64 = 0;
    let mut v_r_394_: *mut LeanObject = core::ptr::null_mut();
    v_x2_74__boxed_392_ = lean_unbox_uint64(v_x2_391_);
    lean_dec_ref(v_x2_391_);
    v_res_393_ = l_Lean_Grind_instCommRingUInt64___lam__1(v_x1_390_, v_x2_74__boxed_392_);
    lean_dec(v_x1_390_);
    v_r_394_ = lean_box_uint64(v_res_393_);
    return v_r_394_;
}
pub unsafe fn l_Lean_Grind_instCommRingUSize___lam__0(
    mut v_x1_419_: *mut LeanObject,
    mut v_x2_420_: usize,
) -> usize {
    let mut v___x_421_: usize = 0;
    let mut v___x_422_: usize = 0;
    v___x_421_ = lean_usize_of_nat(v_x1_419_);
    v___x_422_ = lean_usize_mul(v___x_421_, v_x2_420_);
    return v___x_422_;
}
pub unsafe fn l_Lean_Grind_instCommRingUSize___lam__0___boxed(
    mut v_x1_423_: *mut LeanObject,
    mut v_x2_424_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x2_64__boxed_425_: usize = 0;
    let mut v_res_426_: usize = 0;
    let mut v_r_427_: *mut LeanObject = core::ptr::null_mut();
    v_x2_64__boxed_425_ = lean_unbox_usize(v_x2_424_);
    lean_dec(v_x2_424_);
    v_res_426_ = l_Lean_Grind_instCommRingUSize___lam__0(v_x1_423_, v_x2_64__boxed_425_);
    lean_dec(v_x1_423_);
    v_r_427_ = lean_box_usize(v_res_426_);
    return v_r_427_;
}
pub unsafe fn l_Lean_Grind_instCommRingUSize___lam__1(
    mut v_x1_428_: *mut LeanObject,
    mut v_x2_429_: usize,
) -> usize {
    let mut v___x_430_: usize = 0;
    let mut v___x_431_: usize = 0;
    v___x_430_ = l_USize_ofInt(v_x1_428_);
    v___x_431_ = lean_usize_mul(v___x_430_, v_x2_429_);
    return v___x_431_;
}
pub unsafe fn l_Lean_Grind_instCommRingUSize___lam__1___boxed(
    mut v_x1_432_: *mut LeanObject,
    mut v_x2_433_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x2_74__boxed_434_: usize = 0;
    let mut v_res_435_: usize = 0;
    let mut v_r_436_: *mut LeanObject = core::ptr::null_mut();
    v_x2_74__boxed_434_ = lean_unbox_usize(v_x2_433_);
    lean_dec(v_x2_433_);
    v_res_435_ = l_Lean_Grind_instCommRingUSize___lam__1(v_x1_432_, v_x2_74__boxed_434_);
    lean_dec(v_x1_432_);
    v_r_436_ = lean_box_usize(v_res_435_);
    return v_r_436_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_GrindInstances_Ring_UInt(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_GrindInstances_ToInt(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_UInt_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_UInt_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_Ring_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_Ring_ToInt(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_GrindInstances_Ring_UInt(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_GrindInstances_Ring_UInt(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_GrindInstances_ToInt(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_UInt_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_UInt_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Grind_Ring_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Grind_Ring_ToInt(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_GrindInstances_Ring_UInt(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_GrindInstances_Ring_UInt(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_GrindInstances_Ring_UInt(builtin);
}
