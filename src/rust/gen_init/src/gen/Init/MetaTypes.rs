// Lean compiler output
// Module: Init.MetaTypes
// Imports: Init.Core
use crate::r#gen::Init::Core::{initialize_Init_Core, runtime_initialize_Init_Core};
use crate::r#gen::Init::Prelude::{l_instDecidableEqList___redArg, l_instDecidableEqNat___boxed};
use crate::ffi::lean_nat_dec_eq;
pub static l_Lean_instInhabitedNameGenerator_default___closed__0_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [95, 117, 110, 105, 113, 0],
};
static mut l_Lean_instInhabitedNameGenerator_default___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedNameGenerator_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instInhabitedNameGenerator_default___closed__1_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_instInhabitedNameGenerator_default___closed__0_value)
            as *mut crate::leanh::LeanObject,
        3978731030111751661 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_instInhabitedNameGenerator_default___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedNameGenerator_default___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instInhabitedNameGenerator_default___closed__2_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_instInhabitedNameGenerator_default___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_instInhabitedNameGenerator_default___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedNameGenerator_default___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_instInhabitedNameGenerator_default: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedNameGenerator_default___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_instInhabitedNameGenerator: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedNameGenerator_default___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_instInhabitedTransparencyMode_default: u8 = 0;
pub static mut l_Lean_Meta_instInhabitedTransparencyMode: u8 = 0;
pub static l_Lean_Meta_instBEqTransparencyMode___closed__0_value: crate::leanh::LeanClosureObject<
    0,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Meta_instBEqTransparencyMode_beq___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_instBEqTransparencyMode___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instBEqTransparencyMode___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_instBEqTransparencyMode: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instBEqTransparencyMode___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_instInhabitedEtaStructMode_default: u8 = 0;
pub static mut l_Lean_Meta_instInhabitedEtaStructMode: u8 = 0;
pub static l_Lean_Meta_instBEqEtaStructMode___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_instBEqEtaStructMode_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_instBEqEtaStructMode___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instBEqEtaStructMode___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_instBEqEtaStructMode: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instBEqEtaStructMode___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_DSimp_instInhabitedConfig_default___closed__0_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0
            + 16) as u16,
        other: 0,
        tag: 0,
    },
    m_objs: [
        1103806660865 as *mut crate::leanh::LeanObject,
        1103823372289 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_DSimp_instInhabitedConfig_default___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_DSimp_instInhabitedConfig_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_DSimp_instInhabitedConfig_default: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_DSimp_instInhabitedConfig_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_DSimp_instInhabitedConfig: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_DSimp_instInhabitedConfig_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_DSimp_instBEqConfig___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_DSimp_instBEqConfig_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_DSimp_instBEqConfig___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_DSimp_instBEqConfig___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_DSimp_instBEqConfig: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_DSimp_instBEqConfig___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_Simp_defaultMaxSteps: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Simp_instInhabitedConfig_default___closed__0_value:
    crate::leanh::LeanCtorObject<7> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
            + 32) as u16,
        other: 3,
        tag: 0,
    },
    m_objs: [
        (((100000 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((2 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        72058697861300480 as *mut crate::leanh::LeanObject,
        1103806595073 as *mut crate::leanh::LeanObject,
        72340172838076672 as *mut crate::leanh::LeanObject,
        257 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Simp_instInhabitedConfig_default___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_instInhabitedConfig_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_Simp_instInhabitedConfig_default: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_instInhabitedConfig_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_Simp_instInhabitedConfig: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_instInhabitedConfig_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Simp_instBEqConfig___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_Simp_instBEqConfig_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Simp_instBEqConfig___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_instBEqConfig___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_Simp_instBEqConfig: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_instBEqConfig___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Simp_neutralConfig___closed__0_value: crate::leanh::LeanCtorObject<7> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 32) as u16,
            other: 3,
            tag: 0,
        },
        m_objs: [
            (((100000 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((2 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            256 as *mut crate::leanh::LeanObject,
            1103806595072 as *mut crate::leanh::LeanObject,
            72058697844588800 as *mut crate::leanh::LeanObject,
            257 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Simp_neutralConfig___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_neutralConfig___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_Simp_neutralConfig: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_neutralConfig___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_instInhabitedOccurrences_default: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_instInhabitedOccurrences: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_instBEqOccurrences___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_instBEqOccurrences_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_instBEqOccurrences___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instBEqOccurrences___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_instBEqOccurrences: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instBEqOccurrences___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_instCoeListNatOccurrences___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Meta_instCoeListNatOccurrences___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_instCoeListNatOccurrences___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instCoeListNatOccurrences___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_instCoeListNatOccurrences: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instCoeListNatOccurrences___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_Meta_TransparencyMode_ctorIdx(
    mut v_x_488_: u8,
) -> *mut crate::leanh::LeanObject {
    match v_x_488_ {
        0 => {
            let mut v___x_489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_489_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_489_;
        }
        1 => {
            let mut v___x_490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_490_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_490_;
        }
        2 => {
            let mut v___x_491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_491_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_491_;
        }
        3 => {
            let mut v___x_492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_492_ = crate::leanh::lean_unsigned_to_nat(3);
            return v___x_492_;
        }
        _ => {
            let mut v___x_493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_493_ = crate::leanh::lean_unsigned_to_nat(4);
            return v___x_493_;
        }
    }
}
pub unsafe fn l_Lean_Meta_TransparencyMode_ctorIdx___boxed(
    mut v_x_494_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_495_: u8 = 0;
    let mut v_res_496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_495_ = (crate::leanh::lean_unbox(v_x_494_) as u8);
    v_res_496_ = l_Lean_Meta_TransparencyMode_ctorIdx(v_x_boxed_495_);
    return v_res_496_;
}
pub unsafe fn l_Lean_Meta_TransparencyMode_toCtorIdx(
    mut v_x_497_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_498_ = l_Lean_Meta_TransparencyMode_ctorIdx(v_x_497_);
    return v___x_498_;
}
pub unsafe fn l_Lean_Meta_TransparencyMode_toCtorIdx___boxed(
    mut v_x_499_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_4__boxed_500_: u8 = 0;
    let mut v_res_501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_4__boxed_500_ = (crate::leanh::lean_unbox(v_x_499_) as u8);
    v_res_501_ = l_Lean_Meta_TransparencyMode_toCtorIdx(v_x_4__boxed_500_);
    return v_res_501_;
}
pub unsafe fn l_Lean_Meta_TransparencyMode_ctorElim___redArg(
    mut v_k_502_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_502_);
    return v_k_502_;
}
pub unsafe fn l_Lean_Meta_TransparencyMode_ctorElim___redArg___boxed(
    mut v_k_503_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_504_ = l_Lean_Meta_TransparencyMode_ctorElim___redArg(v_k_503_);
    crate::leanh::lean_dec(v_k_503_);
    return v_res_504_;
}
pub unsafe fn l_Lean_Meta_TransparencyMode_ctorElim(
    mut v_motive_505_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_506_: *mut crate::leanh::LeanObject,
    mut v_t_507_: u8,
    mut v_h_508_: *mut crate::leanh::LeanObject,
    mut v_k_509_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_509_);
    return v_k_509_;
}
pub unsafe fn l_Lean_Meta_TransparencyMode_ctorElim___boxed(
    mut v_motive_510_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_511_: *mut crate::leanh::LeanObject,
    mut v_t_512_: *mut crate::leanh::LeanObject,
    mut v_h_513_: *mut crate::leanh::LeanObject,
    mut v_k_514_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_515_: u8 = 0;
    let mut v_res_516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_515_ = (crate::leanh::lean_unbox(v_t_512_) as u8);
    v_res_516_ = l_Lean_Meta_TransparencyMode_ctorElim(
        v_motive_510_,
        v_ctorIdx_511_,
        v_t_boxed_515_,
        v_h_513_,
        v_k_514_,
    );
    crate::leanh::lean_dec(v_k_514_);
    crate::leanh::lean_dec(v_ctorIdx_511_);
    return v_res_516_;
}
pub unsafe fn l_Lean_Meta_TransparencyMode_all_elim___redArg(
    mut v_all_517_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_all_517_);
    return v_all_517_;
}
pub unsafe fn l_Lean_Meta_TransparencyMode_all_elim___redArg___boxed(
    mut v_all_518_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_519_ = l_Lean_Meta_TransparencyMode_all_elim___redArg(v_all_518_);
    crate::leanh::lean_dec(v_all_518_);
    return v_res_519_;
}
pub unsafe fn l_Lean_Meta_TransparencyMode_all_elim(
    mut v_motive_520_: *mut crate::leanh::LeanObject,
    mut v_t_521_: u8,
    mut v_h_522_: *mut crate::leanh::LeanObject,
    mut v_all_523_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_all_523_);
    return v_all_523_;
}
pub unsafe fn l_Lean_Meta_TransparencyMode_all_elim___boxed(
    mut v_motive_524_: *mut crate::leanh::LeanObject,
    mut v_t_525_: *mut crate::leanh::LeanObject,
    mut v_h_526_: *mut crate::leanh::LeanObject,
    mut v_all_527_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_528_: u8 = 0;
    let mut v_res_529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_528_ = (crate::leanh::lean_unbox(v_t_525_) as u8);
    v_res_529_ =
        l_Lean_Meta_TransparencyMode_all_elim(v_motive_524_, v_t_boxed_528_, v_h_526_, v_all_527_);
    crate::leanh::lean_dec(v_all_527_);
    return v_res_529_;
}
pub unsafe fn l_Lean_Meta_TransparencyMode_default_elim___redArg(
    mut v_default_530_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_default_530_);
    return v_default_530_;
}
pub unsafe fn l_Lean_Meta_TransparencyMode_default_elim___redArg___boxed(
    mut v_default_531_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_532_ = l_Lean_Meta_TransparencyMode_default_elim___redArg(v_default_531_);
    crate::leanh::lean_dec(v_default_531_);
    return v_res_532_;
}
pub unsafe fn l_Lean_Meta_TransparencyMode_default_elim(
    mut v_motive_533_: *mut crate::leanh::LeanObject,
    mut v_t_534_: u8,
    mut v_h_535_: *mut crate::leanh::LeanObject,
    mut v_default_536_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_default_536_);
    return v_default_536_;
}
pub unsafe fn l_Lean_Meta_TransparencyMode_default_elim___boxed(
    mut v_motive_537_: *mut crate::leanh::LeanObject,
    mut v_t_538_: *mut crate::leanh::LeanObject,
    mut v_h_539_: *mut crate::leanh::LeanObject,
    mut v_default_540_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_541_: u8 = 0;
    let mut v_res_542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_541_ = (crate::leanh::lean_unbox(v_t_538_) as u8);
    v_res_542_ = l_Lean_Meta_TransparencyMode_default_elim(
        v_motive_537_,
        v_t_boxed_541_,
        v_h_539_,
        v_default_540_,
    );
    crate::leanh::lean_dec(v_default_540_);
    return v_res_542_;
}
pub unsafe fn l_Lean_Meta_TransparencyMode_reducible_elim___redArg(
    mut v_reducible_543_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_reducible_543_);
    return v_reducible_543_;
}
pub unsafe fn l_Lean_Meta_TransparencyMode_reducible_elim___redArg___boxed(
    mut v_reducible_544_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_545_ = l_Lean_Meta_TransparencyMode_reducible_elim___redArg(v_reducible_544_);
    crate::leanh::lean_dec(v_reducible_544_);
    return v_res_545_;
}
pub unsafe fn l_Lean_Meta_TransparencyMode_reducible_elim(
    mut v_motive_546_: *mut crate::leanh::LeanObject,
    mut v_t_547_: u8,
    mut v_h_548_: *mut crate::leanh::LeanObject,
    mut v_reducible_549_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_reducible_549_);
    return v_reducible_549_;
}
pub unsafe fn l_Lean_Meta_TransparencyMode_reducible_elim___boxed(
    mut v_motive_550_: *mut crate::leanh::LeanObject,
    mut v_t_551_: *mut crate::leanh::LeanObject,
    mut v_h_552_: *mut crate::leanh::LeanObject,
    mut v_reducible_553_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_554_: u8 = 0;
    let mut v_res_555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_554_ = (crate::leanh::lean_unbox(v_t_551_) as u8);
    v_res_555_ = l_Lean_Meta_TransparencyMode_reducible_elim(
        v_motive_550_,
        v_t_boxed_554_,
        v_h_552_,
        v_reducible_553_,
    );
    crate::leanh::lean_dec(v_reducible_553_);
    return v_res_555_;
}
pub unsafe fn l_Lean_Meta_TransparencyMode_instances_elim___redArg(
    mut v_instances_556_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_instances_556_);
    return v_instances_556_;
}
pub unsafe fn l_Lean_Meta_TransparencyMode_instances_elim___redArg___boxed(
    mut v_instances_557_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_558_ = l_Lean_Meta_TransparencyMode_instances_elim___redArg(v_instances_557_);
    crate::leanh::lean_dec(v_instances_557_);
    return v_res_558_;
}
pub unsafe fn l_Lean_Meta_TransparencyMode_instances_elim(
    mut v_motive_559_: *mut crate::leanh::LeanObject,
    mut v_t_560_: u8,
    mut v_h_561_: *mut crate::leanh::LeanObject,
    mut v_instances_562_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_instances_562_);
    return v_instances_562_;
}
pub unsafe fn l_Lean_Meta_TransparencyMode_instances_elim___boxed(
    mut v_motive_563_: *mut crate::leanh::LeanObject,
    mut v_t_564_: *mut crate::leanh::LeanObject,
    mut v_h_565_: *mut crate::leanh::LeanObject,
    mut v_instances_566_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_567_: u8 = 0;
    let mut v_res_568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_567_ = (crate::leanh::lean_unbox(v_t_564_) as u8);
    v_res_568_ = l_Lean_Meta_TransparencyMode_instances_elim(
        v_motive_563_,
        v_t_boxed_567_,
        v_h_565_,
        v_instances_566_,
    );
    crate::leanh::lean_dec(v_instances_566_);
    return v_res_568_;
}
pub unsafe fn l_Lean_Meta_TransparencyMode_none_elim___redArg(
    mut v_none_569_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_none_569_);
    return v_none_569_;
}
pub unsafe fn l_Lean_Meta_TransparencyMode_none_elim___redArg___boxed(
    mut v_none_570_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_571_ = l_Lean_Meta_TransparencyMode_none_elim___redArg(v_none_570_);
    crate::leanh::lean_dec(v_none_570_);
    return v_res_571_;
}
pub unsafe fn l_Lean_Meta_TransparencyMode_none_elim(
    mut v_motive_572_: *mut crate::leanh::LeanObject,
    mut v_t_573_: u8,
    mut v_h_574_: *mut crate::leanh::LeanObject,
    mut v_none_575_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_none_575_);
    return v_none_575_;
}
pub unsafe fn l_Lean_Meta_TransparencyMode_none_elim___boxed(
    mut v_motive_576_: *mut crate::leanh::LeanObject,
    mut v_t_577_: *mut crate::leanh::LeanObject,
    mut v_h_578_: *mut crate::leanh::LeanObject,
    mut v_none_579_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_580_: u8 = 0;
    let mut v_res_581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_580_ = (crate::leanh::lean_unbox(v_t_577_) as u8);
    v_res_581_ = l_Lean_Meta_TransparencyMode_none_elim(
        v_motive_576_,
        v_t_boxed_580_,
        v_h_578_,
        v_none_579_,
    );
    crate::leanh::lean_dec(v_none_579_);
    return v_res_581_;
}
pub unsafe fn _init_l_Lean_Meta_instInhabitedTransparencyMode_default() -> u8 {
    let mut v___x_582_: u8 = 0;
    v___x_582_ = 0;
    return v___x_582_;
}
pub unsafe fn _init_l_Lean_Meta_instInhabitedTransparencyMode() -> u8 {
    let mut v___x_583_: u8 = 0;
    v___x_583_ = 0;
    return v___x_583_;
}
pub unsafe fn l_Lean_Meta_instBEqTransparencyMode_beq(mut v_x_584_: u8, mut v_y_585_: u8) -> u8 {
    let mut v___x_586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_588_: u8 = 0;
    v___x_586_ = l_Lean_Meta_TransparencyMode_ctorIdx(v_x_584_);
    v___x_587_ = l_Lean_Meta_TransparencyMode_ctorIdx(v_y_585_);
    v___x_588_ = lean_nat_dec_eq(v___x_586_, v___x_587_);
    crate::leanh::lean_dec(v___x_587_);
    crate::leanh::lean_dec(v___x_586_);
    return v___x_588_;
}
pub unsafe fn l_Lean_Meta_instBEqTransparencyMode_beq___boxed(
    mut v_x_589_: *mut crate::leanh::LeanObject,
    mut v_y_590_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_17__boxed_591_: u8 = 0;
    let mut v_y_18__boxed_592_: u8 = 0;
    let mut v_res_593_: u8 = 0;
    let mut v_r_594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_17__boxed_591_ = (crate::leanh::lean_unbox(v_x_589_) as u8);
    v_y_18__boxed_592_ = (crate::leanh::lean_unbox(v_y_590_) as u8);
    v_res_593_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_x_17__boxed_591_, v_y_18__boxed_592_);
    v_r_594_ = crate::leanh::lean_box((v_res_593_) as usize);
    return v_r_594_;
}
pub unsafe fn l_Lean_Meta_EtaStructMode_ctorIdx(mut v_x_597_: u8) -> *mut crate::leanh::LeanObject {
    match v_x_597_ {
        0 => {
            let mut v___x_598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_598_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_598_;
        }
        1 => {
            let mut v___x_599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_599_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_599_;
        }
        _ => {
            let mut v___x_600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_600_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_600_;
        }
    }
}
pub unsafe fn l_Lean_Meta_EtaStructMode_ctorIdx___boxed(
    mut v_x_601_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_602_: u8 = 0;
    let mut v_res_603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_602_ = (crate::leanh::lean_unbox(v_x_601_) as u8);
    v_res_603_ = l_Lean_Meta_EtaStructMode_ctorIdx(v_x_boxed_602_);
    return v_res_603_;
}
pub unsafe fn l_Lean_Meta_EtaStructMode_toCtorIdx(
    mut v_x_604_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_605_ = l_Lean_Meta_EtaStructMode_ctorIdx(v_x_604_);
    return v___x_605_;
}
pub unsafe fn l_Lean_Meta_EtaStructMode_toCtorIdx___boxed(
    mut v_x_606_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_4__boxed_607_: u8 = 0;
    let mut v_res_608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_4__boxed_607_ = (crate::leanh::lean_unbox(v_x_606_) as u8);
    v_res_608_ = l_Lean_Meta_EtaStructMode_toCtorIdx(v_x_4__boxed_607_);
    return v_res_608_;
}
pub unsafe fn l_Lean_Meta_EtaStructMode_ctorElim___redArg(
    mut v_k_609_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_609_);
    return v_k_609_;
}
pub unsafe fn l_Lean_Meta_EtaStructMode_ctorElim___redArg___boxed(
    mut v_k_610_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_611_ = l_Lean_Meta_EtaStructMode_ctorElim___redArg(v_k_610_);
    crate::leanh::lean_dec(v_k_610_);
    return v_res_611_;
}
pub unsafe fn l_Lean_Meta_EtaStructMode_ctorElim(
    mut v_motive_612_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_613_: *mut crate::leanh::LeanObject,
    mut v_t_614_: u8,
    mut v_h_615_: *mut crate::leanh::LeanObject,
    mut v_k_616_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_616_);
    return v_k_616_;
}
pub unsafe fn l_Lean_Meta_EtaStructMode_ctorElim___boxed(
    mut v_motive_617_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_618_: *mut crate::leanh::LeanObject,
    mut v_t_619_: *mut crate::leanh::LeanObject,
    mut v_h_620_: *mut crate::leanh::LeanObject,
    mut v_k_621_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_622_: u8 = 0;
    let mut v_res_623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_622_ = (crate::leanh::lean_unbox(v_t_619_) as u8);
    v_res_623_ = l_Lean_Meta_EtaStructMode_ctorElim(
        v_motive_617_,
        v_ctorIdx_618_,
        v_t_boxed_622_,
        v_h_620_,
        v_k_621_,
    );
    crate::leanh::lean_dec(v_k_621_);
    crate::leanh::lean_dec(v_ctorIdx_618_);
    return v_res_623_;
}
pub unsafe fn l_Lean_Meta_EtaStructMode_all_elim___redArg(
    mut v_all_624_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_all_624_);
    return v_all_624_;
}
pub unsafe fn l_Lean_Meta_EtaStructMode_all_elim___redArg___boxed(
    mut v_all_625_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_626_ = l_Lean_Meta_EtaStructMode_all_elim___redArg(v_all_625_);
    crate::leanh::lean_dec(v_all_625_);
    return v_res_626_;
}
pub unsafe fn l_Lean_Meta_EtaStructMode_all_elim(
    mut v_motive_627_: *mut crate::leanh::LeanObject,
    mut v_t_628_: u8,
    mut v_h_629_: *mut crate::leanh::LeanObject,
    mut v_all_630_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_all_630_);
    return v_all_630_;
}
pub unsafe fn l_Lean_Meta_EtaStructMode_all_elim___boxed(
    mut v_motive_631_: *mut crate::leanh::LeanObject,
    mut v_t_632_: *mut crate::leanh::LeanObject,
    mut v_h_633_: *mut crate::leanh::LeanObject,
    mut v_all_634_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_635_: u8 = 0;
    let mut v_res_636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_635_ = (crate::leanh::lean_unbox(v_t_632_) as u8);
    v_res_636_ =
        l_Lean_Meta_EtaStructMode_all_elim(v_motive_631_, v_t_boxed_635_, v_h_633_, v_all_634_);
    crate::leanh::lean_dec(v_all_634_);
    return v_res_636_;
}
pub unsafe fn l_Lean_Meta_EtaStructMode_notClasses_elim___redArg(
    mut v_notClasses_637_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_notClasses_637_);
    return v_notClasses_637_;
}
pub unsafe fn l_Lean_Meta_EtaStructMode_notClasses_elim___redArg___boxed(
    mut v_notClasses_638_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_639_ = l_Lean_Meta_EtaStructMode_notClasses_elim___redArg(v_notClasses_638_);
    crate::leanh::lean_dec(v_notClasses_638_);
    return v_res_639_;
}
pub unsafe fn l_Lean_Meta_EtaStructMode_notClasses_elim(
    mut v_motive_640_: *mut crate::leanh::LeanObject,
    mut v_t_641_: u8,
    mut v_h_642_: *mut crate::leanh::LeanObject,
    mut v_notClasses_643_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_notClasses_643_);
    return v_notClasses_643_;
}
pub unsafe fn l_Lean_Meta_EtaStructMode_notClasses_elim___boxed(
    mut v_motive_644_: *mut crate::leanh::LeanObject,
    mut v_t_645_: *mut crate::leanh::LeanObject,
    mut v_h_646_: *mut crate::leanh::LeanObject,
    mut v_notClasses_647_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_648_: u8 = 0;
    let mut v_res_649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_648_ = (crate::leanh::lean_unbox(v_t_645_) as u8);
    v_res_649_ = l_Lean_Meta_EtaStructMode_notClasses_elim(
        v_motive_644_,
        v_t_boxed_648_,
        v_h_646_,
        v_notClasses_647_,
    );
    crate::leanh::lean_dec(v_notClasses_647_);
    return v_res_649_;
}
pub unsafe fn l_Lean_Meta_EtaStructMode_none_elim___redArg(
    mut v_none_650_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_none_650_);
    return v_none_650_;
}
pub unsafe fn l_Lean_Meta_EtaStructMode_none_elim___redArg___boxed(
    mut v_none_651_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_652_ = l_Lean_Meta_EtaStructMode_none_elim___redArg(v_none_651_);
    crate::leanh::lean_dec(v_none_651_);
    return v_res_652_;
}
pub unsafe fn l_Lean_Meta_EtaStructMode_none_elim(
    mut v_motive_653_: *mut crate::leanh::LeanObject,
    mut v_t_654_: u8,
    mut v_h_655_: *mut crate::leanh::LeanObject,
    mut v_none_656_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_none_656_);
    return v_none_656_;
}
pub unsafe fn l_Lean_Meta_EtaStructMode_none_elim___boxed(
    mut v_motive_657_: *mut crate::leanh::LeanObject,
    mut v_t_658_: *mut crate::leanh::LeanObject,
    mut v_h_659_: *mut crate::leanh::LeanObject,
    mut v_none_660_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_661_: u8 = 0;
    let mut v_res_662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_661_ = (crate::leanh::lean_unbox(v_t_658_) as u8);
    v_res_662_ =
        l_Lean_Meta_EtaStructMode_none_elim(v_motive_657_, v_t_boxed_661_, v_h_659_, v_none_660_);
    crate::leanh::lean_dec(v_none_660_);
    return v_res_662_;
}
pub unsafe fn _init_l_Lean_Meta_instInhabitedEtaStructMode_default() -> u8 {
    let mut v___x_663_: u8 = 0;
    v___x_663_ = 0;
    return v___x_663_;
}
pub unsafe fn _init_l_Lean_Meta_instInhabitedEtaStructMode() -> u8 {
    let mut v___x_664_: u8 = 0;
    v___x_664_ = 0;
    return v___x_664_;
}
pub unsafe fn l_Lean_Meta_instBEqEtaStructMode_beq(mut v_x_665_: u8, mut v_y_666_: u8) -> u8 {
    let mut v___x_667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_669_: u8 = 0;
    v___x_667_ = l_Lean_Meta_EtaStructMode_ctorIdx(v_x_665_);
    v___x_668_ = l_Lean_Meta_EtaStructMode_ctorIdx(v_y_666_);
    v___x_669_ = lean_nat_dec_eq(v___x_667_, v___x_668_);
    crate::leanh::lean_dec(v___x_668_);
    crate::leanh::lean_dec(v___x_667_);
    return v___x_669_;
}
pub unsafe fn l_Lean_Meta_instBEqEtaStructMode_beq___boxed(
    mut v_x_670_: *mut crate::leanh::LeanObject,
    mut v_y_671_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_17__boxed_672_: u8 = 0;
    let mut v_y_18__boxed_673_: u8 = 0;
    let mut v_res_674_: u8 = 0;
    let mut v_r_675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_17__boxed_672_ = (crate::leanh::lean_unbox(v_x_670_) as u8);
    v_y_18__boxed_673_ = (crate::leanh::lean_unbox(v_y_671_) as u8);
    v_res_674_ = l_Lean_Meta_instBEqEtaStructMode_beq(v_x_17__boxed_672_, v_y_18__boxed_673_);
    v_r_675_ = crate::leanh::lean_box((v_res_674_) as usize);
    return v_r_675_;
}
pub unsafe fn l_Lean_Meta_DSimp_instBEqConfig_beq(
    mut v_x_684_: *mut crate::leanh::LeanObject,
    mut v_x_685_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_zeta_686_: u8 = 0;
    let mut v_beta_687_: u8 = 0;
    let mut v_eta_688_: u8 = 0;
    let mut v_etaStruct_689_: u8 = 0;
    let mut v_iota_690_: u8 = 0;
    let mut v_proj_691_: u8 = 0;
    let mut v_decide_692_: u8 = 0;
    let mut v_autoUnfold_693_: u8 = 0;
    let mut v_failIfUnchanged_694_: u8 = 0;
    let mut v_unfoldPartialApp_695_: u8 = 0;
    let mut v_zetaDelta_696_: u8 = 0;
    let mut v_index_697_: u8 = 0;
    let mut v_zetaUnused_698_: u8 = 0;
    let mut v_zetaHave_699_: u8 = 0;
    let mut v_locals_700_: u8 = 0;
    let mut v_instances_701_: u8 = 0;
    let mut v_zeta_702_: u8 = 0;
    let mut v_beta_703_: u8 = 0;
    let mut v_eta_704_: u8 = 0;
    let mut v_etaStruct_705_: u8 = 0;
    let mut v_iota_706_: u8 = 0;
    let mut v_proj_707_: u8 = 0;
    let mut v_decide_708_: u8 = 0;
    let mut v_autoUnfold_709_: u8 = 0;
    let mut v_failIfUnchanged_710_: u8 = 0;
    let mut v_unfoldPartialApp_711_: u8 = 0;
    let mut v_zetaDelta_712_: u8 = 0;
    let mut v_index_713_: u8 = 0;
    let mut v_zetaUnused_714_: u8 = 0;
    let mut v_zetaHave_715_: u8 = 0;
    let mut v_locals_716_: u8 = 0;
    let mut v_instances_717_: u8 = 0;
    let mut v___y_719_: u8 = 0;
    let mut v___y_721_: u8 = 0;
    let mut v___y_723_: u8 = 0;
    let mut v___y_725_: u8 = 0;
    let mut v___y_727_: u8 = 0;
    let mut v___y_729_: u8 = 0;
    let mut v___y_731_: u8 = 0;
    let mut v___y_733_: u8 = 0;
    let mut v___y_735_: u8 = 0;
    let mut v___y_737_: u8 = 0;
    let mut v___y_739_: u8 = 0;
    let mut v___x_741_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zeta_686_ = crate::leanh::lean_ctor_get_uint8(v_x_684_, 0 as u32);
                v_beta_687_ = crate::leanh::lean_ctor_get_uint8(v_x_684_, 1 as u32);
                v_eta_688_ = crate::leanh::lean_ctor_get_uint8(v_x_684_, 2 as u32);
                v_etaStruct_689_ = crate::leanh::lean_ctor_get_uint8(v_x_684_, 3 as u32);
                v_iota_690_ = crate::leanh::lean_ctor_get_uint8(v_x_684_, 4 as u32);
                v_proj_691_ = crate::leanh::lean_ctor_get_uint8(v_x_684_, 5 as u32);
                v_decide_692_ = crate::leanh::lean_ctor_get_uint8(v_x_684_, 6 as u32);
                v_autoUnfold_693_ = crate::leanh::lean_ctor_get_uint8(v_x_684_, 7 as u32);
                v_failIfUnchanged_694_ = crate::leanh::lean_ctor_get_uint8(v_x_684_, 8 as u32);
                v_unfoldPartialApp_695_ = crate::leanh::lean_ctor_get_uint8(v_x_684_, 9 as u32);
                v_zetaDelta_696_ = crate::leanh::lean_ctor_get_uint8(v_x_684_, 10 as u32);
                v_index_697_ = crate::leanh::lean_ctor_get_uint8(v_x_684_, 11 as u32);
                v_zetaUnused_698_ = crate::leanh::lean_ctor_get_uint8(v_x_684_, 12 as u32);
                v_zetaHave_699_ = crate::leanh::lean_ctor_get_uint8(v_x_684_, 13 as u32);
                v_locals_700_ = crate::leanh::lean_ctor_get_uint8(v_x_684_, 14 as u32);
                v_instances_701_ = crate::leanh::lean_ctor_get_uint8(v_x_684_, 15 as u32);
                v_zeta_702_ = crate::leanh::lean_ctor_get_uint8(v_x_685_, 0 as u32);
                v_beta_703_ = crate::leanh::lean_ctor_get_uint8(v_x_685_, 1 as u32);
                v_eta_704_ = crate::leanh::lean_ctor_get_uint8(v_x_685_, 2 as u32);
                v_etaStruct_705_ = crate::leanh::lean_ctor_get_uint8(v_x_685_, 3 as u32);
                v_iota_706_ = crate::leanh::lean_ctor_get_uint8(v_x_685_, 4 as u32);
                v_proj_707_ = crate::leanh::lean_ctor_get_uint8(v_x_685_, 5 as u32);
                v_decide_708_ = crate::leanh::lean_ctor_get_uint8(v_x_685_, 6 as u32);
                v_autoUnfold_709_ = crate::leanh::lean_ctor_get_uint8(v_x_685_, 7 as u32);
                v_failIfUnchanged_710_ = crate::leanh::lean_ctor_get_uint8(v_x_685_, 8 as u32);
                v_unfoldPartialApp_711_ = crate::leanh::lean_ctor_get_uint8(v_x_685_, 9 as u32);
                v_zetaDelta_712_ = crate::leanh::lean_ctor_get_uint8(v_x_685_, 10 as u32);
                v_index_713_ = crate::leanh::lean_ctor_get_uint8(v_x_685_, 11 as u32);
                v_zetaUnused_714_ = crate::leanh::lean_ctor_get_uint8(v_x_685_, 12 as u32);
                v_zetaHave_715_ = crate::leanh::lean_ctor_get_uint8(v_x_685_, 13 as u32);
                v_locals_716_ = crate::leanh::lean_ctor_get_uint8(v_x_685_, 14 as u32);
                v_instances_717_ = crate::leanh::lean_ctor_get_uint8(v_x_685_, 15 as u32);
                if v_zeta_686_ == 0 {
                    if v_zeta_702_ == 0 {
                        state = 14;
                        continue;
                    } else {
                        return v_zeta_686_;
                    }
                } else {
                    if v_zeta_702_ == 0 {
                        return v_zeta_702_;
                    } else {
                        state = 14;
                        continue;
                    }
                }
            }
            1 => {
                if v_instances_701_ == 0 {
                    if v_instances_717_ == 0 {
                        return v___y_719_;
                    } else {
                        return v_instances_701_;
                    }
                } else {
                    return v_instances_717_;
                }
            }
            2 => {
                if v_locals_700_ == 0 {
                    if v_locals_716_ == 0 {
                        v___y_719_ = v___y_721_;
                        state = 1;
                        continue;
                    } else {
                        return v_locals_700_;
                    }
                } else {
                    if v_locals_716_ == 0 {
                        return v_locals_716_;
                    } else {
                        v___y_719_ = v_locals_716_;
                        state = 1;
                        continue;
                    }
                }
            }
            3 => {
                if v_zetaHave_699_ == 0 {
                    if v_zetaHave_715_ == 0 {
                        v___y_721_ = v___y_723_;
                        state = 2;
                        continue;
                    } else {
                        return v_zetaHave_699_;
                    }
                } else {
                    if v_zetaHave_715_ == 0 {
                        return v_zetaHave_715_;
                    } else {
                        v___y_721_ = v_zetaHave_715_;
                        state = 2;
                        continue;
                    }
                }
            }
            4 => {
                if v_zetaUnused_698_ == 0 {
                    if v_zetaUnused_714_ == 0 {
                        v___y_723_ = v___y_725_;
                        state = 3;
                        continue;
                    } else {
                        return v_zetaUnused_698_;
                    }
                } else {
                    if v_zetaUnused_714_ == 0 {
                        return v_zetaUnused_714_;
                    } else {
                        v___y_723_ = v_zetaUnused_714_;
                        state = 3;
                        continue;
                    }
                }
            }
            5 => {
                if v_index_697_ == 0 {
                    if v_index_713_ == 0 {
                        v___y_725_ = v___y_727_;
                        state = 4;
                        continue;
                    } else {
                        return v_index_697_;
                    }
                } else {
                    if v_index_713_ == 0 {
                        return v_index_713_;
                    } else {
                        v___y_725_ = v_index_713_;
                        state = 4;
                        continue;
                    }
                }
            }
            6 => {
                if v_zetaDelta_696_ == 0 {
                    if v_zetaDelta_712_ == 0 {
                        v___y_727_ = v___y_729_;
                        state = 5;
                        continue;
                    } else {
                        return v_zetaDelta_696_;
                    }
                } else {
                    if v_zetaDelta_712_ == 0 {
                        return v_zetaDelta_712_;
                    } else {
                        v___y_727_ = v_zetaDelta_712_;
                        state = 5;
                        continue;
                    }
                }
            }
            7 => {
                if v_unfoldPartialApp_695_ == 0 {
                    if v_unfoldPartialApp_711_ == 0 {
                        v___y_729_ = v___y_731_;
                        state = 6;
                        continue;
                    } else {
                        return v_unfoldPartialApp_695_;
                    }
                } else {
                    if v_unfoldPartialApp_711_ == 0 {
                        return v_unfoldPartialApp_711_;
                    } else {
                        v___y_729_ = v_unfoldPartialApp_711_;
                        state = 6;
                        continue;
                    }
                }
            }
            8 => {
                if v_failIfUnchanged_694_ == 0 {
                    if v_failIfUnchanged_710_ == 0 {
                        v___y_731_ = v___y_733_;
                        state = 7;
                        continue;
                    } else {
                        return v_failIfUnchanged_694_;
                    }
                } else {
                    if v_failIfUnchanged_710_ == 0 {
                        return v_failIfUnchanged_710_;
                    } else {
                        v___y_731_ = v_failIfUnchanged_710_;
                        state = 7;
                        continue;
                    }
                }
            }
            9 => {
                if v_autoUnfold_693_ == 0 {
                    if v_autoUnfold_709_ == 0 {
                        v___y_733_ = v___y_735_;
                        state = 8;
                        continue;
                    } else {
                        return v_autoUnfold_693_;
                    }
                } else {
                    if v_autoUnfold_709_ == 0 {
                        return v_autoUnfold_709_;
                    } else {
                        v___y_733_ = v_autoUnfold_709_;
                        state = 8;
                        continue;
                    }
                }
            }
            10 => {
                if v_decide_692_ == 0 {
                    if v_decide_708_ == 0 {
                        v___y_735_ = v___y_737_;
                        state = 9;
                        continue;
                    } else {
                        return v_decide_692_;
                    }
                } else {
                    if v_decide_708_ == 0 {
                        return v_decide_708_;
                    } else {
                        v___y_735_ = v_decide_708_;
                        state = 9;
                        continue;
                    }
                }
            }
            11 => {
                if v___y_739_ == 0 {
                    return v___y_739_;
                } else {
                    if v_proj_691_ == 0 {
                        if v_proj_707_ == 0 {
                            v___y_737_ = v___y_739_;
                            state = 10;
                            continue;
                        } else {
                            return v_proj_691_;
                        }
                    } else {
                        if v_proj_707_ == 0 {
                            return v_proj_707_;
                        } else {
                            v___y_737_ = v_proj_707_;
                            state = 10;
                            continue;
                        }
                    }
                }
            }
            12 => {
                v___x_741_ =
                    l_Lean_Meta_instBEqEtaStructMode_beq(v_etaStruct_689_, v_etaStruct_705_);
                if v___x_741_ == 0 {
                    return v___x_741_;
                } else {
                    if v_iota_690_ == 0 {
                        if v_iota_706_ == 0 {
                            v___y_739_ = v___x_741_;
                            state = 11;
                            continue;
                        } else {
                            return v_iota_690_;
                        }
                    } else {
                        v___y_739_ = v_iota_706_;
                        state = 11;
                        continue;
                    }
                }
            }
            13 => {
                if v_eta_688_ == 0 {
                    if v_eta_704_ == 0 {
                        state = 12;
                        continue;
                    } else {
                        return v_eta_688_;
                    }
                } else {
                    if v_eta_704_ == 0 {
                        return v_eta_704_;
                    } else {
                        state = 12;
                        continue;
                    }
                }
            }
            14 => {
                if v_beta_687_ == 0 {
                    if v_beta_703_ == 0 {
                        state = 13;
                        continue;
                    } else {
                        return v_beta_687_;
                    }
                } else {
                    if v_beta_703_ == 0 {
                        return v_beta_703_;
                    } else {
                        state = 13;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_DSimp_instBEqConfig_beq___boxed(
    mut v_x_744_: *mut crate::leanh::LeanObject,
    mut v_x_745_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_746_: u8 = 0;
    let mut v_r_747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_746_ = l_Lean_Meta_DSimp_instBEqConfig_beq(v_x_744_, v_x_745_);
    crate::leanh::lean_dec_ref(v_x_745_);
    crate::leanh::lean_dec_ref(v_x_744_);
    v_r_747_ = crate::leanh::lean_box((v_res_746_) as usize);
    return v_r_747_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_defaultMaxSteps() -> *mut crate::leanh::LeanObject {
    let mut v___x_750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_750_ = crate::leanh::lean_unsigned_to_nat(100000);
    return v___x_750_;
}
pub unsafe fn l_instBEqOption_beq___at___00Lean_Meta_Simp_instBEqConfig_beq_spec__0(
    mut v_x_760_: *mut crate::leanh::LeanObject,
    mut v_x_761_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_760_) == 0 {
        if crate::leanh::lean_obj_tag(v_x_761_) == 0 {
            let mut v___x_762_: u8 = 0;
            v___x_762_ = 1;
            return v___x_762_;
        } else {
            let mut v___x_763_: u8 = 0;
            v___x_763_ = 0;
            return v___x_763_;
        }
    } else {
        if crate::leanh::lean_obj_tag(v_x_761_) == 0 {
            let mut v___x_764_: u8 = 0;
            v___x_764_ = 0;
            return v___x_764_;
        } else {
            let mut v_val_765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_767_: u8 = 0;
            v_val_765_ = crate::leanh::lean_ctor_get(v_x_760_, 0);
            v_val_766_ = crate::leanh::lean_ctor_get(v_x_761_, 0);
            v___x_767_ = lean_nat_dec_eq(v_val_765_, v_val_766_);
            return v___x_767_;
        }
    }
}
pub unsafe fn l_instBEqOption_beq___at___00Lean_Meta_Simp_instBEqConfig_beq_spec__0___boxed(
    mut v_x_768_: *mut crate::leanh::LeanObject,
    mut v_x_769_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_770_: u8 = 0;
    let mut v_r_771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_770_ =
        l_instBEqOption_beq___at___00Lean_Meta_Simp_instBEqConfig_beq_spec__0(v_x_768_, v_x_769_);
    crate::leanh::lean_dec(v_x_769_);
    crate::leanh::lean_dec(v_x_768_);
    v_r_771_ = crate::leanh::lean_box((v_res_770_) as usize);
    return v_r_771_;
}
pub unsafe fn l_Lean_Meta_Simp_instBEqConfig_beq(
    mut v_x_772_: *mut crate::leanh::LeanObject,
    mut v_x_773_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_maxSteps_774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxDischargeDepth_775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_contextual_776_: u8 = 0;
    let mut v_memoize_777_: u8 = 0;
    let mut v_singlePass_778_: u8 = 0;
    let mut v_zeta_779_: u8 = 0;
    let mut v_beta_780_: u8 = 0;
    let mut v_eta_781_: u8 = 0;
    let mut v_etaStruct_782_: u8 = 0;
    let mut v_iota_783_: u8 = 0;
    let mut v_proj_784_: u8 = 0;
    let mut v_decide_785_: u8 = 0;
    let mut v_arith_786_: u8 = 0;
    let mut v_autoUnfold_787_: u8 = 0;
    let mut v_dsimp_788_: u8 = 0;
    let mut v_failIfUnchanged_789_: u8 = 0;
    let mut v_ground_790_: u8 = 0;
    let mut v_unfoldPartialApp_791_: u8 = 0;
    let mut v_zetaDelta_792_: u8 = 0;
    let mut v_index_793_: u8 = 0;
    let mut v_implicitDefEqProofs_794_: u8 = 0;
    let mut v_zetaUnused_795_: u8 = 0;
    let mut v_catchRuntime_796_: u8 = 0;
    let mut v_zetaHave_797_: u8 = 0;
    let mut v_letToHave_798_: u8 = 0;
    let mut v_congrConsts_799_: u8 = 0;
    let mut v_bitVecOfNat_800_: u8 = 0;
    let mut v_warnExponents_801_: u8 = 0;
    let mut v_suggestions_802_: u8 = 0;
    let mut v_maxSuggestions_803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_locals_804_: u8 = 0;
    let mut v_instances_805_: u8 = 0;
    let mut v_maxSteps_806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxDischargeDepth_807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_contextual_808_: u8 = 0;
    let mut v_memoize_809_: u8 = 0;
    let mut v_singlePass_810_: u8 = 0;
    let mut v_zeta_811_: u8 = 0;
    let mut v_beta_812_: u8 = 0;
    let mut v_eta_813_: u8 = 0;
    let mut v_etaStruct_814_: u8 = 0;
    let mut v_iota_815_: u8 = 0;
    let mut v_proj_816_: u8 = 0;
    let mut v_decide_817_: u8 = 0;
    let mut v_arith_818_: u8 = 0;
    let mut v_autoUnfold_819_: u8 = 0;
    let mut v_dsimp_820_: u8 = 0;
    let mut v_failIfUnchanged_821_: u8 = 0;
    let mut v_ground_822_: u8 = 0;
    let mut v_unfoldPartialApp_823_: u8 = 0;
    let mut v_zetaDelta_824_: u8 = 0;
    let mut v_index_825_: u8 = 0;
    let mut v_implicitDefEqProofs_826_: u8 = 0;
    let mut v_zetaUnused_827_: u8 = 0;
    let mut v_catchRuntime_828_: u8 = 0;
    let mut v_zetaHave_829_: u8 = 0;
    let mut v_letToHave_830_: u8 = 0;
    let mut v_congrConsts_831_: u8 = 0;
    let mut v_bitVecOfNat_832_: u8 = 0;
    let mut v_warnExponents_833_: u8 = 0;
    let mut v_suggestions_834_: u8 = 0;
    let mut v_maxSuggestions_835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_locals_836_: u8 = 0;
    let mut v_instances_837_: u8 = 0;
    let mut v___y_839_: u8 = 0;
    let mut v___x_841_: u8 = 0;
    let mut v___y_861_: u8 = 0;
    let mut v___x_863_: u8 = 0;
    let mut v___y_869_: u8 = 0;
    let mut v___x_870_: u8 = 0;
    let mut v___x_871_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_maxSteps_774_ = crate::leanh::lean_ctor_get(v_x_772_, 0);
                v_maxDischargeDepth_775_ = crate::leanh::lean_ctor_get(v_x_772_, 1);
                v_contextual_776_ = crate::leanh::lean_ctor_get_uint8(
                    v_x_772_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_memoize_777_ = crate::leanh::lean_ctor_get_uint8(
                    v_x_772_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                );
                v_singlePass_778_ = crate::leanh::lean_ctor_get_uint8(
                    v_x_772_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 2) as u32,
                );
                v_zeta_779_ = crate::leanh::lean_ctor_get_uint8(
                    v_x_772_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 3) as u32,
                );
                v_beta_780_ = crate::leanh::lean_ctor_get_uint8(
                    v_x_772_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 4) as u32,
                );
                v_eta_781_ = crate::leanh::lean_ctor_get_uint8(
                    v_x_772_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 5) as u32,
                );
                v_etaStruct_782_ = crate::leanh::lean_ctor_get_uint8(
                    v_x_772_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 6) as u32,
                );
                v_iota_783_ = crate::leanh::lean_ctor_get_uint8(
                    v_x_772_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 7) as u32,
                );
                v_proj_784_ = crate::leanh::lean_ctor_get_uint8(
                    v_x_772_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                );
                v_decide_785_ = crate::leanh::lean_ctor_get_uint8(
                    v_x_772_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 9) as u32,
                );
                v_arith_786_ = crate::leanh::lean_ctor_get_uint8(
                    v_x_772_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 10) as u32,
                );
                v_autoUnfold_787_ = crate::leanh::lean_ctor_get_uint8(
                    v_x_772_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 11) as u32,
                );
                v_dsimp_788_ = crate::leanh::lean_ctor_get_uint8(
                    v_x_772_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 12) as u32,
                );
                v_failIfUnchanged_789_ = crate::leanh::lean_ctor_get_uint8(
                    v_x_772_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 13) as u32,
                );
                v_ground_790_ = crate::leanh::lean_ctor_get_uint8(
                    v_x_772_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 14) as u32,
                );
                v_unfoldPartialApp_791_ = crate::leanh::lean_ctor_get_uint8(
                    v_x_772_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 15) as u32,
                );
                v_zetaDelta_792_ = crate::leanh::lean_ctor_get_uint8(
                    v_x_772_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
                );
                v_index_793_ = crate::leanh::lean_ctor_get_uint8(
                    v_x_772_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 17) as u32,
                );
                v_implicitDefEqProofs_794_ = crate::leanh::lean_ctor_get_uint8(
                    v_x_772_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 18) as u32,
                );
                v_zetaUnused_795_ = crate::leanh::lean_ctor_get_uint8(
                    v_x_772_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 19) as u32,
                );
                v_catchRuntime_796_ = crate::leanh::lean_ctor_get_uint8(
                    v_x_772_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 20) as u32,
                );
                v_zetaHave_797_ = crate::leanh::lean_ctor_get_uint8(
                    v_x_772_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 21) as u32,
                );
                v_letToHave_798_ = crate::leanh::lean_ctor_get_uint8(
                    v_x_772_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 22) as u32,
                );
                v_congrConsts_799_ = crate::leanh::lean_ctor_get_uint8(
                    v_x_772_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 23) as u32,
                );
                v_bitVecOfNat_800_ = crate::leanh::lean_ctor_get_uint8(
                    v_x_772_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 24) as u32,
                );
                v_warnExponents_801_ = crate::leanh::lean_ctor_get_uint8(
                    v_x_772_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 25) as u32,
                );
                v_suggestions_802_ = crate::leanh::lean_ctor_get_uint8(
                    v_x_772_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 26) as u32,
                );
                v_maxSuggestions_803_ = crate::leanh::lean_ctor_get(v_x_772_, 2);
                v_locals_804_ = crate::leanh::lean_ctor_get_uint8(
                    v_x_772_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 27) as u32,
                );
                v_instances_805_ = crate::leanh::lean_ctor_get_uint8(
                    v_x_772_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 28) as u32,
                );
                v_maxSteps_806_ = crate::leanh::lean_ctor_get(v_x_773_, 0);
                v_maxDischargeDepth_807_ = crate::leanh::lean_ctor_get(v_x_773_, 1);
                v_contextual_808_ = crate::leanh::lean_ctor_get_uint8(
                    v_x_773_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_memoize_809_ = crate::leanh::lean_ctor_get_uint8(
                    v_x_773_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                );
                v_singlePass_810_ = crate::leanh::lean_ctor_get_uint8(
                    v_x_773_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 2) as u32,
                );
                v_zeta_811_ = crate::leanh::lean_ctor_get_uint8(
                    v_x_773_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 3) as u32,
                );
                v_beta_812_ = crate::leanh::lean_ctor_get_uint8(
                    v_x_773_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 4) as u32,
                );
                v_eta_813_ = crate::leanh::lean_ctor_get_uint8(
                    v_x_773_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 5) as u32,
                );
                v_etaStruct_814_ = crate::leanh::lean_ctor_get_uint8(
                    v_x_773_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 6) as u32,
                );
                v_iota_815_ = crate::leanh::lean_ctor_get_uint8(
                    v_x_773_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 7) as u32,
                );
                v_proj_816_ = crate::leanh::lean_ctor_get_uint8(
                    v_x_773_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                );
                v_decide_817_ = crate::leanh::lean_ctor_get_uint8(
                    v_x_773_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 9) as u32,
                );
                v_arith_818_ = crate::leanh::lean_ctor_get_uint8(
                    v_x_773_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 10) as u32,
                );
                v_autoUnfold_819_ = crate::leanh::lean_ctor_get_uint8(
                    v_x_773_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 11) as u32,
                );
                v_dsimp_820_ = crate::leanh::lean_ctor_get_uint8(
                    v_x_773_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 12) as u32,
                );
                v_failIfUnchanged_821_ = crate::leanh::lean_ctor_get_uint8(
                    v_x_773_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 13) as u32,
                );
                v_ground_822_ = crate::leanh::lean_ctor_get_uint8(
                    v_x_773_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 14) as u32,
                );
                v_unfoldPartialApp_823_ = crate::leanh::lean_ctor_get_uint8(
                    v_x_773_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 15) as u32,
                );
                v_zetaDelta_824_ = crate::leanh::lean_ctor_get_uint8(
                    v_x_773_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
                );
                v_index_825_ = crate::leanh::lean_ctor_get_uint8(
                    v_x_773_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 17) as u32,
                );
                v_implicitDefEqProofs_826_ = crate::leanh::lean_ctor_get_uint8(
                    v_x_773_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 18) as u32,
                );
                v_zetaUnused_827_ = crate::leanh::lean_ctor_get_uint8(
                    v_x_773_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 19) as u32,
                );
                v_catchRuntime_828_ = crate::leanh::lean_ctor_get_uint8(
                    v_x_773_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 20) as u32,
                );
                v_zetaHave_829_ = crate::leanh::lean_ctor_get_uint8(
                    v_x_773_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 21) as u32,
                );
                v_letToHave_830_ = crate::leanh::lean_ctor_get_uint8(
                    v_x_773_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 22) as u32,
                );
                v_congrConsts_831_ = crate::leanh::lean_ctor_get_uint8(
                    v_x_773_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 23) as u32,
                );
                v_bitVecOfNat_832_ = crate::leanh::lean_ctor_get_uint8(
                    v_x_773_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 24) as u32,
                );
                v_warnExponents_833_ = crate::leanh::lean_ctor_get_uint8(
                    v_x_773_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 25) as u32,
                );
                v_suggestions_834_ = crate::leanh::lean_ctor_get_uint8(
                    v_x_773_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 26) as u32,
                );
                v_maxSuggestions_835_ = crate::leanh::lean_ctor_get(v_x_773_, 2);
                v_locals_836_ = crate::leanh::lean_ctor_get_uint8(
                    v_x_773_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 27) as u32,
                );
                v_instances_837_ = crate::leanh::lean_ctor_get_uint8(
                    v_x_773_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 28) as u32,
                );
                v___x_870_ = lean_nat_dec_eq(v_maxSteps_774_, v_maxSteps_806_);
                if v___x_870_ == 0 {
                    return v___x_870_;
                } else {
                    v___x_871_ =
                        lean_nat_dec_eq(v_maxDischargeDepth_775_, v_maxDischargeDepth_807_);
                    if v___x_871_ == 0 {
                        return v___x_871_;
                    } else {
                        if v_contextual_776_ == 0 {
                            if v_contextual_808_ == 0 {
                                v___y_869_ = v___x_871_;
                                state = 27;
                                continue;
                            } else {
                                return v_contextual_776_;
                            }
                        } else {
                            v___y_869_ = v_contextual_808_;
                            state = 27;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v___y_839_ == 0 {
                    return v___y_839_;
                } else {
                    if v_instances_805_ == 0 {
                        if v_instances_837_ == 0 {
                            return v___y_839_;
                        } else {
                            return v_instances_805_;
                        }
                    } else {
                        return v_instances_837_;
                    }
                }
            }
            2 => {
                v___x_841_ = l_instBEqOption_beq___at___00Lean_Meta_Simp_instBEqConfig_beq_spec__0(
                    v_maxSuggestions_803_,
                    v_maxSuggestions_835_,
                );
                if v___x_841_ == 0 {
                    return v___x_841_;
                } else {
                    if v_locals_804_ == 0 {
                        if v_locals_836_ == 0 {
                            v___y_839_ = v___x_841_;
                            state = 1;
                            continue;
                        } else {
                            return v_locals_804_;
                        }
                    } else {
                        v___y_839_ = v_locals_836_;
                        state = 1;
                        continue;
                    }
                }
            }
            3 => {
                if v_suggestions_802_ == 0 {
                    if v_suggestions_834_ == 0 {
                        state = 2;
                        continue;
                    } else {
                        return v_suggestions_802_;
                    }
                } else {
                    if v_suggestions_834_ == 0 {
                        return v_suggestions_834_;
                    } else {
                        state = 2;
                        continue;
                    }
                }
            }
            4 => {
                if v_warnExponents_801_ == 0 {
                    if v_warnExponents_833_ == 0 {
                        state = 3;
                        continue;
                    } else {
                        return v_warnExponents_801_;
                    }
                } else {
                    if v_warnExponents_833_ == 0 {
                        return v_warnExponents_833_;
                    } else {
                        state = 3;
                        continue;
                    }
                }
            }
            5 => {
                if v_bitVecOfNat_800_ == 0 {
                    if v_bitVecOfNat_832_ == 0 {
                        state = 4;
                        continue;
                    } else {
                        return v_bitVecOfNat_800_;
                    }
                } else {
                    if v_bitVecOfNat_832_ == 0 {
                        return v_bitVecOfNat_832_;
                    } else {
                        state = 4;
                        continue;
                    }
                }
            }
            6 => {
                if v_congrConsts_799_ == 0 {
                    if v_congrConsts_831_ == 0 {
                        state = 5;
                        continue;
                    } else {
                        return v_congrConsts_799_;
                    }
                } else {
                    if v_congrConsts_831_ == 0 {
                        return v_congrConsts_831_;
                    } else {
                        state = 5;
                        continue;
                    }
                }
            }
            7 => {
                if v_letToHave_798_ == 0 {
                    if v_letToHave_830_ == 0 {
                        state = 6;
                        continue;
                    } else {
                        return v_letToHave_798_;
                    }
                } else {
                    if v_letToHave_830_ == 0 {
                        return v_letToHave_830_;
                    } else {
                        state = 6;
                        continue;
                    }
                }
            }
            8 => {
                if v_zetaHave_797_ == 0 {
                    if v_zetaHave_829_ == 0 {
                        state = 7;
                        continue;
                    } else {
                        return v_zetaHave_797_;
                    }
                } else {
                    if v_zetaHave_829_ == 0 {
                        return v_zetaHave_829_;
                    } else {
                        state = 7;
                        continue;
                    }
                }
            }
            9 => {
                if v_catchRuntime_796_ == 0 {
                    if v_catchRuntime_828_ == 0 {
                        state = 8;
                        continue;
                    } else {
                        return v_catchRuntime_796_;
                    }
                } else {
                    if v_catchRuntime_828_ == 0 {
                        return v_catchRuntime_828_;
                    } else {
                        state = 8;
                        continue;
                    }
                }
            }
            10 => {
                if v_zetaUnused_795_ == 0 {
                    if v_zetaUnused_827_ == 0 {
                        state = 9;
                        continue;
                    } else {
                        return v_zetaUnused_795_;
                    }
                } else {
                    if v_zetaUnused_827_ == 0 {
                        return v_zetaUnused_827_;
                    } else {
                        state = 9;
                        continue;
                    }
                }
            }
            11 => {
                if v_implicitDefEqProofs_794_ == 0 {
                    if v_implicitDefEqProofs_826_ == 0 {
                        state = 10;
                        continue;
                    } else {
                        return v_implicitDefEqProofs_794_;
                    }
                } else {
                    if v_implicitDefEqProofs_826_ == 0 {
                        return v_implicitDefEqProofs_826_;
                    } else {
                        state = 10;
                        continue;
                    }
                }
            }
            12 => {
                if v_index_793_ == 0 {
                    if v_index_825_ == 0 {
                        state = 11;
                        continue;
                    } else {
                        return v_index_793_;
                    }
                } else {
                    if v_index_825_ == 0 {
                        return v_index_825_;
                    } else {
                        state = 11;
                        continue;
                    }
                }
            }
            13 => {
                if v_zetaDelta_792_ == 0 {
                    if v_zetaDelta_824_ == 0 {
                        state = 12;
                        continue;
                    } else {
                        return v_zetaDelta_792_;
                    }
                } else {
                    if v_zetaDelta_824_ == 0 {
                        return v_zetaDelta_824_;
                    } else {
                        state = 12;
                        continue;
                    }
                }
            }
            14 => {
                if v_unfoldPartialApp_791_ == 0 {
                    if v_unfoldPartialApp_823_ == 0 {
                        state = 13;
                        continue;
                    } else {
                        return v_unfoldPartialApp_791_;
                    }
                } else {
                    if v_unfoldPartialApp_823_ == 0 {
                        return v_unfoldPartialApp_823_;
                    } else {
                        state = 13;
                        continue;
                    }
                }
            }
            15 => {
                if v_ground_790_ == 0 {
                    if v_ground_822_ == 0 {
                        state = 14;
                        continue;
                    } else {
                        return v_ground_790_;
                    }
                } else {
                    if v_ground_822_ == 0 {
                        return v_ground_822_;
                    } else {
                        state = 14;
                        continue;
                    }
                }
            }
            16 => {
                if v_failIfUnchanged_789_ == 0 {
                    if v_failIfUnchanged_821_ == 0 {
                        state = 15;
                        continue;
                    } else {
                        return v_failIfUnchanged_789_;
                    }
                } else {
                    if v_failIfUnchanged_821_ == 0 {
                        return v_failIfUnchanged_821_;
                    } else {
                        state = 15;
                        continue;
                    }
                }
            }
            17 => {
                if v_dsimp_788_ == 0 {
                    if v_dsimp_820_ == 0 {
                        state = 16;
                        continue;
                    } else {
                        return v_dsimp_788_;
                    }
                } else {
                    if v_dsimp_820_ == 0 {
                        return v_dsimp_820_;
                    } else {
                        state = 16;
                        continue;
                    }
                }
            }
            18 => {
                if v_autoUnfold_787_ == 0 {
                    if v_autoUnfold_819_ == 0 {
                        state = 17;
                        continue;
                    } else {
                        return v_autoUnfold_787_;
                    }
                } else {
                    if v_autoUnfold_819_ == 0 {
                        return v_autoUnfold_819_;
                    } else {
                        state = 17;
                        continue;
                    }
                }
            }
            19 => {
                if v_arith_786_ == 0 {
                    if v_arith_818_ == 0 {
                        state = 18;
                        continue;
                    } else {
                        return v_arith_786_;
                    }
                } else {
                    if v_arith_818_ == 0 {
                        return v_arith_818_;
                    } else {
                        state = 18;
                        continue;
                    }
                }
            }
            20 => {
                if v_decide_785_ == 0 {
                    if v_decide_817_ == 0 {
                        state = 19;
                        continue;
                    } else {
                        return v_decide_785_;
                    }
                } else {
                    if v_decide_817_ == 0 {
                        return v_decide_817_;
                    } else {
                        state = 19;
                        continue;
                    }
                }
            }
            21 => {
                if v___y_861_ == 0 {
                    return v___y_861_;
                } else {
                    if v_proj_784_ == 0 {
                        if v_proj_816_ == 0 {
                            state = 20;
                            continue;
                        } else {
                            return v_proj_784_;
                        }
                    } else {
                        if v_proj_816_ == 0 {
                            return v_proj_816_;
                        } else {
                            state = 20;
                            continue;
                        }
                    }
                }
            }
            22 => {
                v___x_863_ =
                    l_Lean_Meta_instBEqEtaStructMode_beq(v_etaStruct_782_, v_etaStruct_814_);
                if v___x_863_ == 0 {
                    return v___x_863_;
                } else {
                    if v_iota_783_ == 0 {
                        if v_iota_815_ == 0 {
                            v___y_861_ = v___x_863_;
                            state = 21;
                            continue;
                        } else {
                            return v_iota_783_;
                        }
                    } else {
                        v___y_861_ = v_iota_815_;
                        state = 21;
                        continue;
                    }
                }
            }
            23 => {
                if v_eta_781_ == 0 {
                    if v_eta_813_ == 0 {
                        state = 22;
                        continue;
                    } else {
                        return v_eta_781_;
                    }
                } else {
                    if v_eta_813_ == 0 {
                        return v_eta_813_;
                    } else {
                        state = 22;
                        continue;
                    }
                }
            }
            24 => {
                if v_beta_780_ == 0 {
                    if v_beta_812_ == 0 {
                        state = 23;
                        continue;
                    } else {
                        return v_beta_780_;
                    }
                } else {
                    if v_beta_812_ == 0 {
                        return v_beta_812_;
                    } else {
                        state = 23;
                        continue;
                    }
                }
            }
            25 => {
                if v_zeta_779_ == 0 {
                    if v_zeta_811_ == 0 {
                        state = 24;
                        continue;
                    } else {
                        return v_zeta_779_;
                    }
                } else {
                    if v_zeta_811_ == 0 {
                        return v_zeta_811_;
                    } else {
                        state = 24;
                        continue;
                    }
                }
            }
            26 => {
                if v_singlePass_778_ == 0 {
                    if v_singlePass_810_ == 0 {
                        state = 25;
                        continue;
                    } else {
                        return v_singlePass_778_;
                    }
                } else {
                    if v_singlePass_810_ == 0 {
                        return v_singlePass_810_;
                    } else {
                        state = 25;
                        continue;
                    }
                }
            }
            27 => {
                if v___y_869_ == 0 {
                    return v___y_869_;
                } else {
                    if v_memoize_777_ == 0 {
                        if v_memoize_809_ == 0 {
                            state = 26;
                            continue;
                        } else {
                            return v_memoize_777_;
                        }
                    } else {
                        if v_memoize_809_ == 0 {
                            return v_memoize_809_;
                        } else {
                            state = 26;
                            continue;
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Simp_instBEqConfig_beq___boxed(
    mut v_x_872_: *mut crate::leanh::LeanObject,
    mut v_x_873_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_874_: u8 = 0;
    let mut v_r_875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_874_ = l_Lean_Meta_Simp_instBEqConfig_beq(v_x_872_, v_x_873_);
    crate::leanh::lean_dec_ref(v_x_873_);
    crate::leanh::lean_dec_ref(v_x_872_);
    v_r_875_ = crate::leanh::lean_box((v_res_874_) as usize);
    return v_r_875_;
}
pub unsafe fn l_Lean_Meta_Occurrences_ctorIdx(
    mut v_x_886_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_886_) {
        0 => {
            let mut v___x_887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_887_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_887_;
        }
        1 => {
            let mut v___x_888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_888_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_888_;
        }
        _ => {
            let mut v___x_889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_889_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_889_;
        }
    }
}
pub unsafe fn l_Lean_Meta_Occurrences_ctorIdx___boxed(
    mut v_x_890_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_891_ = l_Lean_Meta_Occurrences_ctorIdx(v_x_890_);
    crate::leanh::lean_dec(v_x_890_);
    return v_res_891_;
}
pub unsafe fn l_Lean_Meta_Occurrences_ctorElim___redArg(
    mut v_t_892_: *mut crate::leanh::LeanObject,
    mut v_k_893_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_t_892_) == 0 {
        return v_k_893_;
    } else {
        let mut v_idxs_894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_idxs_894_ = crate::leanh::lean_ctor_get(v_t_892_, 0);
        crate::leanh::lean_inc(v_idxs_894_);
        crate::leanh::lean_dec(v_t_892_);
        v___x_895_ = crate::leanh::lean_apply_1(v_k_893_, v_idxs_894_);
        return v___x_895_;
    }
}
pub unsafe fn l_Lean_Meta_Occurrences_ctorElim(
    mut v_motive_896_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_897_: *mut crate::leanh::LeanObject,
    mut v_t_898_: *mut crate::leanh::LeanObject,
    mut v_h_899_: *mut crate::leanh::LeanObject,
    mut v_k_900_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_901_ = l_Lean_Meta_Occurrences_ctorElim___redArg(v_t_898_, v_k_900_);
    return v___x_901_;
}
pub unsafe fn l_Lean_Meta_Occurrences_ctorElim___boxed(
    mut v_motive_902_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_903_: *mut crate::leanh::LeanObject,
    mut v_t_904_: *mut crate::leanh::LeanObject,
    mut v_h_905_: *mut crate::leanh::LeanObject,
    mut v_k_906_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_907_ = l_Lean_Meta_Occurrences_ctorElim(
        v_motive_902_,
        v_ctorIdx_903_,
        v_t_904_,
        v_h_905_,
        v_k_906_,
    );
    crate::leanh::lean_dec(v_ctorIdx_903_);
    return v_res_907_;
}
pub unsafe fn l_Lean_Meta_Occurrences_all_elim___redArg(
    mut v_t_908_: *mut crate::leanh::LeanObject,
    mut v_all_909_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_910_ = l_Lean_Meta_Occurrences_ctorElim___redArg(v_t_908_, v_all_909_);
    return v___x_910_;
}
pub unsafe fn l_Lean_Meta_Occurrences_all_elim(
    mut v_motive_911_: *mut crate::leanh::LeanObject,
    mut v_t_912_: *mut crate::leanh::LeanObject,
    mut v_h_913_: *mut crate::leanh::LeanObject,
    mut v_all_914_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_915_ = l_Lean_Meta_Occurrences_ctorElim___redArg(v_t_912_, v_all_914_);
    return v___x_915_;
}
pub unsafe fn l_Lean_Meta_Occurrences_pos_elim___redArg(
    mut v_t_916_: *mut crate::leanh::LeanObject,
    mut v_pos_917_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_918_ = l_Lean_Meta_Occurrences_ctorElim___redArg(v_t_916_, v_pos_917_);
    return v___x_918_;
}
pub unsafe fn l_Lean_Meta_Occurrences_pos_elim(
    mut v_motive_919_: *mut crate::leanh::LeanObject,
    mut v_t_920_: *mut crate::leanh::LeanObject,
    mut v_h_921_: *mut crate::leanh::LeanObject,
    mut v_pos_922_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_923_ = l_Lean_Meta_Occurrences_ctorElim___redArg(v_t_920_, v_pos_922_);
    return v___x_923_;
}
pub unsafe fn l_Lean_Meta_Occurrences_neg_elim___redArg(
    mut v_t_924_: *mut crate::leanh::LeanObject,
    mut v_neg_925_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_926_ = l_Lean_Meta_Occurrences_ctorElim___redArg(v_t_924_, v_neg_925_);
    return v___x_926_;
}
pub unsafe fn l_Lean_Meta_Occurrences_neg_elim(
    mut v_motive_927_: *mut crate::leanh::LeanObject,
    mut v_t_928_: *mut crate::leanh::LeanObject,
    mut v_h_929_: *mut crate::leanh::LeanObject,
    mut v_neg_930_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_931_ = l_Lean_Meta_Occurrences_ctorElim___redArg(v_t_928_, v_neg_930_);
    return v___x_931_;
}
pub unsafe fn _init_l_Lean_Meta_instInhabitedOccurrences_default() -> *mut crate::leanh::LeanObject
{
    let mut v___x_932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_932_ = crate::leanh::lean_box(0);
    return v___x_932_;
}
pub unsafe fn _init_l_Lean_Meta_instInhabitedOccurrences() -> *mut crate::leanh::LeanObject {
    let mut v___x_933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_933_ = crate::leanh::lean_box(0);
    return v___x_933_;
}
pub unsafe fn l_Lean_Meta_instBEqOccurrences_beq(
    mut v_x_934_: *mut crate::leanh::LeanObject,
    mut v_x_935_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_a_937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_940_: u8 = 0;
    let mut v___x_941_: u8 = 0;
    let mut v___x_942_: u8 = 0;
    let mut v_idxs_943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idxs_944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_945_: u8 = 0;
    let mut v_idxs_946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idxs_947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_948_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_934_) {
                0 => {
                    if crate::leanh::lean_obj_tag(v_x_935_) == 0 {
                        v___x_941_ = 1;
                        return v___x_941_;
                    } else {
                        crate::leanh::lean_dec(v_x_935_);
                        v___x_942_ = 0;
                        return v___x_942_;
                    }
                }
                1 => {
                    if crate::leanh::lean_obj_tag(v_x_935_) == 1 {
                        v_idxs_943_ = crate::leanh::lean_ctor_get(v_x_934_, 0);
                        crate::leanh::lean_inc(v_idxs_943_);
                        crate::leanh::lean_dec_ref_known(v_x_934_, 1);
                        v_idxs_944_ = crate::leanh::lean_ctor_get(v_x_935_, 0);
                        crate::leanh::lean_inc(v_idxs_944_);
                        crate::leanh::lean_dec_ref_known(v_x_935_, 1);
                        v_a_937_ = v_idxs_943_;
                        v_b_938_ = v_idxs_944_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref_known(v_x_934_, 1);
                        crate::leanh::lean_dec(v_x_935_);
                        v___x_945_ = 0;
                        return v___x_945_;
                    }
                }
                _ => {
                    if crate::leanh::lean_obj_tag(v_x_935_) == 2 {
                        v_idxs_946_ = crate::leanh::lean_ctor_get(v_x_934_, 0);
                        crate::leanh::lean_inc(v_idxs_946_);
                        crate::leanh::lean_dec_ref_known(v_x_934_, 1);
                        v_idxs_947_ = crate::leanh::lean_ctor_get(v_x_935_, 0);
                        crate::leanh::lean_inc(v_idxs_947_);
                        crate::leanh::lean_dec_ref_known(v_x_935_, 1);
                        v_a_937_ = v_idxs_946_;
                        v_b_938_ = v_idxs_947_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref_known(v_x_934_, 1);
                        crate::leanh::lean_dec(v_x_935_);
                        v___x_948_ = 0;
                        return v___x_948_;
                    }
                }
            },
            1 => {
                v___x_939_ = crate::leanh::lean_alloc_closure(
                    l_instDecidableEqNat___boxed as *mut core::ffi::c_void,
                    2,
                    0,
                );
                v___x_940_ = l_instDecidableEqList___redArg(v___x_939_, v_a_937_, v_b_938_);
                return v___x_940_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_instBEqOccurrences_beq___boxed(
    mut v_x_949_: *mut crate::leanh::LeanObject,
    mut v_x_950_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_951_: u8 = 0;
    let mut v_r_952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_951_ = l_Lean_Meta_instBEqOccurrences_beq(v_x_949_, v_x_950_);
    v_r_952_ = crate::leanh::lean_box((v_res_951_) as usize);
    return v_r_952_;
}
pub unsafe fn l_Lean_Meta_instCoeListNatOccurrences___lam__0(
    mut v_idxs_955_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_956_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_956_, 0, v_idxs_955_);
    return v___x_956_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_MetaTypes(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Core(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lean_Meta_instInhabitedTransparencyMode_default =
        _init_l_Lean_Meta_instInhabitedTransparencyMode_default();
    l_Lean_Meta_instInhabitedTransparencyMode = _init_l_Lean_Meta_instInhabitedTransparencyMode();
    l_Lean_Meta_instInhabitedEtaStructMode_default =
        _init_l_Lean_Meta_instInhabitedEtaStructMode_default();
    l_Lean_Meta_instInhabitedEtaStructMode = _init_l_Lean_Meta_instInhabitedEtaStructMode();
    l_Lean_Meta_Simp_defaultMaxSteps = _init_l_Lean_Meta_Simp_defaultMaxSteps();
    crate::leanh::lean_mark_persistent(l_Lean_Meta_Simp_defaultMaxSteps);
    l_Lean_Meta_instInhabitedOccurrences_default =
        _init_l_Lean_Meta_instInhabitedOccurrences_default();
    crate::leanh::lean_mark_persistent(l_Lean_Meta_instInhabitedOccurrences_default);
    l_Lean_Meta_instInhabitedOccurrences = _init_l_Lean_Meta_instInhabitedOccurrences();
    crate::leanh::lean_mark_persistent(l_Lean_Meta_instInhabitedOccurrences);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_MetaTypes(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_MetaTypes(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Core(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_MetaTypes(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_MetaTypes(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_MetaTypes(builtin);
}
