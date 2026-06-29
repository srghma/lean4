// Lean compiler output
// Module: Init.Data.Float
// Imports: Init.Data.ToString.Basic
use crate::r#gen::Init::Data::Repr::l_Repr_addAppParen;
use crate::r#gen::Init::Data::ToString::Basic::{
    initialize_Init_Data_ToString_Basic, runtime_initialize_Init_Data_ToString_Basic,
};
use crate::lean_imports_rs::Init::Data::Float::{
    acos, acosh, asin, asinh, atan, atan2, atanh, cbrt, ceil, cos, cosh, exp, exp2, fabs, floor,
    lean_float_add, lean_float_beq, lean_float_decLe, lean_float_decLt, lean_float_div,
    lean_float_frexp, lean_float_isfinite, lean_float_isinf, lean_float_isnan, lean_float_mul,
    lean_float_negate, lean_float_of_bits, lean_float_scaleb, lean_float_sub, lean_float_to_bits,
    lean_float_to_string, lean_float_to_uint8, lean_float_to_uint16, lean_float_to_uint32,
    lean_float_to_uint64, lean_float_to_usize, lean_uint8_to_float, lean_uint16_to_float,
    lean_uint32_to_float, lean_uint64_to_float, lean_usize_to_float, log, log2, log10, pow, round,
    sin, sinh, sqrt, tan, tanh,
};
pub static l_floatSpec___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_floatSpec___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_floatSpec___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_floatSpec___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_floatSpec___closed__1_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 0,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_floatSpec___closed__0_value) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_floatSpec___closed__0_value) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_floatSpec___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_floatSpec___closed__1_value) as *mut crate::leanh::LeanObject;
pub static mut l_floatSpec: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_floatSpec___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_instAddFloat___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Float_add___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instAddFloat___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instAddFloat___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instAddFloat: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instAddFloat___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instSubFloat___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Float_sub___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instSubFloat___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instSubFloat___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instSubFloat: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instSubFloat___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instMulFloat___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Float_mul___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instMulFloat___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instMulFloat___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instMulFloat: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instMulFloat___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instDivFloat___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Float_div___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instDivFloat___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instDivFloat___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instDivFloat: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instDivFloat___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instNegFloat___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Float_neg___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instNegFloat___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instNegFloat___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instNegFloat: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instNegFloat___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instLTFloat: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_instLEFloat: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_instBEqFloat___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Float_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instBEqFloat___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instBEqFloat___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instBEqFloat: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instBEqFloat___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instToStringFloat___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Float_toString___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instToStringFloat___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instToStringFloat___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instToStringFloat: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instToStringFloat___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_instInhabitedFloat___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_instInhabitedFloat___closed__0: f64 = 0.0;
pub static mut l_instInhabitedFloat: f64 = 0.0;
pub static l_instReprFloat___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Float_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instReprFloat___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instReprFloat___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instReprFloat: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instReprFloat___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instReprAtomFloat: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_instHomogeneousPowFloat___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Float_pow___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instHomogeneousPowFloat___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instHomogeneousPowFloat___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_instHomogeneousPowFloat: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instHomogeneousPowFloat___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_instMinFloat___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_instMinFloat___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instMinFloat___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instMinFloat___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instMinFloat: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instMinFloat___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instMaxFloat___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_instMaxFloat___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instMaxFloat___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instMaxFloat___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instMaxFloat: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instMaxFloat___closed__0_value) as *mut crate::leanh::LeanObject;
pub unsafe fn l_floatSpec___lam__0(
    mut v_x_354_: *mut crate::leanh::LeanObject,
    mut v_x_355_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_356_: u8 = 0;
    v___x_356_ = 1;
    return v___x_356_;
}
pub unsafe fn l_floatSpec___lam__0___boxed(
    mut v_x_357_: *mut crate::leanh::LeanObject,
    mut v_x_358_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_359_: u8 = 0;
    let mut v_r_360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_359_ = l_floatSpec___lam__0(v_x_357_, v_x_358_);
    v_r_360_ = crate::leanh::lean_box((v_res_359_) as usize);
    return v_r_360_;
}
pub unsafe fn l_Float_add___boxed(
    mut v_a_00___x40___internal___hyg_368_: *mut crate::leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_369_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_370_: f64 = 0.0;
    let mut v_a_00___x40___internal___hyg_2__boxed_371_: f64 = 0.0;
    let mut v_res_372_: f64 = 0.0;
    let mut v_r_373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_370_ =
        crate::leanh::lean_unbox_float(v_a_00___x40___internal___hyg_368_);
    crate::leanh::lean_dec_ref(v_a_00___x40___internal___hyg_368_);
    v_a_00___x40___internal___hyg_2__boxed_371_ =
        crate::leanh::lean_unbox_float(v_a_00___x40___internal___hyg_369_);
    crate::leanh::lean_dec_ref(v_a_00___x40___internal___hyg_369_);
    v_res_372_ = lean_float_add(
        v_a_00___x40___internal___hyg_1__boxed_370_,
        v_a_00___x40___internal___hyg_2__boxed_371_,
    );
    v_r_373_ = crate::leanh::lean_box_float(v_res_372_);
    return v_r_373_;
}
pub unsafe fn l_Float_sub___boxed(
    mut v_a_00___x40___internal___hyg_376_: *mut crate::leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_377_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_378_: f64 = 0.0;
    let mut v_a_00___x40___internal___hyg_2__boxed_379_: f64 = 0.0;
    let mut v_res_380_: f64 = 0.0;
    let mut v_r_381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_378_ =
        crate::leanh::lean_unbox_float(v_a_00___x40___internal___hyg_376_);
    crate::leanh::lean_dec_ref(v_a_00___x40___internal___hyg_376_);
    v_a_00___x40___internal___hyg_2__boxed_379_ =
        crate::leanh::lean_unbox_float(v_a_00___x40___internal___hyg_377_);
    crate::leanh::lean_dec_ref(v_a_00___x40___internal___hyg_377_);
    v_res_380_ = lean_float_sub(
        v_a_00___x40___internal___hyg_1__boxed_378_,
        v_a_00___x40___internal___hyg_2__boxed_379_,
    );
    v_r_381_ = crate::leanh::lean_box_float(v_res_380_);
    return v_r_381_;
}
pub unsafe fn l_Float_mul___boxed(
    mut v_a_00___x40___internal___hyg_384_: *mut crate::leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_385_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_386_: f64 = 0.0;
    let mut v_a_00___x40___internal___hyg_2__boxed_387_: f64 = 0.0;
    let mut v_res_388_: f64 = 0.0;
    let mut v_r_389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_386_ =
        crate::leanh::lean_unbox_float(v_a_00___x40___internal___hyg_384_);
    crate::leanh::lean_dec_ref(v_a_00___x40___internal___hyg_384_);
    v_a_00___x40___internal___hyg_2__boxed_387_ =
        crate::leanh::lean_unbox_float(v_a_00___x40___internal___hyg_385_);
    crate::leanh::lean_dec_ref(v_a_00___x40___internal___hyg_385_);
    v_res_388_ = lean_float_mul(
        v_a_00___x40___internal___hyg_1__boxed_386_,
        v_a_00___x40___internal___hyg_2__boxed_387_,
    );
    v_r_389_ = crate::leanh::lean_box_float(v_res_388_);
    return v_r_389_;
}
pub unsafe fn l_Float_div___boxed(
    mut v_a_00___x40___internal___hyg_392_: *mut crate::leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_393_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_394_: f64 = 0.0;
    let mut v_a_00___x40___internal___hyg_2__boxed_395_: f64 = 0.0;
    let mut v_res_396_: f64 = 0.0;
    let mut v_r_397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_394_ =
        crate::leanh::lean_unbox_float(v_a_00___x40___internal___hyg_392_);
    crate::leanh::lean_dec_ref(v_a_00___x40___internal___hyg_392_);
    v_a_00___x40___internal___hyg_2__boxed_395_ =
        crate::leanh::lean_unbox_float(v_a_00___x40___internal___hyg_393_);
    crate::leanh::lean_dec_ref(v_a_00___x40___internal___hyg_393_);
    v_res_396_ = lean_float_div(
        v_a_00___x40___internal___hyg_1__boxed_394_,
        v_a_00___x40___internal___hyg_2__boxed_395_,
    );
    v_r_397_ = crate::leanh::lean_box_float(v_res_396_);
    return v_r_397_;
}
pub unsafe fn l_Float_neg___boxed(
    mut v_a_00___x40___internal___hyg_399_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_400_: f64 = 0.0;
    let mut v_res_401_: f64 = 0.0;
    let mut v_r_402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_400_ =
        crate::leanh::lean_unbox_float(v_a_00___x40___internal___hyg_399_);
    crate::leanh::lean_dec_ref(v_a_00___x40___internal___hyg_399_);
    v_res_401_ = lean_float_negate(v_a_00___x40___internal___hyg_1__boxed_400_);
    v_r_402_ = crate::leanh::lean_box_float(v_res_401_);
    return v_r_402_;
}
pub unsafe fn l_Float_ofBits___boxed(
    mut v_a_00___x40___internal___hyg_404_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_405_: u64 = 0;
    let mut v_res_406_: f64 = 0.0;
    let mut v_r_407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_405_ =
        crate::leanh::lean_unbox_uint64(v_a_00___x40___internal___hyg_404_);
    crate::leanh::lean_dec_ref(v_a_00___x40___internal___hyg_404_);
    v_res_406_ = lean_float_of_bits(v_a_00___x40___internal___hyg_1__boxed_405_);
    v_r_407_ = crate::leanh::lean_box_float(v_res_406_);
    return v_r_407_;
}
pub unsafe fn l_Float_toBits___boxed(
    mut v_a_00___x40___internal___hyg_409_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_410_: f64 = 0.0;
    let mut v_res_411_: u64 = 0;
    let mut v_r_412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_410_ =
        crate::leanh::lean_unbox_float(v_a_00___x40___internal___hyg_409_);
    crate::leanh::lean_dec_ref(v_a_00___x40___internal___hyg_409_);
    v_res_411_ = lean_float_to_bits(v_a_00___x40___internal___hyg_1__boxed_410_);
    v_r_412_ = crate::leanh::lean_box_uint64(v_res_411_);
    return v_r_412_;
}
pub unsafe fn _init_l_instLTFloat() -> *mut crate::leanh::LeanObject {
    let mut v___x_423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_423_ = crate::leanh::lean_box(0);
    return v___x_423_;
}
pub unsafe fn _init_l_instLEFloat() -> *mut crate::leanh::LeanObject {
    let mut v___x_424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_424_ = crate::leanh::lean_box(0);
    return v___x_424_;
}
pub unsafe fn l_Float_beq___boxed(
    mut v_a_427_: *mut crate::leanh::LeanObject,
    mut v_b_428_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_429_: f64 = 0.0;
    let mut v_b_boxed_430_: f64 = 0.0;
    let mut v_res_431_: u8 = 0;
    let mut v_r_432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_429_ = crate::leanh::lean_unbox_float(v_a_427_);
    crate::leanh::lean_dec_ref(v_a_427_);
    v_b_boxed_430_ = crate::leanh::lean_unbox_float(v_b_428_);
    crate::leanh::lean_dec_ref(v_b_428_);
    v_res_431_ = lean_float_beq(v_a_boxed_429_, v_b_boxed_430_);
    v_r_432_ = crate::leanh::lean_box((v_res_431_) as usize);
    return v_r_432_;
}
pub unsafe fn l_Float_decLt___boxed(
    mut v_a_437_: *mut crate::leanh::LeanObject,
    mut v_b_438_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_439_: f64 = 0.0;
    let mut v_b_boxed_440_: f64 = 0.0;
    let mut v_res_441_: u8 = 0;
    let mut v_r_442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_439_ = crate::leanh::lean_unbox_float(v_a_437_);
    crate::leanh::lean_dec_ref(v_a_437_);
    v_b_boxed_440_ = crate::leanh::lean_unbox_float(v_b_438_);
    crate::leanh::lean_dec_ref(v_b_438_);
    v_res_441_ = lean_float_decLt(v_a_boxed_439_, v_b_boxed_440_);
    v_r_442_ = crate::leanh::lean_box((v_res_441_) as usize);
    return v_r_442_;
}
pub unsafe fn l_Float_decLe___boxed(
    mut v_a_445_: *mut crate::leanh::LeanObject,
    mut v_b_446_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_447_: f64 = 0.0;
    let mut v_b_boxed_448_: f64 = 0.0;
    let mut v_res_449_: u8 = 0;
    let mut v_r_450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_447_ = crate::leanh::lean_unbox_float(v_a_445_);
    crate::leanh::lean_dec_ref(v_a_445_);
    v_b_boxed_448_ = crate::leanh::lean_unbox_float(v_b_446_);
    crate::leanh::lean_dec_ref(v_b_446_);
    v_res_449_ = lean_float_decLe(v_a_boxed_447_, v_b_boxed_448_);
    v_r_450_ = crate::leanh::lean_box((v_res_449_) as usize);
    return v_r_450_;
}
pub unsafe fn l_Float_toString___boxed(
    mut v_a_00___x40___internal___hyg_452_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_453_: f64 = 0.0;
    let mut v_res_454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_453_ =
        crate::leanh::lean_unbox_float(v_a_00___x40___internal___hyg_452_);
    crate::leanh::lean_dec_ref(v_a_00___x40___internal___hyg_452_);
    v_res_454_ = lean_float_to_string(v_a_00___x40___internal___hyg_1__boxed_453_);
    return v_res_454_;
}
pub unsafe fn l_Float_toUInt8___boxed(
    mut v_a_00___x40___internal___hyg_456_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_457_: f64 = 0.0;
    let mut v_res_458_: u8 = 0;
    let mut v_r_459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_457_ =
        crate::leanh::lean_unbox_float(v_a_00___x40___internal___hyg_456_);
    crate::leanh::lean_dec_ref(v_a_00___x40___internal___hyg_456_);
    v_res_458_ = lean_float_to_uint8(v_a_00___x40___internal___hyg_1__boxed_457_);
    v_r_459_ = crate::leanh::lean_box((v_res_458_) as usize);
    return v_r_459_;
}
pub unsafe fn l_Float_toUInt16___boxed(
    mut v_a_00___x40___internal___hyg_461_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_462_: f64 = 0.0;
    let mut v_res_463_: u16 = 0;
    let mut v_r_464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_462_ =
        crate::leanh::lean_unbox_float(v_a_00___x40___internal___hyg_461_);
    crate::leanh::lean_dec_ref(v_a_00___x40___internal___hyg_461_);
    v_res_463_ = lean_float_to_uint16(v_a_00___x40___internal___hyg_1__boxed_462_);
    v_r_464_ = crate::leanh::lean_box((v_res_463_) as usize);
    return v_r_464_;
}
pub unsafe fn l_Float_toUInt32___boxed(
    mut v_a_00___x40___internal___hyg_466_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_467_: f64 = 0.0;
    let mut v_res_468_: u32 = 0;
    let mut v_r_469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_467_ =
        crate::leanh::lean_unbox_float(v_a_00___x40___internal___hyg_466_);
    crate::leanh::lean_dec_ref(v_a_00___x40___internal___hyg_466_);
    v_res_468_ = lean_float_to_uint32(v_a_00___x40___internal___hyg_1__boxed_467_);
    v_r_469_ = crate::leanh::lean_box_uint32(v_res_468_);
    return v_r_469_;
}
pub unsafe fn l_Float_toUInt64___boxed(
    mut v_a_00___x40___internal___hyg_471_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_472_: f64 = 0.0;
    let mut v_res_473_: u64 = 0;
    let mut v_r_474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_472_ =
        crate::leanh::lean_unbox_float(v_a_00___x40___internal___hyg_471_);
    crate::leanh::lean_dec_ref(v_a_00___x40___internal___hyg_471_);
    v_res_473_ = lean_float_to_uint64(v_a_00___x40___internal___hyg_1__boxed_472_);
    v_r_474_ = crate::leanh::lean_box_uint64(v_res_473_);
    return v_r_474_;
}
pub unsafe fn l_Float_toUSize___boxed(
    mut v_a_00___x40___internal___hyg_476_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_477_: f64 = 0.0;
    let mut v_res_478_: usize = 0;
    let mut v_r_479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_477_ =
        crate::leanh::lean_unbox_float(v_a_00___x40___internal___hyg_476_);
    crate::leanh::lean_dec_ref(v_a_00___x40___internal___hyg_476_);
    v_res_478_ = lean_float_to_usize(v_a_00___x40___internal___hyg_1__boxed_477_);
    v_r_479_ = crate::leanh::lean_box_usize(v_res_478_);
    return v_r_479_;
}
pub unsafe fn l_Float_isNaN___boxed(
    mut v_a_00___x40___internal___hyg_481_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_482_: f64 = 0.0;
    let mut v_res_483_: u8 = 0;
    let mut v_r_484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_482_ =
        crate::leanh::lean_unbox_float(v_a_00___x40___internal___hyg_481_);
    crate::leanh::lean_dec_ref(v_a_00___x40___internal___hyg_481_);
    v_res_483_ = lean_float_isnan(v_a_00___x40___internal___hyg_1__boxed_482_);
    v_r_484_ = crate::leanh::lean_box((v_res_483_) as usize);
    return v_r_484_;
}
pub unsafe fn l_Float_isFinite___boxed(
    mut v_a_00___x40___internal___hyg_486_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_487_: f64 = 0.0;
    let mut v_res_488_: u8 = 0;
    let mut v_r_489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_487_ =
        crate::leanh::lean_unbox_float(v_a_00___x40___internal___hyg_486_);
    crate::leanh::lean_dec_ref(v_a_00___x40___internal___hyg_486_);
    v_res_488_ = lean_float_isfinite(v_a_00___x40___internal___hyg_1__boxed_487_);
    v_r_489_ = crate::leanh::lean_box((v_res_488_) as usize);
    return v_r_489_;
}
pub unsafe fn l_Float_isInf___boxed(
    mut v_a_00___x40___internal___hyg_491_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_492_: f64 = 0.0;
    let mut v_res_493_: u8 = 0;
    let mut v_r_494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_492_ =
        crate::leanh::lean_unbox_float(v_a_00___x40___internal___hyg_491_);
    crate::leanh::lean_dec_ref(v_a_00___x40___internal___hyg_491_);
    v_res_493_ = lean_float_isinf(v_a_00___x40___internal___hyg_1__boxed_492_);
    v_r_494_ = crate::leanh::lean_box((v_res_493_) as usize);
    return v_r_494_;
}
pub unsafe fn l_Float_frExp___boxed(
    mut v_a_00___x40___internal___hyg_496_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_497_: f64 = 0.0;
    let mut v_res_498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_497_ =
        crate::leanh::lean_unbox_float(v_a_00___x40___internal___hyg_496_);
    crate::leanh::lean_dec_ref(v_a_00___x40___internal___hyg_496_);
    v_res_498_ = lean_float_frexp(v_a_00___x40___internal___hyg_1__boxed_497_);
    return v_res_498_;
}
pub unsafe fn l_UInt8_toFloat___boxed(
    mut v_n_502_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_n_boxed_503_: u8 = 0;
    let mut v_res_504_: f64 = 0.0;
    let mut v_r_505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_n_boxed_503_ = (crate::leanh::lean_unbox(v_n_502_) as u8);
    v_res_504_ = lean_uint8_to_float(v_n_boxed_503_);
    v_r_505_ = crate::leanh::lean_box_float(v_res_504_);
    return v_r_505_;
}
pub unsafe fn l_UInt16_toFloat___boxed(
    mut v_n_507_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_n_boxed_508_: u16 = 0;
    let mut v_res_509_: f64 = 0.0;
    let mut v_r_510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_n_boxed_508_ = (crate::leanh::lean_unbox(v_n_507_) as u16);
    v_res_509_ = lean_uint16_to_float(v_n_boxed_508_);
    v_r_510_ = crate::leanh::lean_box_float(v_res_509_);
    return v_r_510_;
}
pub unsafe fn l_UInt32_toFloat___boxed(
    mut v_n_512_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_n_boxed_513_: u32 = 0;
    let mut v_res_514_: f64 = 0.0;
    let mut v_r_515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_n_boxed_513_ = crate::leanh::lean_unbox_uint32(v_n_512_);
    crate::leanh::lean_dec(v_n_512_);
    v_res_514_ = lean_uint32_to_float(v_n_boxed_513_);
    v_r_515_ = crate::leanh::lean_box_float(v_res_514_);
    return v_r_515_;
}
pub unsafe fn l_UInt64_toFloat___boxed(
    mut v_n_517_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_n_boxed_518_: u64 = 0;
    let mut v_res_519_: f64 = 0.0;
    let mut v_r_520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_n_boxed_518_ = crate::leanh::lean_unbox_uint64(v_n_517_);
    crate::leanh::lean_dec_ref(v_n_517_);
    v_res_519_ = lean_uint64_to_float(v_n_boxed_518_);
    v_r_520_ = crate::leanh::lean_box_float(v_res_519_);
    return v_r_520_;
}
pub unsafe fn l_USize_toFloat___boxed(
    mut v_n_522_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_n_boxed_523_: usize = 0;
    let mut v_res_524_: f64 = 0.0;
    let mut v_r_525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_n_boxed_523_ = crate::leanh::lean_unbox_usize(v_n_522_);
    crate::leanh::lean_dec(v_n_522_);
    v_res_524_ = lean_usize_to_float(v_n_boxed_523_);
    v_r_525_ = crate::leanh::lean_box_float(v_res_524_);
    return v_r_525_;
}
pub unsafe fn _init_l_instInhabitedFloat___closed__0() -> f64 {
    let mut v___x_526_: u64 = 0;
    let mut v___x_527_: f64 = 0.0;
    v___x_526_ = 0u64;
    v___x_527_ = lean_uint64_to_float(v___x_526_);
    return v___x_527_;
}
pub unsafe fn _init_l_instInhabitedFloat() -> f64 {
    let mut v___x_528_: f64 = 0.0;
    v___x_528_ = crate::leanh::lean_float_once(
        core::ptr::addr_of_mut!(l_instInhabitedFloat___closed__0),
        core::ptr::addr_of_mut!(l_instInhabitedFloat___closed__0_once),
        _init_l_instInhabitedFloat___closed__0,
    );
    return v___x_528_;
}
pub unsafe fn l_Float_repr(
    mut v_n_529_: f64,
    mut v_prec_530_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_531_: f64 = 0.0;
    let mut v___x_532_: u8 = 0;
    v___x_531_ = crate::leanh::lean_float_once(
        core::ptr::addr_of_mut!(l_instInhabitedFloat___closed__0),
        core::ptr::addr_of_mut!(l_instInhabitedFloat___closed__0_once),
        _init_l_instInhabitedFloat___closed__0,
    );
    v___x_532_ = lean_float_decLt(v_n_529_, v___x_531_);
    if v___x_532_ == 0 {
        let mut v___x_533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_533_ = lean_float_to_string(v_n_529_);
        v___x_534_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_534_, 0, v___x_533_);
        return v___x_534_;
    } else {
        let mut v___x_535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_535_ = lean_float_to_string(v_n_529_);
        v___x_536_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_536_, 0, v___x_535_);
        v___x_537_ = l_Repr_addAppParen(v___x_536_, v_prec_530_);
        return v___x_537_;
    }
}
pub unsafe fn l_Float_repr___boxed(
    mut v_n_538_: *mut crate::leanh::LeanObject,
    mut v_prec_539_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_n_boxed_540_: f64 = 0.0;
    let mut v_res_541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_n_boxed_540_ = crate::leanh::lean_unbox_float(v_n_538_);
    crate::leanh::lean_dec_ref(v_n_538_);
    v_res_541_ = l_Float_repr(v_n_boxed_540_, v_prec_539_);
    crate::leanh::lean_dec(v_prec_539_);
    return v_res_541_;
}
pub unsafe fn _init_l_instReprAtomFloat() -> *mut crate::leanh::LeanObject {
    let mut v___x_544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_544_ = crate::leanh::lean_box(0);
    return v___x_544_;
}
pub unsafe fn l_Float_sin___boxed(
    mut v_a_00___x40___internal___hyg_546_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_547_: f64 = 0.0;
    let mut v_res_548_: f64 = 0.0;
    let mut v_r_549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_547_ =
        crate::leanh::lean_unbox_float(v_a_00___x40___internal___hyg_546_);
    crate::leanh::lean_dec_ref(v_a_00___x40___internal___hyg_546_);
    v_res_548_ = sin(v_a_00___x40___internal___hyg_1__boxed_547_);
    v_r_549_ = crate::leanh::lean_box_float(v_res_548_);
    return v_r_549_;
}
pub unsafe fn l_Float_cos___boxed(
    mut v_a_00___x40___internal___hyg_551_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_552_: f64 = 0.0;
    let mut v_res_553_: f64 = 0.0;
    let mut v_r_554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_552_ =
        crate::leanh::lean_unbox_float(v_a_00___x40___internal___hyg_551_);
    crate::leanh::lean_dec_ref(v_a_00___x40___internal___hyg_551_);
    v_res_553_ = cos(v_a_00___x40___internal___hyg_1__boxed_552_);
    v_r_554_ = crate::leanh::lean_box_float(v_res_553_);
    return v_r_554_;
}
pub unsafe fn l_Float_tan___boxed(
    mut v_a_00___x40___internal___hyg_556_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_557_: f64 = 0.0;
    let mut v_res_558_: f64 = 0.0;
    let mut v_r_559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_557_ =
        crate::leanh::lean_unbox_float(v_a_00___x40___internal___hyg_556_);
    crate::leanh::lean_dec_ref(v_a_00___x40___internal___hyg_556_);
    v_res_558_ = tan(v_a_00___x40___internal___hyg_1__boxed_557_);
    v_r_559_ = crate::leanh::lean_box_float(v_res_558_);
    return v_r_559_;
}
pub unsafe fn l_Float_asin___boxed(
    mut v_a_00___x40___internal___hyg_561_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_562_: f64 = 0.0;
    let mut v_res_563_: f64 = 0.0;
    let mut v_r_564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_562_ =
        crate::leanh::lean_unbox_float(v_a_00___x40___internal___hyg_561_);
    crate::leanh::lean_dec_ref(v_a_00___x40___internal___hyg_561_);
    v_res_563_ = asin(v_a_00___x40___internal___hyg_1__boxed_562_);
    v_r_564_ = crate::leanh::lean_box_float(v_res_563_);
    return v_r_564_;
}
pub unsafe fn l_Float_acos___boxed(
    mut v_a_00___x40___internal___hyg_566_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_567_: f64 = 0.0;
    let mut v_res_568_: f64 = 0.0;
    let mut v_r_569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_567_ =
        crate::leanh::lean_unbox_float(v_a_00___x40___internal___hyg_566_);
    crate::leanh::lean_dec_ref(v_a_00___x40___internal___hyg_566_);
    v_res_568_ = acos(v_a_00___x40___internal___hyg_1__boxed_567_);
    v_r_569_ = crate::leanh::lean_box_float(v_res_568_);
    return v_r_569_;
}
pub unsafe fn l_Float_atan___boxed(
    mut v_a_00___x40___internal___hyg_571_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_572_: f64 = 0.0;
    let mut v_res_573_: f64 = 0.0;
    let mut v_r_574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_572_ =
        crate::leanh::lean_unbox_float(v_a_00___x40___internal___hyg_571_);
    crate::leanh::lean_dec_ref(v_a_00___x40___internal___hyg_571_);
    v_res_573_ = atan(v_a_00___x40___internal___hyg_1__boxed_572_);
    v_r_574_ = crate::leanh::lean_box_float(v_res_573_);
    return v_r_574_;
}
pub unsafe fn l_Float_atan2___boxed(
    mut v_y_577_: *mut crate::leanh::LeanObject,
    mut v_x_578_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_y_boxed_579_: f64 = 0.0;
    let mut v_x_boxed_580_: f64 = 0.0;
    let mut v_res_581_: f64 = 0.0;
    let mut v_r_582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_y_boxed_579_ = crate::leanh::lean_unbox_float(v_y_577_);
    crate::leanh::lean_dec_ref(v_y_577_);
    v_x_boxed_580_ = crate::leanh::lean_unbox_float(v_x_578_);
    crate::leanh::lean_dec_ref(v_x_578_);
    v_res_581_ = atan2(v_y_boxed_579_, v_x_boxed_580_);
    v_r_582_ = crate::leanh::lean_box_float(v_res_581_);
    return v_r_582_;
}
pub unsafe fn l_Float_sinh___boxed(
    mut v_a_00___x40___internal___hyg_584_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_585_: f64 = 0.0;
    let mut v_res_586_: f64 = 0.0;
    let mut v_r_587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_585_ =
        crate::leanh::lean_unbox_float(v_a_00___x40___internal___hyg_584_);
    crate::leanh::lean_dec_ref(v_a_00___x40___internal___hyg_584_);
    v_res_586_ = sinh(v_a_00___x40___internal___hyg_1__boxed_585_);
    v_r_587_ = crate::leanh::lean_box_float(v_res_586_);
    return v_r_587_;
}
pub unsafe fn l_Float_cosh___boxed(
    mut v_a_00___x40___internal___hyg_589_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_590_: f64 = 0.0;
    let mut v_res_591_: f64 = 0.0;
    let mut v_r_592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_590_ =
        crate::leanh::lean_unbox_float(v_a_00___x40___internal___hyg_589_);
    crate::leanh::lean_dec_ref(v_a_00___x40___internal___hyg_589_);
    v_res_591_ = cosh(v_a_00___x40___internal___hyg_1__boxed_590_);
    v_r_592_ = crate::leanh::lean_box_float(v_res_591_);
    return v_r_592_;
}
pub unsafe fn l_Float_tanh___boxed(
    mut v_a_00___x40___internal___hyg_594_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_595_: f64 = 0.0;
    let mut v_res_596_: f64 = 0.0;
    let mut v_r_597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_595_ =
        crate::leanh::lean_unbox_float(v_a_00___x40___internal___hyg_594_);
    crate::leanh::lean_dec_ref(v_a_00___x40___internal___hyg_594_);
    v_res_596_ = tanh(v_a_00___x40___internal___hyg_1__boxed_595_);
    v_r_597_ = crate::leanh::lean_box_float(v_res_596_);
    return v_r_597_;
}
pub unsafe fn l_Float_asinh___boxed(
    mut v_a_00___x40___internal___hyg_599_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_600_: f64 = 0.0;
    let mut v_res_601_: f64 = 0.0;
    let mut v_r_602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_600_ =
        crate::leanh::lean_unbox_float(v_a_00___x40___internal___hyg_599_);
    crate::leanh::lean_dec_ref(v_a_00___x40___internal___hyg_599_);
    v_res_601_ = asinh(v_a_00___x40___internal___hyg_1__boxed_600_);
    v_r_602_ = crate::leanh::lean_box_float(v_res_601_);
    return v_r_602_;
}
pub unsafe fn l_Float_acosh___boxed(
    mut v_a_00___x40___internal___hyg_604_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_605_: f64 = 0.0;
    let mut v_res_606_: f64 = 0.0;
    let mut v_r_607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_605_ =
        crate::leanh::lean_unbox_float(v_a_00___x40___internal___hyg_604_);
    crate::leanh::lean_dec_ref(v_a_00___x40___internal___hyg_604_);
    v_res_606_ = acosh(v_a_00___x40___internal___hyg_1__boxed_605_);
    v_r_607_ = crate::leanh::lean_box_float(v_res_606_);
    return v_r_607_;
}
pub unsafe fn l_Float_atanh___boxed(
    mut v_a_00___x40___internal___hyg_609_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_610_: f64 = 0.0;
    let mut v_res_611_: f64 = 0.0;
    let mut v_r_612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_610_ =
        crate::leanh::lean_unbox_float(v_a_00___x40___internal___hyg_609_);
    crate::leanh::lean_dec_ref(v_a_00___x40___internal___hyg_609_);
    v_res_611_ = atanh(v_a_00___x40___internal___hyg_1__boxed_610_);
    v_r_612_ = crate::leanh::lean_box_float(v_res_611_);
    return v_r_612_;
}
pub unsafe fn l_Float_exp___boxed(
    mut v_x_614_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_615_: f64 = 0.0;
    let mut v_res_616_: f64 = 0.0;
    let mut v_r_617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_615_ = crate::leanh::lean_unbox_float(v_x_614_);
    crate::leanh::lean_dec_ref(v_x_614_);
    v_res_616_ = exp(v_x_boxed_615_);
    v_r_617_ = crate::leanh::lean_box_float(v_res_616_);
    return v_r_617_;
}
pub unsafe fn l_Float_exp2___boxed(
    mut v_x_619_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_620_: f64 = 0.0;
    let mut v_res_621_: f64 = 0.0;
    let mut v_r_622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_620_ = crate::leanh::lean_unbox_float(v_x_619_);
    crate::leanh::lean_dec_ref(v_x_619_);
    v_res_621_ = exp2(v_x_boxed_620_);
    v_r_622_ = crate::leanh::lean_box_float(v_res_621_);
    return v_r_622_;
}
pub unsafe fn l_Float_log___boxed(
    mut v_x_624_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_625_: f64 = 0.0;
    let mut v_res_626_: f64 = 0.0;
    let mut v_r_627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_625_ = crate::leanh::lean_unbox_float(v_x_624_);
    crate::leanh::lean_dec_ref(v_x_624_);
    v_res_626_ = log(v_x_boxed_625_);
    v_r_627_ = crate::leanh::lean_box_float(v_res_626_);
    return v_r_627_;
}
pub unsafe fn l_Float_log2___boxed(
    mut v_a_00___x40___internal___hyg_629_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_630_: f64 = 0.0;
    let mut v_res_631_: f64 = 0.0;
    let mut v_r_632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_630_ =
        crate::leanh::lean_unbox_float(v_a_00___x40___internal___hyg_629_);
    crate::leanh::lean_dec_ref(v_a_00___x40___internal___hyg_629_);
    v_res_631_ = log2(v_a_00___x40___internal___hyg_1__boxed_630_);
    v_r_632_ = crate::leanh::lean_box_float(v_res_631_);
    return v_r_632_;
}
pub unsafe fn l_Float_log10___boxed(
    mut v_a_00___x40___internal___hyg_634_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_635_: f64 = 0.0;
    let mut v_res_636_: f64 = 0.0;
    let mut v_r_637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_635_ =
        crate::leanh::lean_unbox_float(v_a_00___x40___internal___hyg_634_);
    crate::leanh::lean_dec_ref(v_a_00___x40___internal___hyg_634_);
    v_res_636_ = log10(v_a_00___x40___internal___hyg_1__boxed_635_);
    v_r_637_ = crate::leanh::lean_box_float(v_res_636_);
    return v_r_637_;
}
pub unsafe fn l_Float_pow___boxed(
    mut v_a_00___x40___internal___hyg_640_: *mut crate::leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_641_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_642_: f64 = 0.0;
    let mut v_a_00___x40___internal___hyg_2__boxed_643_: f64 = 0.0;
    let mut v_res_644_: f64 = 0.0;
    let mut v_r_645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_642_ =
        crate::leanh::lean_unbox_float(v_a_00___x40___internal___hyg_640_);
    crate::leanh::lean_dec_ref(v_a_00___x40___internal___hyg_640_);
    v_a_00___x40___internal___hyg_2__boxed_643_ =
        crate::leanh::lean_unbox_float(v_a_00___x40___internal___hyg_641_);
    crate::leanh::lean_dec_ref(v_a_00___x40___internal___hyg_641_);
    v_res_644_ = pow(
        v_a_00___x40___internal___hyg_1__boxed_642_,
        v_a_00___x40___internal___hyg_2__boxed_643_,
    );
    v_r_645_ = crate::leanh::lean_box_float(v_res_644_);
    return v_r_645_;
}
pub unsafe fn l_Float_sqrt___boxed(
    mut v_a_00___x40___internal___hyg_647_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_648_: f64 = 0.0;
    let mut v_res_649_: f64 = 0.0;
    let mut v_r_650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_648_ =
        crate::leanh::lean_unbox_float(v_a_00___x40___internal___hyg_647_);
    crate::leanh::lean_dec_ref(v_a_00___x40___internal___hyg_647_);
    v_res_649_ = sqrt(v_a_00___x40___internal___hyg_1__boxed_648_);
    v_r_650_ = crate::leanh::lean_box_float(v_res_649_);
    return v_r_650_;
}
pub unsafe fn l_Float_cbrt___boxed(
    mut v_a_00___x40___internal___hyg_652_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_653_: f64 = 0.0;
    let mut v_res_654_: f64 = 0.0;
    let mut v_r_655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_653_ =
        crate::leanh::lean_unbox_float(v_a_00___x40___internal___hyg_652_);
    crate::leanh::lean_dec_ref(v_a_00___x40___internal___hyg_652_);
    v_res_654_ = cbrt(v_a_00___x40___internal___hyg_1__boxed_653_);
    v_r_655_ = crate::leanh::lean_box_float(v_res_654_);
    return v_r_655_;
}
pub unsafe fn l_Float_ceil___boxed(
    mut v_a_00___x40___internal___hyg_657_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_658_: f64 = 0.0;
    let mut v_res_659_: f64 = 0.0;
    let mut v_r_660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_658_ =
        crate::leanh::lean_unbox_float(v_a_00___x40___internal___hyg_657_);
    crate::leanh::lean_dec_ref(v_a_00___x40___internal___hyg_657_);
    v_res_659_ = ceil(v_a_00___x40___internal___hyg_1__boxed_658_);
    v_r_660_ = crate::leanh::lean_box_float(v_res_659_);
    return v_r_660_;
}
pub unsafe fn l_Float_floor___boxed(
    mut v_a_00___x40___internal___hyg_662_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_663_: f64 = 0.0;
    let mut v_res_664_: f64 = 0.0;
    let mut v_r_665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_663_ =
        crate::leanh::lean_unbox_float(v_a_00___x40___internal___hyg_662_);
    crate::leanh::lean_dec_ref(v_a_00___x40___internal___hyg_662_);
    v_res_664_ = floor(v_a_00___x40___internal___hyg_1__boxed_663_);
    v_r_665_ = crate::leanh::lean_box_float(v_res_664_);
    return v_r_665_;
}
pub unsafe fn l_Float_round___boxed(
    mut v_a_00___x40___internal___hyg_667_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_668_: f64 = 0.0;
    let mut v_res_669_: f64 = 0.0;
    let mut v_r_670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_668_ =
        crate::leanh::lean_unbox_float(v_a_00___x40___internal___hyg_667_);
    crate::leanh::lean_dec_ref(v_a_00___x40___internal___hyg_667_);
    v_res_669_ = round(v_a_00___x40___internal___hyg_1__boxed_668_);
    v_r_670_ = crate::leanh::lean_box_float(v_res_669_);
    return v_r_670_;
}
pub unsafe fn l_Float_abs___boxed(
    mut v_a_00___x40___internal___hyg_672_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_673_: f64 = 0.0;
    let mut v_res_674_: f64 = 0.0;
    let mut v_r_675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_673_ =
        crate::leanh::lean_unbox_float(v_a_00___x40___internal___hyg_672_);
    crate::leanh::lean_dec_ref(v_a_00___x40___internal___hyg_672_);
    v_res_674_ = fabs(v_a_00___x40___internal___hyg_1__boxed_673_);
    v_r_675_ = crate::leanh::lean_box_float(v_res_674_);
    return v_r_675_;
}
pub unsafe fn l_instMinFloat___lam__0(mut v_x_678_: f64, mut v_y_679_: f64) -> f64 {
    let mut v___x_680_: u8 = 0;
    v___x_680_ = lean_float_decLe(v_x_678_, v_y_679_);
    if v___x_680_ == 0 {
        return v_y_679_;
    } else {
        return v_x_678_;
    }
}
pub unsafe fn l_instMinFloat___lam__0___boxed(
    mut v_x_681_: *mut crate::leanh::LeanObject,
    mut v_y_682_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_683_: f64 = 0.0;
    let mut v_y_boxed_684_: f64 = 0.0;
    let mut v_res_685_: f64 = 0.0;
    let mut v_r_686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_683_ = crate::leanh::lean_unbox_float(v_x_681_);
    crate::leanh::lean_dec_ref(v_x_681_);
    v_y_boxed_684_ = crate::leanh::lean_unbox_float(v_y_682_);
    crate::leanh::lean_dec_ref(v_y_682_);
    v_res_685_ = l_instMinFloat___lam__0(v_x_boxed_683_, v_y_boxed_684_);
    v_r_686_ = crate::leanh::lean_box_float(v_res_685_);
    return v_r_686_;
}
pub unsafe fn l_instMaxFloat___lam__0(mut v_x_689_: f64, mut v_y_690_: f64) -> f64 {
    let mut v___x_691_: u8 = 0;
    v___x_691_ = lean_float_decLe(v_x_689_, v_y_690_);
    if v___x_691_ == 0 {
        return v_x_689_;
    } else {
        return v_y_690_;
    }
}
pub unsafe fn l_instMaxFloat___lam__0___boxed(
    mut v_x_692_: *mut crate::leanh::LeanObject,
    mut v_y_693_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_694_: f64 = 0.0;
    let mut v_y_boxed_695_: f64 = 0.0;
    let mut v_res_696_: f64 = 0.0;
    let mut v_r_697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_694_ = crate::leanh::lean_unbox_float(v_x_692_);
    crate::leanh::lean_dec_ref(v_x_692_);
    v_y_boxed_695_ = crate::leanh::lean_unbox_float(v_y_693_);
    crate::leanh::lean_dec_ref(v_y_693_);
    v_res_696_ = l_instMaxFloat___lam__0(v_x_boxed_694_, v_y_boxed_695_);
    v_r_697_ = crate::leanh::lean_box_float(v_res_696_);
    return v_r_697_;
}
pub unsafe fn l_Float_scaleB___boxed(
    mut v_x_702_: *mut crate::leanh::LeanObject,
    mut v_i_703_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_704_: f64 = 0.0;
    let mut v_res_705_: f64 = 0.0;
    let mut v_r_706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_704_ = crate::leanh::lean_unbox_float(v_x_702_);
    crate::leanh::lean_dec_ref(v_x_702_);
    v_res_705_ = lean_float_scaleb(v_x_boxed_704_, v_i_703_);
    crate::leanh::lean_dec(v_i_703_);
    v_r_706_ = crate::leanh::lean_box_float(v_res_705_);
    return v_r_706_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Float(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_ToString_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_instLTFloat = _init_l_instLTFloat();
    crate::leanh::lean_mark_persistent(l_instLTFloat);
    l_instLEFloat = _init_l_instLEFloat();
    crate::leanh::lean_mark_persistent(l_instLEFloat);
    l_instInhabitedFloat = _init_l_instInhabitedFloat();
    l_instReprAtomFloat = _init_l_instReprAtomFloat();
    crate::leanh::lean_mark_persistent(l_instReprAtomFloat);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Float(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Float(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_ToString_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Float(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Float(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_Float(builtin);
}
