// Lean compiler output
// Module: Init.Data.Float
// Imports: Init.Data.ToString.Basic
use crate::ffi::{
    acos, acosh, asin, asinh, atan, atan2, atanh, cbrt, ceil, cos, cosh, exp, exp2, fabs, floor,
    lean_float_add, lean_float_beq, lean_float_decLe, lean_float_decLt, lean_float_div,
    lean_float_frexp, lean_float_isfinite, lean_float_isinf, lean_float_isnan, lean_float_mul,
    lean_float_negate, lean_float_of_bits, lean_float_scaleb, lean_float_sub, lean_float_to_bits,
    lean_float_to_string, lean_float_to_uint8, lean_float_to_uint16, lean_float_to_uint32,
    lean_float_to_uint64, lean_float_to_usize, lean_uint8_to_float, lean_uint16_to_float,
    lean_uint32_to_float, lean_uint64_to_float, lean_usize_to_float, log, log2, log10, pow, round,
    sin, sinh, sqrt, tan, tanh,
};
use crate::r#gen::Init::Data::Repr::l_Repr_addAppParen;
use crate::r#gen::Init::Data::ToString::Basic::{
    initialize_Init_Data_ToString_Basic, runtime_initialize_Init_Data_ToString_Basic,
};
pub static l_floatSpec___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_floatSpec___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_floatSpec___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_floatSpec___closed__0_value) as *mut leanh::LeanObject;
pub static l_floatSpec___closed__1_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 0,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_floatSpec___closed__0_value) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_floatSpec___closed__0_value) as *mut leanh::LeanObject,
        ],
    };
static mut l_floatSpec___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_floatSpec___closed__1_value) as *mut leanh::LeanObject;
pub static mut l_floatSpec: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_floatSpec___closed__1_value) as *mut leanh::LeanObject;
pub static l_instAddFloat___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Float_add___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instAddFloat___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instAddFloat___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_instAddFloat: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instAddFloat___closed__0_value) as *mut leanh::LeanObject;
pub static l_instSubFloat___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Float_sub___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instSubFloat___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instSubFloat___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_instSubFloat: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instSubFloat___closed__0_value) as *mut leanh::LeanObject;
pub static l_instMulFloat___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Float_mul___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instMulFloat___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instMulFloat___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_instMulFloat: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instMulFloat___closed__0_value) as *mut leanh::LeanObject;
pub static l_instDivFloat___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Float_div___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instDivFloat___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instDivFloat___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_instDivFloat: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instDivFloat___closed__0_value) as *mut leanh::LeanObject;
pub static l_instNegFloat___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Float_neg___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instNegFloat___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instNegFloat___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_instNegFloat: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instNegFloat___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_instLTFloat: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_instLEFloat: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_instBEqFloat___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Float_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instBEqFloat___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instBEqFloat___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_instBEqFloat: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instBEqFloat___closed__0_value) as *mut leanh::LeanObject;
pub static l_instToStringFloat___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Float_toString___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instToStringFloat___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instToStringFloat___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_instToStringFloat: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instToStringFloat___closed__0_value) as *mut leanh::LeanObject;
static mut l_instInhabitedFloat___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_instInhabitedFloat___closed__0: f64 = 0.0;
pub static mut l_instInhabitedFloat: f64 = 0.0;
pub static l_instReprFloat___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Float_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instReprFloat___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instReprFloat___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_instReprFloat: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instReprFloat___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_instReprAtomFloat: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_instHomogeneousPowFloat___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Float_pow___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instHomogeneousPowFloat___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instHomogeneousPowFloat___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_instHomogeneousPowFloat: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instHomogeneousPowFloat___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_instMinFloat___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_instMinFloat___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instMinFloat___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instMinFloat___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_instMinFloat: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instMinFloat___closed__0_value) as *mut leanh::LeanObject;
pub static l_instMaxFloat___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_instMaxFloat___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instMaxFloat___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instMaxFloat___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_instMaxFloat: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instMaxFloat___closed__0_value) as *mut leanh::LeanObject;
pub unsafe fn l_floatSpec___lam__0(
    mut v_x_354_: *mut leanh::LeanObject,
    mut v_x_355_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_356_: u8 = 0;
    v___x_356_ = 1;
    return v___x_356_;
}
pub unsafe fn l_floatSpec___lam__0___boxed(
    mut v_x_357_: *mut leanh::LeanObject,
    mut v_x_358_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_359_: u8 = 0;
    let mut v_r_360_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_359_ = l_floatSpec___lam__0(v_x_357_, v_x_358_);
    v_r_360_ = leanh::lean_box((v_res_359_) as usize);
    return v_r_360_;
}
pub unsafe fn l_Float_add___boxed(
    mut v_a_00___x40___internal___hyg_368_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_369_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_370_: f64 = 0.0;
    let mut v_a_00___x40___internal___hyg_2__boxed_371_: f64 = 0.0;
    let mut v_res_372_: f64 = 0.0;
    let mut v_r_373_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_370_ =
        leanh::lean_unbox_float(v_a_00___x40___internal___hyg_368_);
    leanh::lean_dec_ref(v_a_00___x40___internal___hyg_368_);
    v_a_00___x40___internal___hyg_2__boxed_371_ =
        leanh::lean_unbox_float(v_a_00___x40___internal___hyg_369_);
    leanh::lean_dec_ref(v_a_00___x40___internal___hyg_369_);
    v_res_372_ = lean_float_add(
        v_a_00___x40___internal___hyg_1__boxed_370_,
        v_a_00___x40___internal___hyg_2__boxed_371_,
    );
    v_r_373_ = leanh::lean_box_float(v_res_372_);
    return v_r_373_;
}
pub unsafe fn l_Float_sub___boxed(
    mut v_a_00___x40___internal___hyg_376_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_377_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_378_: f64 = 0.0;
    let mut v_a_00___x40___internal___hyg_2__boxed_379_: f64 = 0.0;
    let mut v_res_380_: f64 = 0.0;
    let mut v_r_381_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_378_ =
        leanh::lean_unbox_float(v_a_00___x40___internal___hyg_376_);
    leanh::lean_dec_ref(v_a_00___x40___internal___hyg_376_);
    v_a_00___x40___internal___hyg_2__boxed_379_ =
        leanh::lean_unbox_float(v_a_00___x40___internal___hyg_377_);
    leanh::lean_dec_ref(v_a_00___x40___internal___hyg_377_);
    v_res_380_ = lean_float_sub(
        v_a_00___x40___internal___hyg_1__boxed_378_,
        v_a_00___x40___internal___hyg_2__boxed_379_,
    );
    v_r_381_ = leanh::lean_box_float(v_res_380_);
    return v_r_381_;
}
pub unsafe fn l_Float_mul___boxed(
    mut v_a_00___x40___internal___hyg_384_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_385_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_386_: f64 = 0.0;
    let mut v_a_00___x40___internal___hyg_2__boxed_387_: f64 = 0.0;
    let mut v_res_388_: f64 = 0.0;
    let mut v_r_389_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_386_ =
        leanh::lean_unbox_float(v_a_00___x40___internal___hyg_384_);
    leanh::lean_dec_ref(v_a_00___x40___internal___hyg_384_);
    v_a_00___x40___internal___hyg_2__boxed_387_ =
        leanh::lean_unbox_float(v_a_00___x40___internal___hyg_385_);
    leanh::lean_dec_ref(v_a_00___x40___internal___hyg_385_);
    v_res_388_ = lean_float_mul(
        v_a_00___x40___internal___hyg_1__boxed_386_,
        v_a_00___x40___internal___hyg_2__boxed_387_,
    );
    v_r_389_ = leanh::lean_box_float(v_res_388_);
    return v_r_389_;
}
pub unsafe fn l_Float_div___boxed(
    mut v_a_00___x40___internal___hyg_392_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_393_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_394_: f64 = 0.0;
    let mut v_a_00___x40___internal___hyg_2__boxed_395_: f64 = 0.0;
    let mut v_res_396_: f64 = 0.0;
    let mut v_r_397_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_394_ =
        leanh::lean_unbox_float(v_a_00___x40___internal___hyg_392_);
    leanh::lean_dec_ref(v_a_00___x40___internal___hyg_392_);
    v_a_00___x40___internal___hyg_2__boxed_395_ =
        leanh::lean_unbox_float(v_a_00___x40___internal___hyg_393_);
    leanh::lean_dec_ref(v_a_00___x40___internal___hyg_393_);
    v_res_396_ = lean_float_div(
        v_a_00___x40___internal___hyg_1__boxed_394_,
        v_a_00___x40___internal___hyg_2__boxed_395_,
    );
    v_r_397_ = leanh::lean_box_float(v_res_396_);
    return v_r_397_;
}
pub unsafe fn l_Float_neg___boxed(
    mut v_a_00___x40___internal___hyg_399_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_400_: f64 = 0.0;
    let mut v_res_401_: f64 = 0.0;
    let mut v_r_402_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_400_ =
        leanh::lean_unbox_float(v_a_00___x40___internal___hyg_399_);
    leanh::lean_dec_ref(v_a_00___x40___internal___hyg_399_);
    v_res_401_ = lean_float_negate(v_a_00___x40___internal___hyg_1__boxed_400_);
    v_r_402_ = leanh::lean_box_float(v_res_401_);
    return v_r_402_;
}
pub unsafe fn l_Float_ofBits___boxed(
    mut v_a_00___x40___internal___hyg_404_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_405_: u64 = 0;
    let mut v_res_406_: f64 = 0.0;
    let mut v_r_407_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_405_ =
        leanh::lean_unbox_uint64(v_a_00___x40___internal___hyg_404_);
    leanh::lean_dec_ref(v_a_00___x40___internal___hyg_404_);
    v_res_406_ = lean_float_of_bits(v_a_00___x40___internal___hyg_1__boxed_405_);
    v_r_407_ = leanh::lean_box_float(v_res_406_);
    return v_r_407_;
}
pub unsafe fn l_Float_toBits___boxed(
    mut v_a_00___x40___internal___hyg_409_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_410_: f64 = 0.0;
    let mut v_res_411_: u64 = 0;
    let mut v_r_412_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_410_ =
        leanh::lean_unbox_float(v_a_00___x40___internal___hyg_409_);
    leanh::lean_dec_ref(v_a_00___x40___internal___hyg_409_);
    v_res_411_ = lean_float_to_bits(v_a_00___x40___internal___hyg_1__boxed_410_);
    v_r_412_ = leanh::lean_box_uint64(v_res_411_);
    return v_r_412_;
}
pub unsafe fn _init_l_instLTFloat() -> *mut leanh::LeanObject {
    let mut v___x_423_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_423_ = leanh::lean_box(0);
    return v___x_423_;
}
pub unsafe fn _init_l_instLEFloat() -> *mut leanh::LeanObject {
    let mut v___x_424_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_424_ = leanh::lean_box(0);
    return v___x_424_;
}
pub unsafe fn l_Float_beq___boxed(
    mut v_a_427_: *mut leanh::LeanObject,
    mut v_b_428_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_429_: f64 = 0.0;
    let mut v_b_boxed_430_: f64 = 0.0;
    let mut v_res_431_: u8 = 0;
    let mut v_r_432_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_429_ = leanh::lean_unbox_float(v_a_427_);
    leanh::lean_dec_ref(v_a_427_);
    v_b_boxed_430_ = leanh::lean_unbox_float(v_b_428_);
    leanh::lean_dec_ref(v_b_428_);
    v_res_431_ = lean_float_beq(v_a_boxed_429_, v_b_boxed_430_);
    v_r_432_ = leanh::lean_box((v_res_431_) as usize);
    return v_r_432_;
}
pub unsafe fn l_Float_decLt___boxed(
    mut v_a_437_: *mut leanh::LeanObject,
    mut v_b_438_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_439_: f64 = 0.0;
    let mut v_b_boxed_440_: f64 = 0.0;
    let mut v_res_441_: u8 = 0;
    let mut v_r_442_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_439_ = leanh::lean_unbox_float(v_a_437_);
    leanh::lean_dec_ref(v_a_437_);
    v_b_boxed_440_ = leanh::lean_unbox_float(v_b_438_);
    leanh::lean_dec_ref(v_b_438_);
    v_res_441_ = lean_float_decLt(v_a_boxed_439_, v_b_boxed_440_);
    v_r_442_ = leanh::lean_box((v_res_441_) as usize);
    return v_r_442_;
}
pub unsafe fn l_Float_decLe___boxed(
    mut v_a_445_: *mut leanh::LeanObject,
    mut v_b_446_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_447_: f64 = 0.0;
    let mut v_b_boxed_448_: f64 = 0.0;
    let mut v_res_449_: u8 = 0;
    let mut v_r_450_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_447_ = leanh::lean_unbox_float(v_a_445_);
    leanh::lean_dec_ref(v_a_445_);
    v_b_boxed_448_ = leanh::lean_unbox_float(v_b_446_);
    leanh::lean_dec_ref(v_b_446_);
    v_res_449_ = lean_float_decLe(v_a_boxed_447_, v_b_boxed_448_);
    v_r_450_ = leanh::lean_box((v_res_449_) as usize);
    return v_r_450_;
}
pub unsafe fn l_Float_toString___boxed(
    mut v_a_00___x40___internal___hyg_452_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_453_: f64 = 0.0;
    let mut v_res_454_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_453_ =
        leanh::lean_unbox_float(v_a_00___x40___internal___hyg_452_);
    leanh::lean_dec_ref(v_a_00___x40___internal___hyg_452_);
    v_res_454_ = lean_float_to_string(v_a_00___x40___internal___hyg_1__boxed_453_);
    return v_res_454_;
}
pub unsafe fn l_Float_toUInt8___boxed(
    mut v_a_00___x40___internal___hyg_456_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_457_: f64 = 0.0;
    let mut v_res_458_: u8 = 0;
    let mut v_r_459_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_457_ =
        leanh::lean_unbox_float(v_a_00___x40___internal___hyg_456_);
    leanh::lean_dec_ref(v_a_00___x40___internal___hyg_456_);
    v_res_458_ = lean_float_to_uint8(v_a_00___x40___internal___hyg_1__boxed_457_);
    v_r_459_ = leanh::lean_box((v_res_458_) as usize);
    return v_r_459_;
}
pub unsafe fn l_Float_toUInt16___boxed(
    mut v_a_00___x40___internal___hyg_461_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_462_: f64 = 0.0;
    let mut v_res_463_: u16 = 0;
    let mut v_r_464_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_462_ =
        leanh::lean_unbox_float(v_a_00___x40___internal___hyg_461_);
    leanh::lean_dec_ref(v_a_00___x40___internal___hyg_461_);
    v_res_463_ = lean_float_to_uint16(v_a_00___x40___internal___hyg_1__boxed_462_);
    v_r_464_ = leanh::lean_box((v_res_463_) as usize);
    return v_r_464_;
}
pub unsafe fn l_Float_toUInt32___boxed(
    mut v_a_00___x40___internal___hyg_466_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_467_: f64 = 0.0;
    let mut v_res_468_: u32 = 0;
    let mut v_r_469_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_467_ =
        leanh::lean_unbox_float(v_a_00___x40___internal___hyg_466_);
    leanh::lean_dec_ref(v_a_00___x40___internal___hyg_466_);
    v_res_468_ = lean_float_to_uint32(v_a_00___x40___internal___hyg_1__boxed_467_);
    v_r_469_ = leanh::lean_box_uint32(v_res_468_);
    return v_r_469_;
}
pub unsafe fn l_Float_toUInt64___boxed(
    mut v_a_00___x40___internal___hyg_471_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_472_: f64 = 0.0;
    let mut v_res_473_: u64 = 0;
    let mut v_r_474_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_472_ =
        leanh::lean_unbox_float(v_a_00___x40___internal___hyg_471_);
    leanh::lean_dec_ref(v_a_00___x40___internal___hyg_471_);
    v_res_473_ = lean_float_to_uint64(v_a_00___x40___internal___hyg_1__boxed_472_);
    v_r_474_ = leanh::lean_box_uint64(v_res_473_);
    return v_r_474_;
}
pub unsafe fn l_Float_toUSize___boxed(
    mut v_a_00___x40___internal___hyg_476_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_477_: f64 = 0.0;
    let mut v_res_478_: usize = 0;
    let mut v_r_479_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_477_ =
        leanh::lean_unbox_float(v_a_00___x40___internal___hyg_476_);
    leanh::lean_dec_ref(v_a_00___x40___internal___hyg_476_);
    v_res_478_ = lean_float_to_usize(v_a_00___x40___internal___hyg_1__boxed_477_);
    v_r_479_ = leanh::lean_box_usize(v_res_478_);
    return v_r_479_;
}
pub unsafe fn l_Float_isNaN___boxed(
    mut v_a_00___x40___internal___hyg_481_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_482_: f64 = 0.0;
    let mut v_res_483_: u8 = 0;
    let mut v_r_484_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_482_ =
        leanh::lean_unbox_float(v_a_00___x40___internal___hyg_481_);
    leanh::lean_dec_ref(v_a_00___x40___internal___hyg_481_);
    v_res_483_ = lean_float_isnan(v_a_00___x40___internal___hyg_1__boxed_482_);
    v_r_484_ = leanh::lean_box((v_res_483_) as usize);
    return v_r_484_;
}
pub unsafe fn l_Float_isFinite___boxed(
    mut v_a_00___x40___internal___hyg_486_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_487_: f64 = 0.0;
    let mut v_res_488_: u8 = 0;
    let mut v_r_489_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_487_ =
        leanh::lean_unbox_float(v_a_00___x40___internal___hyg_486_);
    leanh::lean_dec_ref(v_a_00___x40___internal___hyg_486_);
    v_res_488_ = lean_float_isfinite(v_a_00___x40___internal___hyg_1__boxed_487_);
    v_r_489_ = leanh::lean_box((v_res_488_) as usize);
    return v_r_489_;
}
pub unsafe fn l_Float_isInf___boxed(
    mut v_a_00___x40___internal___hyg_491_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_492_: f64 = 0.0;
    let mut v_res_493_: u8 = 0;
    let mut v_r_494_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_492_ =
        leanh::lean_unbox_float(v_a_00___x40___internal___hyg_491_);
    leanh::lean_dec_ref(v_a_00___x40___internal___hyg_491_);
    v_res_493_ = lean_float_isinf(v_a_00___x40___internal___hyg_1__boxed_492_);
    v_r_494_ = leanh::lean_box((v_res_493_) as usize);
    return v_r_494_;
}
pub unsafe fn l_Float_frExp___boxed(
    mut v_a_00___x40___internal___hyg_496_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_497_: f64 = 0.0;
    let mut v_res_498_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_497_ =
        leanh::lean_unbox_float(v_a_00___x40___internal___hyg_496_);
    leanh::lean_dec_ref(v_a_00___x40___internal___hyg_496_);
    v_res_498_ = lean_float_frexp(v_a_00___x40___internal___hyg_1__boxed_497_);
    return v_res_498_;
}
pub unsafe fn l_UInt8_toFloat___boxed(
    mut v_n_502_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_n_boxed_503_: u8 = 0;
    let mut v_res_504_: f64 = 0.0;
    let mut v_r_505_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_n_boxed_503_ = (leanh::lean_unbox(v_n_502_) as u8);
    v_res_504_ = lean_uint8_to_float(v_n_boxed_503_);
    v_r_505_ = leanh::lean_box_float(v_res_504_);
    return v_r_505_;
}
pub unsafe fn l_UInt16_toFloat___boxed(
    mut v_n_507_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_n_boxed_508_: u16 = 0;
    let mut v_res_509_: f64 = 0.0;
    let mut v_r_510_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_n_boxed_508_ = (leanh::lean_unbox(v_n_507_) as u16);
    v_res_509_ = lean_uint16_to_float(v_n_boxed_508_);
    v_r_510_ = leanh::lean_box_float(v_res_509_);
    return v_r_510_;
}
pub unsafe fn l_UInt32_toFloat___boxed(
    mut v_n_512_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_n_boxed_513_: u32 = 0;
    let mut v_res_514_: f64 = 0.0;
    let mut v_r_515_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_n_boxed_513_ = leanh::lean_unbox_uint32(v_n_512_);
    leanh::lean_dec(v_n_512_);
    v_res_514_ = lean_uint32_to_float(v_n_boxed_513_);
    v_r_515_ = leanh::lean_box_float(v_res_514_);
    return v_r_515_;
}
pub unsafe fn l_UInt64_toFloat___boxed(
    mut v_n_517_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_n_boxed_518_: u64 = 0;
    let mut v_res_519_: f64 = 0.0;
    let mut v_r_520_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_n_boxed_518_ = leanh::lean_unbox_uint64(v_n_517_);
    leanh::lean_dec_ref(v_n_517_);
    v_res_519_ = lean_uint64_to_float(v_n_boxed_518_);
    v_r_520_ = leanh::lean_box_float(v_res_519_);
    return v_r_520_;
}
pub unsafe fn l_USize_toFloat___boxed(
    mut v_n_522_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_n_boxed_523_: usize = 0;
    let mut v_res_524_: f64 = 0.0;
    let mut v_r_525_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_n_boxed_523_ = leanh::lean_unbox_usize(v_n_522_);
    leanh::lean_dec(v_n_522_);
    v_res_524_ = lean_usize_to_float(v_n_boxed_523_);
    v_r_525_ = leanh::lean_box_float(v_res_524_);
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
    v___x_528_ = leanh::lean_float_once(
        core::ptr::addr_of_mut!(l_instInhabitedFloat___closed__0),
        core::ptr::addr_of_mut!(l_instInhabitedFloat___closed__0_once),
        _init_l_instInhabitedFloat___closed__0,
    );
    return v___x_528_;
}
pub unsafe fn l_Float_repr(
    mut v_n_529_: f64,
    mut v_prec_530_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_531_: f64 = 0.0;
    let mut v___x_532_: u8 = 0;
    v___x_531_ = leanh::lean_float_once(
        core::ptr::addr_of_mut!(l_instInhabitedFloat___closed__0),
        core::ptr::addr_of_mut!(l_instInhabitedFloat___closed__0_once),
        _init_l_instInhabitedFloat___closed__0,
    );
    v___x_532_ = lean_float_decLt(v_n_529_, v___x_531_);
    if v___x_532_ == 0 {
        let mut v___x_533_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_534_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_533_ = lean_float_to_string(v_n_529_);
        v___x_534_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_534_, 0, v___x_533_);
        return v___x_534_;
    } else {
        let mut v___x_535_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_536_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_537_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_535_ = lean_float_to_string(v_n_529_);
        v___x_536_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_536_, 0, v___x_535_);
        v___x_537_ = l_Repr_addAppParen(v___x_536_, v_prec_530_);
        return v___x_537_;
    }
}
pub unsafe fn l_Float_repr___boxed(
    mut v_n_538_: *mut leanh::LeanObject,
    mut v_prec_539_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_n_boxed_540_: f64 = 0.0;
    let mut v_res_541_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_n_boxed_540_ = leanh::lean_unbox_float(v_n_538_);
    leanh::lean_dec_ref(v_n_538_);
    v_res_541_ = l_Float_repr(v_n_boxed_540_, v_prec_539_);
    leanh::lean_dec(v_prec_539_);
    return v_res_541_;
}
pub unsafe fn _init_l_instReprAtomFloat() -> *mut leanh::LeanObject {
    let mut v___x_544_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_544_ = leanh::lean_box(0);
    return v___x_544_;
}
pub unsafe fn l_Float_sin___boxed(
    mut v_a_00___x40___internal___hyg_546_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_547_: f64 = 0.0;
    let mut v_res_548_: f64 = 0.0;
    let mut v_r_549_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_547_ =
        leanh::lean_unbox_float(v_a_00___x40___internal___hyg_546_);
    leanh::lean_dec_ref(v_a_00___x40___internal___hyg_546_);
    v_res_548_ = sin(v_a_00___x40___internal___hyg_1__boxed_547_);
    v_r_549_ = leanh::lean_box_float(v_res_548_);
    return v_r_549_;
}
pub unsafe fn l_Float_cos___boxed(
    mut v_a_00___x40___internal___hyg_551_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_552_: f64 = 0.0;
    let mut v_res_553_: f64 = 0.0;
    let mut v_r_554_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_552_ =
        leanh::lean_unbox_float(v_a_00___x40___internal___hyg_551_);
    leanh::lean_dec_ref(v_a_00___x40___internal___hyg_551_);
    v_res_553_ = cos(v_a_00___x40___internal___hyg_1__boxed_552_);
    v_r_554_ = leanh::lean_box_float(v_res_553_);
    return v_r_554_;
}
pub unsafe fn l_Float_tan___boxed(
    mut v_a_00___x40___internal___hyg_556_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_557_: f64 = 0.0;
    let mut v_res_558_: f64 = 0.0;
    let mut v_r_559_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_557_ =
        leanh::lean_unbox_float(v_a_00___x40___internal___hyg_556_);
    leanh::lean_dec_ref(v_a_00___x40___internal___hyg_556_);
    v_res_558_ = tan(v_a_00___x40___internal___hyg_1__boxed_557_);
    v_r_559_ = leanh::lean_box_float(v_res_558_);
    return v_r_559_;
}
pub unsafe fn l_Float_asin___boxed(
    mut v_a_00___x40___internal___hyg_561_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_562_: f64 = 0.0;
    let mut v_res_563_: f64 = 0.0;
    let mut v_r_564_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_562_ =
        leanh::lean_unbox_float(v_a_00___x40___internal___hyg_561_);
    leanh::lean_dec_ref(v_a_00___x40___internal___hyg_561_);
    v_res_563_ = asin(v_a_00___x40___internal___hyg_1__boxed_562_);
    v_r_564_ = leanh::lean_box_float(v_res_563_);
    return v_r_564_;
}
pub unsafe fn l_Float_acos___boxed(
    mut v_a_00___x40___internal___hyg_566_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_567_: f64 = 0.0;
    let mut v_res_568_: f64 = 0.0;
    let mut v_r_569_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_567_ =
        leanh::lean_unbox_float(v_a_00___x40___internal___hyg_566_);
    leanh::lean_dec_ref(v_a_00___x40___internal___hyg_566_);
    v_res_568_ = acos(v_a_00___x40___internal___hyg_1__boxed_567_);
    v_r_569_ = leanh::lean_box_float(v_res_568_);
    return v_r_569_;
}
pub unsafe fn l_Float_atan___boxed(
    mut v_a_00___x40___internal___hyg_571_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_572_: f64 = 0.0;
    let mut v_res_573_: f64 = 0.0;
    let mut v_r_574_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_572_ =
        leanh::lean_unbox_float(v_a_00___x40___internal___hyg_571_);
    leanh::lean_dec_ref(v_a_00___x40___internal___hyg_571_);
    v_res_573_ = atan(v_a_00___x40___internal___hyg_1__boxed_572_);
    v_r_574_ = leanh::lean_box_float(v_res_573_);
    return v_r_574_;
}
pub unsafe fn l_Float_atan2___boxed(
    mut v_y_577_: *mut leanh::LeanObject,
    mut v_x_578_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_y_boxed_579_: f64 = 0.0;
    let mut v_x_boxed_580_: f64 = 0.0;
    let mut v_res_581_: f64 = 0.0;
    let mut v_r_582_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_y_boxed_579_ = leanh::lean_unbox_float(v_y_577_);
    leanh::lean_dec_ref(v_y_577_);
    v_x_boxed_580_ = leanh::lean_unbox_float(v_x_578_);
    leanh::lean_dec_ref(v_x_578_);
    v_res_581_ = atan2(v_y_boxed_579_, v_x_boxed_580_);
    v_r_582_ = leanh::lean_box_float(v_res_581_);
    return v_r_582_;
}
pub unsafe fn l_Float_sinh___boxed(
    mut v_a_00___x40___internal___hyg_584_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_585_: f64 = 0.0;
    let mut v_res_586_: f64 = 0.0;
    let mut v_r_587_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_585_ =
        leanh::lean_unbox_float(v_a_00___x40___internal___hyg_584_);
    leanh::lean_dec_ref(v_a_00___x40___internal___hyg_584_);
    v_res_586_ = sinh(v_a_00___x40___internal___hyg_1__boxed_585_);
    v_r_587_ = leanh::lean_box_float(v_res_586_);
    return v_r_587_;
}
pub unsafe fn l_Float_cosh___boxed(
    mut v_a_00___x40___internal___hyg_589_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_590_: f64 = 0.0;
    let mut v_res_591_: f64 = 0.0;
    let mut v_r_592_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_590_ =
        leanh::lean_unbox_float(v_a_00___x40___internal___hyg_589_);
    leanh::lean_dec_ref(v_a_00___x40___internal___hyg_589_);
    v_res_591_ = cosh(v_a_00___x40___internal___hyg_1__boxed_590_);
    v_r_592_ = leanh::lean_box_float(v_res_591_);
    return v_r_592_;
}
pub unsafe fn l_Float_tanh___boxed(
    mut v_a_00___x40___internal___hyg_594_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_595_: f64 = 0.0;
    let mut v_res_596_: f64 = 0.0;
    let mut v_r_597_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_595_ =
        leanh::lean_unbox_float(v_a_00___x40___internal___hyg_594_);
    leanh::lean_dec_ref(v_a_00___x40___internal___hyg_594_);
    v_res_596_ = tanh(v_a_00___x40___internal___hyg_1__boxed_595_);
    v_r_597_ = leanh::lean_box_float(v_res_596_);
    return v_r_597_;
}
pub unsafe fn l_Float_asinh___boxed(
    mut v_a_00___x40___internal___hyg_599_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_600_: f64 = 0.0;
    let mut v_res_601_: f64 = 0.0;
    let mut v_r_602_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_600_ =
        leanh::lean_unbox_float(v_a_00___x40___internal___hyg_599_);
    leanh::lean_dec_ref(v_a_00___x40___internal___hyg_599_);
    v_res_601_ = asinh(v_a_00___x40___internal___hyg_1__boxed_600_);
    v_r_602_ = leanh::lean_box_float(v_res_601_);
    return v_r_602_;
}
pub unsafe fn l_Float_acosh___boxed(
    mut v_a_00___x40___internal___hyg_604_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_605_: f64 = 0.0;
    let mut v_res_606_: f64 = 0.0;
    let mut v_r_607_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_605_ =
        leanh::lean_unbox_float(v_a_00___x40___internal___hyg_604_);
    leanh::lean_dec_ref(v_a_00___x40___internal___hyg_604_);
    v_res_606_ = acosh(v_a_00___x40___internal___hyg_1__boxed_605_);
    v_r_607_ = leanh::lean_box_float(v_res_606_);
    return v_r_607_;
}
pub unsafe fn l_Float_atanh___boxed(
    mut v_a_00___x40___internal___hyg_609_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_610_: f64 = 0.0;
    let mut v_res_611_: f64 = 0.0;
    let mut v_r_612_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_610_ =
        leanh::lean_unbox_float(v_a_00___x40___internal___hyg_609_);
    leanh::lean_dec_ref(v_a_00___x40___internal___hyg_609_);
    v_res_611_ = atanh(v_a_00___x40___internal___hyg_1__boxed_610_);
    v_r_612_ = leanh::lean_box_float(v_res_611_);
    return v_r_612_;
}
pub unsafe fn l_Float_exp___boxed(
    mut v_x_614_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_boxed_615_: f64 = 0.0;
    let mut v_res_616_: f64 = 0.0;
    let mut v_r_617_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_615_ = leanh::lean_unbox_float(v_x_614_);
    leanh::lean_dec_ref(v_x_614_);
    v_res_616_ = exp(v_x_boxed_615_);
    v_r_617_ = leanh::lean_box_float(v_res_616_);
    return v_r_617_;
}
pub unsafe fn l_Float_exp2___boxed(
    mut v_x_619_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_boxed_620_: f64 = 0.0;
    let mut v_res_621_: f64 = 0.0;
    let mut v_r_622_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_620_ = leanh::lean_unbox_float(v_x_619_);
    leanh::lean_dec_ref(v_x_619_);
    v_res_621_ = exp2(v_x_boxed_620_);
    v_r_622_ = leanh::lean_box_float(v_res_621_);
    return v_r_622_;
}
pub unsafe fn l_Float_log___boxed(
    mut v_x_624_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_boxed_625_: f64 = 0.0;
    let mut v_res_626_: f64 = 0.0;
    let mut v_r_627_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_625_ = leanh::lean_unbox_float(v_x_624_);
    leanh::lean_dec_ref(v_x_624_);
    v_res_626_ = log(v_x_boxed_625_);
    v_r_627_ = leanh::lean_box_float(v_res_626_);
    return v_r_627_;
}
pub unsafe fn l_Float_log2___boxed(
    mut v_a_00___x40___internal___hyg_629_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_630_: f64 = 0.0;
    let mut v_res_631_: f64 = 0.0;
    let mut v_r_632_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_630_ =
        leanh::lean_unbox_float(v_a_00___x40___internal___hyg_629_);
    leanh::lean_dec_ref(v_a_00___x40___internal___hyg_629_);
    v_res_631_ = log2(v_a_00___x40___internal___hyg_1__boxed_630_);
    v_r_632_ = leanh::lean_box_float(v_res_631_);
    return v_r_632_;
}
pub unsafe fn l_Float_log10___boxed(
    mut v_a_00___x40___internal___hyg_634_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_635_: f64 = 0.0;
    let mut v_res_636_: f64 = 0.0;
    let mut v_r_637_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_635_ =
        leanh::lean_unbox_float(v_a_00___x40___internal___hyg_634_);
    leanh::lean_dec_ref(v_a_00___x40___internal___hyg_634_);
    v_res_636_ = log10(v_a_00___x40___internal___hyg_1__boxed_635_);
    v_r_637_ = leanh::lean_box_float(v_res_636_);
    return v_r_637_;
}
pub unsafe fn l_Float_pow___boxed(
    mut v_a_00___x40___internal___hyg_640_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_641_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_642_: f64 = 0.0;
    let mut v_a_00___x40___internal___hyg_2__boxed_643_: f64 = 0.0;
    let mut v_res_644_: f64 = 0.0;
    let mut v_r_645_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_642_ =
        leanh::lean_unbox_float(v_a_00___x40___internal___hyg_640_);
    leanh::lean_dec_ref(v_a_00___x40___internal___hyg_640_);
    v_a_00___x40___internal___hyg_2__boxed_643_ =
        leanh::lean_unbox_float(v_a_00___x40___internal___hyg_641_);
    leanh::lean_dec_ref(v_a_00___x40___internal___hyg_641_);
    v_res_644_ = pow(
        v_a_00___x40___internal___hyg_1__boxed_642_,
        v_a_00___x40___internal___hyg_2__boxed_643_,
    );
    v_r_645_ = leanh::lean_box_float(v_res_644_);
    return v_r_645_;
}
pub unsafe fn l_Float_sqrt___boxed(
    mut v_a_00___x40___internal___hyg_647_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_648_: f64 = 0.0;
    let mut v_res_649_: f64 = 0.0;
    let mut v_r_650_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_648_ =
        leanh::lean_unbox_float(v_a_00___x40___internal___hyg_647_);
    leanh::lean_dec_ref(v_a_00___x40___internal___hyg_647_);
    v_res_649_ = sqrt(v_a_00___x40___internal___hyg_1__boxed_648_);
    v_r_650_ = leanh::lean_box_float(v_res_649_);
    return v_r_650_;
}
pub unsafe fn l_Float_cbrt___boxed(
    mut v_a_00___x40___internal___hyg_652_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_653_: f64 = 0.0;
    let mut v_res_654_: f64 = 0.0;
    let mut v_r_655_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_653_ =
        leanh::lean_unbox_float(v_a_00___x40___internal___hyg_652_);
    leanh::lean_dec_ref(v_a_00___x40___internal___hyg_652_);
    v_res_654_ = cbrt(v_a_00___x40___internal___hyg_1__boxed_653_);
    v_r_655_ = leanh::lean_box_float(v_res_654_);
    return v_r_655_;
}
pub unsafe fn l_Float_ceil___boxed(
    mut v_a_00___x40___internal___hyg_657_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_658_: f64 = 0.0;
    let mut v_res_659_: f64 = 0.0;
    let mut v_r_660_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_658_ =
        leanh::lean_unbox_float(v_a_00___x40___internal___hyg_657_);
    leanh::lean_dec_ref(v_a_00___x40___internal___hyg_657_);
    v_res_659_ = ceil(v_a_00___x40___internal___hyg_1__boxed_658_);
    v_r_660_ = leanh::lean_box_float(v_res_659_);
    return v_r_660_;
}
pub unsafe fn l_Float_floor___boxed(
    mut v_a_00___x40___internal___hyg_662_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_663_: f64 = 0.0;
    let mut v_res_664_: f64 = 0.0;
    let mut v_r_665_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_663_ =
        leanh::lean_unbox_float(v_a_00___x40___internal___hyg_662_);
    leanh::lean_dec_ref(v_a_00___x40___internal___hyg_662_);
    v_res_664_ = floor(v_a_00___x40___internal___hyg_1__boxed_663_);
    v_r_665_ = leanh::lean_box_float(v_res_664_);
    return v_r_665_;
}
pub unsafe fn l_Float_round___boxed(
    mut v_a_00___x40___internal___hyg_667_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_668_: f64 = 0.0;
    let mut v_res_669_: f64 = 0.0;
    let mut v_r_670_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_668_ =
        leanh::lean_unbox_float(v_a_00___x40___internal___hyg_667_);
    leanh::lean_dec_ref(v_a_00___x40___internal___hyg_667_);
    v_res_669_ = round(v_a_00___x40___internal___hyg_1__boxed_668_);
    v_r_670_ = leanh::lean_box_float(v_res_669_);
    return v_r_670_;
}
pub unsafe fn l_Float_abs___boxed(
    mut v_a_00___x40___internal___hyg_672_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_673_: f64 = 0.0;
    let mut v_res_674_: f64 = 0.0;
    let mut v_r_675_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_673_ =
        leanh::lean_unbox_float(v_a_00___x40___internal___hyg_672_);
    leanh::lean_dec_ref(v_a_00___x40___internal___hyg_672_);
    v_res_674_ = fabs(v_a_00___x40___internal___hyg_1__boxed_673_);
    v_r_675_ = leanh::lean_box_float(v_res_674_);
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
    mut v_x_681_: *mut leanh::LeanObject,
    mut v_y_682_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_boxed_683_: f64 = 0.0;
    let mut v_y_boxed_684_: f64 = 0.0;
    let mut v_res_685_: f64 = 0.0;
    let mut v_r_686_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_683_ = leanh::lean_unbox_float(v_x_681_);
    leanh::lean_dec_ref(v_x_681_);
    v_y_boxed_684_ = leanh::lean_unbox_float(v_y_682_);
    leanh::lean_dec_ref(v_y_682_);
    v_res_685_ = l_instMinFloat___lam__0(v_x_boxed_683_, v_y_boxed_684_);
    v_r_686_ = leanh::lean_box_float(v_res_685_);
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
    mut v_x_692_: *mut leanh::LeanObject,
    mut v_y_693_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_boxed_694_: f64 = 0.0;
    let mut v_y_boxed_695_: f64 = 0.0;
    let mut v_res_696_: f64 = 0.0;
    let mut v_r_697_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_694_ = leanh::lean_unbox_float(v_x_692_);
    leanh::lean_dec_ref(v_x_692_);
    v_y_boxed_695_ = leanh::lean_unbox_float(v_y_693_);
    leanh::lean_dec_ref(v_y_693_);
    v_res_696_ = l_instMaxFloat___lam__0(v_x_boxed_694_, v_y_boxed_695_);
    v_r_697_ = leanh::lean_box_float(v_res_696_);
    return v_r_697_;
}
pub unsafe fn l_Float_scaleB___boxed(
    mut v_x_702_: *mut leanh::LeanObject,
    mut v_i_703_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_boxed_704_: f64 = 0.0;
    let mut v_res_705_: f64 = 0.0;
    let mut v_r_706_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_704_ = leanh::lean_unbox_float(v_x_702_);
    leanh::lean_dec_ref(v_x_702_);
    v_res_705_ = lean_float_scaleb(v_x_boxed_704_, v_i_703_);
    leanh::lean_dec(v_i_703_);
    v_r_706_ = leanh::lean_box_float(v_res_705_);
    return v_r_706_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Float(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_ToString_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_instLTFloat = _init_l_instLTFloat();
    leanh::lean_mark_persistent(l_instLTFloat);
    l_instLEFloat = _init_l_instLEFloat();
    leanh::lean_mark_persistent(l_instLEFloat);
    l_instInhabitedFloat = _init_l_instInhabitedFloat();
    l_instReprAtomFloat = _init_l_instReprAtomFloat();
    leanh::lean_mark_persistent(l_instReprAtomFloat);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Float(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Float(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_ToString_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Float(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Float(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_Float(builtin);
}