// Lean compiler output
// Module: Init.Data.Float
// Imports: Init.Data.ToString.Basic
use crate::r#gen::Init::Data::Repr::l_Repr_addAppParen;
use crate::r#gen::Init::Data::ToString::Basic::{
    initialize_Init_Data_ToString_Basic, runtime_initialize_Init_Data_ToString_Basic,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_box_float, lean_box_uint32,
    lean_box_uint64, lean_box_usize, lean_ctor_set, lean_dec, lean_dec_ref, lean_float_once,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_mark_persistent, lean_unbox,
    lean_unbox_float, lean_unbox_uint32, lean_unbox_uint64, lean_unbox_usize,
};
pub static l_floatSpec___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_floatSpec___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_floatSpec___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_floatSpec___closed__0_value) as *mut LeanObject;
pub static l_floatSpec___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_floatSpec___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_floatSpec___closed__0_value) as *mut LeanObject,
    ],
};
static mut l_floatSpec___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_floatSpec___closed__1_value) as *mut LeanObject;
pub static mut l_floatSpec: *mut LeanObject =
    core::ptr::addr_of!(l_floatSpec___closed__1_value) as *mut LeanObject;
pub static l_instAddFloat___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Float_add___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instAddFloat___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instAddFloat___closed__0_value) as *mut LeanObject;
pub static mut l_instAddFloat: *mut LeanObject =
    core::ptr::addr_of!(l_instAddFloat___closed__0_value) as *mut LeanObject;
pub static l_instSubFloat___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Float_sub___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instSubFloat___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instSubFloat___closed__0_value) as *mut LeanObject;
pub static mut l_instSubFloat: *mut LeanObject =
    core::ptr::addr_of!(l_instSubFloat___closed__0_value) as *mut LeanObject;
pub static l_instMulFloat___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Float_mul___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instMulFloat___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instMulFloat___closed__0_value) as *mut LeanObject;
pub static mut l_instMulFloat: *mut LeanObject =
    core::ptr::addr_of!(l_instMulFloat___closed__0_value) as *mut LeanObject;
pub static l_instDivFloat___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Float_div___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instDivFloat___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instDivFloat___closed__0_value) as *mut LeanObject;
pub static mut l_instDivFloat: *mut LeanObject =
    core::ptr::addr_of!(l_instDivFloat___closed__0_value) as *mut LeanObject;
pub static l_instNegFloat___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Float_neg___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instNegFloat___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instNegFloat___closed__0_value) as *mut LeanObject;
pub static mut l_instNegFloat: *mut LeanObject =
    core::ptr::addr_of!(l_instNegFloat___closed__0_value) as *mut LeanObject;
pub static mut l_instLTFloat: *mut LeanObject = core::ptr::null_mut();
pub static mut l_instLEFloat: *mut LeanObject = core::ptr::null_mut();
pub static l_instBEqFloat___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Float_beq___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instBEqFloat___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instBEqFloat___closed__0_value) as *mut LeanObject;
pub static mut l_instBEqFloat: *mut LeanObject =
    core::ptr::addr_of!(l_instBEqFloat___closed__0_value) as *mut LeanObject;
pub static l_instToStringFloat___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Float_toString___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instToStringFloat___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instToStringFloat___closed__0_value) as *mut LeanObject;
pub static mut l_instToStringFloat: *mut LeanObject =
    core::ptr::addr_of!(l_instToStringFloat___closed__0_value) as *mut LeanObject;
static mut l_instInhabitedFloat___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_instInhabitedFloat___closed__0: f64 = 0.0;
pub static mut l_instInhabitedFloat: f64 = 0.0;
pub static l_instReprFloat___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Float_repr___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instReprFloat___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instReprFloat___closed__0_value) as *mut LeanObject;
pub static mut l_instReprFloat: *mut LeanObject =
    core::ptr::addr_of!(l_instReprFloat___closed__0_value) as *mut LeanObject;
pub static mut l_instReprAtomFloat: *mut LeanObject = core::ptr::null_mut();
pub static l_instHomogeneousPowFloat___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Float_pow___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instHomogeneousPowFloat___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instHomogeneousPowFloat___closed__0_value) as *mut LeanObject;
pub static mut l_instHomogeneousPowFloat: *mut LeanObject =
    core::ptr::addr_of!(l_instHomogeneousPowFloat___closed__0_value) as *mut LeanObject;
pub static l_instMinFloat___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instMinFloat___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instMinFloat___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instMinFloat___closed__0_value) as *mut LeanObject;
pub static mut l_instMinFloat: *mut LeanObject =
    core::ptr::addr_of!(l_instMinFloat___closed__0_value) as *mut LeanObject;
pub static l_instMaxFloat___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instMaxFloat___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instMaxFloat___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instMaxFloat___closed__0_value) as *mut LeanObject;
pub static mut l_instMaxFloat: *mut LeanObject =
    core::ptr::addr_of!(l_instMaxFloat___closed__0_value) as *mut LeanObject;
pub unsafe fn l_floatSpec___lam__0(
    mut v_x_354_: *mut LeanObject,
    mut v_x_355_: *mut LeanObject,
) -> u8 {
    let mut v___x_356_: u8 = 0;
    v___x_356_ = 1;
    return v___x_356_;
}
pub unsafe fn l_floatSpec___lam__0___boxed(
    mut v_x_357_: *mut LeanObject,
    mut v_x_358_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_359_: u8 = 0;
    let mut v_r_360_: *mut LeanObject = core::ptr::null_mut();
    v_res_359_ = l_floatSpec___lam__0(v_x_357_, v_x_358_);
    v_r_360_ = lean_box((v_res_359_) as usize);
    return v_r_360_;
}
pub unsafe fn l_Float_add___boxed(
    mut v_a_00___x40___internal___hyg_368_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_369_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_370_: f64 = 0.0;
    let mut v_a_00___x40___internal___hyg_2__boxed_371_: f64 = 0.0;
    let mut v_res_372_: f64 = 0.0;
    let mut v_r_373_: *mut LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_370_ =
        lean_unbox_float(v_a_00___x40___internal___hyg_368_);
    lean_dec_ref(v_a_00___x40___internal___hyg_368_);
    v_a_00___x40___internal___hyg_2__boxed_371_ =
        lean_unbox_float(v_a_00___x40___internal___hyg_369_);
    lean_dec_ref(v_a_00___x40___internal___hyg_369_);
    v_res_372_ = lean_float_add(
        v_a_00___x40___internal___hyg_1__boxed_370_,
        v_a_00___x40___internal___hyg_2__boxed_371_,
    );
    v_r_373_ = lean_box_float(v_res_372_);
    return v_r_373_;
}
pub unsafe fn l_Float_sub___boxed(
    mut v_a_00___x40___internal___hyg_376_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_377_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_378_: f64 = 0.0;
    let mut v_a_00___x40___internal___hyg_2__boxed_379_: f64 = 0.0;
    let mut v_res_380_: f64 = 0.0;
    let mut v_r_381_: *mut LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_378_ =
        lean_unbox_float(v_a_00___x40___internal___hyg_376_);
    lean_dec_ref(v_a_00___x40___internal___hyg_376_);
    v_a_00___x40___internal___hyg_2__boxed_379_ =
        lean_unbox_float(v_a_00___x40___internal___hyg_377_);
    lean_dec_ref(v_a_00___x40___internal___hyg_377_);
    v_res_380_ = lean_float_sub(
        v_a_00___x40___internal___hyg_1__boxed_378_,
        v_a_00___x40___internal___hyg_2__boxed_379_,
    );
    v_r_381_ = lean_box_float(v_res_380_);
    return v_r_381_;
}
pub unsafe fn l_Float_mul___boxed(
    mut v_a_00___x40___internal___hyg_384_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_385_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_386_: f64 = 0.0;
    let mut v_a_00___x40___internal___hyg_2__boxed_387_: f64 = 0.0;
    let mut v_res_388_: f64 = 0.0;
    let mut v_r_389_: *mut LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_386_ =
        lean_unbox_float(v_a_00___x40___internal___hyg_384_);
    lean_dec_ref(v_a_00___x40___internal___hyg_384_);
    v_a_00___x40___internal___hyg_2__boxed_387_ =
        lean_unbox_float(v_a_00___x40___internal___hyg_385_);
    lean_dec_ref(v_a_00___x40___internal___hyg_385_);
    v_res_388_ = lean_float_mul(
        v_a_00___x40___internal___hyg_1__boxed_386_,
        v_a_00___x40___internal___hyg_2__boxed_387_,
    );
    v_r_389_ = lean_box_float(v_res_388_);
    return v_r_389_;
}
pub unsafe fn l_Float_div___boxed(
    mut v_a_00___x40___internal___hyg_392_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_393_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_394_: f64 = 0.0;
    let mut v_a_00___x40___internal___hyg_2__boxed_395_: f64 = 0.0;
    let mut v_res_396_: f64 = 0.0;
    let mut v_r_397_: *mut LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_394_ =
        lean_unbox_float(v_a_00___x40___internal___hyg_392_);
    lean_dec_ref(v_a_00___x40___internal___hyg_392_);
    v_a_00___x40___internal___hyg_2__boxed_395_ =
        lean_unbox_float(v_a_00___x40___internal___hyg_393_);
    lean_dec_ref(v_a_00___x40___internal___hyg_393_);
    v_res_396_ = lean_float_div(
        v_a_00___x40___internal___hyg_1__boxed_394_,
        v_a_00___x40___internal___hyg_2__boxed_395_,
    );
    v_r_397_ = lean_box_float(v_res_396_);
    return v_r_397_;
}
pub unsafe fn l_Float_neg___boxed(
    mut v_a_00___x40___internal___hyg_399_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_400_: f64 = 0.0;
    let mut v_res_401_: f64 = 0.0;
    let mut v_r_402_: *mut LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_400_ =
        lean_unbox_float(v_a_00___x40___internal___hyg_399_);
    lean_dec_ref(v_a_00___x40___internal___hyg_399_);
    v_res_401_ = lean_float_negate(v_a_00___x40___internal___hyg_1__boxed_400_);
    v_r_402_ = lean_box_float(v_res_401_);
    return v_r_402_;
}
pub unsafe fn l_Float_ofBits___boxed(
    mut v_a_00___x40___internal___hyg_404_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_405_: u64 = 0;
    let mut v_res_406_: f64 = 0.0;
    let mut v_r_407_: *mut LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_405_ =
        lean_unbox_uint64(v_a_00___x40___internal___hyg_404_);
    lean_dec_ref(v_a_00___x40___internal___hyg_404_);
    v_res_406_ = lean_float_of_bits(v_a_00___x40___internal___hyg_1__boxed_405_);
    v_r_407_ = lean_box_float(v_res_406_);
    return v_r_407_;
}
pub unsafe fn l_Float_toBits___boxed(
    mut v_a_00___x40___internal___hyg_409_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_410_: f64 = 0.0;
    let mut v_res_411_: u64 = 0;
    let mut v_r_412_: *mut LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_410_ =
        lean_unbox_float(v_a_00___x40___internal___hyg_409_);
    lean_dec_ref(v_a_00___x40___internal___hyg_409_);
    v_res_411_ = lean_float_to_bits(v_a_00___x40___internal___hyg_1__boxed_410_);
    v_r_412_ = lean_box_uint64(v_res_411_);
    return v_r_412_;
}
pub unsafe fn _init_l_instLTFloat() -> *mut LeanObject {
    let mut v___x_423_: *mut LeanObject = core::ptr::null_mut();
    v___x_423_ = lean_box(0);
    return v___x_423_;
}
pub unsafe fn _init_l_instLEFloat() -> *mut LeanObject {
    let mut v___x_424_: *mut LeanObject = core::ptr::null_mut();
    v___x_424_ = lean_box(0);
    return v___x_424_;
}
pub unsafe fn l_Float_beq___boxed(
    mut v_a_427_: *mut LeanObject,
    mut v_b_428_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_429_: f64 = 0.0;
    let mut v_b_boxed_430_: f64 = 0.0;
    let mut v_res_431_: u8 = 0;
    let mut v_r_432_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_429_ = lean_unbox_float(v_a_427_);
    lean_dec_ref(v_a_427_);
    v_b_boxed_430_ = lean_unbox_float(v_b_428_);
    lean_dec_ref(v_b_428_);
    v_res_431_ = lean_float_beq(v_a_boxed_429_, v_b_boxed_430_);
    v_r_432_ = lean_box((v_res_431_) as usize);
    return v_r_432_;
}
pub unsafe fn l_Float_decLt___boxed(
    mut v_a_437_: *mut LeanObject,
    mut v_b_438_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_439_: f64 = 0.0;
    let mut v_b_boxed_440_: f64 = 0.0;
    let mut v_res_441_: u8 = 0;
    let mut v_r_442_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_439_ = lean_unbox_float(v_a_437_);
    lean_dec_ref(v_a_437_);
    v_b_boxed_440_ = lean_unbox_float(v_b_438_);
    lean_dec_ref(v_b_438_);
    v_res_441_ = lean_float_decLt(v_a_boxed_439_, v_b_boxed_440_);
    v_r_442_ = lean_box((v_res_441_) as usize);
    return v_r_442_;
}
pub unsafe fn l_Float_decLe___boxed(
    mut v_a_445_: *mut LeanObject,
    mut v_b_446_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_447_: f64 = 0.0;
    let mut v_b_boxed_448_: f64 = 0.0;
    let mut v_res_449_: u8 = 0;
    let mut v_r_450_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_447_ = lean_unbox_float(v_a_445_);
    lean_dec_ref(v_a_445_);
    v_b_boxed_448_ = lean_unbox_float(v_b_446_);
    lean_dec_ref(v_b_446_);
    v_res_449_ = lean_float_decLe(v_a_boxed_447_, v_b_boxed_448_);
    v_r_450_ = lean_box((v_res_449_) as usize);
    return v_r_450_;
}
pub unsafe fn l_Float_toString___boxed(
    mut v_a_00___x40___internal___hyg_452_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_453_: f64 = 0.0;
    let mut v_res_454_: *mut LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_453_ =
        lean_unbox_float(v_a_00___x40___internal___hyg_452_);
    lean_dec_ref(v_a_00___x40___internal___hyg_452_);
    v_res_454_ = lean_float_to_string(v_a_00___x40___internal___hyg_1__boxed_453_);
    return v_res_454_;
}
pub unsafe fn l_Float_toUInt8___boxed(
    mut v_a_00___x40___internal___hyg_456_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_457_: f64 = 0.0;
    let mut v_res_458_: u8 = 0;
    let mut v_r_459_: *mut LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_457_ =
        lean_unbox_float(v_a_00___x40___internal___hyg_456_);
    lean_dec_ref(v_a_00___x40___internal___hyg_456_);
    v_res_458_ = lean_float_to_uint8(v_a_00___x40___internal___hyg_1__boxed_457_);
    v_r_459_ = lean_box((v_res_458_) as usize);
    return v_r_459_;
}
pub unsafe fn l_Float_toUInt16___boxed(
    mut v_a_00___x40___internal___hyg_461_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_462_: f64 = 0.0;
    let mut v_res_463_: u16 = 0;
    let mut v_r_464_: *mut LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_462_ =
        lean_unbox_float(v_a_00___x40___internal___hyg_461_);
    lean_dec_ref(v_a_00___x40___internal___hyg_461_);
    v_res_463_ = lean_float_to_uint16(v_a_00___x40___internal___hyg_1__boxed_462_);
    v_r_464_ = lean_box((v_res_463_) as usize);
    return v_r_464_;
}
pub unsafe fn l_Float_toUInt32___boxed(
    mut v_a_00___x40___internal___hyg_466_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_467_: f64 = 0.0;
    let mut v_res_468_: u32 = 0;
    let mut v_r_469_: *mut LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_467_ =
        lean_unbox_float(v_a_00___x40___internal___hyg_466_);
    lean_dec_ref(v_a_00___x40___internal___hyg_466_);
    v_res_468_ = lean_float_to_uint32(v_a_00___x40___internal___hyg_1__boxed_467_);
    v_r_469_ = lean_box_uint32(v_res_468_);
    return v_r_469_;
}
pub unsafe fn l_Float_toUInt64___boxed(
    mut v_a_00___x40___internal___hyg_471_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_472_: f64 = 0.0;
    let mut v_res_473_: u64 = 0;
    let mut v_r_474_: *mut LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_472_ =
        lean_unbox_float(v_a_00___x40___internal___hyg_471_);
    lean_dec_ref(v_a_00___x40___internal___hyg_471_);
    v_res_473_ = lean_float_to_uint64(v_a_00___x40___internal___hyg_1__boxed_472_);
    v_r_474_ = lean_box_uint64(v_res_473_);
    return v_r_474_;
}
pub unsafe fn l_Float_toUSize___boxed(
    mut v_a_00___x40___internal___hyg_476_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_477_: f64 = 0.0;
    let mut v_res_478_: usize = 0;
    let mut v_r_479_: *mut LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_477_ =
        lean_unbox_float(v_a_00___x40___internal___hyg_476_);
    lean_dec_ref(v_a_00___x40___internal___hyg_476_);
    v_res_478_ = lean_float_to_usize(v_a_00___x40___internal___hyg_1__boxed_477_);
    v_r_479_ = lean_box_usize(v_res_478_);
    return v_r_479_;
}
pub unsafe fn l_Float_isNaN___boxed(
    mut v_a_00___x40___internal___hyg_481_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_482_: f64 = 0.0;
    let mut v_res_483_: u8 = 0;
    let mut v_r_484_: *mut LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_482_ =
        lean_unbox_float(v_a_00___x40___internal___hyg_481_);
    lean_dec_ref(v_a_00___x40___internal___hyg_481_);
    v_res_483_ = lean_float_isnan(v_a_00___x40___internal___hyg_1__boxed_482_);
    v_r_484_ = lean_box((v_res_483_) as usize);
    return v_r_484_;
}
pub unsafe fn l_Float_isFinite___boxed(
    mut v_a_00___x40___internal___hyg_486_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_487_: f64 = 0.0;
    let mut v_res_488_: u8 = 0;
    let mut v_r_489_: *mut LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_487_ =
        lean_unbox_float(v_a_00___x40___internal___hyg_486_);
    lean_dec_ref(v_a_00___x40___internal___hyg_486_);
    v_res_488_ = lean_float_isfinite(v_a_00___x40___internal___hyg_1__boxed_487_);
    v_r_489_ = lean_box((v_res_488_) as usize);
    return v_r_489_;
}
pub unsafe fn l_Float_isInf___boxed(
    mut v_a_00___x40___internal___hyg_491_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_492_: f64 = 0.0;
    let mut v_res_493_: u8 = 0;
    let mut v_r_494_: *mut LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_492_ =
        lean_unbox_float(v_a_00___x40___internal___hyg_491_);
    lean_dec_ref(v_a_00___x40___internal___hyg_491_);
    v_res_493_ = lean_float_isinf(v_a_00___x40___internal___hyg_1__boxed_492_);
    v_r_494_ = lean_box((v_res_493_) as usize);
    return v_r_494_;
}
pub unsafe fn l_Float_frExp___boxed(
    mut v_a_00___x40___internal___hyg_496_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_497_: f64 = 0.0;
    let mut v_res_498_: *mut LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_497_ =
        lean_unbox_float(v_a_00___x40___internal___hyg_496_);
    lean_dec_ref(v_a_00___x40___internal___hyg_496_);
    v_res_498_ = lean_float_frexp(v_a_00___x40___internal___hyg_1__boxed_497_);
    return v_res_498_;
}
pub unsafe fn l_UInt8_toFloat___boxed(mut v_n_502_: *mut LeanObject) -> *mut LeanObject {
    let mut v_n_boxed_503_: u8 = 0;
    let mut v_res_504_: f64 = 0.0;
    let mut v_r_505_: *mut LeanObject = core::ptr::null_mut();
    v_n_boxed_503_ = (lean_unbox(v_n_502_) as u8);
    v_res_504_ = lean_uint8_to_float(v_n_boxed_503_);
    v_r_505_ = lean_box_float(v_res_504_);
    return v_r_505_;
}
pub unsafe fn l_UInt16_toFloat___boxed(mut v_n_507_: *mut LeanObject) -> *mut LeanObject {
    let mut v_n_boxed_508_: u16 = 0;
    let mut v_res_509_: f64 = 0.0;
    let mut v_r_510_: *mut LeanObject = core::ptr::null_mut();
    v_n_boxed_508_ = (lean_unbox(v_n_507_) as u16);
    v_res_509_ = lean_uint16_to_float(v_n_boxed_508_);
    v_r_510_ = lean_box_float(v_res_509_);
    return v_r_510_;
}
pub unsafe fn l_UInt32_toFloat___boxed(mut v_n_512_: *mut LeanObject) -> *mut LeanObject {
    let mut v_n_boxed_513_: u32 = 0;
    let mut v_res_514_: f64 = 0.0;
    let mut v_r_515_: *mut LeanObject = core::ptr::null_mut();
    v_n_boxed_513_ = lean_unbox_uint32(v_n_512_);
    lean_dec(v_n_512_);
    v_res_514_ = lean_uint32_to_float(v_n_boxed_513_);
    v_r_515_ = lean_box_float(v_res_514_);
    return v_r_515_;
}
pub unsafe fn l_UInt64_toFloat___boxed(mut v_n_517_: *mut LeanObject) -> *mut LeanObject {
    let mut v_n_boxed_518_: u64 = 0;
    let mut v_res_519_: f64 = 0.0;
    let mut v_r_520_: *mut LeanObject = core::ptr::null_mut();
    v_n_boxed_518_ = lean_unbox_uint64(v_n_517_);
    lean_dec_ref(v_n_517_);
    v_res_519_ = lean_uint64_to_float(v_n_boxed_518_);
    v_r_520_ = lean_box_float(v_res_519_);
    return v_r_520_;
}
pub unsafe fn l_USize_toFloat___boxed(mut v_n_522_: *mut LeanObject) -> *mut LeanObject {
    let mut v_n_boxed_523_: usize = 0;
    let mut v_res_524_: f64 = 0.0;
    let mut v_r_525_: *mut LeanObject = core::ptr::null_mut();
    v_n_boxed_523_ = lean_unbox_usize(v_n_522_);
    lean_dec(v_n_522_);
    v_res_524_ = lean_usize_to_float(v_n_boxed_523_);
    v_r_525_ = lean_box_float(v_res_524_);
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
    v___x_528_ = lean_float_once(
        core::ptr::addr_of_mut!(l_instInhabitedFloat___closed__0),
        core::ptr::addr_of_mut!(l_instInhabitedFloat___closed__0_once),
        _init_l_instInhabitedFloat___closed__0,
    );
    return v___x_528_;
}
pub unsafe fn l_Float_repr(mut v_n_529_: f64, mut v_prec_530_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_531_: f64 = 0.0;
    let mut v___x_532_: u8 = 0;
    v___x_531_ = lean_float_once(
        core::ptr::addr_of_mut!(l_instInhabitedFloat___closed__0),
        core::ptr::addr_of_mut!(l_instInhabitedFloat___closed__0_once),
        _init_l_instInhabitedFloat___closed__0,
    );
    v___x_532_ = lean_float_decLt(v_n_529_, v___x_531_);
    if v___x_532_ == 0 {
        let mut v___x_533_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_534_: *mut LeanObject = core::ptr::null_mut();
        v___x_533_ = lean_float_to_string(v_n_529_);
        v___x_534_ = lean_alloc_ctor(3, 1, (0) as u32);
        lean_ctor_set(v___x_534_, 0, v___x_533_);
        return v___x_534_;
    } else {
        let mut v___x_535_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_536_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_537_: *mut LeanObject = core::ptr::null_mut();
        v___x_535_ = lean_float_to_string(v_n_529_);
        v___x_536_ = lean_alloc_ctor(3, 1, (0) as u32);
        lean_ctor_set(v___x_536_, 0, v___x_535_);
        v___x_537_ = l_Repr_addAppParen(v___x_536_, v_prec_530_);
        return v___x_537_;
    }
}
pub unsafe fn l_Float_repr___boxed(
    mut v_n_538_: *mut LeanObject,
    mut v_prec_539_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_n_boxed_540_: f64 = 0.0;
    let mut v_res_541_: *mut LeanObject = core::ptr::null_mut();
    v_n_boxed_540_ = lean_unbox_float(v_n_538_);
    lean_dec_ref(v_n_538_);
    v_res_541_ = l_Float_repr(v_n_boxed_540_, v_prec_539_);
    lean_dec(v_prec_539_);
    return v_res_541_;
}
pub unsafe fn _init_l_instReprAtomFloat() -> *mut LeanObject {
    let mut v___x_544_: *mut LeanObject = core::ptr::null_mut();
    v___x_544_ = lean_box(0);
    return v___x_544_;
}
pub unsafe fn l_Float_sin___boxed(
    mut v_a_00___x40___internal___hyg_546_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_547_: f64 = 0.0;
    let mut v_res_548_: f64 = 0.0;
    let mut v_r_549_: *mut LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_547_ =
        lean_unbox_float(v_a_00___x40___internal___hyg_546_);
    lean_dec_ref(v_a_00___x40___internal___hyg_546_);
    v_res_548_ = sin(v_a_00___x40___internal___hyg_1__boxed_547_);
    v_r_549_ = lean_box_float(v_res_548_);
    return v_r_549_;
}
pub unsafe fn l_Float_cos___boxed(
    mut v_a_00___x40___internal___hyg_551_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_552_: f64 = 0.0;
    let mut v_res_553_: f64 = 0.0;
    let mut v_r_554_: *mut LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_552_ =
        lean_unbox_float(v_a_00___x40___internal___hyg_551_);
    lean_dec_ref(v_a_00___x40___internal___hyg_551_);
    v_res_553_ = cos(v_a_00___x40___internal___hyg_1__boxed_552_);
    v_r_554_ = lean_box_float(v_res_553_);
    return v_r_554_;
}
pub unsafe fn l_Float_tan___boxed(
    mut v_a_00___x40___internal___hyg_556_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_557_: f64 = 0.0;
    let mut v_res_558_: f64 = 0.0;
    let mut v_r_559_: *mut LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_557_ =
        lean_unbox_float(v_a_00___x40___internal___hyg_556_);
    lean_dec_ref(v_a_00___x40___internal___hyg_556_);
    v_res_558_ = tan(v_a_00___x40___internal___hyg_1__boxed_557_);
    v_r_559_ = lean_box_float(v_res_558_);
    return v_r_559_;
}
pub unsafe fn l_Float_asin___boxed(
    mut v_a_00___x40___internal___hyg_561_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_562_: f64 = 0.0;
    let mut v_res_563_: f64 = 0.0;
    let mut v_r_564_: *mut LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_562_ =
        lean_unbox_float(v_a_00___x40___internal___hyg_561_);
    lean_dec_ref(v_a_00___x40___internal___hyg_561_);
    v_res_563_ = asin(v_a_00___x40___internal___hyg_1__boxed_562_);
    v_r_564_ = lean_box_float(v_res_563_);
    return v_r_564_;
}
pub unsafe fn l_Float_acos___boxed(
    mut v_a_00___x40___internal___hyg_566_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_567_: f64 = 0.0;
    let mut v_res_568_: f64 = 0.0;
    let mut v_r_569_: *mut LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_567_ =
        lean_unbox_float(v_a_00___x40___internal___hyg_566_);
    lean_dec_ref(v_a_00___x40___internal___hyg_566_);
    v_res_568_ = acos(v_a_00___x40___internal___hyg_1__boxed_567_);
    v_r_569_ = lean_box_float(v_res_568_);
    return v_r_569_;
}
pub unsafe fn l_Float_atan___boxed(
    mut v_a_00___x40___internal___hyg_571_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_572_: f64 = 0.0;
    let mut v_res_573_: f64 = 0.0;
    let mut v_r_574_: *mut LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_572_ =
        lean_unbox_float(v_a_00___x40___internal___hyg_571_);
    lean_dec_ref(v_a_00___x40___internal___hyg_571_);
    v_res_573_ = atan(v_a_00___x40___internal___hyg_1__boxed_572_);
    v_r_574_ = lean_box_float(v_res_573_);
    return v_r_574_;
}
pub unsafe fn l_Float_atan2___boxed(
    mut v_y_577_: *mut LeanObject,
    mut v_x_578_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_y_boxed_579_: f64 = 0.0;
    let mut v_x_boxed_580_: f64 = 0.0;
    let mut v_res_581_: f64 = 0.0;
    let mut v_r_582_: *mut LeanObject = core::ptr::null_mut();
    v_y_boxed_579_ = lean_unbox_float(v_y_577_);
    lean_dec_ref(v_y_577_);
    v_x_boxed_580_ = lean_unbox_float(v_x_578_);
    lean_dec_ref(v_x_578_);
    v_res_581_ = atan2(v_y_boxed_579_, v_x_boxed_580_);
    v_r_582_ = lean_box_float(v_res_581_);
    return v_r_582_;
}
pub unsafe fn l_Float_sinh___boxed(
    mut v_a_00___x40___internal___hyg_584_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_585_: f64 = 0.0;
    let mut v_res_586_: f64 = 0.0;
    let mut v_r_587_: *mut LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_585_ =
        lean_unbox_float(v_a_00___x40___internal___hyg_584_);
    lean_dec_ref(v_a_00___x40___internal___hyg_584_);
    v_res_586_ = sinh(v_a_00___x40___internal___hyg_1__boxed_585_);
    v_r_587_ = lean_box_float(v_res_586_);
    return v_r_587_;
}
pub unsafe fn l_Float_cosh___boxed(
    mut v_a_00___x40___internal___hyg_589_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_590_: f64 = 0.0;
    let mut v_res_591_: f64 = 0.0;
    let mut v_r_592_: *mut LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_590_ =
        lean_unbox_float(v_a_00___x40___internal___hyg_589_);
    lean_dec_ref(v_a_00___x40___internal___hyg_589_);
    v_res_591_ = cosh(v_a_00___x40___internal___hyg_1__boxed_590_);
    v_r_592_ = lean_box_float(v_res_591_);
    return v_r_592_;
}
pub unsafe fn l_Float_tanh___boxed(
    mut v_a_00___x40___internal___hyg_594_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_595_: f64 = 0.0;
    let mut v_res_596_: f64 = 0.0;
    let mut v_r_597_: *mut LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_595_ =
        lean_unbox_float(v_a_00___x40___internal___hyg_594_);
    lean_dec_ref(v_a_00___x40___internal___hyg_594_);
    v_res_596_ = tanh(v_a_00___x40___internal___hyg_1__boxed_595_);
    v_r_597_ = lean_box_float(v_res_596_);
    return v_r_597_;
}
pub unsafe fn l_Float_asinh___boxed(
    mut v_a_00___x40___internal___hyg_599_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_600_: f64 = 0.0;
    let mut v_res_601_: f64 = 0.0;
    let mut v_r_602_: *mut LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_600_ =
        lean_unbox_float(v_a_00___x40___internal___hyg_599_);
    lean_dec_ref(v_a_00___x40___internal___hyg_599_);
    v_res_601_ = asinh(v_a_00___x40___internal___hyg_1__boxed_600_);
    v_r_602_ = lean_box_float(v_res_601_);
    return v_r_602_;
}
pub unsafe fn l_Float_acosh___boxed(
    mut v_a_00___x40___internal___hyg_604_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_605_: f64 = 0.0;
    let mut v_res_606_: f64 = 0.0;
    let mut v_r_607_: *mut LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_605_ =
        lean_unbox_float(v_a_00___x40___internal___hyg_604_);
    lean_dec_ref(v_a_00___x40___internal___hyg_604_);
    v_res_606_ = acosh(v_a_00___x40___internal___hyg_1__boxed_605_);
    v_r_607_ = lean_box_float(v_res_606_);
    return v_r_607_;
}
pub unsafe fn l_Float_atanh___boxed(
    mut v_a_00___x40___internal___hyg_609_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_610_: f64 = 0.0;
    let mut v_res_611_: f64 = 0.0;
    let mut v_r_612_: *mut LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_610_ =
        lean_unbox_float(v_a_00___x40___internal___hyg_609_);
    lean_dec_ref(v_a_00___x40___internal___hyg_609_);
    v_res_611_ = atanh(v_a_00___x40___internal___hyg_1__boxed_610_);
    v_r_612_ = lean_box_float(v_res_611_);
    return v_r_612_;
}
pub unsafe fn l_Float_exp___boxed(mut v_x_614_: *mut LeanObject) -> *mut LeanObject {
    let mut v_x_boxed_615_: f64 = 0.0;
    let mut v_res_616_: f64 = 0.0;
    let mut v_r_617_: *mut LeanObject = core::ptr::null_mut();
    v_x_boxed_615_ = lean_unbox_float(v_x_614_);
    lean_dec_ref(v_x_614_);
    v_res_616_ = exp(v_x_boxed_615_);
    v_r_617_ = lean_box_float(v_res_616_);
    return v_r_617_;
}
pub unsafe fn l_Float_exp2___boxed(mut v_x_619_: *mut LeanObject) -> *mut LeanObject {
    let mut v_x_boxed_620_: f64 = 0.0;
    let mut v_res_621_: f64 = 0.0;
    let mut v_r_622_: *mut LeanObject = core::ptr::null_mut();
    v_x_boxed_620_ = lean_unbox_float(v_x_619_);
    lean_dec_ref(v_x_619_);
    v_res_621_ = exp2(v_x_boxed_620_);
    v_r_622_ = lean_box_float(v_res_621_);
    return v_r_622_;
}
pub unsafe fn l_Float_log___boxed(mut v_x_624_: *mut LeanObject) -> *mut LeanObject {
    let mut v_x_boxed_625_: f64 = 0.0;
    let mut v_res_626_: f64 = 0.0;
    let mut v_r_627_: *mut LeanObject = core::ptr::null_mut();
    v_x_boxed_625_ = lean_unbox_float(v_x_624_);
    lean_dec_ref(v_x_624_);
    v_res_626_ = log(v_x_boxed_625_);
    v_r_627_ = lean_box_float(v_res_626_);
    return v_r_627_;
}
pub unsafe fn l_Float_log2___boxed(
    mut v_a_00___x40___internal___hyg_629_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_630_: f64 = 0.0;
    let mut v_res_631_: f64 = 0.0;
    let mut v_r_632_: *mut LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_630_ =
        lean_unbox_float(v_a_00___x40___internal___hyg_629_);
    lean_dec_ref(v_a_00___x40___internal___hyg_629_);
    v_res_631_ = log2(v_a_00___x40___internal___hyg_1__boxed_630_);
    v_r_632_ = lean_box_float(v_res_631_);
    return v_r_632_;
}
pub unsafe fn l_Float_log10___boxed(
    mut v_a_00___x40___internal___hyg_634_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_635_: f64 = 0.0;
    let mut v_res_636_: f64 = 0.0;
    let mut v_r_637_: *mut LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_635_ =
        lean_unbox_float(v_a_00___x40___internal___hyg_634_);
    lean_dec_ref(v_a_00___x40___internal___hyg_634_);
    v_res_636_ = log10(v_a_00___x40___internal___hyg_1__boxed_635_);
    v_r_637_ = lean_box_float(v_res_636_);
    return v_r_637_;
}
pub unsafe fn l_Float_pow___boxed(
    mut v_a_00___x40___internal___hyg_640_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_641_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_642_: f64 = 0.0;
    let mut v_a_00___x40___internal___hyg_2__boxed_643_: f64 = 0.0;
    let mut v_res_644_: f64 = 0.0;
    let mut v_r_645_: *mut LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_642_ =
        lean_unbox_float(v_a_00___x40___internal___hyg_640_);
    lean_dec_ref(v_a_00___x40___internal___hyg_640_);
    v_a_00___x40___internal___hyg_2__boxed_643_ =
        lean_unbox_float(v_a_00___x40___internal___hyg_641_);
    lean_dec_ref(v_a_00___x40___internal___hyg_641_);
    v_res_644_ = pow(
        v_a_00___x40___internal___hyg_1__boxed_642_,
        v_a_00___x40___internal___hyg_2__boxed_643_,
    );
    v_r_645_ = lean_box_float(v_res_644_);
    return v_r_645_;
}
pub unsafe fn l_Float_sqrt___boxed(
    mut v_a_00___x40___internal___hyg_647_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_648_: f64 = 0.0;
    let mut v_res_649_: f64 = 0.0;
    let mut v_r_650_: *mut LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_648_ =
        lean_unbox_float(v_a_00___x40___internal___hyg_647_);
    lean_dec_ref(v_a_00___x40___internal___hyg_647_);
    v_res_649_ = sqrt(v_a_00___x40___internal___hyg_1__boxed_648_);
    v_r_650_ = lean_box_float(v_res_649_);
    return v_r_650_;
}
pub unsafe fn l_Float_cbrt___boxed(
    mut v_a_00___x40___internal___hyg_652_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_653_: f64 = 0.0;
    let mut v_res_654_: f64 = 0.0;
    let mut v_r_655_: *mut LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_653_ =
        lean_unbox_float(v_a_00___x40___internal___hyg_652_);
    lean_dec_ref(v_a_00___x40___internal___hyg_652_);
    v_res_654_ = cbrt(v_a_00___x40___internal___hyg_1__boxed_653_);
    v_r_655_ = lean_box_float(v_res_654_);
    return v_r_655_;
}
pub unsafe fn l_Float_ceil___boxed(
    mut v_a_00___x40___internal___hyg_657_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_658_: f64 = 0.0;
    let mut v_res_659_: f64 = 0.0;
    let mut v_r_660_: *mut LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_658_ =
        lean_unbox_float(v_a_00___x40___internal___hyg_657_);
    lean_dec_ref(v_a_00___x40___internal___hyg_657_);
    v_res_659_ = ceil(v_a_00___x40___internal___hyg_1__boxed_658_);
    v_r_660_ = lean_box_float(v_res_659_);
    return v_r_660_;
}
pub unsafe fn l_Float_floor___boxed(
    mut v_a_00___x40___internal___hyg_662_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_663_: f64 = 0.0;
    let mut v_res_664_: f64 = 0.0;
    let mut v_r_665_: *mut LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_663_ =
        lean_unbox_float(v_a_00___x40___internal___hyg_662_);
    lean_dec_ref(v_a_00___x40___internal___hyg_662_);
    v_res_664_ = floor(v_a_00___x40___internal___hyg_1__boxed_663_);
    v_r_665_ = lean_box_float(v_res_664_);
    return v_r_665_;
}
pub unsafe fn l_Float_round___boxed(
    mut v_a_00___x40___internal___hyg_667_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_668_: f64 = 0.0;
    let mut v_res_669_: f64 = 0.0;
    let mut v_r_670_: *mut LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_668_ =
        lean_unbox_float(v_a_00___x40___internal___hyg_667_);
    lean_dec_ref(v_a_00___x40___internal___hyg_667_);
    v_res_669_ = round(v_a_00___x40___internal___hyg_1__boxed_668_);
    v_r_670_ = lean_box_float(v_res_669_);
    return v_r_670_;
}
pub unsafe fn l_Float_abs___boxed(
    mut v_a_00___x40___internal___hyg_672_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_673_: f64 = 0.0;
    let mut v_res_674_: f64 = 0.0;
    let mut v_r_675_: *mut LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_673_ =
        lean_unbox_float(v_a_00___x40___internal___hyg_672_);
    lean_dec_ref(v_a_00___x40___internal___hyg_672_);
    v_res_674_ = fabs(v_a_00___x40___internal___hyg_1__boxed_673_);
    v_r_675_ = lean_box_float(v_res_674_);
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
    mut v_x_681_: *mut LeanObject,
    mut v_y_682_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_boxed_683_: f64 = 0.0;
    let mut v_y_boxed_684_: f64 = 0.0;
    let mut v_res_685_: f64 = 0.0;
    let mut v_r_686_: *mut LeanObject = core::ptr::null_mut();
    v_x_boxed_683_ = lean_unbox_float(v_x_681_);
    lean_dec_ref(v_x_681_);
    v_y_boxed_684_ = lean_unbox_float(v_y_682_);
    lean_dec_ref(v_y_682_);
    v_res_685_ = l_instMinFloat___lam__0(v_x_boxed_683_, v_y_boxed_684_);
    v_r_686_ = lean_box_float(v_res_685_);
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
    mut v_x_692_: *mut LeanObject,
    mut v_y_693_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_boxed_694_: f64 = 0.0;
    let mut v_y_boxed_695_: f64 = 0.0;
    let mut v_res_696_: f64 = 0.0;
    let mut v_r_697_: *mut LeanObject = core::ptr::null_mut();
    v_x_boxed_694_ = lean_unbox_float(v_x_692_);
    lean_dec_ref(v_x_692_);
    v_y_boxed_695_ = lean_unbox_float(v_y_693_);
    lean_dec_ref(v_y_693_);
    v_res_696_ = l_instMaxFloat___lam__0(v_x_boxed_694_, v_y_boxed_695_);
    v_r_697_ = lean_box_float(v_res_696_);
    return v_r_697_;
}
pub unsafe fn l_Float_scaleB___boxed(
    mut v_x_702_: *mut LeanObject,
    mut v_i_703_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_boxed_704_: f64 = 0.0;
    let mut v_res_705_: f64 = 0.0;
    let mut v_r_706_: *mut LeanObject = core::ptr::null_mut();
    v_x_boxed_704_ = lean_unbox_float(v_x_702_);
    lean_dec_ref(v_x_702_);
    v_res_705_ = lean_float_scaleb(v_x_boxed_704_, v_i_703_);
    lean_dec(v_i_703_);
    v_r_706_ = lean_box_float(v_res_705_);
    return v_r_706_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Float(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_ToString_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_instLTFloat = _init_l_instLTFloat();
    lean_mark_persistent(l_instLTFloat);
    l_instLEFloat = _init_l_instLEFloat();
    lean_mark_persistent(l_instLEFloat);
    l_instInhabitedFloat = _init_l_instInhabitedFloat();
    l_instReprAtomFloat = _init_l_instReprAtomFloat();
    lean_mark_persistent(l_instReprAtomFloat);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Float(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Float(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_ToString_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Float(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_Float(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_Float(builtin);
}
