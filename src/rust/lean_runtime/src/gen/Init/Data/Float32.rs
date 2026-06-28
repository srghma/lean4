// Lean compiler output
// Module: Init.Data.Float32
// Imports: Init.Data.Float
use crate::r#gen::Init::Data::Float::{
    initialize_Init_Data_Float, runtime_initialize_Init_Data_Float,
};
use crate::r#gen::Init::Data::Repr::l_Repr_addAppParen;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_box_float, lean_box_float32,
    lean_box_uint32, lean_box_uint64, lean_box_usize, lean_ctor_set, lean_dec, lean_dec_ref,
    lean_float32_once, lean_io_result_is_error, lean_io_result_mk_ok, lean_mark_persistent,
    lean_unbox, lean_unbox_float, lean_unbox_float32, lean_unbox_uint32, lean_unbox_uint64,
    lean_unbox_usize,
};
pub static l_float32Spec___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_float32Spec___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_float32Spec___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_float32Spec___closed__0_value) as *mut LeanObject;
pub static l_float32Spec___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_float32Spec___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_float32Spec___closed__0_value) as *mut LeanObject,
    ],
};
static mut l_float32Spec___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_float32Spec___closed__1_value) as *mut LeanObject;
pub static mut l_float32Spec: *mut LeanObject =
    core::ptr::addr_of!(l_float32Spec___closed__1_value) as *mut LeanObject;
pub static l_instAddFloat32___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Float32_add___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instAddFloat32___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instAddFloat32___closed__0_value) as *mut LeanObject;
pub static mut l_instAddFloat32: *mut LeanObject =
    core::ptr::addr_of!(l_instAddFloat32___closed__0_value) as *mut LeanObject;
pub static l_instSubFloat32___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Float32_sub___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instSubFloat32___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instSubFloat32___closed__0_value) as *mut LeanObject;
pub static mut l_instSubFloat32: *mut LeanObject =
    core::ptr::addr_of!(l_instSubFloat32___closed__0_value) as *mut LeanObject;
pub static l_instMulFloat32___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Float32_mul___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instMulFloat32___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instMulFloat32___closed__0_value) as *mut LeanObject;
pub static mut l_instMulFloat32: *mut LeanObject =
    core::ptr::addr_of!(l_instMulFloat32___closed__0_value) as *mut LeanObject;
pub static l_instDivFloat32___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Float32_div___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instDivFloat32___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instDivFloat32___closed__0_value) as *mut LeanObject;
pub static mut l_instDivFloat32: *mut LeanObject =
    core::ptr::addr_of!(l_instDivFloat32___closed__0_value) as *mut LeanObject;
pub static l_instNegFloat32___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Float32_neg___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instNegFloat32___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instNegFloat32___closed__0_value) as *mut LeanObject;
pub static mut l_instNegFloat32: *mut LeanObject =
    core::ptr::addr_of!(l_instNegFloat32___closed__0_value) as *mut LeanObject;
pub static mut l_instLTFloat32: *mut LeanObject = core::ptr::null_mut();
pub static mut l_instLEFloat32: *mut LeanObject = core::ptr::null_mut();
pub static l_instBEqFloat32___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Float32_beq___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instBEqFloat32___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instBEqFloat32___closed__0_value) as *mut LeanObject;
pub static mut l_instBEqFloat32: *mut LeanObject =
    core::ptr::addr_of!(l_instBEqFloat32___closed__0_value) as *mut LeanObject;
pub static l_instToStringFloat32___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Float32_toString___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instToStringFloat32___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instToStringFloat32___closed__0_value) as *mut LeanObject;
pub static mut l_instToStringFloat32: *mut LeanObject =
    core::ptr::addr_of!(l_instToStringFloat32___closed__0_value) as *mut LeanObject;
static mut l_instInhabitedFloat32___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_instInhabitedFloat32___closed__0: f32 = 0.0f32;
pub static mut l_instInhabitedFloat32: f32 = 0.0f32;
pub static l_instReprFloat32___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Float32_repr___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instReprFloat32___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instReprFloat32___closed__0_value) as *mut LeanObject;
pub static mut l_instReprFloat32: *mut LeanObject =
    core::ptr::addr_of!(l_instReprFloat32___closed__0_value) as *mut LeanObject;
pub static mut l_instReprAtomFloat32: *mut LeanObject = core::ptr::null_mut();
pub static l_instHomogeneousPowFloat32___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Float32_pow___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instHomogeneousPowFloat32___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instHomogeneousPowFloat32___closed__0_value) as *mut LeanObject;
pub static mut l_instHomogeneousPowFloat32: *mut LeanObject =
    core::ptr::addr_of!(l_instHomogeneousPowFloat32___closed__0_value) as *mut LeanObject;
pub static l_instMinFloat32___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instMinFloat32___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instMinFloat32___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instMinFloat32___closed__0_value) as *mut LeanObject;
pub static mut l_instMinFloat32: *mut LeanObject =
    core::ptr::addr_of!(l_instMinFloat32___closed__0_value) as *mut LeanObject;
pub static l_instMaxFloat32___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instMaxFloat32___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instMaxFloat32___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instMaxFloat32___closed__0_value) as *mut LeanObject;
pub static mut l_instMaxFloat32: *mut LeanObject =
    core::ptr::addr_of!(l_instMaxFloat32___closed__0_value) as *mut LeanObject;
pub unsafe fn l_float32Spec___lam__0(
    mut v_x_364_: *mut LeanObject,
    mut v_x_365_: *mut LeanObject,
) -> u8 {
    let mut v___x_366_: u8 = 0;
    v___x_366_ = 1;
    return v___x_366_;
}
pub unsafe fn l_float32Spec___lam__0___boxed(
    mut v_x_367_: *mut LeanObject,
    mut v_x_368_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_369_: u8 = 0;
    let mut v_r_370_: *mut LeanObject = core::ptr::null_mut();
    v_res_369_ = l_float32Spec___lam__0(v_x_367_, v_x_368_);
    v_r_370_ = lean_box((v_res_369_) as usize);
    return v_r_370_;
}
pub unsafe fn l_Float32_add___boxed(
    mut v_a_00___x40___internal___hyg_378_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_379_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_380_: f32 = 0.0f32;
    let mut v_a_00___x40___internal___hyg_2__boxed_381_: f32 = 0.0f32;
    let mut v_res_382_: f32 = 0.0f32;
    let mut v_r_383_: *mut LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_380_ =
        lean_unbox_float32(v_a_00___x40___internal___hyg_378_);
    lean_dec_ref(v_a_00___x40___internal___hyg_378_);
    v_a_00___x40___internal___hyg_2__boxed_381_ =
        lean_unbox_float32(v_a_00___x40___internal___hyg_379_);
    lean_dec_ref(v_a_00___x40___internal___hyg_379_);
    v_res_382_ = lean_float32_add(
        v_a_00___x40___internal___hyg_1__boxed_380_,
        v_a_00___x40___internal___hyg_2__boxed_381_,
    );
    v_r_383_ = lean_box_float32(v_res_382_);
    return v_r_383_;
}
pub unsafe fn l_Float32_sub___boxed(
    mut v_a_00___x40___internal___hyg_386_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_387_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_388_: f32 = 0.0f32;
    let mut v_a_00___x40___internal___hyg_2__boxed_389_: f32 = 0.0f32;
    let mut v_res_390_: f32 = 0.0f32;
    let mut v_r_391_: *mut LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_388_ =
        lean_unbox_float32(v_a_00___x40___internal___hyg_386_);
    lean_dec_ref(v_a_00___x40___internal___hyg_386_);
    v_a_00___x40___internal___hyg_2__boxed_389_ =
        lean_unbox_float32(v_a_00___x40___internal___hyg_387_);
    lean_dec_ref(v_a_00___x40___internal___hyg_387_);
    v_res_390_ = lean_float32_sub(
        v_a_00___x40___internal___hyg_1__boxed_388_,
        v_a_00___x40___internal___hyg_2__boxed_389_,
    );
    v_r_391_ = lean_box_float32(v_res_390_);
    return v_r_391_;
}
pub unsafe fn l_Float32_mul___boxed(
    mut v_a_00___x40___internal___hyg_394_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_395_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_396_: f32 = 0.0f32;
    let mut v_a_00___x40___internal___hyg_2__boxed_397_: f32 = 0.0f32;
    let mut v_res_398_: f32 = 0.0f32;
    let mut v_r_399_: *mut LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_396_ =
        lean_unbox_float32(v_a_00___x40___internal___hyg_394_);
    lean_dec_ref(v_a_00___x40___internal___hyg_394_);
    v_a_00___x40___internal___hyg_2__boxed_397_ =
        lean_unbox_float32(v_a_00___x40___internal___hyg_395_);
    lean_dec_ref(v_a_00___x40___internal___hyg_395_);
    v_res_398_ = lean_float32_mul(
        v_a_00___x40___internal___hyg_1__boxed_396_,
        v_a_00___x40___internal___hyg_2__boxed_397_,
    );
    v_r_399_ = lean_box_float32(v_res_398_);
    return v_r_399_;
}
pub unsafe fn l_Float32_div___boxed(
    mut v_a_00___x40___internal___hyg_402_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_403_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_404_: f32 = 0.0f32;
    let mut v_a_00___x40___internal___hyg_2__boxed_405_: f32 = 0.0f32;
    let mut v_res_406_: f32 = 0.0f32;
    let mut v_r_407_: *mut LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_404_ =
        lean_unbox_float32(v_a_00___x40___internal___hyg_402_);
    lean_dec_ref(v_a_00___x40___internal___hyg_402_);
    v_a_00___x40___internal___hyg_2__boxed_405_ =
        lean_unbox_float32(v_a_00___x40___internal___hyg_403_);
    lean_dec_ref(v_a_00___x40___internal___hyg_403_);
    v_res_406_ = lean_float32_div(
        v_a_00___x40___internal___hyg_1__boxed_404_,
        v_a_00___x40___internal___hyg_2__boxed_405_,
    );
    v_r_407_ = lean_box_float32(v_res_406_);
    return v_r_407_;
}
pub unsafe fn l_Float32_neg___boxed(
    mut v_a_00___x40___internal___hyg_409_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_410_: f32 = 0.0f32;
    let mut v_res_411_: f32 = 0.0f32;
    let mut v_r_412_: *mut LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_410_ =
        lean_unbox_float32(v_a_00___x40___internal___hyg_409_);
    lean_dec_ref(v_a_00___x40___internal___hyg_409_);
    v_res_411_ = lean_float32_negate(v_a_00___x40___internal___hyg_1__boxed_410_);
    v_r_412_ = lean_box_float32(v_res_411_);
    return v_r_412_;
}
pub unsafe fn l_Float32_ofBits___boxed(
    mut v_a_00___x40___internal___hyg_414_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_415_: u32 = 0;
    let mut v_res_416_: f32 = 0.0f32;
    let mut v_r_417_: *mut LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_415_ =
        lean_unbox_uint32(v_a_00___x40___internal___hyg_414_);
    lean_dec(v_a_00___x40___internal___hyg_414_);
    v_res_416_ = lean_float32_of_bits(v_a_00___x40___internal___hyg_1__boxed_415_);
    v_r_417_ = lean_box_float32(v_res_416_);
    return v_r_417_;
}
pub unsafe fn l_Float32_toBits___boxed(
    mut v_a_00___x40___internal___hyg_419_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_420_: f32 = 0.0f32;
    let mut v_res_421_: u32 = 0;
    let mut v_r_422_: *mut LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_420_ =
        lean_unbox_float32(v_a_00___x40___internal___hyg_419_);
    lean_dec_ref(v_a_00___x40___internal___hyg_419_);
    v_res_421_ = lean_float32_to_bits(v_a_00___x40___internal___hyg_1__boxed_420_);
    v_r_422_ = lean_box_uint32(v_res_421_);
    return v_r_422_;
}
pub unsafe fn _init_l_instLTFloat32() -> *mut LeanObject {
    let mut v___x_433_: *mut LeanObject = core::ptr::null_mut();
    v___x_433_ = lean_box(0);
    return v___x_433_;
}
pub unsafe fn _init_l_instLEFloat32() -> *mut LeanObject {
    let mut v___x_434_: *mut LeanObject = core::ptr::null_mut();
    v___x_434_ = lean_box(0);
    return v___x_434_;
}
pub unsafe fn l_Float32_beq___boxed(
    mut v_a_437_: *mut LeanObject,
    mut v_b_438_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_439_: f32 = 0.0f32;
    let mut v_b_boxed_440_: f32 = 0.0f32;
    let mut v_res_441_: u8 = 0;
    let mut v_r_442_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_439_ = lean_unbox_float32(v_a_437_);
    lean_dec_ref(v_a_437_);
    v_b_boxed_440_ = lean_unbox_float32(v_b_438_);
    lean_dec_ref(v_b_438_);
    v_res_441_ = lean_float32_beq(v_a_boxed_439_, v_b_boxed_440_);
    v_r_442_ = lean_box((v_res_441_) as usize);
    return v_r_442_;
}
pub unsafe fn l_Float32_decLt___boxed(
    mut v_a_447_: *mut LeanObject,
    mut v_b_448_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_449_: f32 = 0.0f32;
    let mut v_b_boxed_450_: f32 = 0.0f32;
    let mut v_res_451_: u8 = 0;
    let mut v_r_452_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_449_ = lean_unbox_float32(v_a_447_);
    lean_dec_ref(v_a_447_);
    v_b_boxed_450_ = lean_unbox_float32(v_b_448_);
    lean_dec_ref(v_b_448_);
    v_res_451_ = lean_float32_decLt(v_a_boxed_449_, v_b_boxed_450_);
    v_r_452_ = lean_box((v_res_451_) as usize);
    return v_r_452_;
}
pub unsafe fn l_Float32_decLe___boxed(
    mut v_a_455_: *mut LeanObject,
    mut v_b_456_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_457_: f32 = 0.0f32;
    let mut v_b_boxed_458_: f32 = 0.0f32;
    let mut v_res_459_: u8 = 0;
    let mut v_r_460_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_457_ = lean_unbox_float32(v_a_455_);
    lean_dec_ref(v_a_455_);
    v_b_boxed_458_ = lean_unbox_float32(v_b_456_);
    lean_dec_ref(v_b_456_);
    v_res_459_ = lean_float32_decLe(v_a_boxed_457_, v_b_boxed_458_);
    v_r_460_ = lean_box((v_res_459_) as usize);
    return v_r_460_;
}
pub unsafe fn l_Float32_toString___boxed(
    mut v_a_00___x40___internal___hyg_462_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_463_: f32 = 0.0f32;
    let mut v_res_464_: *mut LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_463_ =
        lean_unbox_float32(v_a_00___x40___internal___hyg_462_);
    lean_dec_ref(v_a_00___x40___internal___hyg_462_);
    v_res_464_ = lean_float32_to_string(v_a_00___x40___internal___hyg_1__boxed_463_);
    return v_res_464_;
}
pub unsafe fn l_Float32_toUInt8___boxed(
    mut v_a_00___x40___internal___hyg_466_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_467_: f32 = 0.0f32;
    let mut v_res_468_: u8 = 0;
    let mut v_r_469_: *mut LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_467_ =
        lean_unbox_float32(v_a_00___x40___internal___hyg_466_);
    lean_dec_ref(v_a_00___x40___internal___hyg_466_);
    v_res_468_ = lean_float32_to_uint8(v_a_00___x40___internal___hyg_1__boxed_467_);
    v_r_469_ = lean_box((v_res_468_) as usize);
    return v_r_469_;
}
pub unsafe fn l_Float32_toUInt16___boxed(
    mut v_a_00___x40___internal___hyg_471_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_472_: f32 = 0.0f32;
    let mut v_res_473_: u16 = 0;
    let mut v_r_474_: *mut LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_472_ =
        lean_unbox_float32(v_a_00___x40___internal___hyg_471_);
    lean_dec_ref(v_a_00___x40___internal___hyg_471_);
    v_res_473_ = lean_float32_to_uint16(v_a_00___x40___internal___hyg_1__boxed_472_);
    v_r_474_ = lean_box((v_res_473_) as usize);
    return v_r_474_;
}
pub unsafe fn l_Float32_toUInt32___boxed(
    mut v_a_00___x40___internal___hyg_476_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_477_: f32 = 0.0f32;
    let mut v_res_478_: u32 = 0;
    let mut v_r_479_: *mut LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_477_ =
        lean_unbox_float32(v_a_00___x40___internal___hyg_476_);
    lean_dec_ref(v_a_00___x40___internal___hyg_476_);
    v_res_478_ = lean_float32_to_uint32(v_a_00___x40___internal___hyg_1__boxed_477_);
    v_r_479_ = lean_box_uint32(v_res_478_);
    return v_r_479_;
}
pub unsafe fn l_Float32_toUInt64___boxed(
    mut v_a_00___x40___internal___hyg_481_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_482_: f32 = 0.0f32;
    let mut v_res_483_: u64 = 0;
    let mut v_r_484_: *mut LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_482_ =
        lean_unbox_float32(v_a_00___x40___internal___hyg_481_);
    lean_dec_ref(v_a_00___x40___internal___hyg_481_);
    v_res_483_ = lean_float32_to_uint64(v_a_00___x40___internal___hyg_1__boxed_482_);
    v_r_484_ = lean_box_uint64(v_res_483_);
    return v_r_484_;
}
pub unsafe fn l_Float32_toUSize___boxed(
    mut v_a_00___x40___internal___hyg_486_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_487_: f32 = 0.0f32;
    let mut v_res_488_: usize = 0;
    let mut v_r_489_: *mut LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_487_ =
        lean_unbox_float32(v_a_00___x40___internal___hyg_486_);
    lean_dec_ref(v_a_00___x40___internal___hyg_486_);
    v_res_488_ = lean_float32_to_usize(v_a_00___x40___internal___hyg_1__boxed_487_);
    v_r_489_ = lean_box_usize(v_res_488_);
    return v_r_489_;
}
pub unsafe fn l_Float32_isNaN___boxed(
    mut v_a_00___x40___internal___hyg_491_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_492_: f32 = 0.0f32;
    let mut v_res_493_: u8 = 0;
    let mut v_r_494_: *mut LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_492_ =
        lean_unbox_float32(v_a_00___x40___internal___hyg_491_);
    lean_dec_ref(v_a_00___x40___internal___hyg_491_);
    v_res_493_ = lean_float32_isnan(v_a_00___x40___internal___hyg_1__boxed_492_);
    v_r_494_ = lean_box((v_res_493_) as usize);
    return v_r_494_;
}
pub unsafe fn l_Float32_isFinite___boxed(
    mut v_a_00___x40___internal___hyg_496_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_497_: f32 = 0.0f32;
    let mut v_res_498_: u8 = 0;
    let mut v_r_499_: *mut LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_497_ =
        lean_unbox_float32(v_a_00___x40___internal___hyg_496_);
    lean_dec_ref(v_a_00___x40___internal___hyg_496_);
    v_res_498_ = lean_float32_isfinite(v_a_00___x40___internal___hyg_1__boxed_497_);
    v_r_499_ = lean_box((v_res_498_) as usize);
    return v_r_499_;
}
pub unsafe fn l_Float32_isInf___boxed(
    mut v_a_00___x40___internal___hyg_501_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_502_: f32 = 0.0f32;
    let mut v_res_503_: u8 = 0;
    let mut v_r_504_: *mut LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_502_ =
        lean_unbox_float32(v_a_00___x40___internal___hyg_501_);
    lean_dec_ref(v_a_00___x40___internal___hyg_501_);
    v_res_503_ = lean_float32_isinf(v_a_00___x40___internal___hyg_1__boxed_502_);
    v_r_504_ = lean_box((v_res_503_) as usize);
    return v_r_504_;
}
pub unsafe fn l_Float32_frExp___boxed(
    mut v_a_00___x40___internal___hyg_506_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_507_: f32 = 0.0f32;
    let mut v_res_508_: *mut LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_507_ =
        lean_unbox_float32(v_a_00___x40___internal___hyg_506_);
    lean_dec_ref(v_a_00___x40___internal___hyg_506_);
    v_res_508_ = lean_float32_frexp(v_a_00___x40___internal___hyg_1__boxed_507_);
    return v_res_508_;
}
pub unsafe fn l_UInt8_toFloat32___boxed(mut v_n_512_: *mut LeanObject) -> *mut LeanObject {
    let mut v_n_boxed_513_: u8 = 0;
    let mut v_res_514_: f32 = 0.0f32;
    let mut v_r_515_: *mut LeanObject = core::ptr::null_mut();
    v_n_boxed_513_ = (lean_unbox(v_n_512_) as u8);
    v_res_514_ = lean_uint8_to_float32(v_n_boxed_513_);
    v_r_515_ = lean_box_float32(v_res_514_);
    return v_r_515_;
}
pub unsafe fn l_UInt16_toFloat32___boxed(mut v_n_517_: *mut LeanObject) -> *mut LeanObject {
    let mut v_n_boxed_518_: u16 = 0;
    let mut v_res_519_: f32 = 0.0f32;
    let mut v_r_520_: *mut LeanObject = core::ptr::null_mut();
    v_n_boxed_518_ = (lean_unbox(v_n_517_) as u16);
    v_res_519_ = lean_uint16_to_float32(v_n_boxed_518_);
    v_r_520_ = lean_box_float32(v_res_519_);
    return v_r_520_;
}
pub unsafe fn l_UInt32_toFloat32___boxed(mut v_n_522_: *mut LeanObject) -> *mut LeanObject {
    let mut v_n_boxed_523_: u32 = 0;
    let mut v_res_524_: f32 = 0.0f32;
    let mut v_r_525_: *mut LeanObject = core::ptr::null_mut();
    v_n_boxed_523_ = lean_unbox_uint32(v_n_522_);
    lean_dec(v_n_522_);
    v_res_524_ = lean_uint32_to_float32(v_n_boxed_523_);
    v_r_525_ = lean_box_float32(v_res_524_);
    return v_r_525_;
}
pub unsafe fn l_UInt64_toFloat32___boxed(mut v_n_527_: *mut LeanObject) -> *mut LeanObject {
    let mut v_n_boxed_528_: u64 = 0;
    let mut v_res_529_: f32 = 0.0f32;
    let mut v_r_530_: *mut LeanObject = core::ptr::null_mut();
    v_n_boxed_528_ = lean_unbox_uint64(v_n_527_);
    lean_dec_ref(v_n_527_);
    v_res_529_ = lean_uint64_to_float32(v_n_boxed_528_);
    v_r_530_ = lean_box_float32(v_res_529_);
    return v_r_530_;
}
pub unsafe fn l_USize_toFloat32___boxed(mut v_n_532_: *mut LeanObject) -> *mut LeanObject {
    let mut v_n_boxed_533_: usize = 0;
    let mut v_res_534_: f32 = 0.0f32;
    let mut v_r_535_: *mut LeanObject = core::ptr::null_mut();
    v_n_boxed_533_ = lean_unbox_usize(v_n_532_);
    lean_dec(v_n_532_);
    v_res_534_ = lean_usize_to_float32(v_n_boxed_533_);
    v_r_535_ = lean_box_float32(v_res_534_);
    return v_r_535_;
}
pub unsafe fn _init_l_instInhabitedFloat32___closed__0() -> f32 {
    let mut v___x_536_: u64 = 0;
    let mut v___x_537_: f32 = 0.0f32;
    v___x_536_ = 0u64;
    v___x_537_ = lean_uint64_to_float32(v___x_536_);
    return v___x_537_;
}
pub unsafe fn _init_l_instInhabitedFloat32() -> f32 {
    let mut v___x_538_: f32 = 0.0f32;
    v___x_538_ = lean_float32_once(
        core::ptr::addr_of_mut!(l_instInhabitedFloat32___closed__0),
        core::ptr::addr_of_mut!(l_instInhabitedFloat32___closed__0_once),
        _init_l_instInhabitedFloat32___closed__0,
    );
    return v___x_538_;
}
pub unsafe fn l_Float32_repr(
    mut v_n_539_: f32,
    mut v_prec_540_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_541_: f32 = 0.0f32;
    let mut v___x_542_: u8 = 0;
    v___x_541_ = lean_float32_once(
        core::ptr::addr_of_mut!(l_instInhabitedFloat32___closed__0),
        core::ptr::addr_of_mut!(l_instInhabitedFloat32___closed__0_once),
        _init_l_instInhabitedFloat32___closed__0,
    );
    v___x_542_ = lean_float32_decLt(v_n_539_, v___x_541_);
    if v___x_542_ == 0 {
        let mut v___x_543_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_544_: *mut LeanObject = core::ptr::null_mut();
        v___x_543_ = lean_float32_to_string(v_n_539_);
        v___x_544_ = lean_alloc_ctor(3, 1, (0) as u32);
        lean_ctor_set(v___x_544_, 0, v___x_543_);
        return v___x_544_;
    } else {
        let mut v___x_545_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_546_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_547_: *mut LeanObject = core::ptr::null_mut();
        v___x_545_ = lean_float32_to_string(v_n_539_);
        v___x_546_ = lean_alloc_ctor(3, 1, (0) as u32);
        lean_ctor_set(v___x_546_, 0, v___x_545_);
        v___x_547_ = l_Repr_addAppParen(v___x_546_, v_prec_540_);
        return v___x_547_;
    }
}
pub unsafe fn l_Float32_repr___boxed(
    mut v_n_548_: *mut LeanObject,
    mut v_prec_549_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_n_boxed_550_: f32 = 0.0f32;
    let mut v_res_551_: *mut LeanObject = core::ptr::null_mut();
    v_n_boxed_550_ = lean_unbox_float32(v_n_548_);
    lean_dec_ref(v_n_548_);
    v_res_551_ = l_Float32_repr(v_n_boxed_550_, v_prec_549_);
    lean_dec(v_prec_549_);
    return v_res_551_;
}
pub unsafe fn _init_l_instReprAtomFloat32() -> *mut LeanObject {
    let mut v___x_554_: *mut LeanObject = core::ptr::null_mut();
    v___x_554_ = lean_box(0);
    return v___x_554_;
}
pub unsafe fn l_Float32_sin___boxed(
    mut v_a_00___x40___internal___hyg_556_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_557_: f32 = 0.0f32;
    let mut v_res_558_: f32 = 0.0f32;
    let mut v_r_559_: *mut LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_557_ =
        lean_unbox_float32(v_a_00___x40___internal___hyg_556_);
    lean_dec_ref(v_a_00___x40___internal___hyg_556_);
    v_res_558_ = sinf(v_a_00___x40___internal___hyg_1__boxed_557_);
    v_r_559_ = lean_box_float32(v_res_558_);
    return v_r_559_;
}
pub unsafe fn l_Float32_cos___boxed(
    mut v_a_00___x40___internal___hyg_561_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_562_: f32 = 0.0f32;
    let mut v_res_563_: f32 = 0.0f32;
    let mut v_r_564_: *mut LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_562_ =
        lean_unbox_float32(v_a_00___x40___internal___hyg_561_);
    lean_dec_ref(v_a_00___x40___internal___hyg_561_);
    v_res_563_ = cosf(v_a_00___x40___internal___hyg_1__boxed_562_);
    v_r_564_ = lean_box_float32(v_res_563_);
    return v_r_564_;
}
pub unsafe fn l_Float32_tan___boxed(
    mut v_a_00___x40___internal___hyg_566_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_567_: f32 = 0.0f32;
    let mut v_res_568_: f32 = 0.0f32;
    let mut v_r_569_: *mut LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_567_ =
        lean_unbox_float32(v_a_00___x40___internal___hyg_566_);
    lean_dec_ref(v_a_00___x40___internal___hyg_566_);
    v_res_568_ = tanf(v_a_00___x40___internal___hyg_1__boxed_567_);
    v_r_569_ = lean_box_float32(v_res_568_);
    return v_r_569_;
}
pub unsafe fn l_Float32_asin___boxed(
    mut v_a_00___x40___internal___hyg_571_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_572_: f32 = 0.0f32;
    let mut v_res_573_: f32 = 0.0f32;
    let mut v_r_574_: *mut LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_572_ =
        lean_unbox_float32(v_a_00___x40___internal___hyg_571_);
    lean_dec_ref(v_a_00___x40___internal___hyg_571_);
    v_res_573_ = asinf(v_a_00___x40___internal___hyg_1__boxed_572_);
    v_r_574_ = lean_box_float32(v_res_573_);
    return v_r_574_;
}
pub unsafe fn l_Float32_acos___boxed(
    mut v_a_00___x40___internal___hyg_576_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_577_: f32 = 0.0f32;
    let mut v_res_578_: f32 = 0.0f32;
    let mut v_r_579_: *mut LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_577_ =
        lean_unbox_float32(v_a_00___x40___internal___hyg_576_);
    lean_dec_ref(v_a_00___x40___internal___hyg_576_);
    v_res_578_ = acosf(v_a_00___x40___internal___hyg_1__boxed_577_);
    v_r_579_ = lean_box_float32(v_res_578_);
    return v_r_579_;
}
pub unsafe fn l_Float32_atan___boxed(
    mut v_a_00___x40___internal___hyg_581_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_582_: f32 = 0.0f32;
    let mut v_res_583_: f32 = 0.0f32;
    let mut v_r_584_: *mut LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_582_ =
        lean_unbox_float32(v_a_00___x40___internal___hyg_581_);
    lean_dec_ref(v_a_00___x40___internal___hyg_581_);
    v_res_583_ = atanf(v_a_00___x40___internal___hyg_1__boxed_582_);
    v_r_584_ = lean_box_float32(v_res_583_);
    return v_r_584_;
}
pub unsafe fn l_Float32_atan2___boxed(
    mut v_a_00___x40___internal___hyg_587_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_588_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_589_: f32 = 0.0f32;
    let mut v_a_00___x40___internal___hyg_2__boxed_590_: f32 = 0.0f32;
    let mut v_res_591_: f32 = 0.0f32;
    let mut v_r_592_: *mut LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_589_ =
        lean_unbox_float32(v_a_00___x40___internal___hyg_587_);
    lean_dec_ref(v_a_00___x40___internal___hyg_587_);
    v_a_00___x40___internal___hyg_2__boxed_590_ =
        lean_unbox_float32(v_a_00___x40___internal___hyg_588_);
    lean_dec_ref(v_a_00___x40___internal___hyg_588_);
    v_res_591_ = atan2f(
        v_a_00___x40___internal___hyg_1__boxed_589_,
        v_a_00___x40___internal___hyg_2__boxed_590_,
    );
    v_r_592_ = lean_box_float32(v_res_591_);
    return v_r_592_;
}
pub unsafe fn l_Float32_sinh___boxed(
    mut v_a_00___x40___internal___hyg_594_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_595_: f32 = 0.0f32;
    let mut v_res_596_: f32 = 0.0f32;
    let mut v_r_597_: *mut LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_595_ =
        lean_unbox_float32(v_a_00___x40___internal___hyg_594_);
    lean_dec_ref(v_a_00___x40___internal___hyg_594_);
    v_res_596_ = sinhf(v_a_00___x40___internal___hyg_1__boxed_595_);
    v_r_597_ = lean_box_float32(v_res_596_);
    return v_r_597_;
}
pub unsafe fn l_Float32_cosh___boxed(
    mut v_a_00___x40___internal___hyg_599_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_600_: f32 = 0.0f32;
    let mut v_res_601_: f32 = 0.0f32;
    let mut v_r_602_: *mut LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_600_ =
        lean_unbox_float32(v_a_00___x40___internal___hyg_599_);
    lean_dec_ref(v_a_00___x40___internal___hyg_599_);
    v_res_601_ = coshf(v_a_00___x40___internal___hyg_1__boxed_600_);
    v_r_602_ = lean_box_float32(v_res_601_);
    return v_r_602_;
}
pub unsafe fn l_Float32_tanh___boxed(
    mut v_a_00___x40___internal___hyg_604_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_605_: f32 = 0.0f32;
    let mut v_res_606_: f32 = 0.0f32;
    let mut v_r_607_: *mut LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_605_ =
        lean_unbox_float32(v_a_00___x40___internal___hyg_604_);
    lean_dec_ref(v_a_00___x40___internal___hyg_604_);
    v_res_606_ = tanhf(v_a_00___x40___internal___hyg_1__boxed_605_);
    v_r_607_ = lean_box_float32(v_res_606_);
    return v_r_607_;
}
pub unsafe fn l_Float32_asinh___boxed(
    mut v_a_00___x40___internal___hyg_609_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_610_: f32 = 0.0f32;
    let mut v_res_611_: f32 = 0.0f32;
    let mut v_r_612_: *mut LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_610_ =
        lean_unbox_float32(v_a_00___x40___internal___hyg_609_);
    lean_dec_ref(v_a_00___x40___internal___hyg_609_);
    v_res_611_ = asinhf(v_a_00___x40___internal___hyg_1__boxed_610_);
    v_r_612_ = lean_box_float32(v_res_611_);
    return v_r_612_;
}
pub unsafe fn l_Float32_acosh___boxed(
    mut v_a_00___x40___internal___hyg_614_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_615_: f32 = 0.0f32;
    let mut v_res_616_: f32 = 0.0f32;
    let mut v_r_617_: *mut LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_615_ =
        lean_unbox_float32(v_a_00___x40___internal___hyg_614_);
    lean_dec_ref(v_a_00___x40___internal___hyg_614_);
    v_res_616_ = acoshf(v_a_00___x40___internal___hyg_1__boxed_615_);
    v_r_617_ = lean_box_float32(v_res_616_);
    return v_r_617_;
}
pub unsafe fn l_Float32_atanh___boxed(
    mut v_a_00___x40___internal___hyg_619_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_620_: f32 = 0.0f32;
    let mut v_res_621_: f32 = 0.0f32;
    let mut v_r_622_: *mut LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_620_ =
        lean_unbox_float32(v_a_00___x40___internal___hyg_619_);
    lean_dec_ref(v_a_00___x40___internal___hyg_619_);
    v_res_621_ = atanhf(v_a_00___x40___internal___hyg_1__boxed_620_);
    v_r_622_ = lean_box_float32(v_res_621_);
    return v_r_622_;
}
pub unsafe fn l_Float32_exp___boxed(
    mut v_a_00___x40___internal___hyg_624_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_625_: f32 = 0.0f32;
    let mut v_res_626_: f32 = 0.0f32;
    let mut v_r_627_: *mut LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_625_ =
        lean_unbox_float32(v_a_00___x40___internal___hyg_624_);
    lean_dec_ref(v_a_00___x40___internal___hyg_624_);
    v_res_626_ = expf(v_a_00___x40___internal___hyg_1__boxed_625_);
    v_r_627_ = lean_box_float32(v_res_626_);
    return v_r_627_;
}
pub unsafe fn l_Float32_exp2___boxed(
    mut v_a_00___x40___internal___hyg_629_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_630_: f32 = 0.0f32;
    let mut v_res_631_: f32 = 0.0f32;
    let mut v_r_632_: *mut LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_630_ =
        lean_unbox_float32(v_a_00___x40___internal___hyg_629_);
    lean_dec_ref(v_a_00___x40___internal___hyg_629_);
    v_res_631_ = exp2f(v_a_00___x40___internal___hyg_1__boxed_630_);
    v_r_632_ = lean_box_float32(v_res_631_);
    return v_r_632_;
}
pub unsafe fn l_Float32_log___boxed(
    mut v_a_00___x40___internal___hyg_634_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_635_: f32 = 0.0f32;
    let mut v_res_636_: f32 = 0.0f32;
    let mut v_r_637_: *mut LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_635_ =
        lean_unbox_float32(v_a_00___x40___internal___hyg_634_);
    lean_dec_ref(v_a_00___x40___internal___hyg_634_);
    v_res_636_ = logf(v_a_00___x40___internal___hyg_1__boxed_635_);
    v_r_637_ = lean_box_float32(v_res_636_);
    return v_r_637_;
}
pub unsafe fn l_Float32_log2___boxed(
    mut v_a_00___x40___internal___hyg_639_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_640_: f32 = 0.0f32;
    let mut v_res_641_: f32 = 0.0f32;
    let mut v_r_642_: *mut LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_640_ =
        lean_unbox_float32(v_a_00___x40___internal___hyg_639_);
    lean_dec_ref(v_a_00___x40___internal___hyg_639_);
    v_res_641_ = log2f(v_a_00___x40___internal___hyg_1__boxed_640_);
    v_r_642_ = lean_box_float32(v_res_641_);
    return v_r_642_;
}
pub unsafe fn l_Float32_log10___boxed(
    mut v_a_00___x40___internal___hyg_644_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_645_: f32 = 0.0f32;
    let mut v_res_646_: f32 = 0.0f32;
    let mut v_r_647_: *mut LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_645_ =
        lean_unbox_float32(v_a_00___x40___internal___hyg_644_);
    lean_dec_ref(v_a_00___x40___internal___hyg_644_);
    v_res_646_ = log10f(v_a_00___x40___internal___hyg_1__boxed_645_);
    v_r_647_ = lean_box_float32(v_res_646_);
    return v_r_647_;
}
pub unsafe fn l_Float32_pow___boxed(
    mut v_a_00___x40___internal___hyg_650_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_651_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_652_: f32 = 0.0f32;
    let mut v_a_00___x40___internal___hyg_2__boxed_653_: f32 = 0.0f32;
    let mut v_res_654_: f32 = 0.0f32;
    let mut v_r_655_: *mut LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_652_ =
        lean_unbox_float32(v_a_00___x40___internal___hyg_650_);
    lean_dec_ref(v_a_00___x40___internal___hyg_650_);
    v_a_00___x40___internal___hyg_2__boxed_653_ =
        lean_unbox_float32(v_a_00___x40___internal___hyg_651_);
    lean_dec_ref(v_a_00___x40___internal___hyg_651_);
    v_res_654_ = powf(
        v_a_00___x40___internal___hyg_1__boxed_652_,
        v_a_00___x40___internal___hyg_2__boxed_653_,
    );
    v_r_655_ = lean_box_float32(v_res_654_);
    return v_r_655_;
}
pub unsafe fn l_Float32_sqrt___boxed(
    mut v_a_00___x40___internal___hyg_657_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_658_: f32 = 0.0f32;
    let mut v_res_659_: f32 = 0.0f32;
    let mut v_r_660_: *mut LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_658_ =
        lean_unbox_float32(v_a_00___x40___internal___hyg_657_);
    lean_dec_ref(v_a_00___x40___internal___hyg_657_);
    v_res_659_ = sqrtf(v_a_00___x40___internal___hyg_1__boxed_658_);
    v_r_660_ = lean_box_float32(v_res_659_);
    return v_r_660_;
}
pub unsafe fn l_Float32_cbrt___boxed(
    mut v_a_00___x40___internal___hyg_662_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_663_: f32 = 0.0f32;
    let mut v_res_664_: f32 = 0.0f32;
    let mut v_r_665_: *mut LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_663_ =
        lean_unbox_float32(v_a_00___x40___internal___hyg_662_);
    lean_dec_ref(v_a_00___x40___internal___hyg_662_);
    v_res_664_ = cbrtf(v_a_00___x40___internal___hyg_1__boxed_663_);
    v_r_665_ = lean_box_float32(v_res_664_);
    return v_r_665_;
}
pub unsafe fn l_Float32_ceil___boxed(
    mut v_a_00___x40___internal___hyg_667_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_668_: f32 = 0.0f32;
    let mut v_res_669_: f32 = 0.0f32;
    let mut v_r_670_: *mut LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_668_ =
        lean_unbox_float32(v_a_00___x40___internal___hyg_667_);
    lean_dec_ref(v_a_00___x40___internal___hyg_667_);
    v_res_669_ = ceilf(v_a_00___x40___internal___hyg_1__boxed_668_);
    v_r_670_ = lean_box_float32(v_res_669_);
    return v_r_670_;
}
pub unsafe fn l_Float32_floor___boxed(
    mut v_a_00___x40___internal___hyg_672_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_673_: f32 = 0.0f32;
    let mut v_res_674_: f32 = 0.0f32;
    let mut v_r_675_: *mut LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_673_ =
        lean_unbox_float32(v_a_00___x40___internal___hyg_672_);
    lean_dec_ref(v_a_00___x40___internal___hyg_672_);
    v_res_674_ = floorf(v_a_00___x40___internal___hyg_1__boxed_673_);
    v_r_675_ = lean_box_float32(v_res_674_);
    return v_r_675_;
}
pub unsafe fn l_Float32_round___boxed(
    mut v_a_00___x40___internal___hyg_677_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_678_: f32 = 0.0f32;
    let mut v_res_679_: f32 = 0.0f32;
    let mut v_r_680_: *mut LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_678_ =
        lean_unbox_float32(v_a_00___x40___internal___hyg_677_);
    lean_dec_ref(v_a_00___x40___internal___hyg_677_);
    v_res_679_ = roundf(v_a_00___x40___internal___hyg_1__boxed_678_);
    v_r_680_ = lean_box_float32(v_res_679_);
    return v_r_680_;
}
pub unsafe fn l_Float32_abs___boxed(
    mut v_a_00___x40___internal___hyg_682_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_683_: f32 = 0.0f32;
    let mut v_res_684_: f32 = 0.0f32;
    let mut v_r_685_: *mut LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_683_ =
        lean_unbox_float32(v_a_00___x40___internal___hyg_682_);
    lean_dec_ref(v_a_00___x40___internal___hyg_682_);
    v_res_684_ = fabsf(v_a_00___x40___internal___hyg_1__boxed_683_);
    v_r_685_ = lean_box_float32(v_res_684_);
    return v_r_685_;
}
pub unsafe fn l_instMinFloat32___lam__0(mut v_x_688_: f32, mut v_y_689_: f32) -> f32 {
    let mut v___x_690_: u8 = 0;
    v___x_690_ = lean_float32_decLe(v_x_688_, v_y_689_);
    if v___x_690_ == 0 {
        return v_y_689_;
    } else {
        return v_x_688_;
    }
}
pub unsafe fn l_instMinFloat32___lam__0___boxed(
    mut v_x_691_: *mut LeanObject,
    mut v_y_692_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_boxed_693_: f32 = 0.0f32;
    let mut v_y_boxed_694_: f32 = 0.0f32;
    let mut v_res_695_: f32 = 0.0f32;
    let mut v_r_696_: *mut LeanObject = core::ptr::null_mut();
    v_x_boxed_693_ = lean_unbox_float32(v_x_691_);
    lean_dec_ref(v_x_691_);
    v_y_boxed_694_ = lean_unbox_float32(v_y_692_);
    lean_dec_ref(v_y_692_);
    v_res_695_ = l_instMinFloat32___lam__0(v_x_boxed_693_, v_y_boxed_694_);
    v_r_696_ = lean_box_float32(v_res_695_);
    return v_r_696_;
}
pub unsafe fn l_instMaxFloat32___lam__0(mut v_x_699_: f32, mut v_y_700_: f32) -> f32 {
    let mut v___x_701_: u8 = 0;
    v___x_701_ = lean_float32_decLe(v_x_699_, v_y_700_);
    if v___x_701_ == 0 {
        return v_x_699_;
    } else {
        return v_y_700_;
    }
}
pub unsafe fn l_instMaxFloat32___lam__0___boxed(
    mut v_x_702_: *mut LeanObject,
    mut v_y_703_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_boxed_704_: f32 = 0.0f32;
    let mut v_y_boxed_705_: f32 = 0.0f32;
    let mut v_res_706_: f32 = 0.0f32;
    let mut v_r_707_: *mut LeanObject = core::ptr::null_mut();
    v_x_boxed_704_ = lean_unbox_float32(v_x_702_);
    lean_dec_ref(v_x_702_);
    v_y_boxed_705_ = lean_unbox_float32(v_y_703_);
    lean_dec_ref(v_y_703_);
    v_res_706_ = l_instMaxFloat32___lam__0(v_x_boxed_704_, v_y_boxed_705_);
    v_r_707_ = lean_box_float32(v_res_706_);
    return v_r_707_;
}
pub unsafe fn l_Float32_scaleB___boxed(
    mut v_x_712_: *mut LeanObject,
    mut v_i_713_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_boxed_714_: f32 = 0.0f32;
    let mut v_res_715_: f32 = 0.0f32;
    let mut v_r_716_: *mut LeanObject = core::ptr::null_mut();
    v_x_boxed_714_ = lean_unbox_float32(v_x_712_);
    lean_dec_ref(v_x_712_);
    v_res_715_ = lean_float32_scaleb(v_x_boxed_714_, v_i_713_);
    lean_dec(v_i_713_);
    v_r_716_ = lean_box_float32(v_res_715_);
    return v_r_716_;
}
pub unsafe fn l_Float32_toFloat___boxed(
    mut v_a_00___x40___internal___hyg_718_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_719_: f32 = 0.0f32;
    let mut v_res_720_: f64 = 0.0;
    let mut v_r_721_: *mut LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_719_ =
        lean_unbox_float32(v_a_00___x40___internal___hyg_718_);
    lean_dec_ref(v_a_00___x40___internal___hyg_718_);
    v_res_720_ = lean_float32_to_float(v_a_00___x40___internal___hyg_1__boxed_719_);
    v_r_721_ = lean_box_float(v_res_720_);
    return v_r_721_;
}
pub unsafe fn l_Float_toFloat32___boxed(
    mut v_a_00___x40___internal___hyg_723_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_724_: f64 = 0.0;
    let mut v_res_725_: f32 = 0.0f32;
    let mut v_r_726_: *mut LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_724_ =
        lean_unbox_float(v_a_00___x40___internal___hyg_723_);
    lean_dec_ref(v_a_00___x40___internal___hyg_723_);
    v_res_725_ = lean_float_to_float32(v_a_00___x40___internal___hyg_1__boxed_724_);
    v_r_726_ = lean_box_float32(v_res_725_);
    return v_r_726_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Float32(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Float(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_instLTFloat32 = _init_l_instLTFloat32();
    lean_mark_persistent(l_instLTFloat32);
    l_instLEFloat32 = _init_l_instLEFloat32();
    lean_mark_persistent(l_instLEFloat32);
    l_instInhabitedFloat32 = _init_l_instInhabitedFloat32();
    l_instReprAtomFloat32 = _init_l_instReprAtomFloat32();
    lean_mark_persistent(l_instReprAtomFloat32);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Float32(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Float32(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Float(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Float32(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_Float32(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_Float32(builtin);
}
