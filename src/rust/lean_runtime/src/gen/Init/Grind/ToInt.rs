// Lean compiler output
// Module: Init.Grind.ToInt
// Imports: Init.LawfulBEqTactics Init.Data.Int.DivMod.Basic Init.Grind.Tactics Init.ByCases Init.Data.Int.DivMod.Lemmas Init.Omega
use crate::r#gen::Init::ByCases::{initialize_Init_ByCases, runtime_initialize_Init_ByCases};
use crate::r#gen::Init::Data::Int::Basic::l_Int_pow;
use crate::r#gen::Init::Data::Int::DivMod::Basic::{
    initialize_Init_Data_Int_DivMod_Basic, runtime_initialize_Init_Data_Int_DivMod_Basic,
};
use crate::r#gen::Init::Data::Int::DivMod::Lemmas::{
    initialize_Init_Data_Int_DivMod_Lemmas, runtime_initialize_Init_Data_Int_DivMod_Lemmas,
};
use crate::r#gen::Init::Grind::Tactics::{
    initialize_Init_Grind_Tactics, meta_initialize_Init_Grind_Tactics,
};
use crate::r#gen::Init::LawfulBEqTactics::{
    initialize_Init_LawfulBEqTactics, runtime_initialize_Init_LawfulBEqTactics,
};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr4, l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg,
    l_Lean_Syntax_isOfKind, l_Lean_Syntax_matchesNull, l_Lean_Syntax_node2,
};
use crate::lean_imports_rs::Init::Data::Int::Basic::{
    lean_int_add, lean_int_dec_eq, lean_int_dec_le, lean_int_dec_lt, lean_int_neg, lean_int_sub,
    lean_nat_to_int,
};
use crate::lean_imports_rs::Init::Data::Int::DivMod::Basic::lean_int_emod;
use crate::lean_imports_rs::Init::Prelude::lean_nat_sub;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_apply_1, lean_apply_2, lean_apply_4,
    lean_apply_6, lean_box, lean_ctor_get, lean_ctor_set, lean_ctor_set_tag, lean_dec,
    lean_dec_ref, lean_dec_ref_known, lean_inc, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_is_exclusive, lean_mark_persistent, lean_obj_once, lean_obj_tag, lean_unsigned_to_nat,
};
pub static l_Lean_Grind_instBEqIntInterval___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Grind_instBEqIntInterval_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_instBEqIntInterval___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instBEqIntInterval___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Grind_instBEqIntInterval: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instBEqIntInterval___closed__0_value) as *mut LeanObject;
static mut l_Lean_Grind_instInhabitedIntInterval_default___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Grind_instInhabitedIntInterval_default___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Grind_instInhabitedIntInterval_default___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Grind_instInhabitedIntInterval_default___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Grind_instInhabitedIntInterval_default: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Grind_instInhabitedIntInterval: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_IntInterval_uint___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_IntInterval_uint___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Grind_IntInterval_instMembershipInt: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_IntInterval_wrap___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_IntInterval_wrap___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Grind_toIntUnexpander___closed__0_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [76, 101, 97, 110, 0],
};
static mut l_Lean_Grind_toIntUnexpander___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_toIntUnexpander___closed__0_value) as *mut LeanObject;
pub static l_Lean_Grind_toIntUnexpander___closed__1_value: LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [80, 97, 114, 115, 101, 114, 0],
};
static mut l_Lean_Grind_toIntUnexpander___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_toIntUnexpander___closed__1_value) as *mut LeanObject;
pub static l_Lean_Grind_toIntUnexpander___closed__2_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [84, 101, 114, 109, 0],
};
static mut l_Lean_Grind_toIntUnexpander___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_toIntUnexpander___closed__2_value) as *mut LeanObject;
pub static l_Lean_Grind_toIntUnexpander___closed__3_value: LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [97, 112, 112, 0],
};
static mut l_Lean_Grind_toIntUnexpander___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_toIntUnexpander___closed__3_value) as *mut LeanObject;
static l_Lean_Grind_toIntUnexpander___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Grind_toIntUnexpander___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Grind_toIntUnexpander___closed__4_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Grind_toIntUnexpander___closed__4_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_toIntUnexpander___closed__1_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_Grind_toIntUnexpander___closed__4_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Grind_toIntUnexpander___closed__4_value_aux_1)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_toIntUnexpander___closed__2_value) as *mut LeanObject,
        16572064140653406795 as *mut LeanObject,
    ],
};
pub static l_Lean_Grind_toIntUnexpander___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Grind_toIntUnexpander___closed__4_value_aux_2)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_toIntUnexpander___closed__3_value) as *mut LeanObject,
        12966880221525079621 as *mut LeanObject,
    ],
};
static mut l_Lean_Grind_toIntUnexpander___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_toIntUnexpander___closed__4_value) as *mut LeanObject;
pub static l_Lean_Grind_toIntUnexpander___closed__5_value: LeanStringObject<12> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 11,
        m_data: [99, 111, 101, 78, 111, 116, 97, 116, 105, 111, 110, 0],
    };
static mut l_Lean_Grind_toIntUnexpander___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_toIntUnexpander___closed__5_value) as *mut LeanObject;
pub static l_Lean_Grind_toIntUnexpander___closed__6_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Grind_toIntUnexpander___closed__5_value) as *mut LeanObject,
        4193428478068483112 as *mut LeanObject,
    ],
};
static mut l_Lean_Grind_toIntUnexpander___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_toIntUnexpander___closed__6_value) as *mut LeanObject;
pub static l_Lean_Grind_toIntUnexpander___closed__7_value: LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 1,
    m_data: [226, 134, 145, 0],
};
static mut l_Lean_Grind_toIntUnexpander___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_toIntUnexpander___closed__7_value) as *mut LeanObject;
pub unsafe fn l_Lean_Grind_IntInterval_ctorIdx(mut v_x_314_: *mut LeanObject) -> *mut LeanObject {
    match lean_obj_tag(v_x_314_) {
        0 => {
            let mut v___x_315_: *mut LeanObject = core::ptr::null_mut();
            v___x_315_ = lean_unsigned_to_nat(0);
            return v___x_315_;
        }
        1 => {
            let mut v___x_316_: *mut LeanObject = core::ptr::null_mut();
            v___x_316_ = lean_unsigned_to_nat(1);
            return v___x_316_;
        }
        2 => {
            let mut v___x_317_: *mut LeanObject = core::ptr::null_mut();
            v___x_317_ = lean_unsigned_to_nat(2);
            return v___x_317_;
        }
        _ => {
            let mut v___x_318_: *mut LeanObject = core::ptr::null_mut();
            v___x_318_ = lean_unsigned_to_nat(3);
            return v___x_318_;
        }
    }
}
pub unsafe fn l_Lean_Grind_IntInterval_ctorIdx___boxed(
    mut v_x_319_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_320_: *mut LeanObject = core::ptr::null_mut();
    v_res_320_ = l_Lean_Grind_IntInterval_ctorIdx(v_x_319_);
    lean_dec(v_x_319_);
    return v_res_320_;
}
pub unsafe fn l_Lean_Grind_IntInterval_ctorElim___redArg(
    mut v_t_321_: *mut LeanObject,
    mut v_k_322_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_t_321_) {
        0 => {
            let mut v_lo_323_: *mut LeanObject = core::ptr::null_mut();
            let mut v_hi_324_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_325_: *mut LeanObject = core::ptr::null_mut();
            v_lo_323_ = lean_ctor_get(v_t_321_, 0);
            lean_inc(v_lo_323_);
            v_hi_324_ = lean_ctor_get(v_t_321_, 1);
            lean_inc(v_hi_324_);
            lean_dec_ref_known(v_t_321_, 2);
            v___x_325_ = lean_apply_2(v_k_322_, v_lo_323_, v_hi_324_);
            return v___x_325_;
        }
        3 => {
            return v_k_322_;
        }
        _ => {
            let mut v_lo_326_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_327_: *mut LeanObject = core::ptr::null_mut();
            v_lo_326_ = lean_ctor_get(v_t_321_, 0);
            lean_inc(v_lo_326_);
            lean_dec(v_t_321_);
            v___x_327_ = lean_apply_1(v_k_322_, v_lo_326_);
            return v___x_327_;
        }
    }
}
pub unsafe fn l_Lean_Grind_IntInterval_ctorElim(
    mut v_motive_328_: *mut LeanObject,
    mut v_ctorIdx_329_: *mut LeanObject,
    mut v_t_330_: *mut LeanObject,
    mut v_h_331_: *mut LeanObject,
    mut v_k_332_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_333_: *mut LeanObject = core::ptr::null_mut();
    v___x_333_ = l_Lean_Grind_IntInterval_ctorElim___redArg(v_t_330_, v_k_332_);
    return v___x_333_;
}
pub unsafe fn l_Lean_Grind_IntInterval_ctorElim___boxed(
    mut v_motive_334_: *mut LeanObject,
    mut v_ctorIdx_335_: *mut LeanObject,
    mut v_t_336_: *mut LeanObject,
    mut v_h_337_: *mut LeanObject,
    mut v_k_338_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_339_: *mut LeanObject = core::ptr::null_mut();
    v_res_339_ = l_Lean_Grind_IntInterval_ctorElim(
        v_motive_334_,
        v_ctorIdx_335_,
        v_t_336_,
        v_h_337_,
        v_k_338_,
    );
    lean_dec(v_ctorIdx_335_);
    return v_res_339_;
}
pub unsafe fn l_Lean_Grind_IntInterval_co_elim___redArg(
    mut v_t_340_: *mut LeanObject,
    mut v_co_341_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_342_: *mut LeanObject = core::ptr::null_mut();
    v___x_342_ = l_Lean_Grind_IntInterval_ctorElim___redArg(v_t_340_, v_co_341_);
    return v___x_342_;
}
pub unsafe fn l_Lean_Grind_IntInterval_co_elim(
    mut v_motive_343_: *mut LeanObject,
    mut v_t_344_: *mut LeanObject,
    mut v_h_345_: *mut LeanObject,
    mut v_co_346_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_347_: *mut LeanObject = core::ptr::null_mut();
    v___x_347_ = l_Lean_Grind_IntInterval_ctorElim___redArg(v_t_344_, v_co_346_);
    return v___x_347_;
}
pub unsafe fn l_Lean_Grind_IntInterval_ci_elim___redArg(
    mut v_t_348_: *mut LeanObject,
    mut v_ci_349_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_350_: *mut LeanObject = core::ptr::null_mut();
    v___x_350_ = l_Lean_Grind_IntInterval_ctorElim___redArg(v_t_348_, v_ci_349_);
    return v___x_350_;
}
pub unsafe fn l_Lean_Grind_IntInterval_ci_elim(
    mut v_motive_351_: *mut LeanObject,
    mut v_t_352_: *mut LeanObject,
    mut v_h_353_: *mut LeanObject,
    mut v_ci_354_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_355_: *mut LeanObject = core::ptr::null_mut();
    v___x_355_ = l_Lean_Grind_IntInterval_ctorElim___redArg(v_t_352_, v_ci_354_);
    return v___x_355_;
}
pub unsafe fn l_Lean_Grind_IntInterval_io_elim___redArg(
    mut v_t_356_: *mut LeanObject,
    mut v_io_357_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_358_: *mut LeanObject = core::ptr::null_mut();
    v___x_358_ = l_Lean_Grind_IntInterval_ctorElim___redArg(v_t_356_, v_io_357_);
    return v___x_358_;
}
pub unsafe fn l_Lean_Grind_IntInterval_io_elim(
    mut v_motive_359_: *mut LeanObject,
    mut v_t_360_: *mut LeanObject,
    mut v_h_361_: *mut LeanObject,
    mut v_io_362_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_363_: *mut LeanObject = core::ptr::null_mut();
    v___x_363_ = l_Lean_Grind_IntInterval_ctorElim___redArg(v_t_360_, v_io_362_);
    return v___x_363_;
}
pub unsafe fn l_Lean_Grind_IntInterval_ii_elim___redArg(
    mut v_t_364_: *mut LeanObject,
    mut v_ii_365_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_366_: *mut LeanObject = core::ptr::null_mut();
    v___x_366_ = l_Lean_Grind_IntInterval_ctorElim___redArg(v_t_364_, v_ii_365_);
    return v___x_366_;
}
pub unsafe fn l_Lean_Grind_IntInterval_ii_elim(
    mut v_motive_367_: *mut LeanObject,
    mut v_t_368_: *mut LeanObject,
    mut v_h_369_: *mut LeanObject,
    mut v_ii_370_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_371_: *mut LeanObject = core::ptr::null_mut();
    v___x_371_ = l_Lean_Grind_IntInterval_ctorElim___redArg(v_t_368_, v_ii_370_);
    return v___x_371_;
}
pub unsafe fn l_Lean_Grind_instBEqIntInterval_beq(
    mut v_x_372_: *mut LeanObject,
    mut v_x_373_: *mut LeanObject,
) -> u8 {
    match lean_obj_tag(v_x_372_) {
        0 => {
            if lean_obj_tag(v_x_373_) == 0 {
                let mut v_lo_374_: *mut LeanObject = core::ptr::null_mut();
                let mut v_hi_375_: *mut LeanObject = core::ptr::null_mut();
                let mut v_lo_376_: *mut LeanObject = core::ptr::null_mut();
                let mut v_hi_377_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_378_: u8 = 0;
                v_lo_374_ = lean_ctor_get(v_x_372_, 0);
                v_hi_375_ = lean_ctor_get(v_x_372_, 1);
                v_lo_376_ = lean_ctor_get(v_x_373_, 0);
                v_hi_377_ = lean_ctor_get(v_x_373_, 1);
                v___x_378_ = lean_int_dec_eq(v_lo_374_, v_lo_376_);
                if v___x_378_ == 0 {
                    return v___x_378_;
                } else {
                    let mut v___x_379_: u8 = 0;
                    v___x_379_ = lean_int_dec_eq(v_hi_375_, v_hi_377_);
                    return v___x_379_;
                }
            } else {
                let mut v___x_380_: u8 = 0;
                v___x_380_ = 0;
                return v___x_380_;
            }
        }
        1 => {
            if lean_obj_tag(v_x_373_) == 1 {
                let mut v_lo_381_: *mut LeanObject = core::ptr::null_mut();
                let mut v_lo_382_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_383_: u8 = 0;
                v_lo_381_ = lean_ctor_get(v_x_372_, 0);
                v_lo_382_ = lean_ctor_get(v_x_373_, 0);
                v___x_383_ = lean_int_dec_eq(v_lo_381_, v_lo_382_);
                return v___x_383_;
            } else {
                let mut v___x_384_: u8 = 0;
                v___x_384_ = 0;
                return v___x_384_;
            }
        }
        2 => {
            if lean_obj_tag(v_x_373_) == 2 {
                let mut v_hi_385_: *mut LeanObject = core::ptr::null_mut();
                let mut v_hi_386_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_387_: u8 = 0;
                v_hi_385_ = lean_ctor_get(v_x_372_, 0);
                v_hi_386_ = lean_ctor_get(v_x_373_, 0);
                v___x_387_ = lean_int_dec_eq(v_hi_385_, v_hi_386_);
                return v___x_387_;
            } else {
                let mut v___x_388_: u8 = 0;
                v___x_388_ = 0;
                return v___x_388_;
            }
        }
        _ => {
            if lean_obj_tag(v_x_373_) == 3 {
                let mut v___x_389_: u8 = 0;
                v___x_389_ = 1;
                return v___x_389_;
            } else {
                let mut v___x_390_: u8 = 0;
                v___x_390_ = 0;
                return v___x_390_;
            }
        }
    }
}
pub unsafe fn l_Lean_Grind_instBEqIntInterval_beq___boxed(
    mut v_x_391_: *mut LeanObject,
    mut v_x_392_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_393_: u8 = 0;
    let mut v_r_394_: *mut LeanObject = core::ptr::null_mut();
    v_res_393_ = l_Lean_Grind_instBEqIntInterval_beq(v_x_391_, v_x_392_);
    lean_dec(v_x_392_);
    lean_dec(v_x_391_);
    v_r_394_ = lean_box((v_res_393_) as usize);
    return v_r_394_;
}
pub unsafe fn l___private_Init_Grind_ToInt_0__Lean_Grind_instBEqIntInterval_beq_match__1_splitter___redArg(
    mut v_x_397_: *mut LeanObject,
    mut v_x_398_: *mut LeanObject,
    mut v_h__1_399_: *mut LeanObject,
    mut v_h__2_400_: *mut LeanObject,
    mut v_h__3_401_: *mut LeanObject,
    mut v_h__4_402_: *mut LeanObject,
    mut v_h__5_403_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_397_) {
        0 => {
            lean_dec(v_h__4_402_);
            lean_dec(v_h__3_401_);
            lean_dec(v_h__2_400_);
            if lean_obj_tag(v_x_398_) == 0 {
                let mut v_lo_404_: *mut LeanObject = core::ptr::null_mut();
                let mut v_hi_405_: *mut LeanObject = core::ptr::null_mut();
                let mut v_lo_406_: *mut LeanObject = core::ptr::null_mut();
                let mut v_hi_407_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_408_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v_h__5_403_);
                v_lo_404_ = lean_ctor_get(v_x_397_, 0);
                lean_inc(v_lo_404_);
                v_hi_405_ = lean_ctor_get(v_x_397_, 1);
                lean_inc(v_hi_405_);
                lean_dec_ref_known(v_x_397_, 2);
                v_lo_406_ = lean_ctor_get(v_x_398_, 0);
                lean_inc(v_lo_406_);
                v_hi_407_ = lean_ctor_get(v_x_398_, 1);
                lean_inc(v_hi_407_);
                lean_dec_ref_known(v_x_398_, 2);
                v___x_408_ = lean_apply_4(v_h__1_399_, v_lo_404_, v_hi_405_, v_lo_406_, v_hi_407_);
                return v___x_408_;
            } else {
                let mut v___x_409_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v_h__1_399_);
                v___x_409_ = lean_apply_6(
                    v_h__5_403_,
                    v_x_397_,
                    v_x_398_,
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
                );
                return v___x_409_;
            }
        }
        1 => {
            lean_dec(v_h__4_402_);
            lean_dec(v_h__3_401_);
            lean_dec(v_h__1_399_);
            if lean_obj_tag(v_x_398_) == 1 {
                let mut v_lo_410_: *mut LeanObject = core::ptr::null_mut();
                let mut v_lo_411_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_412_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v_h__5_403_);
                v_lo_410_ = lean_ctor_get(v_x_397_, 0);
                lean_inc(v_lo_410_);
                lean_dec_ref_known(v_x_397_, 1);
                v_lo_411_ = lean_ctor_get(v_x_398_, 0);
                lean_inc(v_lo_411_);
                lean_dec_ref_known(v_x_398_, 1);
                v___x_412_ = lean_apply_2(v_h__2_400_, v_lo_410_, v_lo_411_);
                return v___x_412_;
            } else {
                let mut v___x_413_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v_h__2_400_);
                v___x_413_ = lean_apply_6(
                    v_h__5_403_,
                    v_x_397_,
                    v_x_398_,
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
                );
                return v___x_413_;
            }
        }
        2 => {
            lean_dec(v_h__4_402_);
            lean_dec(v_h__2_400_);
            lean_dec(v_h__1_399_);
            if lean_obj_tag(v_x_398_) == 2 {
                let mut v_hi_414_: *mut LeanObject = core::ptr::null_mut();
                let mut v_hi_415_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_416_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v_h__5_403_);
                v_hi_414_ = lean_ctor_get(v_x_397_, 0);
                lean_inc(v_hi_414_);
                lean_dec_ref_known(v_x_397_, 1);
                v_hi_415_ = lean_ctor_get(v_x_398_, 0);
                lean_inc(v_hi_415_);
                lean_dec_ref_known(v_x_398_, 1);
                v___x_416_ = lean_apply_2(v_h__3_401_, v_hi_414_, v_hi_415_);
                return v___x_416_;
            } else {
                let mut v___x_417_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v_h__3_401_);
                v___x_417_ = lean_apply_6(
                    v_h__5_403_,
                    v_x_397_,
                    v_x_398_,
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
                );
                return v___x_417_;
            }
        }
        _ => {
            lean_dec(v_h__3_401_);
            lean_dec(v_h__2_400_);
            lean_dec(v_h__1_399_);
            if lean_obj_tag(v_x_398_) == 3 {
                let mut v___x_418_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_419_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v_h__5_403_);
                v___x_418_ = lean_box(0);
                v___x_419_ = lean_apply_1(v_h__4_402_, v___x_418_);
                return v___x_419_;
            } else {
                let mut v___x_420_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v_h__4_402_);
                v___x_420_ = lean_apply_6(
                    v_h__5_403_,
                    v_x_397_,
                    v_x_398_,
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
                );
                return v___x_420_;
            }
        }
    }
}
pub unsafe fn l___private_Init_Grind_ToInt_0__Lean_Grind_instBEqIntInterval_beq_match__1_splitter(
    mut v_motive_421_: *mut LeanObject,
    mut v_x_422_: *mut LeanObject,
    mut v_x_423_: *mut LeanObject,
    mut v_h__1_424_: *mut LeanObject,
    mut v_h__2_425_: *mut LeanObject,
    mut v_h__3_426_: *mut LeanObject,
    mut v_h__4_427_: *mut LeanObject,
    mut v_h__5_428_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_422_) {
        0 => {
            lean_dec(v_h__4_427_);
            lean_dec(v_h__3_426_);
            lean_dec(v_h__2_425_);
            if lean_obj_tag(v_x_423_) == 0 {
                let mut v_lo_429_: *mut LeanObject = core::ptr::null_mut();
                let mut v_hi_430_: *mut LeanObject = core::ptr::null_mut();
                let mut v_lo_431_: *mut LeanObject = core::ptr::null_mut();
                let mut v_hi_432_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_433_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v_h__5_428_);
                v_lo_429_ = lean_ctor_get(v_x_422_, 0);
                lean_inc(v_lo_429_);
                v_hi_430_ = lean_ctor_get(v_x_422_, 1);
                lean_inc(v_hi_430_);
                lean_dec_ref_known(v_x_422_, 2);
                v_lo_431_ = lean_ctor_get(v_x_423_, 0);
                lean_inc(v_lo_431_);
                v_hi_432_ = lean_ctor_get(v_x_423_, 1);
                lean_inc(v_hi_432_);
                lean_dec_ref_known(v_x_423_, 2);
                v___x_433_ = lean_apply_4(v_h__1_424_, v_lo_429_, v_hi_430_, v_lo_431_, v_hi_432_);
                return v___x_433_;
            } else {
                let mut v___x_434_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v_h__1_424_);
                v___x_434_ = lean_apply_6(
                    v_h__5_428_,
                    v_x_422_,
                    v_x_423_,
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
                );
                return v___x_434_;
            }
        }
        1 => {
            lean_dec(v_h__4_427_);
            lean_dec(v_h__3_426_);
            lean_dec(v_h__1_424_);
            if lean_obj_tag(v_x_423_) == 1 {
                let mut v_lo_435_: *mut LeanObject = core::ptr::null_mut();
                let mut v_lo_436_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_437_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v_h__5_428_);
                v_lo_435_ = lean_ctor_get(v_x_422_, 0);
                lean_inc(v_lo_435_);
                lean_dec_ref_known(v_x_422_, 1);
                v_lo_436_ = lean_ctor_get(v_x_423_, 0);
                lean_inc(v_lo_436_);
                lean_dec_ref_known(v_x_423_, 1);
                v___x_437_ = lean_apply_2(v_h__2_425_, v_lo_435_, v_lo_436_);
                return v___x_437_;
            } else {
                let mut v___x_438_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v_h__2_425_);
                v___x_438_ = lean_apply_6(
                    v_h__5_428_,
                    v_x_422_,
                    v_x_423_,
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
                );
                return v___x_438_;
            }
        }
        2 => {
            lean_dec(v_h__4_427_);
            lean_dec(v_h__2_425_);
            lean_dec(v_h__1_424_);
            if lean_obj_tag(v_x_423_) == 2 {
                let mut v_hi_439_: *mut LeanObject = core::ptr::null_mut();
                let mut v_hi_440_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_441_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v_h__5_428_);
                v_hi_439_ = lean_ctor_get(v_x_422_, 0);
                lean_inc(v_hi_439_);
                lean_dec_ref_known(v_x_422_, 1);
                v_hi_440_ = lean_ctor_get(v_x_423_, 0);
                lean_inc(v_hi_440_);
                lean_dec_ref_known(v_x_423_, 1);
                v___x_441_ = lean_apply_2(v_h__3_426_, v_hi_439_, v_hi_440_);
                return v___x_441_;
            } else {
                let mut v___x_442_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v_h__3_426_);
                v___x_442_ = lean_apply_6(
                    v_h__5_428_,
                    v_x_422_,
                    v_x_423_,
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
                );
                return v___x_442_;
            }
        }
        _ => {
            lean_dec(v_h__3_426_);
            lean_dec(v_h__2_425_);
            lean_dec(v_h__1_424_);
            if lean_obj_tag(v_x_423_) == 3 {
                let mut v___x_443_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_444_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v_h__5_428_);
                v___x_443_ = lean_box(0);
                v___x_444_ = lean_apply_1(v_h__4_427_, v___x_443_);
                return v___x_444_;
            } else {
                let mut v___x_445_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v_h__4_427_);
                v___x_445_ = lean_apply_6(
                    v_h__5_428_,
                    v_x_422_,
                    v_x_423_,
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
                );
                return v___x_445_;
            }
        }
    }
}
pub unsafe fn l_Lean_Grind_instDecidableEqIntInterval_decEq(
    mut v_x_446_: *mut LeanObject,
    mut v_x_447_: *mut LeanObject,
) -> u8 {
    match lean_obj_tag(v_x_446_) {
        0 => {
            let mut v_lo_448_: *mut LeanObject = core::ptr::null_mut();
            let mut v_hi_449_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_450_: u8 = 0;
            v_lo_448_ = lean_ctor_get(v_x_446_, 0);
            v_hi_449_ = lean_ctor_get(v_x_446_, 1);
            v___x_450_ = 0;
            match lean_obj_tag(v_x_447_) {
                0 => {
                    let mut v_lo_451_: *mut LeanObject = core::ptr::null_mut();
                    let mut v_hi_452_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_453_: u8 = 0;
                    v_lo_451_ = lean_ctor_get(v_x_447_, 0);
                    v_hi_452_ = lean_ctor_get(v_x_447_, 1);
                    v___x_453_ = lean_int_dec_eq(v_lo_448_, v_lo_451_);
                    if v___x_453_ == 0 {
                        return v___x_450_;
                    } else {
                        let mut v___x_454_: u8 = 0;
                        v___x_454_ = lean_int_dec_eq(v_hi_449_, v_hi_452_);
                        if v___x_454_ == 0 {
                            return v___x_450_;
                        } else {
                            return v___x_454_;
                        }
                    }
                }
                3 => {
                    return v___x_450_;
                }
                _ => {
                    return v___x_450_;
                }
            }
        }
        1 => {
            let mut v_lo_455_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_456_: u8 = 0;
            v_lo_455_ = lean_ctor_get(v_x_446_, 0);
            v___x_456_ = 0;
            match lean_obj_tag(v_x_447_) {
                1 => {
                    let mut v_lo_457_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_458_: u8 = 0;
                    v_lo_457_ = lean_ctor_get(v_x_447_, 0);
                    v___x_458_ = lean_int_dec_eq(v_lo_455_, v_lo_457_);
                    if v___x_458_ == 0 {
                        return v___x_456_;
                    } else {
                        return v___x_458_;
                    }
                }
                3 => {
                    return v___x_456_;
                }
                _ => {
                    return v___x_456_;
                }
            }
        }
        2 => {
            let mut v_hi_459_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_460_: u8 = 0;
            v_hi_459_ = lean_ctor_get(v_x_446_, 0);
            v___x_460_ = 0;
            match lean_obj_tag(v_x_447_) {
                2 => {
                    let mut v_hi_461_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_462_: u8 = 0;
                    v_hi_461_ = lean_ctor_get(v_x_447_, 0);
                    v___x_462_ = lean_int_dec_eq(v_hi_459_, v_hi_461_);
                    if v___x_462_ == 0 {
                        return v___x_460_;
                    } else {
                        return v___x_462_;
                    }
                }
                3 => {
                    return v___x_460_;
                }
                _ => {
                    return v___x_460_;
                }
            }
        }
        _ => {
            if lean_obj_tag(v_x_447_) == 3 {
                let mut v___x_463_: u8 = 0;
                v___x_463_ = 1;
                return v___x_463_;
            } else {
                let mut v___x_464_: u8 = 0;
                v___x_464_ = 0;
                return v___x_464_;
            }
        }
    }
}
pub unsafe fn l_Lean_Grind_instDecidableEqIntInterval_decEq___boxed(
    mut v_x_465_: *mut LeanObject,
    mut v_x_466_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_467_: u8 = 0;
    let mut v_r_468_: *mut LeanObject = core::ptr::null_mut();
    v_res_467_ = l_Lean_Grind_instDecidableEqIntInterval_decEq(v_x_465_, v_x_466_);
    lean_dec(v_x_466_);
    lean_dec(v_x_465_);
    v_r_468_ = lean_box((v_res_467_) as usize);
    return v_r_468_;
}
pub unsafe fn l_Lean_Grind_instDecidableEqIntInterval(
    mut v_x_469_: *mut LeanObject,
    mut v_x_470_: *mut LeanObject,
) -> u8 {
    let mut v___x_471_: u8 = 0;
    v___x_471_ = l_Lean_Grind_instDecidableEqIntInterval_decEq(v_x_469_, v_x_470_);
    return v___x_471_;
}
pub unsafe fn l_Lean_Grind_instDecidableEqIntInterval___boxed(
    mut v_x_472_: *mut LeanObject,
    mut v_x_473_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_474_: u8 = 0;
    let mut v_r_475_: *mut LeanObject = core::ptr::null_mut();
    v_res_474_ = l_Lean_Grind_instDecidableEqIntInterval(v_x_472_, v_x_473_);
    lean_dec(v_x_473_);
    lean_dec(v_x_472_);
    v_r_475_ = lean_box((v_res_474_) as usize);
    return v_r_475_;
}
pub unsafe fn _init_l_Lean_Grind_instInhabitedIntInterval_default___closed__0() -> *mut LeanObject {
    let mut v___x_476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_477_: *mut LeanObject = core::ptr::null_mut();
    v___x_476_ = lean_unsigned_to_nat(0);
    v___x_477_ = lean_nat_to_int(v___x_476_);
    return v___x_477_;
}
pub unsafe fn _init_l_Lean_Grind_instInhabitedIntInterval_default___closed__1() -> *mut LeanObject {
    let mut v___x_478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_479_: *mut LeanObject = core::ptr::null_mut();
    v___x_478_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_instInhabitedIntInterval_default___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Grind_instInhabitedIntInterval_default___closed__0_once),
        _init_l_Lean_Grind_instInhabitedIntInterval_default___closed__0,
    );
    v___x_479_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_479_, 0, v___x_478_);
    lean_ctor_set(v___x_479_, 1, v___x_478_);
    return v___x_479_;
}
pub unsafe fn _init_l_Lean_Grind_instInhabitedIntInterval_default() -> *mut LeanObject {
    let mut v___x_480_: *mut LeanObject = core::ptr::null_mut();
    v___x_480_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_instInhabitedIntInterval_default___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Grind_instInhabitedIntInterval_default___closed__1_once),
        _init_l_Lean_Grind_instInhabitedIntInterval_default___closed__1,
    );
    return v___x_480_;
}
pub unsafe fn _init_l_Lean_Grind_instInhabitedIntInterval() -> *mut LeanObject {
    let mut v___x_481_: *mut LeanObject = core::ptr::null_mut();
    v___x_481_ = l_Lean_Grind_instInhabitedIntInterval_default;
    return v___x_481_;
}
pub unsafe fn _init_l_Lean_Grind_IntInterval_uint___closed__0() -> *mut LeanObject {
    let mut v___x_482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_483_: *mut LeanObject = core::ptr::null_mut();
    v___x_482_ = lean_unsigned_to_nat(2);
    v___x_483_ = lean_nat_to_int(v___x_482_);
    return v___x_483_;
}
pub unsafe fn l_Lean_Grind_IntInterval_uint(mut v_n_484_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_488_: *mut LeanObject = core::ptr::null_mut();
    v___x_485_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_instInhabitedIntInterval_default___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Grind_instInhabitedIntInterval_default___closed__0_once),
        _init_l_Lean_Grind_instInhabitedIntInterval_default___closed__0,
    );
    v___x_486_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_IntInterval_uint___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Grind_IntInterval_uint___closed__0_once),
        _init_l_Lean_Grind_IntInterval_uint___closed__0,
    );
    v___x_487_ = l_Int_pow(v___x_486_, v_n_484_);
    v___x_488_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_488_, 0, v___x_485_);
    lean_ctor_set(v___x_488_, 1, v___x_487_);
    return v___x_488_;
}
pub unsafe fn l_Lean_Grind_IntInterval_uint___boxed(
    mut v_n_489_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_490_: *mut LeanObject = core::ptr::null_mut();
    v_res_490_ = l_Lean_Grind_IntInterval_uint(v_n_489_);
    lean_dec(v_n_489_);
    return v_res_490_;
}
pub unsafe fn l_Lean_Grind_IntInterval_sint(mut v_n_491_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_497_: *mut LeanObject = core::ptr::null_mut();
    v___x_492_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_IntInterval_uint___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Grind_IntInterval_uint___closed__0_once),
        _init_l_Lean_Grind_IntInterval_uint___closed__0,
    );
    v___x_493_ = lean_unsigned_to_nat(1);
    v___x_494_ = lean_nat_sub(v_n_491_, v___x_493_);
    v___x_495_ = l_Int_pow(v___x_492_, v___x_494_);
    lean_dec(v___x_494_);
    v___x_496_ = lean_int_neg(v___x_495_);
    v___x_497_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_497_, 0, v___x_496_);
    lean_ctor_set(v___x_497_, 1, v___x_495_);
    return v___x_497_;
}
pub unsafe fn l_Lean_Grind_IntInterval_sint___boxed(
    mut v_n_498_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_499_: *mut LeanObject = core::ptr::null_mut();
    v_res_499_ = l_Lean_Grind_IntInterval_sint(v_n_498_);
    lean_dec(v_n_498_);
    return v_res_499_;
}
pub unsafe fn l_Lean_Grind_IntInterval_lo_x3f(mut v_i_500_: *mut LeanObject) -> *mut LeanObject {
    let mut v_lo_501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lo_503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_506_: u8 = 0;
    let mut v___x_508_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_510_: u8 = 0;
    let mut v___x_511_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_i_500_) {
                0 => {
                    v_lo_501_ = lean_ctor_get(v_i_500_, 0);
                    lean_inc(v_lo_501_);
                    lean_dec_ref_known(v_i_500_, 2);
                    v___x_502_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_502_, 0, v_lo_501_);
                    return v___x_502_;
                }
                1 => {
                    v_lo_503_ = lean_ctor_get(v_i_500_, 0);
                    v_isSharedCheck_510_ = (!lean_is_exclusive(v_i_500_)) as u8;
                    if v_isSharedCheck_510_ == 0 {
                        v___x_505_ = v_i_500_;
                        v_isShared_506_ = v_isSharedCheck_510_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_lo_503_);
                        lean_dec(v_i_500_);
                        v___x_505_ = lean_box(0);
                        v_isShared_506_ = v_isSharedCheck_510_;
                        state = 1;
                        continue;
                    }
                }
                _ => {
                    lean_dec(v_i_500_);
                    v___x_511_ = lean_box(0);
                    return v___x_511_;
                }
            },
            1 => {
                if v_isShared_506_ == 0 {
                    v___x_508_ = v___x_505_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_509_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_509_, 0, v_lo_503_);
                    v___x_508_ = v_reuseFailAlloc_509_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_508_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_IntInterval_hi_x3f(mut v_i_512_: *mut LeanObject) -> *mut LeanObject {
    let mut v_hi_513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_514_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hi_515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_518_: u8 = 0;
    let mut v___x_520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_521_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_522_: u8 = 0;
    let mut v___x_523_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_i_512_) {
                0 => {
                    v_hi_513_ = lean_ctor_get(v_i_512_, 1);
                    lean_inc(v_hi_513_);
                    lean_dec_ref_known(v_i_512_, 2);
                    v___x_514_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_514_, 0, v_hi_513_);
                    return v___x_514_;
                }
                2 => {
                    v_hi_515_ = lean_ctor_get(v_i_512_, 0);
                    v_isSharedCheck_522_ = (!lean_is_exclusive(v_i_512_)) as u8;
                    if v_isSharedCheck_522_ == 0 {
                        v___x_517_ = v_i_512_;
                        v_isShared_518_ = v_isSharedCheck_522_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_hi_515_);
                        lean_dec(v_i_512_);
                        v___x_517_ = lean_box(0);
                        v_isShared_518_ = v_isSharedCheck_522_;
                        state = 1;
                        continue;
                    }
                }
                _ => {
                    lean_dec(v_i_512_);
                    v___x_523_ = lean_box(0);
                    return v___x_523_;
                }
            },
            1 => {
                if v_isShared_518_ == 0 {
                    lean_ctor_set_tag(v___x_517_, 1);
                    v___x_520_ = v___x_517_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_521_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_521_, 0, v_hi_515_);
                    v___x_520_ = v_reuseFailAlloc_521_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_520_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_IntInterval_nonEmpty(mut v_i_524_: *mut LeanObject) -> u8 {
    match lean_obj_tag(v_i_524_) {
        0 => {
            let mut v_lo_525_: *mut LeanObject = core::ptr::null_mut();
            let mut v_hi_526_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_527_: u8 = 0;
            v_lo_525_ = lean_ctor_get(v_i_524_, 0);
            v_hi_526_ = lean_ctor_get(v_i_524_, 1);
            v___x_527_ = lean_int_dec_lt(v_lo_525_, v_hi_526_);
            return v___x_527_;
        }
        3 => {
            let mut v___x_528_: u8 = 0;
            v___x_528_ = 1;
            return v___x_528_;
        }
        _ => {
            let mut v___x_529_: u8 = 0;
            v___x_529_ = 1;
            return v___x_529_;
        }
    }
}
pub unsafe fn l_Lean_Grind_IntInterval_nonEmpty___boxed(
    mut v_i_530_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_531_: u8 = 0;
    let mut v_r_532_: *mut LeanObject = core::ptr::null_mut();
    v_res_531_ = l_Lean_Grind_IntInterval_nonEmpty(v_i_530_);
    lean_dec(v_i_530_);
    v_r_532_ = lean_box((v_res_531_) as usize);
    return v_r_532_;
}
pub unsafe fn l___private_Init_Grind_ToInt_0__Lean_Grind_IntInterval_lo_x3f_match__1_splitter___redArg(
    mut v_i_533_: *mut LeanObject,
    mut v_h__1_534_: *mut LeanObject,
    mut v_h__2_535_: *mut LeanObject,
    mut v_h__3_536_: *mut LeanObject,
    mut v_h__4_537_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_i_533_) {
        0 => {
            let mut v_lo_538_: *mut LeanObject = core::ptr::null_mut();
            let mut v_hi_539_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_540_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__4_537_);
            lean_dec(v_h__3_536_);
            lean_dec(v_h__2_535_);
            v_lo_538_ = lean_ctor_get(v_i_533_, 0);
            lean_inc(v_lo_538_);
            v_hi_539_ = lean_ctor_get(v_i_533_, 1);
            lean_inc(v_hi_539_);
            lean_dec_ref_known(v_i_533_, 2);
            v___x_540_ = lean_apply_2(v_h__1_534_, v_lo_538_, v_hi_539_);
            return v___x_540_;
        }
        1 => {
            let mut v_lo_541_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_542_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__4_537_);
            lean_dec(v_h__3_536_);
            lean_dec(v_h__1_534_);
            v_lo_541_ = lean_ctor_get(v_i_533_, 0);
            lean_inc(v_lo_541_);
            lean_dec_ref_known(v_i_533_, 1);
            v___x_542_ = lean_apply_1(v_h__2_535_, v_lo_541_);
            return v___x_542_;
        }
        2 => {
            let mut v_hi_543_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_544_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__4_537_);
            lean_dec(v_h__2_535_);
            lean_dec(v_h__1_534_);
            v_hi_543_ = lean_ctor_get(v_i_533_, 0);
            lean_inc(v_hi_543_);
            lean_dec_ref_known(v_i_533_, 1);
            v___x_544_ = lean_apply_1(v_h__3_536_, v_hi_543_);
            return v___x_544_;
        }
        _ => {
            let mut v___x_545_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_546_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_536_);
            lean_dec(v_h__2_535_);
            lean_dec(v_h__1_534_);
            v___x_545_ = lean_box(0);
            v___x_546_ = lean_apply_1(v_h__4_537_, v___x_545_);
            return v___x_546_;
        }
    }
}
pub unsafe fn l___private_Init_Grind_ToInt_0__Lean_Grind_IntInterval_lo_x3f_match__1_splitter(
    mut v_motive_547_: *mut LeanObject,
    mut v_i_548_: *mut LeanObject,
    mut v_h__1_549_: *mut LeanObject,
    mut v_h__2_550_: *mut LeanObject,
    mut v_h__3_551_: *mut LeanObject,
    mut v_h__4_552_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_i_548_) {
        0 => {
            let mut v_lo_553_: *mut LeanObject = core::ptr::null_mut();
            let mut v_hi_554_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_555_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__4_552_);
            lean_dec(v_h__3_551_);
            lean_dec(v_h__2_550_);
            v_lo_553_ = lean_ctor_get(v_i_548_, 0);
            lean_inc(v_lo_553_);
            v_hi_554_ = lean_ctor_get(v_i_548_, 1);
            lean_inc(v_hi_554_);
            lean_dec_ref_known(v_i_548_, 2);
            v___x_555_ = lean_apply_2(v_h__1_549_, v_lo_553_, v_hi_554_);
            return v___x_555_;
        }
        1 => {
            let mut v_lo_556_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_557_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__4_552_);
            lean_dec(v_h__3_551_);
            lean_dec(v_h__1_549_);
            v_lo_556_ = lean_ctor_get(v_i_548_, 0);
            lean_inc(v_lo_556_);
            lean_dec_ref_known(v_i_548_, 1);
            v___x_557_ = lean_apply_1(v_h__2_550_, v_lo_556_);
            return v___x_557_;
        }
        2 => {
            let mut v_hi_558_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_559_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__4_552_);
            lean_dec(v_h__2_550_);
            lean_dec(v_h__1_549_);
            v_hi_558_ = lean_ctor_get(v_i_548_, 0);
            lean_inc(v_hi_558_);
            lean_dec_ref_known(v_i_548_, 1);
            v___x_559_ = lean_apply_1(v_h__3_551_, v_hi_558_);
            return v___x_559_;
        }
        _ => {
            let mut v___x_560_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_561_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_551_);
            lean_dec(v_h__2_550_);
            lean_dec(v_h__1_549_);
            v___x_560_ = lean_box(0);
            v___x_561_ = lean_apply_1(v_h__4_552_, v___x_560_);
            return v___x_561_;
        }
    }
}
pub unsafe fn l_Lean_Grind_IntInterval_isFinite(mut v_i_562_: *mut LeanObject) -> u8 {
    match lean_obj_tag(v_i_562_) {
        0 => {
            let mut v___x_563_: u8 = 0;
            v___x_563_ = 1;
            return v___x_563_;
        }
        3 => {
            let mut v___x_564_: u8 = 0;
            v___x_564_ = 0;
            return v___x_564_;
        }
        _ => {
            let mut v___x_565_: u8 = 0;
            v___x_565_ = 0;
            return v___x_565_;
        }
    }
}
pub unsafe fn l_Lean_Grind_IntInterval_isFinite___boxed(
    mut v_i_566_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_567_: u8 = 0;
    let mut v_r_568_: *mut LeanObject = core::ptr::null_mut();
    v_res_567_ = l_Lean_Grind_IntInterval_isFinite(v_i_566_);
    lean_dec(v_i_566_);
    v_r_568_ = lean_box((v_res_567_) as usize);
    return v_r_568_;
}
pub unsafe fn _init_l_Lean_Grind_IntInterval_instMembershipInt() -> *mut LeanObject {
    let mut v___x_569_: *mut LeanObject = core::ptr::null_mut();
    v___x_569_ = lean_box(0);
    return v___x_569_;
}
pub unsafe fn _init_l_Lean_Grind_IntInterval_wrap___closed__0() -> *mut LeanObject {
    let mut v___x_570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_571_: *mut LeanObject = core::ptr::null_mut();
    v___x_570_ = lean_unsigned_to_nat(1);
    v___x_571_ = lean_nat_to_int(v___x_570_);
    return v___x_571_;
}
pub unsafe fn l_Lean_Grind_IntInterval_wrap(
    mut v_i_572_: *mut LeanObject,
    mut v_x_573_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_i_572_) {
        0 => {
            let mut v_lo_574_: *mut LeanObject = core::ptr::null_mut();
            let mut v_hi_575_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_576_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_577_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_578_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_579_: *mut LeanObject = core::ptr::null_mut();
            v_lo_574_ = lean_ctor_get(v_i_572_, 0);
            v_hi_575_ = lean_ctor_get(v_i_572_, 1);
            v___x_576_ = lean_int_sub(v_x_573_, v_lo_574_);
            v___x_577_ = lean_int_sub(v_hi_575_, v_lo_574_);
            v___x_578_ = lean_int_emod(v___x_576_, v___x_577_);
            lean_dec(v___x_577_);
            lean_dec(v___x_576_);
            v___x_579_ = lean_int_add(v___x_578_, v_lo_574_);
            lean_dec(v___x_578_);
            return v___x_579_;
        }
        1 => {
            let mut v_lo_580_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_581_: u8 = 0;
            v_lo_580_ = lean_ctor_get(v_i_572_, 0);
            v___x_581_ = lean_int_dec_le(v_x_573_, v_lo_580_);
            if v___x_581_ == 0 {
                lean_inc(v_x_573_);
                return v_x_573_;
            } else {
                lean_inc(v_lo_580_);
                return v_lo_580_;
            }
        }
        2 => {
            let mut v_hi_582_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_583_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_584_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_585_: u8 = 0;
            v_hi_582_ = lean_ctor_get(v_i_572_, 0);
            v___x_583_ = lean_obj_once(
                core::ptr::addr_of_mut!(l_Lean_Grind_IntInterval_wrap___closed__0),
                core::ptr::addr_of_mut!(l_Lean_Grind_IntInterval_wrap___closed__0_once),
                _init_l_Lean_Grind_IntInterval_wrap___closed__0,
            );
            v___x_584_ = lean_int_sub(v_hi_582_, v___x_583_);
            v___x_585_ = lean_int_dec_le(v_x_573_, v___x_584_);
            if v___x_585_ == 0 {
                return v___x_584_;
            } else {
                lean_dec(v___x_584_);
                lean_inc(v_x_573_);
                return v_x_573_;
            }
        }
        _ => {
            lean_inc(v_x_573_);
            return v_x_573_;
        }
    }
}
pub unsafe fn l_Lean_Grind_IntInterval_wrap___boxed(
    mut v_i_586_: *mut LeanObject,
    mut v_x_587_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_588_: *mut LeanObject = core::ptr::null_mut();
    v_res_588_ = l_Lean_Grind_IntInterval_wrap(v_i_586_, v_x_587_);
    lean_dec(v_x_587_);
    lean_dec(v_i_586_);
    return v_res_588_;
}
pub unsafe fn l_Lean_Grind_toIntUnexpander(
    mut v_stx_602_: *mut LeanObject,
    mut v_a_603_: *mut LeanObject,
    mut v_a_604_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_606_: u8 = 0;
    v___x_605_ = l_Lean_Grind_toIntUnexpander___closed__4;
    lean_inc(v_stx_602_);
    v___x_606_ = l_Lean_Syntax_isOfKind(v_stx_602_, v___x_605_);
    if v___x_606_ == 0 {
        let mut v___x_607_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_608_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_stx_602_);
        v___x_607_ = lean_box(0);
        v___x_608_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_608_, 0, v___x_607_);
        lean_ctor_set(v___x_608_, 1, v_a_604_);
        return v___x_608_;
    } else {
        let mut v___x_609_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_610_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_611_: u8 = 0;
        v___x_609_ = lean_unsigned_to_nat(1);
        v___x_610_ = l_Lean_Syntax_getArg(v_stx_602_, v___x_609_);
        lean_dec(v_stx_602_);
        lean_inc(v___x_610_);
        v___x_611_ = l_Lean_Syntax_matchesNull(v___x_610_, v___x_609_);
        if v___x_611_ == 0 {
            let mut v___x_612_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_613_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v___x_610_);
            v___x_612_ = lean_box(0);
            v___x_613_ = lean_alloc_ctor(1, 2, (0) as u32);
            lean_ctor_set(v___x_613_, 0, v___x_612_);
            lean_ctor_set(v___x_613_, 1, v_a_604_);
            return v___x_613_;
        } else {
            let mut v___x_614_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_615_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_616_: u8 = 0;
            let mut v___x_617_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_618_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_619_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_620_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_621_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_622_: *mut LeanObject = core::ptr::null_mut();
            v___x_614_ = lean_unsigned_to_nat(0);
            v___x_615_ = l_Lean_Syntax_getArg(v___x_610_, v___x_614_);
            lean_dec(v___x_610_);
            v___x_616_ = 0;
            v___x_617_ = l_Lean_SourceInfo_fromRef(v_a_603_, v___x_616_);
            v___x_618_ = l_Lean_Grind_toIntUnexpander___closed__6;
            v___x_619_ = l_Lean_Grind_toIntUnexpander___closed__7;
            lean_inc(v___x_617_);
            v___x_620_ = lean_alloc_ctor(2, 2, (0) as u32);
            lean_ctor_set(v___x_620_, 0, v___x_617_);
            lean_ctor_set(v___x_620_, 1, v___x_619_);
            v___x_621_ = l_Lean_Syntax_node2(v___x_617_, v___x_618_, v___x_620_, v___x_615_);
            v___x_622_ = lean_alloc_ctor(0, 2, (0) as u32);
            lean_ctor_set(v___x_622_, 0, v___x_621_);
            lean_ctor_set(v___x_622_, 1, v_a_604_);
            return v___x_622_;
        }
    }
}
pub unsafe fn l_Lean_Grind_toIntUnexpander___boxed(
    mut v_stx_623_: *mut LeanObject,
    mut v_a_624_: *mut LeanObject,
    mut v_a_625_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_626_: *mut LeanObject = core::ptr::null_mut();
    v_res_626_ = l_Lean_Grind_toIntUnexpander(v_stx_623_, v_a_624_, v_a_625_);
    lean_dec(v_a_624_);
    return v_res_626_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Grind_ToInt(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_LawfulBEqTactics(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Int_DivMod_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_ByCases(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Int_DivMod_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_Grind_instInhabitedIntInterval_default =
        _init_l_Lean_Grind_instInhabitedIntInterval_default();
    lean_mark_persistent(l_Lean_Grind_instInhabitedIntInterval_default);
    l_Lean_Grind_instInhabitedIntInterval = _init_l_Lean_Grind_instInhabitedIntInterval();
    lean_mark_persistent(l_Lean_Grind_instInhabitedIntInterval);
    l_Lean_Grind_IntInterval_instMembershipInt = _init_l_Lean_Grind_IntInterval_instMembershipInt();
    lean_mark_persistent(l_Lean_Grind_IntInterval_instMembershipInt);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Grind_ToInt(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    res = runtime_initialize_Init_Grind_Tactics(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Grind_ToInt(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_LawfulBEqTactics(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Int_DivMod_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Grind_Tactics(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_ByCases(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Int_DivMod_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_ToInt(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Grind_ToInt(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Grind_ToInt(builtin);
}
