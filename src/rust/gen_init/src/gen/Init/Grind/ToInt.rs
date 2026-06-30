// Lean compiler output
// Module: Init.Grind.ToInt
// Imports: Init.LawfulBEqTactics Init.Data.Int.DivMod.Basic Init.Grind.Tactics Init.ByCases Init.Data.Int.DivMod.Lemmas Init.Omega
use crate::ffi::{
    lean_int_add, lean_int_dec_eq, lean_int_dec_le, lean_int_dec_lt, lean_int_emod, lean_int_neg,
    lean_int_sub, lean_nat_sub, lean_nat_to_int,
};
use crate::r#gen::Init::ByCases::{initialize_Init_ByCases, runtime_initialize_Init_ByCases};
use crate::r#gen::Init::Data::Int::Basic::l_Int_pow;
use crate::r#gen::Init::Data::Int::DivMod::Basic::{
    initialize_Init_Data_Int_DivMod_Basic, runtime_initialize_Init_Data_Int_DivMod_Basic,
};
use crate::r#gen::Init::Data::Int::DivMod::Lemmas::{
    initialize_Init_Data_Int_DivMod_Lemmas, runtime_initialize_Init_Data_Int_DivMod_Lemmas,
};
use crate::r#gen::Init::Grind::Tactics::{
    initialize_Init_Grind_Tactics, runtime_initialize_Init_Grind_Tactics,
};
use crate::r#gen::Init::LawfulBEqTactics::{
    initialize_Init_LawfulBEqTactics, runtime_initialize_Init_LawfulBEqTactics,
};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::Prelude::{
    l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg, l_Lean_Syntax_isOfKind,
    l_Lean_Syntax_matchesNull, l_Lean_Syntax_node2,
};
pub static l_Lean_Grind_instBEqIntInterval___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Grind_instBEqIntInterval_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_instBEqIntInterval___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instBEqIntInterval___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Grind_instBEqIntInterval: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instBEqIntInterval___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Grind_instInhabitedIntInterval_default___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_instInhabitedIntInterval_default___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_instInhabitedIntInterval_default___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_instInhabitedIntInterval_default___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Grind_instInhabitedIntInterval_default: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Grind_instInhabitedIntInterval: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Grind_IntInterval_uint___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Grind_IntInterval_uint___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Grind_IntInterval_instMembershipInt: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Grind_IntInterval_wrap___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Grind_IntInterval_wrap___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Grind_toIntUnexpander___closed__0_value: leanh::LeanStringObject<5> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Grind_toIntUnexpander___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_toIntUnexpander___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Grind_toIntUnexpander___closed__1_value: leanh::LeanStringObject<7> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Grind_toIntUnexpander___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_toIntUnexpander___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Grind_toIntUnexpander___closed__2_value: leanh::LeanStringObject<5> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Grind_toIntUnexpander___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_toIntUnexpander___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Grind_toIntUnexpander___closed__3_value: leanh::LeanStringObject<4> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Grind_toIntUnexpander___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_toIntUnexpander___closed__3_value)
        as *mut leanh::LeanObject;
static l_Lean_Grind_toIntUnexpander___closed__4_value_aux_0: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Grind_toIntUnexpander___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Grind_toIntUnexpander___closed__4_value_aux_1: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Grind_toIntUnexpander___closed__4_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Grind_toIntUnexpander___closed__1_value)
                as *mut leanh::LeanObject,
            8018486133748762727 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Grind_toIntUnexpander___closed__4_value_aux_2: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Grind_toIntUnexpander___closed__4_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Grind_toIntUnexpander___closed__2_value)
                as *mut leanh::LeanObject,
            16572064140653406795 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Grind_toIntUnexpander___closed__4_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Grind_toIntUnexpander___closed__4_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Grind_toIntUnexpander___closed__3_value)
                as *mut leanh::LeanObject,
            12966880221525079621 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Grind_toIntUnexpander___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_toIntUnexpander___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Grind_toIntUnexpander___closed__5_value: leanh::LeanStringObject<12> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Grind_toIntUnexpander___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_toIntUnexpander___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Grind_toIntUnexpander___closed__6_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Grind_toIntUnexpander___closed__5_value)
                as *mut leanh::LeanObject,
            4193428478068483112 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Grind_toIntUnexpander___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_toIntUnexpander___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Grind_toIntUnexpander___closed__7_value: leanh::LeanStringObject<4> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Grind_toIntUnexpander___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_toIntUnexpander___closed__7_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Lean_Grind_IntInterval_ctorIdx(
    mut v_x_314_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_314_) {
        0 => {
            let mut v___x_315_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_315_ = leanh::lean_unsigned_to_nat(0);
            return v___x_315_;
        }
        1 => {
            let mut v___x_316_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_316_ = leanh::lean_unsigned_to_nat(1);
            return v___x_316_;
        }
        2 => {
            let mut v___x_317_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_317_ = leanh::lean_unsigned_to_nat(2);
            return v___x_317_;
        }
        _ => {
            let mut v___x_318_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_318_ = leanh::lean_unsigned_to_nat(3);
            return v___x_318_;
        }
    }
}
pub unsafe fn l_Lean_Grind_IntInterval_ctorIdx___boxed(
    mut v_x_319_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_320_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_320_ = l_Lean_Grind_IntInterval_ctorIdx(v_x_319_);
    leanh::lean_dec(v_x_319_);
    return v_res_320_;
}
pub unsafe fn l_Lean_Grind_IntInterval_ctorElim___redArg(
    mut v_t_321_: *mut leanh::LeanObject,
    mut v_k_322_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_t_321_) {
        0 => {
            let mut v_lo_323_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_hi_324_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_325_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_lo_323_ = leanh::lean_ctor_get(v_t_321_, 0);
            leanh::lean_inc(v_lo_323_);
            v_hi_324_ = leanh::lean_ctor_get(v_t_321_, 1);
            leanh::lean_inc(v_hi_324_);
            leanh::lean_dec_ref_known(v_t_321_, 2);
            v___x_325_ = leanh::lean_apply_2(v_k_322_, v_lo_323_, v_hi_324_);
            return v___x_325_;
        }
        3 => {
            return v_k_322_;
        }
        _ => {
            let mut v_lo_326_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_327_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_lo_326_ = leanh::lean_ctor_get(v_t_321_, 0);
            leanh::lean_inc(v_lo_326_);
            leanh::lean_dec(v_t_321_);
            v___x_327_ = leanh::lean_apply_1(v_k_322_, v_lo_326_);
            return v___x_327_;
        }
    }
}
pub unsafe fn l_Lean_Grind_IntInterval_ctorElim(
    mut v_motive_328_: *mut leanh::LeanObject,
    mut v_ctorIdx_329_: *mut leanh::LeanObject,
    mut v_t_330_: *mut leanh::LeanObject,
    mut v_h_331_: *mut leanh::LeanObject,
    mut v_k_332_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_333_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_333_ = l_Lean_Grind_IntInterval_ctorElim___redArg(v_t_330_, v_k_332_);
    return v___x_333_;
}
pub unsafe fn l_Lean_Grind_IntInterval_ctorElim___boxed(
    mut v_motive_334_: *mut leanh::LeanObject,
    mut v_ctorIdx_335_: *mut leanh::LeanObject,
    mut v_t_336_: *mut leanh::LeanObject,
    mut v_h_337_: *mut leanh::LeanObject,
    mut v_k_338_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_339_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_339_ = l_Lean_Grind_IntInterval_ctorElim(
        v_motive_334_,
        v_ctorIdx_335_,
        v_t_336_,
        v_h_337_,
        v_k_338_,
    );
    leanh::lean_dec(v_ctorIdx_335_);
    return v_res_339_;
}
pub unsafe fn l_Lean_Grind_IntInterval_co_elim___redArg(
    mut v_t_340_: *mut leanh::LeanObject,
    mut v_co_341_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_342_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_342_ = l_Lean_Grind_IntInterval_ctorElim___redArg(v_t_340_, v_co_341_);
    return v___x_342_;
}
pub unsafe fn l_Lean_Grind_IntInterval_co_elim(
    mut v_motive_343_: *mut leanh::LeanObject,
    mut v_t_344_: *mut leanh::LeanObject,
    mut v_h_345_: *mut leanh::LeanObject,
    mut v_co_346_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_347_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_347_ = l_Lean_Grind_IntInterval_ctorElim___redArg(v_t_344_, v_co_346_);
    return v___x_347_;
}
pub unsafe fn l_Lean_Grind_IntInterval_ci_elim___redArg(
    mut v_t_348_: *mut leanh::LeanObject,
    mut v_ci_349_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_350_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_350_ = l_Lean_Grind_IntInterval_ctorElim___redArg(v_t_348_, v_ci_349_);
    return v___x_350_;
}
pub unsafe fn l_Lean_Grind_IntInterval_ci_elim(
    mut v_motive_351_: *mut leanh::LeanObject,
    mut v_t_352_: *mut leanh::LeanObject,
    mut v_h_353_: *mut leanh::LeanObject,
    mut v_ci_354_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_355_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_355_ = l_Lean_Grind_IntInterval_ctorElim___redArg(v_t_352_, v_ci_354_);
    return v___x_355_;
}
pub unsafe fn l_Lean_Grind_IntInterval_io_elim___redArg(
    mut v_t_356_: *mut leanh::LeanObject,
    mut v_io_357_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_358_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_358_ = l_Lean_Grind_IntInterval_ctorElim___redArg(v_t_356_, v_io_357_);
    return v___x_358_;
}
pub unsafe fn l_Lean_Grind_IntInterval_io_elim(
    mut v_motive_359_: *mut leanh::LeanObject,
    mut v_t_360_: *mut leanh::LeanObject,
    mut v_h_361_: *mut leanh::LeanObject,
    mut v_io_362_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_363_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_363_ = l_Lean_Grind_IntInterval_ctorElim___redArg(v_t_360_, v_io_362_);
    return v___x_363_;
}
pub unsafe fn l_Lean_Grind_IntInterval_ii_elim___redArg(
    mut v_t_364_: *mut leanh::LeanObject,
    mut v_ii_365_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_366_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_366_ = l_Lean_Grind_IntInterval_ctorElim___redArg(v_t_364_, v_ii_365_);
    return v___x_366_;
}
pub unsafe fn l_Lean_Grind_IntInterval_ii_elim(
    mut v_motive_367_: *mut leanh::LeanObject,
    mut v_t_368_: *mut leanh::LeanObject,
    mut v_h_369_: *mut leanh::LeanObject,
    mut v_ii_370_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_371_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_371_ = l_Lean_Grind_IntInterval_ctorElim___redArg(v_t_368_, v_ii_370_);
    return v___x_371_;
}
pub unsafe fn l_Lean_Grind_instBEqIntInterval_beq(
    mut v_x_372_: *mut leanh::LeanObject,
    mut v_x_373_: *mut leanh::LeanObject,
) -> u8 {
    match leanh::lean_obj_tag(v_x_372_) {
        0 => {
            if leanh::lean_obj_tag(v_x_373_) == 0 {
                let mut v_lo_374_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_hi_375_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_lo_376_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_hi_377_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_378_: u8 = 0;
                v_lo_374_ = leanh::lean_ctor_get(v_x_372_, 0);
                v_hi_375_ = leanh::lean_ctor_get(v_x_372_, 1);
                v_lo_376_ = leanh::lean_ctor_get(v_x_373_, 0);
                v_hi_377_ = leanh::lean_ctor_get(v_x_373_, 1);
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
            if leanh::lean_obj_tag(v_x_373_) == 1 {
                let mut v_lo_381_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_lo_382_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_383_: u8 = 0;
                v_lo_381_ = leanh::lean_ctor_get(v_x_372_, 0);
                v_lo_382_ = leanh::lean_ctor_get(v_x_373_, 0);
                v___x_383_ = lean_int_dec_eq(v_lo_381_, v_lo_382_);
                return v___x_383_;
            } else {
                let mut v___x_384_: u8 = 0;
                v___x_384_ = 0;
                return v___x_384_;
            }
        }
        2 => {
            if leanh::lean_obj_tag(v_x_373_) == 2 {
                let mut v_hi_385_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_hi_386_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_387_: u8 = 0;
                v_hi_385_ = leanh::lean_ctor_get(v_x_372_, 0);
                v_hi_386_ = leanh::lean_ctor_get(v_x_373_, 0);
                v___x_387_ = lean_int_dec_eq(v_hi_385_, v_hi_386_);
                return v___x_387_;
            } else {
                let mut v___x_388_: u8 = 0;
                v___x_388_ = 0;
                return v___x_388_;
            }
        }
        _ => {
            if leanh::lean_obj_tag(v_x_373_) == 3 {
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
    mut v_x_391_: *mut leanh::LeanObject,
    mut v_x_392_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_393_: u8 = 0;
    let mut v_r_394_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_393_ = l_Lean_Grind_instBEqIntInterval_beq(v_x_391_, v_x_392_);
    leanh::lean_dec(v_x_392_);
    leanh::lean_dec(v_x_391_);
    v_r_394_ = leanh::lean_box((v_res_393_) as usize);
    return v_r_394_;
}
pub unsafe fn l___private_Init_Grind_ToInt_0__Lean_Grind_instBEqIntInterval_beq_match__1_splitter___redArg(
    mut v_x_397_: *mut leanh::LeanObject,
    mut v_x_398_: *mut leanh::LeanObject,
    mut v_h__1_399_: *mut leanh::LeanObject,
    mut v_h__2_400_: *mut leanh::LeanObject,
    mut v_h__3_401_: *mut leanh::LeanObject,
    mut v_h__4_402_: *mut leanh::LeanObject,
    mut v_h__5_403_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_397_) {
        0 => {
            leanh::lean_dec(v_h__4_402_);
            leanh::lean_dec(v_h__3_401_);
            leanh::lean_dec(v_h__2_400_);
            if leanh::lean_obj_tag(v_x_398_) == 0 {
                let mut v_lo_404_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_hi_405_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_lo_406_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_hi_407_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_408_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v_h__5_403_);
                v_lo_404_ = leanh::lean_ctor_get(v_x_397_, 0);
                leanh::lean_inc(v_lo_404_);
                v_hi_405_ = leanh::lean_ctor_get(v_x_397_, 1);
                leanh::lean_inc(v_hi_405_);
                leanh::lean_dec_ref_known(v_x_397_, 2);
                v_lo_406_ = leanh::lean_ctor_get(v_x_398_, 0);
                leanh::lean_inc(v_lo_406_);
                v_hi_407_ = leanh::lean_ctor_get(v_x_398_, 1);
                leanh::lean_inc(v_hi_407_);
                leanh::lean_dec_ref_known(v_x_398_, 2);
                v___x_408_ = leanh::lean_apply_4(
                    v_h__1_399_,
                    v_lo_404_,
                    v_hi_405_,
                    v_lo_406_,
                    v_hi_407_,
                );
                return v___x_408_;
            } else {
                let mut v___x_409_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v_h__1_399_);
                v___x_409_ = leanh::lean_apply_6(
                    v_h__5_403_,
                    v_x_397_,
                    v_x_398_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                );
                return v___x_409_;
            }
        }
        1 => {
            leanh::lean_dec(v_h__4_402_);
            leanh::lean_dec(v_h__3_401_);
            leanh::lean_dec(v_h__1_399_);
            if leanh::lean_obj_tag(v_x_398_) == 1 {
                let mut v_lo_410_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_lo_411_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_412_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v_h__5_403_);
                v_lo_410_ = leanh::lean_ctor_get(v_x_397_, 0);
                leanh::lean_inc(v_lo_410_);
                leanh::lean_dec_ref_known(v_x_397_, 1);
                v_lo_411_ = leanh::lean_ctor_get(v_x_398_, 0);
                leanh::lean_inc(v_lo_411_);
                leanh::lean_dec_ref_known(v_x_398_, 1);
                v___x_412_ = leanh::lean_apply_2(v_h__2_400_, v_lo_410_, v_lo_411_);
                return v___x_412_;
            } else {
                let mut v___x_413_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v_h__2_400_);
                v___x_413_ = leanh::lean_apply_6(
                    v_h__5_403_,
                    v_x_397_,
                    v_x_398_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                );
                return v___x_413_;
            }
        }
        2 => {
            leanh::lean_dec(v_h__4_402_);
            leanh::lean_dec(v_h__2_400_);
            leanh::lean_dec(v_h__1_399_);
            if leanh::lean_obj_tag(v_x_398_) == 2 {
                let mut v_hi_414_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_hi_415_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_416_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v_h__5_403_);
                v_hi_414_ = leanh::lean_ctor_get(v_x_397_, 0);
                leanh::lean_inc(v_hi_414_);
                leanh::lean_dec_ref_known(v_x_397_, 1);
                v_hi_415_ = leanh::lean_ctor_get(v_x_398_, 0);
                leanh::lean_inc(v_hi_415_);
                leanh::lean_dec_ref_known(v_x_398_, 1);
                v___x_416_ = leanh::lean_apply_2(v_h__3_401_, v_hi_414_, v_hi_415_);
                return v___x_416_;
            } else {
                let mut v___x_417_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v_h__3_401_);
                v___x_417_ = leanh::lean_apply_6(
                    v_h__5_403_,
                    v_x_397_,
                    v_x_398_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                );
                return v___x_417_;
            }
        }
        _ => {
            leanh::lean_dec(v_h__3_401_);
            leanh::lean_dec(v_h__2_400_);
            leanh::lean_dec(v_h__1_399_);
            if leanh::lean_obj_tag(v_x_398_) == 3 {
                let mut v___x_418_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_419_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v_h__5_403_);
                v___x_418_ = leanh::lean_box(0);
                v___x_419_ = leanh::lean_apply_1(v_h__4_402_, v___x_418_);
                return v___x_419_;
            } else {
                let mut v___x_420_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v_h__4_402_);
                v___x_420_ = leanh::lean_apply_6(
                    v_h__5_403_,
                    v_x_397_,
                    v_x_398_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                );
                return v___x_420_;
            }
        }
    }
}
pub unsafe fn l___private_Init_Grind_ToInt_0__Lean_Grind_instBEqIntInterval_beq_match__1_splitter(
    mut v_motive_421_: *mut leanh::LeanObject,
    mut v_x_422_: *mut leanh::LeanObject,
    mut v_x_423_: *mut leanh::LeanObject,
    mut v_h__1_424_: *mut leanh::LeanObject,
    mut v_h__2_425_: *mut leanh::LeanObject,
    mut v_h__3_426_: *mut leanh::LeanObject,
    mut v_h__4_427_: *mut leanh::LeanObject,
    mut v_h__5_428_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_422_) {
        0 => {
            leanh::lean_dec(v_h__4_427_);
            leanh::lean_dec(v_h__3_426_);
            leanh::lean_dec(v_h__2_425_);
            if leanh::lean_obj_tag(v_x_423_) == 0 {
                let mut v_lo_429_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_hi_430_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_lo_431_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_hi_432_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_433_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v_h__5_428_);
                v_lo_429_ = leanh::lean_ctor_get(v_x_422_, 0);
                leanh::lean_inc(v_lo_429_);
                v_hi_430_ = leanh::lean_ctor_get(v_x_422_, 1);
                leanh::lean_inc(v_hi_430_);
                leanh::lean_dec_ref_known(v_x_422_, 2);
                v_lo_431_ = leanh::lean_ctor_get(v_x_423_, 0);
                leanh::lean_inc(v_lo_431_);
                v_hi_432_ = leanh::lean_ctor_get(v_x_423_, 1);
                leanh::lean_inc(v_hi_432_);
                leanh::lean_dec_ref_known(v_x_423_, 2);
                v___x_433_ = leanh::lean_apply_4(
                    v_h__1_424_,
                    v_lo_429_,
                    v_hi_430_,
                    v_lo_431_,
                    v_hi_432_,
                );
                return v___x_433_;
            } else {
                let mut v___x_434_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v_h__1_424_);
                v___x_434_ = leanh::lean_apply_6(
                    v_h__5_428_,
                    v_x_422_,
                    v_x_423_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                );
                return v___x_434_;
            }
        }
        1 => {
            leanh::lean_dec(v_h__4_427_);
            leanh::lean_dec(v_h__3_426_);
            leanh::lean_dec(v_h__1_424_);
            if leanh::lean_obj_tag(v_x_423_) == 1 {
                let mut v_lo_435_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_lo_436_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_437_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v_h__5_428_);
                v_lo_435_ = leanh::lean_ctor_get(v_x_422_, 0);
                leanh::lean_inc(v_lo_435_);
                leanh::lean_dec_ref_known(v_x_422_, 1);
                v_lo_436_ = leanh::lean_ctor_get(v_x_423_, 0);
                leanh::lean_inc(v_lo_436_);
                leanh::lean_dec_ref_known(v_x_423_, 1);
                v___x_437_ = leanh::lean_apply_2(v_h__2_425_, v_lo_435_, v_lo_436_);
                return v___x_437_;
            } else {
                let mut v___x_438_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v_h__2_425_);
                v___x_438_ = leanh::lean_apply_6(
                    v_h__5_428_,
                    v_x_422_,
                    v_x_423_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                );
                return v___x_438_;
            }
        }
        2 => {
            leanh::lean_dec(v_h__4_427_);
            leanh::lean_dec(v_h__2_425_);
            leanh::lean_dec(v_h__1_424_);
            if leanh::lean_obj_tag(v_x_423_) == 2 {
                let mut v_hi_439_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_hi_440_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_441_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v_h__5_428_);
                v_hi_439_ = leanh::lean_ctor_get(v_x_422_, 0);
                leanh::lean_inc(v_hi_439_);
                leanh::lean_dec_ref_known(v_x_422_, 1);
                v_hi_440_ = leanh::lean_ctor_get(v_x_423_, 0);
                leanh::lean_inc(v_hi_440_);
                leanh::lean_dec_ref_known(v_x_423_, 1);
                v___x_441_ = leanh::lean_apply_2(v_h__3_426_, v_hi_439_, v_hi_440_);
                return v___x_441_;
            } else {
                let mut v___x_442_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v_h__3_426_);
                v___x_442_ = leanh::lean_apply_6(
                    v_h__5_428_,
                    v_x_422_,
                    v_x_423_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                );
                return v___x_442_;
            }
        }
        _ => {
            leanh::lean_dec(v_h__3_426_);
            leanh::lean_dec(v_h__2_425_);
            leanh::lean_dec(v_h__1_424_);
            if leanh::lean_obj_tag(v_x_423_) == 3 {
                let mut v___x_443_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_444_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v_h__5_428_);
                v___x_443_ = leanh::lean_box(0);
                v___x_444_ = leanh::lean_apply_1(v_h__4_427_, v___x_443_);
                return v___x_444_;
            } else {
                let mut v___x_445_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v_h__4_427_);
                v___x_445_ = leanh::lean_apply_6(
                    v_h__5_428_,
                    v_x_422_,
                    v_x_423_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                );
                return v___x_445_;
            }
        }
    }
}
pub unsafe fn l_Lean_Grind_instDecidableEqIntInterval_decEq(
    mut v_x_446_: *mut leanh::LeanObject,
    mut v_x_447_: *mut leanh::LeanObject,
) -> u8 {
    match leanh::lean_obj_tag(v_x_446_) {
        0 => {
            let mut v_lo_448_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_hi_449_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_450_: u8 = 0;
            v_lo_448_ = leanh::lean_ctor_get(v_x_446_, 0);
            v_hi_449_ = leanh::lean_ctor_get(v_x_446_, 1);
            v___x_450_ = 0;
            match leanh::lean_obj_tag(v_x_447_) {
                0 => {
                    let mut v_lo_451_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v_hi_452_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_453_: u8 = 0;
                    v_lo_451_ = leanh::lean_ctor_get(v_x_447_, 0);
                    v_hi_452_ = leanh::lean_ctor_get(v_x_447_, 1);
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
            let mut v_lo_455_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_456_: u8 = 0;
            v_lo_455_ = leanh::lean_ctor_get(v_x_446_, 0);
            v___x_456_ = 0;
            match leanh::lean_obj_tag(v_x_447_) {
                1 => {
                    let mut v_lo_457_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_458_: u8 = 0;
                    v_lo_457_ = leanh::lean_ctor_get(v_x_447_, 0);
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
            let mut v_hi_459_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_460_: u8 = 0;
            v_hi_459_ = leanh::lean_ctor_get(v_x_446_, 0);
            v___x_460_ = 0;
            match leanh::lean_obj_tag(v_x_447_) {
                2 => {
                    let mut v_hi_461_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_462_: u8 = 0;
                    v_hi_461_ = leanh::lean_ctor_get(v_x_447_, 0);
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
            if leanh::lean_obj_tag(v_x_447_) == 3 {
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
    mut v_x_465_: *mut leanh::LeanObject,
    mut v_x_466_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_467_: u8 = 0;
    let mut v_r_468_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_467_ = l_Lean_Grind_instDecidableEqIntInterval_decEq(v_x_465_, v_x_466_);
    leanh::lean_dec(v_x_466_);
    leanh::lean_dec(v_x_465_);
    v_r_468_ = leanh::lean_box((v_res_467_) as usize);
    return v_r_468_;
}
pub unsafe fn l_Lean_Grind_instDecidableEqIntInterval(
    mut v_x_469_: *mut leanh::LeanObject,
    mut v_x_470_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_471_: u8 = 0;
    v___x_471_ = l_Lean_Grind_instDecidableEqIntInterval_decEq(v_x_469_, v_x_470_);
    return v___x_471_;
}
pub unsafe fn l_Lean_Grind_instDecidableEqIntInterval___boxed(
    mut v_x_472_: *mut leanh::LeanObject,
    mut v_x_473_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_474_: u8 = 0;
    let mut v_r_475_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_474_ = l_Lean_Grind_instDecidableEqIntInterval(v_x_472_, v_x_473_);
    leanh::lean_dec(v_x_473_);
    leanh::lean_dec(v_x_472_);
    v_r_475_ = leanh::lean_box((v_res_474_) as usize);
    return v_r_475_;
}
pub unsafe fn _init_l_Lean_Grind_instInhabitedIntInterval_default___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_477_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_476_ = leanh::lean_unsigned_to_nat(0);
    v___x_477_ = lean_nat_to_int(v___x_476_);
    return v___x_477_;
}
pub unsafe fn _init_l_Lean_Grind_instInhabitedIntInterval_default___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_479_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_478_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_instInhabitedIntInterval_default___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Grind_instInhabitedIntInterval_default___closed__0_once),
        _init_l_Lean_Grind_instInhabitedIntInterval_default___closed__0,
    );
    v___x_479_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_479_, 0, v___x_478_);
    leanh::lean_ctor_set(v___x_479_, 1, v___x_478_);
    return v___x_479_;
}
pub unsafe fn _init_l_Lean_Grind_instInhabitedIntInterval_default() -> *mut leanh::LeanObject
{
    let mut v___x_480_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_480_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_instInhabitedIntInterval_default___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Grind_instInhabitedIntInterval_default___closed__1_once),
        _init_l_Lean_Grind_instInhabitedIntInterval_default___closed__1,
    );
    return v___x_480_;
}
pub unsafe fn _init_l_Lean_Grind_instInhabitedIntInterval() -> *mut leanh::LeanObject {
    let mut v___x_481_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_481_ = l_Lean_Grind_instInhabitedIntInterval_default;
    return v___x_481_;
}
pub unsafe fn _init_l_Lean_Grind_IntInterval_uint___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_483_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_482_ = leanh::lean_unsigned_to_nat(2);
    v___x_483_ = lean_nat_to_int(v___x_482_);
    return v___x_483_;
}
pub unsafe fn l_Lean_Grind_IntInterval_uint(
    mut v_n_484_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_488_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_485_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_instInhabitedIntInterval_default___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Grind_instInhabitedIntInterval_default___closed__0_once),
        _init_l_Lean_Grind_instInhabitedIntInterval_default___closed__0,
    );
    v___x_486_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_IntInterval_uint___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Grind_IntInterval_uint___closed__0_once),
        _init_l_Lean_Grind_IntInterval_uint___closed__0,
    );
    v___x_487_ = l_Int_pow(v___x_486_, v_n_484_);
    v___x_488_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_488_, 0, v___x_485_);
    leanh::lean_ctor_set(v___x_488_, 1, v___x_487_);
    return v___x_488_;
}
pub unsafe fn l_Lean_Grind_IntInterval_uint___boxed(
    mut v_n_489_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_490_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_490_ = l_Lean_Grind_IntInterval_uint(v_n_489_);
    leanh::lean_dec(v_n_489_);
    return v_res_490_;
}
pub unsafe fn l_Lean_Grind_IntInterval_sint(
    mut v_n_491_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_497_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_492_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_IntInterval_uint___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Grind_IntInterval_uint___closed__0_once),
        _init_l_Lean_Grind_IntInterval_uint___closed__0,
    );
    v___x_493_ = leanh::lean_unsigned_to_nat(1);
    v___x_494_ = lean_nat_sub(v_n_491_, v___x_493_);
    v___x_495_ = l_Int_pow(v___x_492_, v___x_494_);
    leanh::lean_dec(v___x_494_);
    v___x_496_ = lean_int_neg(v___x_495_);
    v___x_497_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_497_, 0, v___x_496_);
    leanh::lean_ctor_set(v___x_497_, 1, v___x_495_);
    return v___x_497_;
}
pub unsafe fn l_Lean_Grind_IntInterval_sint___boxed(
    mut v_n_498_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_499_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_499_ = l_Lean_Grind_IntInterval_sint(v_n_498_);
    leanh::lean_dec(v_n_498_);
    return v_res_499_;
}
pub unsafe fn l_Lean_Grind_IntInterval_lo_x3f(
    mut v_i_500_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lo_501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lo_503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_506_: u8 = 0;
    let mut v___x_508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_510_: u8 = 0;
    let mut v___x_511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_i_500_) {
                0 => {
                    v_lo_501_ = leanh::lean_ctor_get(v_i_500_, 0);
                    leanh::lean_inc(v_lo_501_);
                    leanh::lean_dec_ref_known(v_i_500_, 2);
                    v___x_502_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_502_, 0, v_lo_501_);
                    return v___x_502_;
                }
                1 => {
                    v_lo_503_ = leanh::lean_ctor_get(v_i_500_, 0);
                    v_isSharedCheck_510_ = (!leanh::lean_is_exclusive(v_i_500_)) as u8;
                    if v_isSharedCheck_510_ == 0 {
                        v___x_505_ = v_i_500_;
                        v_isShared_506_ = v_isSharedCheck_510_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_lo_503_);
                        leanh::lean_dec(v_i_500_);
                        v___x_505_ = leanh::lean_box(0);
                        v_isShared_506_ = v_isSharedCheck_510_;
                        state = 1;
                        continue;
                    }
                }
                _ => {
                    leanh::lean_dec(v_i_500_);
                    v___x_511_ = leanh::lean_box(0);
                    return v___x_511_;
                }
            },
            1 => {
                if v_isShared_506_ == 0 {
                    v___x_508_ = v___x_505_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_509_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_509_, 0, v_lo_503_);
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
pub unsafe fn l_Lean_Grind_IntInterval_hi_x3f(
    mut v_i_512_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_hi_513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hi_515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_518_: u8 = 0;
    let mut v___x_520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_522_: u8 = 0;
    let mut v___x_523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_i_512_) {
                0 => {
                    v_hi_513_ = leanh::lean_ctor_get(v_i_512_, 1);
                    leanh::lean_inc(v_hi_513_);
                    leanh::lean_dec_ref_known(v_i_512_, 2);
                    v___x_514_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_514_, 0, v_hi_513_);
                    return v___x_514_;
                }
                2 => {
                    v_hi_515_ = leanh::lean_ctor_get(v_i_512_, 0);
                    v_isSharedCheck_522_ = (!leanh::lean_is_exclusive(v_i_512_)) as u8;
                    if v_isSharedCheck_522_ == 0 {
                        v___x_517_ = v_i_512_;
                        v_isShared_518_ = v_isSharedCheck_522_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_hi_515_);
                        leanh::lean_dec(v_i_512_);
                        v___x_517_ = leanh::lean_box(0);
                        v_isShared_518_ = v_isSharedCheck_522_;
                        state = 1;
                        continue;
                    }
                }
                _ => {
                    leanh::lean_dec(v_i_512_);
                    v___x_523_ = leanh::lean_box(0);
                    return v___x_523_;
                }
            },
            1 => {
                if v_isShared_518_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_517_, 1);
                    v___x_520_ = v___x_517_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_521_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_521_, 0, v_hi_515_);
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
pub unsafe fn l_Lean_Grind_IntInterval_nonEmpty(mut v_i_524_: *mut leanh::LeanObject) -> u8 {
    match leanh::lean_obj_tag(v_i_524_) {
        0 => {
            let mut v_lo_525_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_hi_526_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_527_: u8 = 0;
            v_lo_525_ = leanh::lean_ctor_get(v_i_524_, 0);
            v_hi_526_ = leanh::lean_ctor_get(v_i_524_, 1);
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
    mut v_i_530_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_531_: u8 = 0;
    let mut v_r_532_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_531_ = l_Lean_Grind_IntInterval_nonEmpty(v_i_530_);
    leanh::lean_dec(v_i_530_);
    v_r_532_ = leanh::lean_box((v_res_531_) as usize);
    return v_r_532_;
}
pub unsafe fn l___private_Init_Grind_ToInt_0__Lean_Grind_IntInterval_lo_x3f_match__1_splitter___redArg(
    mut v_i_533_: *mut leanh::LeanObject,
    mut v_h__1_534_: *mut leanh::LeanObject,
    mut v_h__2_535_: *mut leanh::LeanObject,
    mut v_h__3_536_: *mut leanh::LeanObject,
    mut v_h__4_537_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_i_533_) {
        0 => {
            let mut v_lo_538_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_hi_539_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_540_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__4_537_);
            leanh::lean_dec(v_h__3_536_);
            leanh::lean_dec(v_h__2_535_);
            v_lo_538_ = leanh::lean_ctor_get(v_i_533_, 0);
            leanh::lean_inc(v_lo_538_);
            v_hi_539_ = leanh::lean_ctor_get(v_i_533_, 1);
            leanh::lean_inc(v_hi_539_);
            leanh::lean_dec_ref_known(v_i_533_, 2);
            v___x_540_ = leanh::lean_apply_2(v_h__1_534_, v_lo_538_, v_hi_539_);
            return v___x_540_;
        }
        1 => {
            let mut v_lo_541_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_542_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__4_537_);
            leanh::lean_dec(v_h__3_536_);
            leanh::lean_dec(v_h__1_534_);
            v_lo_541_ = leanh::lean_ctor_get(v_i_533_, 0);
            leanh::lean_inc(v_lo_541_);
            leanh::lean_dec_ref_known(v_i_533_, 1);
            v___x_542_ = leanh::lean_apply_1(v_h__2_535_, v_lo_541_);
            return v___x_542_;
        }
        2 => {
            let mut v_hi_543_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_544_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__4_537_);
            leanh::lean_dec(v_h__2_535_);
            leanh::lean_dec(v_h__1_534_);
            v_hi_543_ = leanh::lean_ctor_get(v_i_533_, 0);
            leanh::lean_inc(v_hi_543_);
            leanh::lean_dec_ref_known(v_i_533_, 1);
            v___x_544_ = leanh::lean_apply_1(v_h__3_536_, v_hi_543_);
            return v___x_544_;
        }
        _ => {
            let mut v___x_545_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_546_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_536_);
            leanh::lean_dec(v_h__2_535_);
            leanh::lean_dec(v_h__1_534_);
            v___x_545_ = leanh::lean_box(0);
            v___x_546_ = leanh::lean_apply_1(v_h__4_537_, v___x_545_);
            return v___x_546_;
        }
    }
}
pub unsafe fn l___private_Init_Grind_ToInt_0__Lean_Grind_IntInterval_lo_x3f_match__1_splitter(
    mut v_motive_547_: *mut leanh::LeanObject,
    mut v_i_548_: *mut leanh::LeanObject,
    mut v_h__1_549_: *mut leanh::LeanObject,
    mut v_h__2_550_: *mut leanh::LeanObject,
    mut v_h__3_551_: *mut leanh::LeanObject,
    mut v_h__4_552_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_i_548_) {
        0 => {
            let mut v_lo_553_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_hi_554_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_555_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__4_552_);
            leanh::lean_dec(v_h__3_551_);
            leanh::lean_dec(v_h__2_550_);
            v_lo_553_ = leanh::lean_ctor_get(v_i_548_, 0);
            leanh::lean_inc(v_lo_553_);
            v_hi_554_ = leanh::lean_ctor_get(v_i_548_, 1);
            leanh::lean_inc(v_hi_554_);
            leanh::lean_dec_ref_known(v_i_548_, 2);
            v___x_555_ = leanh::lean_apply_2(v_h__1_549_, v_lo_553_, v_hi_554_);
            return v___x_555_;
        }
        1 => {
            let mut v_lo_556_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_557_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__4_552_);
            leanh::lean_dec(v_h__3_551_);
            leanh::lean_dec(v_h__1_549_);
            v_lo_556_ = leanh::lean_ctor_get(v_i_548_, 0);
            leanh::lean_inc(v_lo_556_);
            leanh::lean_dec_ref_known(v_i_548_, 1);
            v___x_557_ = leanh::lean_apply_1(v_h__2_550_, v_lo_556_);
            return v___x_557_;
        }
        2 => {
            let mut v_hi_558_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_559_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__4_552_);
            leanh::lean_dec(v_h__2_550_);
            leanh::lean_dec(v_h__1_549_);
            v_hi_558_ = leanh::lean_ctor_get(v_i_548_, 0);
            leanh::lean_inc(v_hi_558_);
            leanh::lean_dec_ref_known(v_i_548_, 1);
            v___x_559_ = leanh::lean_apply_1(v_h__3_551_, v_hi_558_);
            return v___x_559_;
        }
        _ => {
            let mut v___x_560_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_561_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_551_);
            leanh::lean_dec(v_h__2_550_);
            leanh::lean_dec(v_h__1_549_);
            v___x_560_ = leanh::lean_box(0);
            v___x_561_ = leanh::lean_apply_1(v_h__4_552_, v___x_560_);
            return v___x_561_;
        }
    }
}
pub unsafe fn l_Lean_Grind_IntInterval_isFinite(mut v_i_562_: *mut leanh::LeanObject) -> u8 {
    match leanh::lean_obj_tag(v_i_562_) {
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
    mut v_i_566_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_567_: u8 = 0;
    let mut v_r_568_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_567_ = l_Lean_Grind_IntInterval_isFinite(v_i_566_);
    leanh::lean_dec(v_i_566_);
    v_r_568_ = leanh::lean_box((v_res_567_) as usize);
    return v_r_568_;
}
pub unsafe fn _init_l_Lean_Grind_IntInterval_instMembershipInt() -> *mut leanh::LeanObject {
    let mut v___x_569_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_569_ = leanh::lean_box(0);
    return v___x_569_;
}
pub unsafe fn _init_l_Lean_Grind_IntInterval_wrap___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_571_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_570_ = leanh::lean_unsigned_to_nat(1);
    v___x_571_ = lean_nat_to_int(v___x_570_);
    return v___x_571_;
}
pub unsafe fn l_Lean_Grind_IntInterval_wrap(
    mut v_i_572_: *mut leanh::LeanObject,
    mut v_x_573_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_i_572_) {
        0 => {
            let mut v_lo_574_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_hi_575_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_576_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_577_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_578_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_579_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_lo_574_ = leanh::lean_ctor_get(v_i_572_, 0);
            v_hi_575_ = leanh::lean_ctor_get(v_i_572_, 1);
            v___x_576_ = lean_int_sub(v_x_573_, v_lo_574_);
            v___x_577_ = lean_int_sub(v_hi_575_, v_lo_574_);
            v___x_578_ = lean_int_emod(v___x_576_, v___x_577_);
            leanh::lean_dec(v___x_577_);
            leanh::lean_dec(v___x_576_);
            v___x_579_ = lean_int_add(v___x_578_, v_lo_574_);
            leanh::lean_dec(v___x_578_);
            return v___x_579_;
        }
        1 => {
            let mut v_lo_580_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_581_: u8 = 0;
            v_lo_580_ = leanh::lean_ctor_get(v_i_572_, 0);
            v___x_581_ = lean_int_dec_le(v_x_573_, v_lo_580_);
            if v___x_581_ == 0 {
                leanh::lean_inc(v_x_573_);
                return v_x_573_;
            } else {
                leanh::lean_inc(v_lo_580_);
                return v_lo_580_;
            }
        }
        2 => {
            let mut v_hi_582_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_583_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_584_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_585_: u8 = 0;
            v_hi_582_ = leanh::lean_ctor_get(v_i_572_, 0);
            v___x_583_ = leanh::lean_obj_once(
                core::ptr::addr_of_mut!(l_Lean_Grind_IntInterval_wrap___closed__0),
                core::ptr::addr_of_mut!(l_Lean_Grind_IntInterval_wrap___closed__0_once),
                _init_l_Lean_Grind_IntInterval_wrap___closed__0,
            );
            v___x_584_ = lean_int_sub(v_hi_582_, v___x_583_);
            v___x_585_ = lean_int_dec_le(v_x_573_, v___x_584_);
            if v___x_585_ == 0 {
                return v___x_584_;
            } else {
                leanh::lean_dec(v___x_584_);
                leanh::lean_inc(v_x_573_);
                return v_x_573_;
            }
        }
        _ => {
            leanh::lean_inc(v_x_573_);
            return v_x_573_;
        }
    }
}
pub unsafe fn l_Lean_Grind_IntInterval_wrap___boxed(
    mut v_i_586_: *mut leanh::LeanObject,
    mut v_x_587_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_588_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_588_ = l_Lean_Grind_IntInterval_wrap(v_i_586_, v_x_587_);
    leanh::lean_dec(v_x_587_);
    leanh::lean_dec(v_i_586_);
    return v_res_588_;
}
pub unsafe fn l_Lean_Grind_toIntUnexpander(
    mut v_stx_602_: *mut leanh::LeanObject,
    mut v_a_603_: *mut leanh::LeanObject,
    mut v_a_604_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_606_: u8 = 0;
    v___x_605_ = l_Lean_Grind_toIntUnexpander___closed__4;
    leanh::lean_inc(v_stx_602_);
    v___x_606_ = l_Lean_Syntax_isOfKind(v_stx_602_, v___x_605_);
    if v___x_606_ == 0 {
        let mut v___x_607_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_608_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_stx_602_);
        v___x_607_ = leanh::lean_box(0);
        v___x_608_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_608_, 0, v___x_607_);
        leanh::lean_ctor_set(v___x_608_, 1, v_a_604_);
        return v___x_608_;
    } else {
        let mut v___x_609_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_610_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_611_: u8 = 0;
        v___x_609_ = leanh::lean_unsigned_to_nat(1);
        v___x_610_ = l_Lean_Syntax_getArg(v_stx_602_, v___x_609_);
        leanh::lean_dec(v_stx_602_);
        leanh::lean_inc(v___x_610_);
        v___x_611_ = l_Lean_Syntax_matchesNull(v___x_610_, v___x_609_);
        if v___x_611_ == 0 {
            let mut v___x_612_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_613_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v___x_610_);
            v___x_612_ = leanh::lean_box(0);
            v___x_613_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_613_, 0, v___x_612_);
            leanh::lean_ctor_set(v___x_613_, 1, v_a_604_);
            return v___x_613_;
        } else {
            let mut v___x_614_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_615_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_616_: u8 = 0;
            let mut v___x_617_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_618_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_619_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_620_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_621_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_622_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_614_ = leanh::lean_unsigned_to_nat(0);
            v___x_615_ = l_Lean_Syntax_getArg(v___x_610_, v___x_614_);
            leanh::lean_dec(v___x_610_);
            v___x_616_ = 0;
            v___x_617_ = l_Lean_SourceInfo_fromRef(v_a_603_, v___x_616_);
            v___x_618_ = l_Lean_Grind_toIntUnexpander___closed__6;
            v___x_619_ = l_Lean_Grind_toIntUnexpander___closed__7;
            leanh::lean_inc(v___x_617_);
            v___x_620_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_620_, 0, v___x_617_);
            leanh::lean_ctor_set(v___x_620_, 1, v___x_619_);
            v___x_621_ = l_Lean_Syntax_node2(v___x_617_, v___x_618_, v___x_620_, v___x_615_);
            v___x_622_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_622_, 0, v___x_621_);
            leanh::lean_ctor_set(v___x_622_, 1, v_a_604_);
            return v___x_622_;
        }
    }
}
pub unsafe fn l_Lean_Grind_toIntUnexpander___boxed(
    mut v_stx_623_: *mut leanh::LeanObject,
    mut v_a_624_: *mut leanh::LeanObject,
    mut v_a_625_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_626_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_626_ = l_Lean_Grind_toIntUnexpander(v_stx_623_, v_a_624_, v_a_625_);
    leanh::lean_dec(v_a_624_);
    return v_res_626_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Grind_ToInt(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_LawfulBEqTactics(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Int_DivMod_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_ByCases(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Int_DivMod_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Lean_Grind_instInhabitedIntInterval_default =
        _init_l_Lean_Grind_instInhabitedIntInterval_default();
    leanh::lean_mark_persistent(l_Lean_Grind_instInhabitedIntInterval_default);
    l_Lean_Grind_instInhabitedIntInterval = _init_l_Lean_Grind_instInhabitedIntInterval();
    leanh::lean_mark_persistent(l_Lean_Grind_instInhabitedIntInterval);
    l_Lean_Grind_IntInterval_instMembershipInt = _init_l_Lean_Grind_IntInterval_instMembershipInt();
    leanh::lean_mark_persistent(l_Lean_Grind_IntInterval_instMembershipInt);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Grind_ToInt(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    res = runtime_initialize_Init_Grind_Tactics(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Grind_ToInt(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_LawfulBEqTactics(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Int_DivMod_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Grind_Tactics(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_ByCases(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Int_DivMod_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_ToInt(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Grind_ToInt(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Grind_ToInt(builtin);
}