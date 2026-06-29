// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Linear.Den
// Imports: Lean.Meta.Tactic.Grind.Arith.Linear.LinearM Lean.Meta.Tactic.Grind.Arith.CommRing.SafePoly
use crate::r#gen::Init::Data::Int::Basic::l_Int_pow;
use crate::r#gen::Init::Grind::Ring::CommSolver::{
    l_Lean_Grind_CommRing_Poly_cancelVar, l_Lean_Grind_CommRing_Poly_mulConst,
};
use crate::r#gen::Lean::Meta::Sym::Arith::Poly::l_Lean_Grind_CommRing_Poly_maxDegreeOf;
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::CommRing::SafePoly::{
    initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly,
    l_Lean_Grind_CommRing_Poly_findInvNumeralVar_x3f,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Linear::LinearM::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM,
    l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct,
    l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM,
};
use crate::ffi::lean_nat_to_int;
use crate::ffi::lean_nat_dec_eq;
pub static l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstr_cleanupDenominators___closed__0_value:
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
    m_fun: l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstr_cleanupDenominators___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstr_cleanupDenominators___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstr_cleanupDenominators___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstr_cleanupDenominators___closed__1_value:
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
    m_fun: l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstr_cleanupDenominators___lam__1
        as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstr_cleanupDenominators___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstr_cleanupDenominators___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_Linear_RingEqCnstr_cleanupDenominators___closed__0_value:
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
    m_fun: l_Lean_Meta_Grind_Arith_Linear_RingEqCnstr_cleanupDenominators___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_Arith_Linear_RingEqCnstr_cleanupDenominators___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_Linear_RingEqCnstr_cleanupDenominators___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_Linear_RingEqCnstr_cleanupDenominators___closed__1_value:
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
    m_fun: l_Lean_Meta_Grind_Arith_Linear_RingEqCnstr_cleanupDenominators___lam__1
        as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_Arith_Linear_RingEqCnstr_cleanupDenominators___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_Linear_RingEqCnstr_cleanupDenominators___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstr_cleanupDenominators___closed__0_value:
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
    m_fun: l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstr_cleanupDenominators___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstr_cleanupDenominators___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstr_cleanupDenominators___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstr_cleanupDenominators___closed__1_value:
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
    m_fun: l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstr_cleanupDenominators___lam__1
        as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstr_cleanupDenominators___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstr_cleanupDenominators___closed__1_value
) as *mut crate::leanh::LeanObject;
pub unsafe fn l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Den_0__Lean_Meta_Grind_Arith_Linear_cleanupDenominators_x27_go_spec__0(
    mut v_a_340_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_341_ = lean_nat_to_int(v_a_340_);
    return v___x_341_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Den_0__Lean_Meta_Grind_Arith_Linear_cleanupDenominators_x27_go___redArg(
    mut v_getPoly_342_: *mut crate::leanh::LeanObject,
    mut v_updateCnstr_343_: *mut crate::leanh::LeanObject,
    mut v_c_344_: *mut crate::leanh::LeanObject,
    mut v_a_345_: *mut crate::leanh::LeanObject,
    mut v_a_346_: *mut crate::leanh::LeanObject,
    mut v_a_347_: *mut crate::leanh::LeanObject,
    mut v_a_348_: *mut crate::leanh::LeanObject,
    mut v_a_349_: *mut crate::leanh::LeanObject,
    mut v_a_350_: *mut crate::leanh::LeanObject,
    mut v_a_351_: *mut crate::leanh::LeanObject,
    mut v_a_352_: *mut crate::leanh::LeanObject,
    mut v_a_353_: *mut crate::leanh::LeanObject,
    mut v_a_354_: *mut crate::leanh::LeanObject,
    mut v_a_355_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_p_357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_362_: u8 = 0;
    let mut v_val_363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_376_: u8 = 0;
    let mut v_a_377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_380_: u8 = 0;
    let mut v___x_382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_384_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_getPoly_342_);
                crate::leanh::lean_inc(v_c_344_);
                v_p_357_ = crate::leanh::lean_apply_1(v_getPoly_342_, v_c_344_);
                crate::leanh::lean_inc_ref(v_p_357_);
                v___x_358_ = l_Lean_Grind_CommRing_Poly_findInvNumeralVar_x3f(
                    v_p_357_, v_a_345_, v_a_346_, v_a_347_, v_a_348_, v_a_349_, v_a_350_, v_a_351_,
                    v_a_352_, v_a_353_, v_a_354_, v_a_355_,
                );
                if crate::leanh::lean_obj_tag(v___x_358_) == 0 {
                    v_a_359_ = crate::leanh::lean_ctor_get(v___x_358_, 0);
                    v_isSharedCheck_376_ = (!crate::leanh::lean_is_exclusive(v___x_358_)) as u8;
                    if v_isSharedCheck_376_ == 0 {
                        v___x_361_ = v___x_358_;
                        v_isShared_362_ = v_isSharedCheck_376_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_359_);
                        crate::leanh::lean_dec(v___x_358_);
                        v___x_361_ = crate::leanh::lean_box(0);
                        v_isShared_362_ = v_isSharedCheck_376_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_p_357_);
                    crate::leanh::lean_dec(v_c_344_);
                    crate::leanh::lean_dec(v_updateCnstr_343_);
                    crate::leanh::lean_dec_ref(v_getPoly_342_);
                    v_a_377_ = crate::leanh::lean_ctor_get(v___x_358_, 0);
                    v_isSharedCheck_384_ = (!crate::leanh::lean_is_exclusive(v___x_358_)) as u8;
                    if v_isSharedCheck_384_ == 0 {
                        v___x_379_ = v___x_358_;
                        v_isShared_380_ = v_isSharedCheck_384_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_377_);
                        crate::leanh::lean_dec(v___x_358_);
                        v___x_379_ = crate::leanh::lean_box(0);
                        v_isShared_380_ = v_isSharedCheck_384_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_359_) == 1 {
                    crate::leanh::lean_del_object(v___x_361_);
                    v_val_363_ = crate::leanh::lean_ctor_get(v_a_359_, 0);
                    crate::leanh::lean_inc(v_val_363_);
                    crate::leanh::lean_dec_ref_known(v_a_359_, 1);
                    v_fst_364_ = crate::leanh::lean_ctor_get(v_val_363_, 0);
                    crate::leanh::lean_inc(v_fst_364_);
                    v_snd_365_ = crate::leanh::lean_ctor_get(v_val_363_, 1);
                    crate::leanh::lean_inc(v_snd_365_);
                    crate::leanh::lean_dec(v_val_363_);
                    v___x_366_ = l_Lean_Grind_CommRing_Poly_maxDegreeOf(v_p_357_, v_snd_365_);
                    v___x_367_ = lean_nat_to_int(v_fst_364_);
                    v___x_368_ = l_Int_pow(v___x_367_, v___x_366_);
                    v___x_369_ = l_Lean_Grind_CommRing_Poly_mulConst(v___x_368_, v_p_357_);
                    crate::leanh::lean_dec(v___x_368_);
                    v___x_370_ =
                        l_Lean_Grind_CommRing_Poly_cancelVar(v___x_367_, v_snd_365_, v___x_369_);
                    crate::leanh::lean_inc(v_updateCnstr_343_);
                    v___x_371_ = crate::leanh::lean_apply_5(
                        v_updateCnstr_343_,
                        v_c_344_,
                        v___x_370_,
                        v___x_367_,
                        v_snd_365_,
                        v___x_366_,
                    );
                    v_c_344_ = v___x_371_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_a_359_);
                    crate::leanh::lean_dec_ref(v_p_357_);
                    crate::leanh::lean_dec(v_updateCnstr_343_);
                    crate::leanh::lean_dec_ref(v_getPoly_342_);
                    if v_isShared_362_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_361_, 0, v_c_344_);
                        v___x_374_ = v___x_361_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_375_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_375_, 0, v_c_344_);
                        v___x_374_ = v_reuseFailAlloc_375_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_374_;
            }
            3 => {
                if v_isShared_380_ == 0 {
                    v___x_382_ = v___x_379_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_383_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_383_, 0, v_a_377_);
                    v___x_382_ = v_reuseFailAlloc_383_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_382_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Den_0__Lean_Meta_Grind_Arith_Linear_cleanupDenominators_x27_go___redArg___boxed(
    mut v_getPoly_385_: *mut crate::leanh::LeanObject,
    mut v_updateCnstr_386_: *mut crate::leanh::LeanObject,
    mut v_c_387_: *mut crate::leanh::LeanObject,
    mut v_a_388_: *mut crate::leanh::LeanObject,
    mut v_a_389_: *mut crate::leanh::LeanObject,
    mut v_a_390_: *mut crate::leanh::LeanObject,
    mut v_a_391_: *mut crate::leanh::LeanObject,
    mut v_a_392_: *mut crate::leanh::LeanObject,
    mut v_a_393_: *mut crate::leanh::LeanObject,
    mut v_a_394_: *mut crate::leanh::LeanObject,
    mut v_a_395_: *mut crate::leanh::LeanObject,
    mut v_a_396_: *mut crate::leanh::LeanObject,
    mut v_a_397_: *mut crate::leanh::LeanObject,
    mut v_a_398_: *mut crate::leanh::LeanObject,
    mut v_a_399_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_400_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Den_0__Lean_Meta_Grind_Arith_Linear_cleanupDenominators_x27_go___redArg(v_getPoly_385_, v_updateCnstr_386_, v_c_387_, v_a_388_, v_a_389_, v_a_390_, v_a_391_, v_a_392_, v_a_393_, v_a_394_, v_a_395_, v_a_396_, v_a_397_, v_a_398_);
    crate::leanh::lean_dec(v_a_398_);
    crate::leanh::lean_dec_ref(v_a_397_);
    crate::leanh::lean_dec(v_a_396_);
    crate::leanh::lean_dec_ref(v_a_395_);
    crate::leanh::lean_dec(v_a_394_);
    crate::leanh::lean_dec_ref(v_a_393_);
    crate::leanh::lean_dec(v_a_392_);
    crate::leanh::lean_dec_ref(v_a_391_);
    crate::leanh::lean_dec(v_a_390_);
    crate::leanh::lean_dec(v_a_389_);
    crate::leanh::lean_dec_ref(v_a_388_);
    return v_res_400_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Den_0__Lean_Meta_Grind_Arith_Linear_cleanupDenominators_x27_go(
    mut v_00_u03b1_401_: *mut crate::leanh::LeanObject,
    mut v_getPoly_402_: *mut crate::leanh::LeanObject,
    mut v_updateCnstr_403_: *mut crate::leanh::LeanObject,
    mut v_c_404_: *mut crate::leanh::LeanObject,
    mut v_a_405_: *mut crate::leanh::LeanObject,
    mut v_a_406_: *mut crate::leanh::LeanObject,
    mut v_a_407_: *mut crate::leanh::LeanObject,
    mut v_a_408_: *mut crate::leanh::LeanObject,
    mut v_a_409_: *mut crate::leanh::LeanObject,
    mut v_a_410_: *mut crate::leanh::LeanObject,
    mut v_a_411_: *mut crate::leanh::LeanObject,
    mut v_a_412_: *mut crate::leanh::LeanObject,
    mut v_a_413_: *mut crate::leanh::LeanObject,
    mut v_a_414_: *mut crate::leanh::LeanObject,
    mut v_a_415_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_417_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Den_0__Lean_Meta_Grind_Arith_Linear_cleanupDenominators_x27_go___redArg(v_getPoly_402_, v_updateCnstr_403_, v_c_404_, v_a_405_, v_a_406_, v_a_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_, v_a_415_);
    return v___x_417_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Den_0__Lean_Meta_Grind_Arith_Linear_cleanupDenominators_x27_go___boxed(
    mut v_00_u03b1_418_: *mut crate::leanh::LeanObject,
    mut v_getPoly_419_: *mut crate::leanh::LeanObject,
    mut v_updateCnstr_420_: *mut crate::leanh::LeanObject,
    mut v_c_421_: *mut crate::leanh::LeanObject,
    mut v_a_422_: *mut crate::leanh::LeanObject,
    mut v_a_423_: *mut crate::leanh::LeanObject,
    mut v_a_424_: *mut crate::leanh::LeanObject,
    mut v_a_425_: *mut crate::leanh::LeanObject,
    mut v_a_426_: *mut crate::leanh::LeanObject,
    mut v_a_427_: *mut crate::leanh::LeanObject,
    mut v_a_428_: *mut crate::leanh::LeanObject,
    mut v_a_429_: *mut crate::leanh::LeanObject,
    mut v_a_430_: *mut crate::leanh::LeanObject,
    mut v_a_431_: *mut crate::leanh::LeanObject,
    mut v_a_432_: *mut crate::leanh::LeanObject,
    mut v_a_433_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_434_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Den_0__Lean_Meta_Grind_Arith_Linear_cleanupDenominators_x27_go(v_00_u03b1_418_, v_getPoly_419_, v_updateCnstr_420_, v_c_421_, v_a_422_, v_a_423_, v_a_424_, v_a_425_, v_a_426_, v_a_427_, v_a_428_, v_a_429_, v_a_430_, v_a_431_, v_a_432_);
    crate::leanh::lean_dec(v_a_432_);
    crate::leanh::lean_dec_ref(v_a_431_);
    crate::leanh::lean_dec(v_a_430_);
    crate::leanh::lean_dec_ref(v_a_429_);
    crate::leanh::lean_dec(v_a_428_);
    crate::leanh::lean_dec_ref(v_a_427_);
    crate::leanh::lean_dec(v_a_426_);
    crate::leanh::lean_dec_ref(v_a_425_);
    crate::leanh::lean_dec(v_a_424_);
    crate::leanh::lean_dec(v_a_423_);
    crate::leanh::lean_dec_ref(v_a_422_);
    return v_res_434_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Den_0__Lean_Meta_Grind_Arith_Linear_cleanupDenominators_x27___redArg(
    mut v_c_435_: *mut crate::leanh::LeanObject,
    mut v_getPoly_436_: *mut crate::leanh::LeanObject,
    mut v_updateCnstr_437_: *mut crate::leanh::LeanObject,
    mut v_a_438_: *mut crate::leanh::LeanObject,
    mut v_a_439_: *mut crate::leanh::LeanObject,
    mut v_a_440_: *mut crate::leanh::LeanObject,
    mut v_a_441_: *mut crate::leanh::LeanObject,
    mut v_a_442_: *mut crate::leanh::LeanObject,
    mut v_a_443_: *mut crate::leanh::LeanObject,
    mut v_a_444_: *mut crate::leanh::LeanObject,
    mut v_a_445_: *mut crate::leanh::LeanObject,
    mut v_a_446_: *mut crate::leanh::LeanObject,
    mut v_a_447_: *mut crate::leanh::LeanObject,
    mut v_a_448_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_454_: u8 = 0;
    let mut v_fieldInst_x3f_455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_charInst_x3f_459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_463_: u8 = 0;
    let mut v___x_465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_472_: u8 = 0;
    let mut v_a_473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_476_: u8 = 0;
    let mut v___x_478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_480_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_450_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(
                    v_a_438_, v_a_439_, v_a_440_, v_a_441_, v_a_442_, v_a_443_, v_a_444_, v_a_445_,
                    v_a_446_, v_a_447_, v_a_448_,
                );
                if crate::leanh::lean_obj_tag(v___x_450_) == 0 {
                    v_a_451_ = crate::leanh::lean_ctor_get(v___x_450_, 0);
                    v_isSharedCheck_472_ = (!crate::leanh::lean_is_exclusive(v___x_450_)) as u8;
                    if v_isSharedCheck_472_ == 0 {
                        v___x_453_ = v___x_450_;
                        v_isShared_454_ = v_isSharedCheck_472_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_451_);
                        crate::leanh::lean_dec(v___x_450_);
                        v___x_453_ = crate::leanh::lean_box(0);
                        v_isShared_454_ = v_isSharedCheck_472_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_updateCnstr_437_);
                    crate::leanh::lean_dec_ref(v_getPoly_436_);
                    crate::leanh::lean_dec(v_c_435_);
                    v_a_473_ = crate::leanh::lean_ctor_get(v___x_450_, 0);
                    v_isSharedCheck_480_ = (!crate::leanh::lean_is_exclusive(v___x_450_)) as u8;
                    if v_isSharedCheck_480_ == 0 {
                        v___x_475_ = v___x_450_;
                        v_isShared_476_ = v_isSharedCheck_480_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_473_);
                        crate::leanh::lean_dec(v___x_450_);
                        v___x_475_ = crate::leanh::lean_box(0);
                        v_isShared_476_ = v_isSharedCheck_480_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_fieldInst_x3f_455_ = crate::leanh::lean_ctor_get(v_a_451_, 15);
                if crate::leanh::lean_obj_tag(v_fieldInst_x3f_455_) == 0 {
                    crate::leanh::lean_dec(v_a_451_);
                    crate::leanh::lean_dec(v_updateCnstr_437_);
                    crate::leanh::lean_dec_ref(v_getPoly_436_);
                    if v_isShared_454_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_453_, 0, v_c_435_);
                        v___x_457_ = v___x_453_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_458_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_458_, 0, v_c_435_);
                        v___x_457_ = v_reuseFailAlloc_458_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_charInst_x3f_459_ = crate::leanh::lean_ctor_get(v_a_451_, 16);
                    crate::leanh::lean_inc(v_charInst_x3f_459_);
                    crate::leanh::lean_dec(v_a_451_);
                    if crate::leanh::lean_obj_tag(v_charInst_x3f_459_) == 1 {
                        v_val_460_ = crate::leanh::lean_ctor_get(v_charInst_x3f_459_, 0);
                        crate::leanh::lean_inc(v_val_460_);
                        crate::leanh::lean_dec_ref_known(v_charInst_x3f_459_, 1);
                        v_snd_461_ = crate::leanh::lean_ctor_get(v_val_460_, 1);
                        crate::leanh::lean_inc(v_snd_461_);
                        crate::leanh::lean_dec(v_val_460_);
                        v___x_462_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_463_ = lean_nat_dec_eq(v_snd_461_, v___x_462_);
                        crate::leanh::lean_dec(v_snd_461_);
                        if v___x_463_ == 0 {
                            crate::leanh::lean_dec(v_updateCnstr_437_);
                            crate::leanh::lean_dec_ref(v_getPoly_436_);
                            if v_isShared_454_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_453_, 0, v_c_435_);
                                v___x_465_ = v___x_453_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_466_ =
                                    crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_466_, 0, v_c_435_);
                                v___x_465_ = v_reuseFailAlloc_466_;
                                state = 3;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_453_);
                            v___x_467_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Den_0__Lean_Meta_Grind_Arith_Linear_cleanupDenominators_x27_go___boxed as *mut core::ffi::c_void, 16, 4);
                            crate::leanh::lean_closure_set(
                                v___x_467_,
                                0,
                                crate::leanh::lean_box(0),
                            );
                            crate::leanh::lean_closure_set(v___x_467_, 1, v_getPoly_436_);
                            crate::leanh::lean_closure_set(v___x_467_, 2, v_updateCnstr_437_);
                            crate::leanh::lean_closure_set(v___x_467_, 3, v_c_435_);
                            v___x_468_ = l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(
                                v___x_467_, v_a_438_, v_a_439_, v_a_440_, v_a_441_, v_a_442_,
                                v_a_443_, v_a_444_, v_a_445_, v_a_446_, v_a_447_, v_a_448_,
                            );
                            return v___x_468_;
                        }
                    } else {
                        crate::leanh::lean_dec(v_charInst_x3f_459_);
                        crate::leanh::lean_dec(v_updateCnstr_437_);
                        crate::leanh::lean_dec_ref(v_getPoly_436_);
                        if v_isShared_454_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_453_, 0, v_c_435_);
                            v___x_470_ = v___x_453_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_471_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_471_, 0, v_c_435_);
                            v___x_470_ = v_reuseFailAlloc_471_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_457_;
            }
            3 => {
                return v___x_465_;
            }
            4 => {
                return v___x_470_;
            }
            5 => {
                if v_isShared_476_ == 0 {
                    v___x_478_ = v___x_475_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_479_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_479_, 0, v_a_473_);
                    v___x_478_ = v_reuseFailAlloc_479_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_478_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Den_0__Lean_Meta_Grind_Arith_Linear_cleanupDenominators_x27___redArg___boxed(
    mut v_c_481_: *mut crate::leanh::LeanObject,
    mut v_getPoly_482_: *mut crate::leanh::LeanObject,
    mut v_updateCnstr_483_: *mut crate::leanh::LeanObject,
    mut v_a_484_: *mut crate::leanh::LeanObject,
    mut v_a_485_: *mut crate::leanh::LeanObject,
    mut v_a_486_: *mut crate::leanh::LeanObject,
    mut v_a_487_: *mut crate::leanh::LeanObject,
    mut v_a_488_: *mut crate::leanh::LeanObject,
    mut v_a_489_: *mut crate::leanh::LeanObject,
    mut v_a_490_: *mut crate::leanh::LeanObject,
    mut v_a_491_: *mut crate::leanh::LeanObject,
    mut v_a_492_: *mut crate::leanh::LeanObject,
    mut v_a_493_: *mut crate::leanh::LeanObject,
    mut v_a_494_: *mut crate::leanh::LeanObject,
    mut v_a_495_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_496_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Den_0__Lean_Meta_Grind_Arith_Linear_cleanupDenominators_x27___redArg(v_c_481_, v_getPoly_482_, v_updateCnstr_483_, v_a_484_, v_a_485_, v_a_486_, v_a_487_, v_a_488_, v_a_489_, v_a_490_, v_a_491_, v_a_492_, v_a_493_, v_a_494_);
    crate::leanh::lean_dec(v_a_494_);
    crate::leanh::lean_dec_ref(v_a_493_);
    crate::leanh::lean_dec(v_a_492_);
    crate::leanh::lean_dec_ref(v_a_491_);
    crate::leanh::lean_dec(v_a_490_);
    crate::leanh::lean_dec_ref(v_a_489_);
    crate::leanh::lean_dec(v_a_488_);
    crate::leanh::lean_dec_ref(v_a_487_);
    crate::leanh::lean_dec(v_a_486_);
    crate::leanh::lean_dec(v_a_485_);
    crate::leanh::lean_dec(v_a_484_);
    return v_res_496_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Den_0__Lean_Meta_Grind_Arith_Linear_cleanupDenominators_x27(
    mut v_00_u03b1_497_: *mut crate::leanh::LeanObject,
    mut v_c_498_: *mut crate::leanh::LeanObject,
    mut v_getPoly_499_: *mut crate::leanh::LeanObject,
    mut v_updateCnstr_500_: *mut crate::leanh::LeanObject,
    mut v_a_501_: *mut crate::leanh::LeanObject,
    mut v_a_502_: *mut crate::leanh::LeanObject,
    mut v_a_503_: *mut crate::leanh::LeanObject,
    mut v_a_504_: *mut crate::leanh::LeanObject,
    mut v_a_505_: *mut crate::leanh::LeanObject,
    mut v_a_506_: *mut crate::leanh::LeanObject,
    mut v_a_507_: *mut crate::leanh::LeanObject,
    mut v_a_508_: *mut crate::leanh::LeanObject,
    mut v_a_509_: *mut crate::leanh::LeanObject,
    mut v_a_510_: *mut crate::leanh::LeanObject,
    mut v_a_511_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_513_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Den_0__Lean_Meta_Grind_Arith_Linear_cleanupDenominators_x27___redArg(v_c_498_, v_getPoly_499_, v_updateCnstr_500_, v_a_501_, v_a_502_, v_a_503_, v_a_504_, v_a_505_, v_a_506_, v_a_507_, v_a_508_, v_a_509_, v_a_510_, v_a_511_);
    return v___x_513_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Den_0__Lean_Meta_Grind_Arith_Linear_cleanupDenominators_x27___boxed(
    mut v_00_u03b1_514_: *mut crate::leanh::LeanObject,
    mut v_c_515_: *mut crate::leanh::LeanObject,
    mut v_getPoly_516_: *mut crate::leanh::LeanObject,
    mut v_updateCnstr_517_: *mut crate::leanh::LeanObject,
    mut v_a_518_: *mut crate::leanh::LeanObject,
    mut v_a_519_: *mut crate::leanh::LeanObject,
    mut v_a_520_: *mut crate::leanh::LeanObject,
    mut v_a_521_: *mut crate::leanh::LeanObject,
    mut v_a_522_: *mut crate::leanh::LeanObject,
    mut v_a_523_: *mut crate::leanh::LeanObject,
    mut v_a_524_: *mut crate::leanh::LeanObject,
    mut v_a_525_: *mut crate::leanh::LeanObject,
    mut v_a_526_: *mut crate::leanh::LeanObject,
    mut v_a_527_: *mut crate::leanh::LeanObject,
    mut v_a_528_: *mut crate::leanh::LeanObject,
    mut v_a_529_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_530_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Den_0__Lean_Meta_Grind_Arith_Linear_cleanupDenominators_x27(v_00_u03b1_514_, v_c_515_, v_getPoly_516_, v_updateCnstr_517_, v_a_518_, v_a_519_, v_a_520_, v_a_521_, v_a_522_, v_a_523_, v_a_524_, v_a_525_, v_a_526_, v_a_527_, v_a_528_);
    crate::leanh::lean_dec(v_a_528_);
    crate::leanh::lean_dec_ref(v_a_527_);
    crate::leanh::lean_dec(v_a_526_);
    crate::leanh::lean_dec_ref(v_a_525_);
    crate::leanh::lean_dec(v_a_524_);
    crate::leanh::lean_dec_ref(v_a_523_);
    crate::leanh::lean_dec(v_a_522_);
    crate::leanh::lean_dec_ref(v_a_521_);
    crate::leanh::lean_dec(v_a_520_);
    crate::leanh::lean_dec(v_a_519_);
    crate::leanh::lean_dec(v_a_518_);
    return v_res_530_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstr_cleanupDenominators___lam__0(
    mut v_x_531_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_p_532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_p_532_ = crate::leanh::lean_ctor_get(v_x_531_, 0);
    crate::leanh::lean_inc_ref(v_p_532_);
    return v_p_532_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstr_cleanupDenominators___lam__0___boxed(
    mut v_x_533_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_534_ =
        l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstr_cleanupDenominators___lam__0(v_x_533_);
    crate::leanh::lean_dec_ref(v_x_533_);
    return v_res_534_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstr_cleanupDenominators___lam__1(
    mut v_c_535_: *mut crate::leanh::LeanObject,
    mut v_p_536_: *mut crate::leanh::LeanObject,
    mut v_val_537_: *mut crate::leanh::LeanObject,
    mut v_x_538_: *mut crate::leanh::LeanObject,
    mut v_n_539_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_strict_540_: u8 = 0;
    let mut v___x_541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_strict_540_ = crate::leanh::lean_ctor_get_uint8(
        v_c_535_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
    );
    v___x_541_ = crate::leanh::lean_alloc_ctor(2, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_541_, 0, v_c_535_);
    crate::leanh::lean_ctor_set(v___x_541_, 1, v_val_537_);
    crate::leanh::lean_ctor_set(v___x_541_, 2, v_x_538_);
    crate::leanh::lean_ctor_set(v___x_541_, 3, v_n_539_);
    v___x_542_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_542_, 0, v_p_536_);
    crate::leanh::lean_ctor_set(v___x_542_, 1, v___x_541_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_542_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
        v_strict_540_,
    );
    return v___x_542_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstr_cleanupDenominators(
    mut v_c_545_: *mut crate::leanh::LeanObject,
    mut v_a_546_: *mut crate::leanh::LeanObject,
    mut v_a_547_: *mut crate::leanh::LeanObject,
    mut v_a_548_: *mut crate::leanh::LeanObject,
    mut v_a_549_: *mut crate::leanh::LeanObject,
    mut v_a_550_: *mut crate::leanh::LeanObject,
    mut v_a_551_: *mut crate::leanh::LeanObject,
    mut v_a_552_: *mut crate::leanh::LeanObject,
    mut v_a_553_: *mut crate::leanh::LeanObject,
    mut v_a_554_: *mut crate::leanh::LeanObject,
    mut v_a_555_: *mut crate::leanh::LeanObject,
    mut v_a_556_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_558_ = l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstr_cleanupDenominators___closed__0;
    v___f_559_ = l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstr_cleanupDenominators___closed__1;
    v___x_560_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Den_0__Lean_Meta_Grind_Arith_Linear_cleanupDenominators_x27___redArg(v_c_545_, v___f_558_, v___f_559_, v_a_546_, v_a_547_, v_a_548_, v_a_549_, v_a_550_, v_a_551_, v_a_552_, v_a_553_, v_a_554_, v_a_555_, v_a_556_);
    return v___x_560_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstr_cleanupDenominators___boxed(
    mut v_c_561_: *mut crate::leanh::LeanObject,
    mut v_a_562_: *mut crate::leanh::LeanObject,
    mut v_a_563_: *mut crate::leanh::LeanObject,
    mut v_a_564_: *mut crate::leanh::LeanObject,
    mut v_a_565_: *mut crate::leanh::LeanObject,
    mut v_a_566_: *mut crate::leanh::LeanObject,
    mut v_a_567_: *mut crate::leanh::LeanObject,
    mut v_a_568_: *mut crate::leanh::LeanObject,
    mut v_a_569_: *mut crate::leanh::LeanObject,
    mut v_a_570_: *mut crate::leanh::LeanObject,
    mut v_a_571_: *mut crate::leanh::LeanObject,
    mut v_a_572_: *mut crate::leanh::LeanObject,
    mut v_a_573_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_574_ = l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstr_cleanupDenominators(
        v_c_561_, v_a_562_, v_a_563_, v_a_564_, v_a_565_, v_a_566_, v_a_567_, v_a_568_, v_a_569_,
        v_a_570_, v_a_571_, v_a_572_,
    );
    crate::leanh::lean_dec(v_a_572_);
    crate::leanh::lean_dec_ref(v_a_571_);
    crate::leanh::lean_dec(v_a_570_);
    crate::leanh::lean_dec_ref(v_a_569_);
    crate::leanh::lean_dec(v_a_568_);
    crate::leanh::lean_dec_ref(v_a_567_);
    crate::leanh::lean_dec(v_a_566_);
    crate::leanh::lean_dec_ref(v_a_565_);
    crate::leanh::lean_dec(v_a_564_);
    crate::leanh::lean_dec(v_a_563_);
    crate::leanh::lean_dec(v_a_562_);
    return v_res_574_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_RingEqCnstr_cleanupDenominators___lam__0(
    mut v_x_575_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_p_576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_p_576_ = crate::leanh::lean_ctor_get(v_x_575_, 0);
    crate::leanh::lean_inc_ref(v_p_576_);
    return v_p_576_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_RingEqCnstr_cleanupDenominators___lam__0___boxed(
    mut v_x_577_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_578_ = l_Lean_Meta_Grind_Arith_Linear_RingEqCnstr_cleanupDenominators___lam__0(v_x_577_);
    crate::leanh::lean_dec_ref(v_x_577_);
    return v_res_578_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_RingEqCnstr_cleanupDenominators___lam__1(
    mut v_c_579_: *mut crate::leanh::LeanObject,
    mut v_p_580_: *mut crate::leanh::LeanObject,
    mut v_val_581_: *mut crate::leanh::LeanObject,
    mut v_x_582_: *mut crate::leanh::LeanObject,
    mut v_n_583_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_584_ = crate::leanh::lean_alloc_ctor(2, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_584_, 0, v_c_579_);
    crate::leanh::lean_ctor_set(v___x_584_, 1, v_val_581_);
    crate::leanh::lean_ctor_set(v___x_584_, 2, v_x_582_);
    crate::leanh::lean_ctor_set(v___x_584_, 3, v_n_583_);
    v___x_585_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_585_, 0, v_p_580_);
    crate::leanh::lean_ctor_set(v___x_585_, 1, v___x_584_);
    return v___x_585_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_RingEqCnstr_cleanupDenominators(
    mut v_c_588_: *mut crate::leanh::LeanObject,
    mut v_a_589_: *mut crate::leanh::LeanObject,
    mut v_a_590_: *mut crate::leanh::LeanObject,
    mut v_a_591_: *mut crate::leanh::LeanObject,
    mut v_a_592_: *mut crate::leanh::LeanObject,
    mut v_a_593_: *mut crate::leanh::LeanObject,
    mut v_a_594_: *mut crate::leanh::LeanObject,
    mut v_a_595_: *mut crate::leanh::LeanObject,
    mut v_a_596_: *mut crate::leanh::LeanObject,
    mut v_a_597_: *mut crate::leanh::LeanObject,
    mut v_a_598_: *mut crate::leanh::LeanObject,
    mut v_a_599_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_601_ = l_Lean_Meta_Grind_Arith_Linear_RingEqCnstr_cleanupDenominators___closed__0;
    v___f_602_ = l_Lean_Meta_Grind_Arith_Linear_RingEqCnstr_cleanupDenominators___closed__1;
    v___x_603_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Den_0__Lean_Meta_Grind_Arith_Linear_cleanupDenominators_x27___redArg(v_c_588_, v___f_601_, v___f_602_, v_a_589_, v_a_590_, v_a_591_, v_a_592_, v_a_593_, v_a_594_, v_a_595_, v_a_596_, v_a_597_, v_a_598_, v_a_599_);
    return v___x_603_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_RingEqCnstr_cleanupDenominators___boxed(
    mut v_c_604_: *mut crate::leanh::LeanObject,
    mut v_a_605_: *mut crate::leanh::LeanObject,
    mut v_a_606_: *mut crate::leanh::LeanObject,
    mut v_a_607_: *mut crate::leanh::LeanObject,
    mut v_a_608_: *mut crate::leanh::LeanObject,
    mut v_a_609_: *mut crate::leanh::LeanObject,
    mut v_a_610_: *mut crate::leanh::LeanObject,
    mut v_a_611_: *mut crate::leanh::LeanObject,
    mut v_a_612_: *mut crate::leanh::LeanObject,
    mut v_a_613_: *mut crate::leanh::LeanObject,
    mut v_a_614_: *mut crate::leanh::LeanObject,
    mut v_a_615_: *mut crate::leanh::LeanObject,
    mut v_a_616_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_617_ = l_Lean_Meta_Grind_Arith_Linear_RingEqCnstr_cleanupDenominators(
        v_c_604_, v_a_605_, v_a_606_, v_a_607_, v_a_608_, v_a_609_, v_a_610_, v_a_611_, v_a_612_,
        v_a_613_, v_a_614_, v_a_615_,
    );
    crate::leanh::lean_dec(v_a_615_);
    crate::leanh::lean_dec_ref(v_a_614_);
    crate::leanh::lean_dec(v_a_613_);
    crate::leanh::lean_dec_ref(v_a_612_);
    crate::leanh::lean_dec(v_a_611_);
    crate::leanh::lean_dec_ref(v_a_610_);
    crate::leanh::lean_dec(v_a_609_);
    crate::leanh::lean_dec_ref(v_a_608_);
    crate::leanh::lean_dec(v_a_607_);
    crate::leanh::lean_dec(v_a_606_);
    crate::leanh::lean_dec(v_a_605_);
    return v_res_617_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstr_cleanupDenominators___lam__0(
    mut v_x_618_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_p_619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_p_619_ = crate::leanh::lean_ctor_get(v_x_618_, 0);
    crate::leanh::lean_inc_ref(v_p_619_);
    return v_p_619_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstr_cleanupDenominators___lam__0___boxed(
    mut v_x_620_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_621_ =
        l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstr_cleanupDenominators___lam__0(v_x_620_);
    crate::leanh::lean_dec_ref(v_x_620_);
    return v_res_621_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstr_cleanupDenominators___lam__1(
    mut v_c_622_: *mut crate::leanh::LeanObject,
    mut v_p_623_: *mut crate::leanh::LeanObject,
    mut v_val_624_: *mut crate::leanh::LeanObject,
    mut v_x_625_: *mut crate::leanh::LeanObject,
    mut v_n_626_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_627_ = crate::leanh::lean_alloc_ctor(1, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_627_, 0, v_c_622_);
    crate::leanh::lean_ctor_set(v___x_627_, 1, v_val_624_);
    crate::leanh::lean_ctor_set(v___x_627_, 2, v_x_625_);
    crate::leanh::lean_ctor_set(v___x_627_, 3, v_n_626_);
    v___x_628_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_628_, 0, v_p_623_);
    crate::leanh::lean_ctor_set(v___x_628_, 1, v___x_627_);
    return v___x_628_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstr_cleanupDenominators(
    mut v_c_631_: *mut crate::leanh::LeanObject,
    mut v_a_632_: *mut crate::leanh::LeanObject,
    mut v_a_633_: *mut crate::leanh::LeanObject,
    mut v_a_634_: *mut crate::leanh::LeanObject,
    mut v_a_635_: *mut crate::leanh::LeanObject,
    mut v_a_636_: *mut crate::leanh::LeanObject,
    mut v_a_637_: *mut crate::leanh::LeanObject,
    mut v_a_638_: *mut crate::leanh::LeanObject,
    mut v_a_639_: *mut crate::leanh::LeanObject,
    mut v_a_640_: *mut crate::leanh::LeanObject,
    mut v_a_641_: *mut crate::leanh::LeanObject,
    mut v_a_642_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_648_: u8 = 0;
    let mut v_noNatDivInst_x3f_649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_656_: u8 = 0;
    let mut v_a_657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_660_: u8 = 0;
    let mut v___x_662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_664_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_644_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(
                    v_a_632_, v_a_633_, v_a_634_, v_a_635_, v_a_636_, v_a_637_, v_a_638_, v_a_639_,
                    v_a_640_, v_a_641_, v_a_642_,
                );
                if crate::leanh::lean_obj_tag(v___x_644_) == 0 {
                    v_a_645_ = crate::leanh::lean_ctor_get(v___x_644_, 0);
                    v_isSharedCheck_656_ = (!crate::leanh::lean_is_exclusive(v___x_644_)) as u8;
                    if v_isSharedCheck_656_ == 0 {
                        v___x_647_ = v___x_644_;
                        v_isShared_648_ = v_isSharedCheck_656_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_645_);
                        crate::leanh::lean_dec(v___x_644_);
                        v___x_647_ = crate::leanh::lean_box(0);
                        v_isShared_648_ = v_isSharedCheck_656_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_c_631_);
                    v_a_657_ = crate::leanh::lean_ctor_get(v___x_644_, 0);
                    v_isSharedCheck_664_ = (!crate::leanh::lean_is_exclusive(v___x_644_)) as u8;
                    if v_isSharedCheck_664_ == 0 {
                        v___x_659_ = v___x_644_;
                        v_isShared_660_ = v_isSharedCheck_664_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_657_);
                        crate::leanh::lean_dec(v___x_644_);
                        v___x_659_ = crate::leanh::lean_box(0);
                        v_isShared_660_ = v_isSharedCheck_664_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_noNatDivInst_x3f_649_ = crate::leanh::lean_ctor_get(v_a_645_, 11);
                crate::leanh::lean_inc(v_noNatDivInst_x3f_649_);
                crate::leanh::lean_dec(v_a_645_);
                if crate::leanh::lean_obj_tag(v_noNatDivInst_x3f_649_) == 0 {
                    if v_isShared_648_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_647_, 0, v_c_631_);
                        v___x_651_ = v___x_647_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_652_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_652_, 0, v_c_631_);
                        v___x_651_ = v_reuseFailAlloc_652_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v_noNatDivInst_x3f_649_, 1);
                    crate::leanh::lean_del_object(v___x_647_);
                    v___f_653_ = l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstr_cleanupDenominators___closed__0;
                    v___f_654_ = l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstr_cleanupDenominators___closed__1;
                    v___x_655_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Den_0__Lean_Meta_Grind_Arith_Linear_cleanupDenominators_x27___redArg(v_c_631_, v___f_653_, v___f_654_, v_a_632_, v_a_633_, v_a_634_, v_a_635_, v_a_636_, v_a_637_, v_a_638_, v_a_639_, v_a_640_, v_a_641_, v_a_642_);
                    return v___x_655_;
                }
            }
            2 => {
                return v___x_651_;
            }
            3 => {
                if v_isShared_660_ == 0 {
                    v___x_662_ = v___x_659_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_663_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_663_, 0, v_a_657_);
                    v___x_662_ = v_reuseFailAlloc_663_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_662_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstr_cleanupDenominators___boxed(
    mut v_c_665_: *mut crate::leanh::LeanObject,
    mut v_a_666_: *mut crate::leanh::LeanObject,
    mut v_a_667_: *mut crate::leanh::LeanObject,
    mut v_a_668_: *mut crate::leanh::LeanObject,
    mut v_a_669_: *mut crate::leanh::LeanObject,
    mut v_a_670_: *mut crate::leanh::LeanObject,
    mut v_a_671_: *mut crate::leanh::LeanObject,
    mut v_a_672_: *mut crate::leanh::LeanObject,
    mut v_a_673_: *mut crate::leanh::LeanObject,
    mut v_a_674_: *mut crate::leanh::LeanObject,
    mut v_a_675_: *mut crate::leanh::LeanObject,
    mut v_a_676_: *mut crate::leanh::LeanObject,
    mut v_a_677_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_678_ = l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstr_cleanupDenominators(
        v_c_665_, v_a_666_, v_a_667_, v_a_668_, v_a_669_, v_a_670_, v_a_671_, v_a_672_, v_a_673_,
        v_a_674_, v_a_675_, v_a_676_,
    );
    crate::leanh::lean_dec(v_a_676_);
    crate::leanh::lean_dec_ref(v_a_675_);
    crate::leanh::lean_dec(v_a_674_);
    crate::leanh::lean_dec_ref(v_a_673_);
    crate::leanh::lean_dec(v_a_672_);
    crate::leanh::lean_dec_ref(v_a_671_);
    crate::leanh::lean_dec(v_a_670_);
    crate::leanh::lean_dec_ref(v_a_669_);
    crate::leanh::lean_dec(v_a_668_);
    crate::leanh::lean_dec(v_a_667_);
    crate::leanh::lean_dec(v_a_666_);
    return v_res_678_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Den(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Den(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Den(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Den(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Den(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Den(builtin);
}
