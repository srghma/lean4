// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Linear.Den
// Imports: Lean.Meta.Tactic.Grind.Arith.Linear.LinearM Lean.Meta.Tactic.Grind.Arith.CommRing.SafePoly
use crate::ffi::{lean_nat_dec_eq, lean_nat_to_int};
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
pub static l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstr_cleanupDenominators___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
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
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstr_cleanupDenominators___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstr_cleanupDenominators___closed__1_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
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
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstr_cleanupDenominators___closed__1_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_Linear_RingEqCnstr_cleanupDenominators___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
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
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_Linear_RingEqCnstr_cleanupDenominators___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_Linear_RingEqCnstr_cleanupDenominators___closed__1_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
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
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_Linear_RingEqCnstr_cleanupDenominators___closed__1_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstr_cleanupDenominators___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
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
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstr_cleanupDenominators___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstr_cleanupDenominators___closed__1_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
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
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstr_cleanupDenominators___closed__1_value
) as *mut leanh::LeanObject;
pub unsafe fn l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Den_0__Lean_Meta_Grind_Arith_Linear_cleanupDenominators_x27_go_spec__0(
    mut v_a_340_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_341_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_341_ = lean_nat_to_int(v_a_340_);
    return v___x_341_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Den_0__Lean_Meta_Grind_Arith_Linear_cleanupDenominators_x27_go___redArg(
    mut v_getPoly_342_: *mut leanh::LeanObject,
    mut v_updateCnstr_343_: *mut leanh::LeanObject,
    mut v_c_344_: *mut leanh::LeanObject,
    mut v_a_345_: *mut leanh::LeanObject,
    mut v_a_346_: *mut leanh::LeanObject,
    mut v_a_347_: *mut leanh::LeanObject,
    mut v_a_348_: *mut leanh::LeanObject,
    mut v_a_349_: *mut leanh::LeanObject,
    mut v_a_350_: *mut leanh::LeanObject,
    mut v_a_351_: *mut leanh::LeanObject,
    mut v_a_352_: *mut leanh::LeanObject,
    mut v_a_353_: *mut leanh::LeanObject,
    mut v_a_354_: *mut leanh::LeanObject,
    mut v_a_355_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_p_357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_362_: u8 = 0;
    let mut v_val_363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_376_: u8 = 0;
    let mut v_a_377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_380_: u8 = 0;
    let mut v___x_382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_384_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_getPoly_342_);
                leanh::lean_inc(v_c_344_);
                v_p_357_ = leanh::lean_apply_1(v_getPoly_342_, v_c_344_);
                leanh::lean_inc_ref(v_p_357_);
                v___x_358_ = l_Lean_Grind_CommRing_Poly_findInvNumeralVar_x3f(
                    v_p_357_, v_a_345_, v_a_346_, v_a_347_, v_a_348_, v_a_349_, v_a_350_, v_a_351_,
                    v_a_352_, v_a_353_, v_a_354_, v_a_355_,
                );
                if leanh::lean_obj_tag(v___x_358_) == 0 {
                    v_a_359_ = leanh::lean_ctor_get(v___x_358_, 0);
                    v_isSharedCheck_376_ = (!leanh::lean_is_exclusive(v___x_358_)) as u8;
                    if v_isSharedCheck_376_ == 0 {
                        v___x_361_ = v___x_358_;
                        v_isShared_362_ = v_isSharedCheck_376_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_359_);
                        leanh::lean_dec(v___x_358_);
                        v___x_361_ = leanh::lean_box(0);
                        v_isShared_362_ = v_isSharedCheck_376_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_p_357_);
                    leanh::lean_dec(v_c_344_);
                    leanh::lean_dec(v_updateCnstr_343_);
                    leanh::lean_dec_ref(v_getPoly_342_);
                    v_a_377_ = leanh::lean_ctor_get(v___x_358_, 0);
                    v_isSharedCheck_384_ = (!leanh::lean_is_exclusive(v___x_358_)) as u8;
                    if v_isSharedCheck_384_ == 0 {
                        v___x_379_ = v___x_358_;
                        v_isShared_380_ = v_isSharedCheck_384_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_377_);
                        leanh::lean_dec(v___x_358_);
                        v___x_379_ = leanh::lean_box(0);
                        v_isShared_380_ = v_isSharedCheck_384_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_359_) == 1 {
                    leanh::lean_del_object(v___x_361_);
                    v_val_363_ = leanh::lean_ctor_get(v_a_359_, 0);
                    leanh::lean_inc(v_val_363_);
                    leanh::lean_dec_ref_known(v_a_359_, 1);
                    v_fst_364_ = leanh::lean_ctor_get(v_val_363_, 0);
                    leanh::lean_inc(v_fst_364_);
                    v_snd_365_ = leanh::lean_ctor_get(v_val_363_, 1);
                    leanh::lean_inc(v_snd_365_);
                    leanh::lean_dec(v_val_363_);
                    v___x_366_ = l_Lean_Grind_CommRing_Poly_maxDegreeOf(v_p_357_, v_snd_365_);
                    v___x_367_ = lean_nat_to_int(v_fst_364_);
                    v___x_368_ = l_Int_pow(v___x_367_, v___x_366_);
                    v___x_369_ = l_Lean_Grind_CommRing_Poly_mulConst(v___x_368_, v_p_357_);
                    leanh::lean_dec(v___x_368_);
                    v___x_370_ =
                        l_Lean_Grind_CommRing_Poly_cancelVar(v___x_367_, v_snd_365_, v___x_369_);
                    leanh::lean_inc(v_updateCnstr_343_);
                    v___x_371_ = leanh::lean_apply_5(
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
                    leanh::lean_dec(v_a_359_);
                    leanh::lean_dec_ref(v_p_357_);
                    leanh::lean_dec(v_updateCnstr_343_);
                    leanh::lean_dec_ref(v_getPoly_342_);
                    if v_isShared_362_ == 0 {
                        leanh::lean_ctor_set(v___x_361_, 0, v_c_344_);
                        v___x_374_ = v___x_361_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_375_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_375_, 0, v_c_344_);
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
                    v_reuseFailAlloc_383_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_383_, 0, v_a_377_);
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
    mut v_getPoly_385_: *mut leanh::LeanObject,
    mut v_updateCnstr_386_: *mut leanh::LeanObject,
    mut v_c_387_: *mut leanh::LeanObject,
    mut v_a_388_: *mut leanh::LeanObject,
    mut v_a_389_: *mut leanh::LeanObject,
    mut v_a_390_: *mut leanh::LeanObject,
    mut v_a_391_: *mut leanh::LeanObject,
    mut v_a_392_: *mut leanh::LeanObject,
    mut v_a_393_: *mut leanh::LeanObject,
    mut v_a_394_: *mut leanh::LeanObject,
    mut v_a_395_: *mut leanh::LeanObject,
    mut v_a_396_: *mut leanh::LeanObject,
    mut v_a_397_: *mut leanh::LeanObject,
    mut v_a_398_: *mut leanh::LeanObject,
    mut v_a_399_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_400_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_400_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Den_0__Lean_Meta_Grind_Arith_Linear_cleanupDenominators_x27_go___redArg(v_getPoly_385_, v_updateCnstr_386_, v_c_387_, v_a_388_, v_a_389_, v_a_390_, v_a_391_, v_a_392_, v_a_393_, v_a_394_, v_a_395_, v_a_396_, v_a_397_, v_a_398_);
    leanh::lean_dec(v_a_398_);
    leanh::lean_dec_ref(v_a_397_);
    leanh::lean_dec(v_a_396_);
    leanh::lean_dec_ref(v_a_395_);
    leanh::lean_dec(v_a_394_);
    leanh::lean_dec_ref(v_a_393_);
    leanh::lean_dec(v_a_392_);
    leanh::lean_dec_ref(v_a_391_);
    leanh::lean_dec(v_a_390_);
    leanh::lean_dec(v_a_389_);
    leanh::lean_dec_ref(v_a_388_);
    return v_res_400_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Den_0__Lean_Meta_Grind_Arith_Linear_cleanupDenominators_x27_go(
    mut v_00_u03b1_401_: *mut leanh::LeanObject,
    mut v_getPoly_402_: *mut leanh::LeanObject,
    mut v_updateCnstr_403_: *mut leanh::LeanObject,
    mut v_c_404_: *mut leanh::LeanObject,
    mut v_a_405_: *mut leanh::LeanObject,
    mut v_a_406_: *mut leanh::LeanObject,
    mut v_a_407_: *mut leanh::LeanObject,
    mut v_a_408_: *mut leanh::LeanObject,
    mut v_a_409_: *mut leanh::LeanObject,
    mut v_a_410_: *mut leanh::LeanObject,
    mut v_a_411_: *mut leanh::LeanObject,
    mut v_a_412_: *mut leanh::LeanObject,
    mut v_a_413_: *mut leanh::LeanObject,
    mut v_a_414_: *mut leanh::LeanObject,
    mut v_a_415_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_417_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_417_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Den_0__Lean_Meta_Grind_Arith_Linear_cleanupDenominators_x27_go___redArg(v_getPoly_402_, v_updateCnstr_403_, v_c_404_, v_a_405_, v_a_406_, v_a_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_, v_a_415_);
    return v___x_417_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Den_0__Lean_Meta_Grind_Arith_Linear_cleanupDenominators_x27_go___boxed(
    mut v_00_u03b1_418_: *mut leanh::LeanObject,
    mut v_getPoly_419_: *mut leanh::LeanObject,
    mut v_updateCnstr_420_: *mut leanh::LeanObject,
    mut v_c_421_: *mut leanh::LeanObject,
    mut v_a_422_: *mut leanh::LeanObject,
    mut v_a_423_: *mut leanh::LeanObject,
    mut v_a_424_: *mut leanh::LeanObject,
    mut v_a_425_: *mut leanh::LeanObject,
    mut v_a_426_: *mut leanh::LeanObject,
    mut v_a_427_: *mut leanh::LeanObject,
    mut v_a_428_: *mut leanh::LeanObject,
    mut v_a_429_: *mut leanh::LeanObject,
    mut v_a_430_: *mut leanh::LeanObject,
    mut v_a_431_: *mut leanh::LeanObject,
    mut v_a_432_: *mut leanh::LeanObject,
    mut v_a_433_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_434_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_434_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Den_0__Lean_Meta_Grind_Arith_Linear_cleanupDenominators_x27_go(v_00_u03b1_418_, v_getPoly_419_, v_updateCnstr_420_, v_c_421_, v_a_422_, v_a_423_, v_a_424_, v_a_425_, v_a_426_, v_a_427_, v_a_428_, v_a_429_, v_a_430_, v_a_431_, v_a_432_);
    leanh::lean_dec(v_a_432_);
    leanh::lean_dec_ref(v_a_431_);
    leanh::lean_dec(v_a_430_);
    leanh::lean_dec_ref(v_a_429_);
    leanh::lean_dec(v_a_428_);
    leanh::lean_dec_ref(v_a_427_);
    leanh::lean_dec(v_a_426_);
    leanh::lean_dec_ref(v_a_425_);
    leanh::lean_dec(v_a_424_);
    leanh::lean_dec(v_a_423_);
    leanh::lean_dec_ref(v_a_422_);
    return v_res_434_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Den_0__Lean_Meta_Grind_Arith_Linear_cleanupDenominators_x27___redArg(
    mut v_c_435_: *mut leanh::LeanObject,
    mut v_getPoly_436_: *mut leanh::LeanObject,
    mut v_updateCnstr_437_: *mut leanh::LeanObject,
    mut v_a_438_: *mut leanh::LeanObject,
    mut v_a_439_: *mut leanh::LeanObject,
    mut v_a_440_: *mut leanh::LeanObject,
    mut v_a_441_: *mut leanh::LeanObject,
    mut v_a_442_: *mut leanh::LeanObject,
    mut v_a_443_: *mut leanh::LeanObject,
    mut v_a_444_: *mut leanh::LeanObject,
    mut v_a_445_: *mut leanh::LeanObject,
    mut v_a_446_: *mut leanh::LeanObject,
    mut v_a_447_: *mut leanh::LeanObject,
    mut v_a_448_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_454_: u8 = 0;
    let mut v_fieldInst_x3f_455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_charInst_x3f_459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_463_: u8 = 0;
    let mut v___x_465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_472_: u8 = 0;
    let mut v_a_473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_476_: u8 = 0;
    let mut v___x_478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_480_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_450_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(
                    v_a_438_, v_a_439_, v_a_440_, v_a_441_, v_a_442_, v_a_443_, v_a_444_, v_a_445_,
                    v_a_446_, v_a_447_, v_a_448_,
                );
                if leanh::lean_obj_tag(v___x_450_) == 0 {
                    v_a_451_ = leanh::lean_ctor_get(v___x_450_, 0);
                    v_isSharedCheck_472_ = (!leanh::lean_is_exclusive(v___x_450_)) as u8;
                    if v_isSharedCheck_472_ == 0 {
                        v___x_453_ = v___x_450_;
                        v_isShared_454_ = v_isSharedCheck_472_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_451_);
                        leanh::lean_dec(v___x_450_);
                        v___x_453_ = leanh::lean_box(0);
                        v_isShared_454_ = v_isSharedCheck_472_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_updateCnstr_437_);
                    leanh::lean_dec_ref(v_getPoly_436_);
                    leanh::lean_dec(v_c_435_);
                    v_a_473_ = leanh::lean_ctor_get(v___x_450_, 0);
                    v_isSharedCheck_480_ = (!leanh::lean_is_exclusive(v___x_450_)) as u8;
                    if v_isSharedCheck_480_ == 0 {
                        v___x_475_ = v___x_450_;
                        v_isShared_476_ = v_isSharedCheck_480_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_473_);
                        leanh::lean_dec(v___x_450_);
                        v___x_475_ = leanh::lean_box(0);
                        v_isShared_476_ = v_isSharedCheck_480_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_fieldInst_x3f_455_ = leanh::lean_ctor_get(v_a_451_, 15);
                if leanh::lean_obj_tag(v_fieldInst_x3f_455_) == 0 {
                    leanh::lean_dec(v_a_451_);
                    leanh::lean_dec(v_updateCnstr_437_);
                    leanh::lean_dec_ref(v_getPoly_436_);
                    if v_isShared_454_ == 0 {
                        leanh::lean_ctor_set(v___x_453_, 0, v_c_435_);
                        v___x_457_ = v___x_453_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_458_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_458_, 0, v_c_435_);
                        v___x_457_ = v_reuseFailAlloc_458_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_charInst_x3f_459_ = leanh::lean_ctor_get(v_a_451_, 16);
                    leanh::lean_inc(v_charInst_x3f_459_);
                    leanh::lean_dec(v_a_451_);
                    if leanh::lean_obj_tag(v_charInst_x3f_459_) == 1 {
                        v_val_460_ = leanh::lean_ctor_get(v_charInst_x3f_459_, 0);
                        leanh::lean_inc(v_val_460_);
                        leanh::lean_dec_ref_known(v_charInst_x3f_459_, 1);
                        v_snd_461_ = leanh::lean_ctor_get(v_val_460_, 1);
                        leanh::lean_inc(v_snd_461_);
                        leanh::lean_dec(v_val_460_);
                        v___x_462_ = leanh::lean_unsigned_to_nat(0);
                        v___x_463_ = lean_nat_dec_eq(v_snd_461_, v___x_462_);
                        leanh::lean_dec(v_snd_461_);
                        if v___x_463_ == 0 {
                            leanh::lean_dec(v_updateCnstr_437_);
                            leanh::lean_dec_ref(v_getPoly_436_);
                            if v_isShared_454_ == 0 {
                                leanh::lean_ctor_set(v___x_453_, 0, v_c_435_);
                                v___x_465_ = v___x_453_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_466_ =
                                    leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_466_, 0, v_c_435_);
                                v___x_465_ = v_reuseFailAlloc_466_;
                                state = 3;
                                continue;
                            }
                        } else {
                            leanh::lean_del_object(v___x_453_);
                            v___x_467_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Den_0__Lean_Meta_Grind_Arith_Linear_cleanupDenominators_x27_go___boxed as *mut core::ffi::c_void, 16, 4);
                            leanh::lean_closure_set(
                                v___x_467_,
                                0,
                                leanh::lean_box(0),
                            );
                            leanh::lean_closure_set(v___x_467_, 1, v_getPoly_436_);
                            leanh::lean_closure_set(v___x_467_, 2, v_updateCnstr_437_);
                            leanh::lean_closure_set(v___x_467_, 3, v_c_435_);
                            v___x_468_ = l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(
                                v___x_467_, v_a_438_, v_a_439_, v_a_440_, v_a_441_, v_a_442_,
                                v_a_443_, v_a_444_, v_a_445_, v_a_446_, v_a_447_, v_a_448_,
                            );
                            return v___x_468_;
                        }
                    } else {
                        leanh::lean_dec(v_charInst_x3f_459_);
                        leanh::lean_dec(v_updateCnstr_437_);
                        leanh::lean_dec_ref(v_getPoly_436_);
                        if v_isShared_454_ == 0 {
                            leanh::lean_ctor_set(v___x_453_, 0, v_c_435_);
                            v___x_470_ = v___x_453_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_471_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_471_, 0, v_c_435_);
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
                    v_reuseFailAlloc_479_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_479_, 0, v_a_473_);
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
    mut v_c_481_: *mut leanh::LeanObject,
    mut v_getPoly_482_: *mut leanh::LeanObject,
    mut v_updateCnstr_483_: *mut leanh::LeanObject,
    mut v_a_484_: *mut leanh::LeanObject,
    mut v_a_485_: *mut leanh::LeanObject,
    mut v_a_486_: *mut leanh::LeanObject,
    mut v_a_487_: *mut leanh::LeanObject,
    mut v_a_488_: *mut leanh::LeanObject,
    mut v_a_489_: *mut leanh::LeanObject,
    mut v_a_490_: *mut leanh::LeanObject,
    mut v_a_491_: *mut leanh::LeanObject,
    mut v_a_492_: *mut leanh::LeanObject,
    mut v_a_493_: *mut leanh::LeanObject,
    mut v_a_494_: *mut leanh::LeanObject,
    mut v_a_495_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_496_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_496_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Den_0__Lean_Meta_Grind_Arith_Linear_cleanupDenominators_x27___redArg(v_c_481_, v_getPoly_482_, v_updateCnstr_483_, v_a_484_, v_a_485_, v_a_486_, v_a_487_, v_a_488_, v_a_489_, v_a_490_, v_a_491_, v_a_492_, v_a_493_, v_a_494_);
    leanh::lean_dec(v_a_494_);
    leanh::lean_dec_ref(v_a_493_);
    leanh::lean_dec(v_a_492_);
    leanh::lean_dec_ref(v_a_491_);
    leanh::lean_dec(v_a_490_);
    leanh::lean_dec_ref(v_a_489_);
    leanh::lean_dec(v_a_488_);
    leanh::lean_dec_ref(v_a_487_);
    leanh::lean_dec(v_a_486_);
    leanh::lean_dec(v_a_485_);
    leanh::lean_dec(v_a_484_);
    return v_res_496_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Den_0__Lean_Meta_Grind_Arith_Linear_cleanupDenominators_x27(
    mut v_00_u03b1_497_: *mut leanh::LeanObject,
    mut v_c_498_: *mut leanh::LeanObject,
    mut v_getPoly_499_: *mut leanh::LeanObject,
    mut v_updateCnstr_500_: *mut leanh::LeanObject,
    mut v_a_501_: *mut leanh::LeanObject,
    mut v_a_502_: *mut leanh::LeanObject,
    mut v_a_503_: *mut leanh::LeanObject,
    mut v_a_504_: *mut leanh::LeanObject,
    mut v_a_505_: *mut leanh::LeanObject,
    mut v_a_506_: *mut leanh::LeanObject,
    mut v_a_507_: *mut leanh::LeanObject,
    mut v_a_508_: *mut leanh::LeanObject,
    mut v_a_509_: *mut leanh::LeanObject,
    mut v_a_510_: *mut leanh::LeanObject,
    mut v_a_511_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_513_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_513_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Den_0__Lean_Meta_Grind_Arith_Linear_cleanupDenominators_x27___redArg(v_c_498_, v_getPoly_499_, v_updateCnstr_500_, v_a_501_, v_a_502_, v_a_503_, v_a_504_, v_a_505_, v_a_506_, v_a_507_, v_a_508_, v_a_509_, v_a_510_, v_a_511_);
    return v___x_513_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Den_0__Lean_Meta_Grind_Arith_Linear_cleanupDenominators_x27___boxed(
    mut v_00_u03b1_514_: *mut leanh::LeanObject,
    mut v_c_515_: *mut leanh::LeanObject,
    mut v_getPoly_516_: *mut leanh::LeanObject,
    mut v_updateCnstr_517_: *mut leanh::LeanObject,
    mut v_a_518_: *mut leanh::LeanObject,
    mut v_a_519_: *mut leanh::LeanObject,
    mut v_a_520_: *mut leanh::LeanObject,
    mut v_a_521_: *mut leanh::LeanObject,
    mut v_a_522_: *mut leanh::LeanObject,
    mut v_a_523_: *mut leanh::LeanObject,
    mut v_a_524_: *mut leanh::LeanObject,
    mut v_a_525_: *mut leanh::LeanObject,
    mut v_a_526_: *mut leanh::LeanObject,
    mut v_a_527_: *mut leanh::LeanObject,
    mut v_a_528_: *mut leanh::LeanObject,
    mut v_a_529_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_530_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_530_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Den_0__Lean_Meta_Grind_Arith_Linear_cleanupDenominators_x27(v_00_u03b1_514_, v_c_515_, v_getPoly_516_, v_updateCnstr_517_, v_a_518_, v_a_519_, v_a_520_, v_a_521_, v_a_522_, v_a_523_, v_a_524_, v_a_525_, v_a_526_, v_a_527_, v_a_528_);
    leanh::lean_dec(v_a_528_);
    leanh::lean_dec_ref(v_a_527_);
    leanh::lean_dec(v_a_526_);
    leanh::lean_dec_ref(v_a_525_);
    leanh::lean_dec(v_a_524_);
    leanh::lean_dec_ref(v_a_523_);
    leanh::lean_dec(v_a_522_);
    leanh::lean_dec_ref(v_a_521_);
    leanh::lean_dec(v_a_520_);
    leanh::lean_dec(v_a_519_);
    leanh::lean_dec(v_a_518_);
    return v_res_530_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstr_cleanupDenominators___lam__0(
    mut v_x_531_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_p_532_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_p_532_ = leanh::lean_ctor_get(v_x_531_, 0);
    leanh::lean_inc_ref(v_p_532_);
    return v_p_532_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstr_cleanupDenominators___lam__0___boxed(
    mut v_x_533_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_534_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_534_ =
        l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstr_cleanupDenominators___lam__0(v_x_533_);
    leanh::lean_dec_ref(v_x_533_);
    return v_res_534_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstr_cleanupDenominators___lam__1(
    mut v_c_535_: *mut leanh::LeanObject,
    mut v_p_536_: *mut leanh::LeanObject,
    mut v_val_537_: *mut leanh::LeanObject,
    mut v_x_538_: *mut leanh::LeanObject,
    mut v_n_539_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_strict_540_: u8 = 0;
    let mut v___x_541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_542_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_strict_540_ = leanh::lean_ctor_get_uint8(
        v_c_535_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
    );
    v___x_541_ = leanh::lean_alloc_ctor(2, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_541_, 0, v_c_535_);
    leanh::lean_ctor_set(v___x_541_, 1, v_val_537_);
    leanh::lean_ctor_set(v___x_541_, 2, v_x_538_);
    leanh::lean_ctor_set(v___x_541_, 3, v_n_539_);
    v___x_542_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
    leanh::lean_ctor_set(v___x_542_, 0, v_p_536_);
    leanh::lean_ctor_set(v___x_542_, 1, v___x_541_);
    leanh::lean_ctor_set_uint8(
        v___x_542_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
        v_strict_540_,
    );
    return v___x_542_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstr_cleanupDenominators(
    mut v_c_545_: *mut leanh::LeanObject,
    mut v_a_546_: *mut leanh::LeanObject,
    mut v_a_547_: *mut leanh::LeanObject,
    mut v_a_548_: *mut leanh::LeanObject,
    mut v_a_549_: *mut leanh::LeanObject,
    mut v_a_550_: *mut leanh::LeanObject,
    mut v_a_551_: *mut leanh::LeanObject,
    mut v_a_552_: *mut leanh::LeanObject,
    mut v_a_553_: *mut leanh::LeanObject,
    mut v_a_554_: *mut leanh::LeanObject,
    mut v_a_555_: *mut leanh::LeanObject,
    mut v_a_556_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_560_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_558_ = l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstr_cleanupDenominators___closed__0;
    v___f_559_ = l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstr_cleanupDenominators___closed__1;
    v___x_560_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Den_0__Lean_Meta_Grind_Arith_Linear_cleanupDenominators_x27___redArg(v_c_545_, v___f_558_, v___f_559_, v_a_546_, v_a_547_, v_a_548_, v_a_549_, v_a_550_, v_a_551_, v_a_552_, v_a_553_, v_a_554_, v_a_555_, v_a_556_);
    return v___x_560_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstr_cleanupDenominators___boxed(
    mut v_c_561_: *mut leanh::LeanObject,
    mut v_a_562_: *mut leanh::LeanObject,
    mut v_a_563_: *mut leanh::LeanObject,
    mut v_a_564_: *mut leanh::LeanObject,
    mut v_a_565_: *mut leanh::LeanObject,
    mut v_a_566_: *mut leanh::LeanObject,
    mut v_a_567_: *mut leanh::LeanObject,
    mut v_a_568_: *mut leanh::LeanObject,
    mut v_a_569_: *mut leanh::LeanObject,
    mut v_a_570_: *mut leanh::LeanObject,
    mut v_a_571_: *mut leanh::LeanObject,
    mut v_a_572_: *mut leanh::LeanObject,
    mut v_a_573_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_574_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_574_ = l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstr_cleanupDenominators(
        v_c_561_, v_a_562_, v_a_563_, v_a_564_, v_a_565_, v_a_566_, v_a_567_, v_a_568_, v_a_569_,
        v_a_570_, v_a_571_, v_a_572_,
    );
    leanh::lean_dec(v_a_572_);
    leanh::lean_dec_ref(v_a_571_);
    leanh::lean_dec(v_a_570_);
    leanh::lean_dec_ref(v_a_569_);
    leanh::lean_dec(v_a_568_);
    leanh::lean_dec_ref(v_a_567_);
    leanh::lean_dec(v_a_566_);
    leanh::lean_dec_ref(v_a_565_);
    leanh::lean_dec(v_a_564_);
    leanh::lean_dec(v_a_563_);
    leanh::lean_dec(v_a_562_);
    return v_res_574_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_RingEqCnstr_cleanupDenominators___lam__0(
    mut v_x_575_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_p_576_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_p_576_ = leanh::lean_ctor_get(v_x_575_, 0);
    leanh::lean_inc_ref(v_p_576_);
    return v_p_576_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_RingEqCnstr_cleanupDenominators___lam__0___boxed(
    mut v_x_577_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_578_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_578_ = l_Lean_Meta_Grind_Arith_Linear_RingEqCnstr_cleanupDenominators___lam__0(v_x_577_);
    leanh::lean_dec_ref(v_x_577_);
    return v_res_578_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_RingEqCnstr_cleanupDenominators___lam__1(
    mut v_c_579_: *mut leanh::LeanObject,
    mut v_p_580_: *mut leanh::LeanObject,
    mut v_val_581_: *mut leanh::LeanObject,
    mut v_x_582_: *mut leanh::LeanObject,
    mut v_n_583_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_585_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_584_ = leanh::lean_alloc_ctor(2, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_584_, 0, v_c_579_);
    leanh::lean_ctor_set(v___x_584_, 1, v_val_581_);
    leanh::lean_ctor_set(v___x_584_, 2, v_x_582_);
    leanh::lean_ctor_set(v___x_584_, 3, v_n_583_);
    v___x_585_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_585_, 0, v_p_580_);
    leanh::lean_ctor_set(v___x_585_, 1, v___x_584_);
    return v___x_585_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_RingEqCnstr_cleanupDenominators(
    mut v_c_588_: *mut leanh::LeanObject,
    mut v_a_589_: *mut leanh::LeanObject,
    mut v_a_590_: *mut leanh::LeanObject,
    mut v_a_591_: *mut leanh::LeanObject,
    mut v_a_592_: *mut leanh::LeanObject,
    mut v_a_593_: *mut leanh::LeanObject,
    mut v_a_594_: *mut leanh::LeanObject,
    mut v_a_595_: *mut leanh::LeanObject,
    mut v_a_596_: *mut leanh::LeanObject,
    mut v_a_597_: *mut leanh::LeanObject,
    mut v_a_598_: *mut leanh::LeanObject,
    mut v_a_599_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_603_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_601_ = l_Lean_Meta_Grind_Arith_Linear_RingEqCnstr_cleanupDenominators___closed__0;
    v___f_602_ = l_Lean_Meta_Grind_Arith_Linear_RingEqCnstr_cleanupDenominators___closed__1;
    v___x_603_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Den_0__Lean_Meta_Grind_Arith_Linear_cleanupDenominators_x27___redArg(v_c_588_, v___f_601_, v___f_602_, v_a_589_, v_a_590_, v_a_591_, v_a_592_, v_a_593_, v_a_594_, v_a_595_, v_a_596_, v_a_597_, v_a_598_, v_a_599_);
    return v___x_603_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_RingEqCnstr_cleanupDenominators___boxed(
    mut v_c_604_: *mut leanh::LeanObject,
    mut v_a_605_: *mut leanh::LeanObject,
    mut v_a_606_: *mut leanh::LeanObject,
    mut v_a_607_: *mut leanh::LeanObject,
    mut v_a_608_: *mut leanh::LeanObject,
    mut v_a_609_: *mut leanh::LeanObject,
    mut v_a_610_: *mut leanh::LeanObject,
    mut v_a_611_: *mut leanh::LeanObject,
    mut v_a_612_: *mut leanh::LeanObject,
    mut v_a_613_: *mut leanh::LeanObject,
    mut v_a_614_: *mut leanh::LeanObject,
    mut v_a_615_: *mut leanh::LeanObject,
    mut v_a_616_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_617_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_617_ = l_Lean_Meta_Grind_Arith_Linear_RingEqCnstr_cleanupDenominators(
        v_c_604_, v_a_605_, v_a_606_, v_a_607_, v_a_608_, v_a_609_, v_a_610_, v_a_611_, v_a_612_,
        v_a_613_, v_a_614_, v_a_615_,
    );
    leanh::lean_dec(v_a_615_);
    leanh::lean_dec_ref(v_a_614_);
    leanh::lean_dec(v_a_613_);
    leanh::lean_dec_ref(v_a_612_);
    leanh::lean_dec(v_a_611_);
    leanh::lean_dec_ref(v_a_610_);
    leanh::lean_dec(v_a_609_);
    leanh::lean_dec_ref(v_a_608_);
    leanh::lean_dec(v_a_607_);
    leanh::lean_dec(v_a_606_);
    leanh::lean_dec(v_a_605_);
    return v_res_617_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstr_cleanupDenominators___lam__0(
    mut v_x_618_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_p_619_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_p_619_ = leanh::lean_ctor_get(v_x_618_, 0);
    leanh::lean_inc_ref(v_p_619_);
    return v_p_619_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstr_cleanupDenominators___lam__0___boxed(
    mut v_x_620_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_621_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_621_ =
        l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstr_cleanupDenominators___lam__0(v_x_620_);
    leanh::lean_dec_ref(v_x_620_);
    return v_res_621_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstr_cleanupDenominators___lam__1(
    mut v_c_622_: *mut leanh::LeanObject,
    mut v_p_623_: *mut leanh::LeanObject,
    mut v_val_624_: *mut leanh::LeanObject,
    mut v_x_625_: *mut leanh::LeanObject,
    mut v_n_626_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_628_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_627_ = leanh::lean_alloc_ctor(1, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_627_, 0, v_c_622_);
    leanh::lean_ctor_set(v___x_627_, 1, v_val_624_);
    leanh::lean_ctor_set(v___x_627_, 2, v_x_625_);
    leanh::lean_ctor_set(v___x_627_, 3, v_n_626_);
    v___x_628_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_628_, 0, v_p_623_);
    leanh::lean_ctor_set(v___x_628_, 1, v___x_627_);
    return v___x_628_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstr_cleanupDenominators(
    mut v_c_631_: *mut leanh::LeanObject,
    mut v_a_632_: *mut leanh::LeanObject,
    mut v_a_633_: *mut leanh::LeanObject,
    mut v_a_634_: *mut leanh::LeanObject,
    mut v_a_635_: *mut leanh::LeanObject,
    mut v_a_636_: *mut leanh::LeanObject,
    mut v_a_637_: *mut leanh::LeanObject,
    mut v_a_638_: *mut leanh::LeanObject,
    mut v_a_639_: *mut leanh::LeanObject,
    mut v_a_640_: *mut leanh::LeanObject,
    mut v_a_641_: *mut leanh::LeanObject,
    mut v_a_642_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_648_: u8 = 0;
    let mut v_noNatDivInst_x3f_649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_656_: u8 = 0;
    let mut v_a_657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_660_: u8 = 0;
    let mut v___x_662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_664_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_644_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(
                    v_a_632_, v_a_633_, v_a_634_, v_a_635_, v_a_636_, v_a_637_, v_a_638_, v_a_639_,
                    v_a_640_, v_a_641_, v_a_642_,
                );
                if leanh::lean_obj_tag(v___x_644_) == 0 {
                    v_a_645_ = leanh::lean_ctor_get(v___x_644_, 0);
                    v_isSharedCheck_656_ = (!leanh::lean_is_exclusive(v___x_644_)) as u8;
                    if v_isSharedCheck_656_ == 0 {
                        v___x_647_ = v___x_644_;
                        v_isShared_648_ = v_isSharedCheck_656_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_645_);
                        leanh::lean_dec(v___x_644_);
                        v___x_647_ = leanh::lean_box(0);
                        v_isShared_648_ = v_isSharedCheck_656_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_c_631_);
                    v_a_657_ = leanh::lean_ctor_get(v___x_644_, 0);
                    v_isSharedCheck_664_ = (!leanh::lean_is_exclusive(v___x_644_)) as u8;
                    if v_isSharedCheck_664_ == 0 {
                        v___x_659_ = v___x_644_;
                        v_isShared_660_ = v_isSharedCheck_664_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_657_);
                        leanh::lean_dec(v___x_644_);
                        v___x_659_ = leanh::lean_box(0);
                        v_isShared_660_ = v_isSharedCheck_664_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_noNatDivInst_x3f_649_ = leanh::lean_ctor_get(v_a_645_, 11);
                leanh::lean_inc(v_noNatDivInst_x3f_649_);
                leanh::lean_dec(v_a_645_);
                if leanh::lean_obj_tag(v_noNatDivInst_x3f_649_) == 0 {
                    if v_isShared_648_ == 0 {
                        leanh::lean_ctor_set(v___x_647_, 0, v_c_631_);
                        v___x_651_ = v___x_647_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_652_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_652_, 0, v_c_631_);
                        v___x_651_ = v_reuseFailAlloc_652_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref_known(v_noNatDivInst_x3f_649_, 1);
                    leanh::lean_del_object(v___x_647_);
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
                    v_reuseFailAlloc_663_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_663_, 0, v_a_657_);
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
    mut v_c_665_: *mut leanh::LeanObject,
    mut v_a_666_: *mut leanh::LeanObject,
    mut v_a_667_: *mut leanh::LeanObject,
    mut v_a_668_: *mut leanh::LeanObject,
    mut v_a_669_: *mut leanh::LeanObject,
    mut v_a_670_: *mut leanh::LeanObject,
    mut v_a_671_: *mut leanh::LeanObject,
    mut v_a_672_: *mut leanh::LeanObject,
    mut v_a_673_: *mut leanh::LeanObject,
    mut v_a_674_: *mut leanh::LeanObject,
    mut v_a_675_: *mut leanh::LeanObject,
    mut v_a_676_: *mut leanh::LeanObject,
    mut v_a_677_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_678_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_678_ = l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstr_cleanupDenominators(
        v_c_665_, v_a_666_, v_a_667_, v_a_668_, v_a_669_, v_a_670_, v_a_671_, v_a_672_, v_a_673_,
        v_a_674_, v_a_675_, v_a_676_,
    );
    leanh::lean_dec(v_a_676_);
    leanh::lean_dec_ref(v_a_675_);
    leanh::lean_dec(v_a_674_);
    leanh::lean_dec_ref(v_a_673_);
    leanh::lean_dec(v_a_672_);
    leanh::lean_dec_ref(v_a_671_);
    leanh::lean_dec(v_a_670_);
    leanh::lean_dec_ref(v_a_669_);
    leanh::lean_dec(v_a_668_);
    leanh::lean_dec(v_a_667_);
    leanh::lean_dec(v_a_666_);
    return v_res_678_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Den(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Den(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Den(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Den(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Den(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Den(builtin);
}