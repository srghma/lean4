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
use crate::lean_imports_rs::Init::Data::Int::Basic::lean_nat_to_int;
use crate::lean_imports_rs::Init::Prelude::lean_nat_dec_eq;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_5, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set,
    lean_ctor_set_uint8, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc,
    lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_tag,
    lean_unsigned_to_nat,
};
pub static l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstr_cleanupDenominators___closed__0_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
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
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstr_cleanupDenominators___closed__0_value
) as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstr_cleanupDenominators___closed__1_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
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
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstr_cleanupDenominators___closed__1_value
) as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_Linear_RingEqCnstr_cleanupDenominators___closed__0_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
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
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_Linear_RingEqCnstr_cleanupDenominators___closed__0_value
) as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_Linear_RingEqCnstr_cleanupDenominators___closed__1_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
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
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_Linear_RingEqCnstr_cleanupDenominators___closed__1_value
) as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstr_cleanupDenominators___closed__0_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
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
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstr_cleanupDenominators___closed__0_value
) as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstr_cleanupDenominators___closed__1_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
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
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstr_cleanupDenominators___closed__1_value
) as *mut LeanObject;
pub unsafe fn l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Den_0__Lean_Meta_Grind_Arith_Linear_cleanupDenominators_x27_go_spec__0(
    mut v_a_340_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_341_: *mut LeanObject = core::ptr::null_mut();
    v___x_341_ = lean_nat_to_int(v_a_340_);
    return v___x_341_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Den_0__Lean_Meta_Grind_Arith_Linear_cleanupDenominators_x27_go___redArg(
    mut v_getPoly_342_: *mut LeanObject,
    mut v_updateCnstr_343_: *mut LeanObject,
    mut v_c_344_: *mut LeanObject,
    mut v_a_345_: *mut LeanObject,
    mut v_a_346_: *mut LeanObject,
    mut v_a_347_: *mut LeanObject,
    mut v_a_348_: *mut LeanObject,
    mut v_a_349_: *mut LeanObject,
    mut v_a_350_: *mut LeanObject,
    mut v_a_351_: *mut LeanObject,
    mut v_a_352_: *mut LeanObject,
    mut v_a_353_: *mut LeanObject,
    mut v_a_354_: *mut LeanObject,
    mut v_a_355_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_p_357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_358_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_362_: u8 = 0;
    let mut v_val_363_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_364_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_374_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_376_: u8 = 0;
    let mut v_a_377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_380_: u8 = 0;
    let mut v___x_382_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_383_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_384_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_getPoly_342_);
                lean_inc(v_c_344_);
                v_p_357_ = lean_apply_1(v_getPoly_342_, v_c_344_);
                lean_inc_ref(v_p_357_);
                v___x_358_ = l_Lean_Grind_CommRing_Poly_findInvNumeralVar_x3f(
                    v_p_357_, v_a_345_, v_a_346_, v_a_347_, v_a_348_, v_a_349_, v_a_350_, v_a_351_,
                    v_a_352_, v_a_353_, v_a_354_, v_a_355_,
                );
                if lean_obj_tag(v___x_358_) == 0 {
                    v_a_359_ = lean_ctor_get(v___x_358_, 0);
                    v_isSharedCheck_376_ = (!lean_is_exclusive(v___x_358_)) as u8;
                    if v_isSharedCheck_376_ == 0 {
                        v___x_361_ = v___x_358_;
                        v_isShared_362_ = v_isSharedCheck_376_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_359_);
                        lean_dec(v___x_358_);
                        v___x_361_ = lean_box(0);
                        v_isShared_362_ = v_isSharedCheck_376_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_p_357_);
                    lean_dec(v_c_344_);
                    lean_dec(v_updateCnstr_343_);
                    lean_dec_ref(v_getPoly_342_);
                    v_a_377_ = lean_ctor_get(v___x_358_, 0);
                    v_isSharedCheck_384_ = (!lean_is_exclusive(v___x_358_)) as u8;
                    if v_isSharedCheck_384_ == 0 {
                        v___x_379_ = v___x_358_;
                        v_isShared_380_ = v_isSharedCheck_384_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_377_);
                        lean_dec(v___x_358_);
                        v___x_379_ = lean_box(0);
                        v_isShared_380_ = v_isSharedCheck_384_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_359_) == 1 {
                    lean_del_object(v___x_361_);
                    v_val_363_ = lean_ctor_get(v_a_359_, 0);
                    lean_inc(v_val_363_);
                    lean_dec_ref_known(v_a_359_, 1);
                    v_fst_364_ = lean_ctor_get(v_val_363_, 0);
                    lean_inc(v_fst_364_);
                    v_snd_365_ = lean_ctor_get(v_val_363_, 1);
                    lean_inc(v_snd_365_);
                    lean_dec(v_val_363_);
                    v___x_366_ = l_Lean_Grind_CommRing_Poly_maxDegreeOf(v_p_357_, v_snd_365_);
                    v___x_367_ = lean_nat_to_int(v_fst_364_);
                    v___x_368_ = l_Int_pow(v___x_367_, v___x_366_);
                    v___x_369_ = l_Lean_Grind_CommRing_Poly_mulConst(v___x_368_, v_p_357_);
                    lean_dec(v___x_368_);
                    v___x_370_ =
                        l_Lean_Grind_CommRing_Poly_cancelVar(v___x_367_, v_snd_365_, v___x_369_);
                    lean_inc(v_updateCnstr_343_);
                    v___x_371_ = lean_apply_5(
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
                    lean_dec(v_a_359_);
                    lean_dec_ref(v_p_357_);
                    lean_dec(v_updateCnstr_343_);
                    lean_dec_ref(v_getPoly_342_);
                    if v_isShared_362_ == 0 {
                        lean_ctor_set(v___x_361_, 0, v_c_344_);
                        v___x_374_ = v___x_361_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_375_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_375_, 0, v_c_344_);
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
                    v_reuseFailAlloc_383_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_383_, 0, v_a_377_);
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
    mut v_getPoly_385_: *mut LeanObject,
    mut v_updateCnstr_386_: *mut LeanObject,
    mut v_c_387_: *mut LeanObject,
    mut v_a_388_: *mut LeanObject,
    mut v_a_389_: *mut LeanObject,
    mut v_a_390_: *mut LeanObject,
    mut v_a_391_: *mut LeanObject,
    mut v_a_392_: *mut LeanObject,
    mut v_a_393_: *mut LeanObject,
    mut v_a_394_: *mut LeanObject,
    mut v_a_395_: *mut LeanObject,
    mut v_a_396_: *mut LeanObject,
    mut v_a_397_: *mut LeanObject,
    mut v_a_398_: *mut LeanObject,
    mut v_a_399_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_400_: *mut LeanObject = core::ptr::null_mut();
    v_res_400_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Den_0__Lean_Meta_Grind_Arith_Linear_cleanupDenominators_x27_go___redArg(v_getPoly_385_, v_updateCnstr_386_, v_c_387_, v_a_388_, v_a_389_, v_a_390_, v_a_391_, v_a_392_, v_a_393_, v_a_394_, v_a_395_, v_a_396_, v_a_397_, v_a_398_);
    lean_dec(v_a_398_);
    lean_dec_ref(v_a_397_);
    lean_dec(v_a_396_);
    lean_dec_ref(v_a_395_);
    lean_dec(v_a_394_);
    lean_dec_ref(v_a_393_);
    lean_dec(v_a_392_);
    lean_dec_ref(v_a_391_);
    lean_dec(v_a_390_);
    lean_dec(v_a_389_);
    lean_dec_ref(v_a_388_);
    return v_res_400_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Den_0__Lean_Meta_Grind_Arith_Linear_cleanupDenominators_x27_go(
    mut v_00_u03b1_401_: *mut LeanObject,
    mut v_getPoly_402_: *mut LeanObject,
    mut v_updateCnstr_403_: *mut LeanObject,
    mut v_c_404_: *mut LeanObject,
    mut v_a_405_: *mut LeanObject,
    mut v_a_406_: *mut LeanObject,
    mut v_a_407_: *mut LeanObject,
    mut v_a_408_: *mut LeanObject,
    mut v_a_409_: *mut LeanObject,
    mut v_a_410_: *mut LeanObject,
    mut v_a_411_: *mut LeanObject,
    mut v_a_412_: *mut LeanObject,
    mut v_a_413_: *mut LeanObject,
    mut v_a_414_: *mut LeanObject,
    mut v_a_415_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_417_: *mut LeanObject = core::ptr::null_mut();
    v___x_417_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Den_0__Lean_Meta_Grind_Arith_Linear_cleanupDenominators_x27_go___redArg(v_getPoly_402_, v_updateCnstr_403_, v_c_404_, v_a_405_, v_a_406_, v_a_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_, v_a_415_);
    return v___x_417_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Den_0__Lean_Meta_Grind_Arith_Linear_cleanupDenominators_x27_go___boxed(
    mut v_00_u03b1_418_: *mut LeanObject,
    mut v_getPoly_419_: *mut LeanObject,
    mut v_updateCnstr_420_: *mut LeanObject,
    mut v_c_421_: *mut LeanObject,
    mut v_a_422_: *mut LeanObject,
    mut v_a_423_: *mut LeanObject,
    mut v_a_424_: *mut LeanObject,
    mut v_a_425_: *mut LeanObject,
    mut v_a_426_: *mut LeanObject,
    mut v_a_427_: *mut LeanObject,
    mut v_a_428_: *mut LeanObject,
    mut v_a_429_: *mut LeanObject,
    mut v_a_430_: *mut LeanObject,
    mut v_a_431_: *mut LeanObject,
    mut v_a_432_: *mut LeanObject,
    mut v_a_433_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_434_: *mut LeanObject = core::ptr::null_mut();
    v_res_434_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Den_0__Lean_Meta_Grind_Arith_Linear_cleanupDenominators_x27_go(v_00_u03b1_418_, v_getPoly_419_, v_updateCnstr_420_, v_c_421_, v_a_422_, v_a_423_, v_a_424_, v_a_425_, v_a_426_, v_a_427_, v_a_428_, v_a_429_, v_a_430_, v_a_431_, v_a_432_);
    lean_dec(v_a_432_);
    lean_dec_ref(v_a_431_);
    lean_dec(v_a_430_);
    lean_dec_ref(v_a_429_);
    lean_dec(v_a_428_);
    lean_dec_ref(v_a_427_);
    lean_dec(v_a_426_);
    lean_dec_ref(v_a_425_);
    lean_dec(v_a_424_);
    lean_dec(v_a_423_);
    lean_dec_ref(v_a_422_);
    return v_res_434_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Den_0__Lean_Meta_Grind_Arith_Linear_cleanupDenominators_x27___redArg(
    mut v_c_435_: *mut LeanObject,
    mut v_getPoly_436_: *mut LeanObject,
    mut v_updateCnstr_437_: *mut LeanObject,
    mut v_a_438_: *mut LeanObject,
    mut v_a_439_: *mut LeanObject,
    mut v_a_440_: *mut LeanObject,
    mut v_a_441_: *mut LeanObject,
    mut v_a_442_: *mut LeanObject,
    mut v_a_443_: *mut LeanObject,
    mut v_a_444_: *mut LeanObject,
    mut v_a_445_: *mut LeanObject,
    mut v_a_446_: *mut LeanObject,
    mut v_a_447_: *mut LeanObject,
    mut v_a_448_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_450_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_454_: u8 = 0;
    let mut v_fieldInst_x3f_455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_charInst_x3f_459_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_460_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_463_: u8 = 0;
    let mut v___x_465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_470_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_472_: u8 = 0;
    let mut v_a_473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_476_: u8 = 0;
    let mut v___x_478_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_480_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_450_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(
                    v_a_438_, v_a_439_, v_a_440_, v_a_441_, v_a_442_, v_a_443_, v_a_444_, v_a_445_,
                    v_a_446_, v_a_447_, v_a_448_,
                );
                if lean_obj_tag(v___x_450_) == 0 {
                    v_a_451_ = lean_ctor_get(v___x_450_, 0);
                    v_isSharedCheck_472_ = (!lean_is_exclusive(v___x_450_)) as u8;
                    if v_isSharedCheck_472_ == 0 {
                        v___x_453_ = v___x_450_;
                        v_isShared_454_ = v_isSharedCheck_472_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_451_);
                        lean_dec(v___x_450_);
                        v___x_453_ = lean_box(0);
                        v_isShared_454_ = v_isSharedCheck_472_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_updateCnstr_437_);
                    lean_dec_ref(v_getPoly_436_);
                    lean_dec(v_c_435_);
                    v_a_473_ = lean_ctor_get(v___x_450_, 0);
                    v_isSharedCheck_480_ = (!lean_is_exclusive(v___x_450_)) as u8;
                    if v_isSharedCheck_480_ == 0 {
                        v___x_475_ = v___x_450_;
                        v_isShared_476_ = v_isSharedCheck_480_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_473_);
                        lean_dec(v___x_450_);
                        v___x_475_ = lean_box(0);
                        v_isShared_476_ = v_isSharedCheck_480_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_fieldInst_x3f_455_ = lean_ctor_get(v_a_451_, 15);
                if lean_obj_tag(v_fieldInst_x3f_455_) == 0 {
                    lean_dec(v_a_451_);
                    lean_dec(v_updateCnstr_437_);
                    lean_dec_ref(v_getPoly_436_);
                    if v_isShared_454_ == 0 {
                        lean_ctor_set(v___x_453_, 0, v_c_435_);
                        v___x_457_ = v___x_453_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_458_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_458_, 0, v_c_435_);
                        v___x_457_ = v_reuseFailAlloc_458_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_charInst_x3f_459_ = lean_ctor_get(v_a_451_, 16);
                    lean_inc(v_charInst_x3f_459_);
                    lean_dec(v_a_451_);
                    if lean_obj_tag(v_charInst_x3f_459_) == 1 {
                        v_val_460_ = lean_ctor_get(v_charInst_x3f_459_, 0);
                        lean_inc(v_val_460_);
                        lean_dec_ref_known(v_charInst_x3f_459_, 1);
                        v_snd_461_ = lean_ctor_get(v_val_460_, 1);
                        lean_inc(v_snd_461_);
                        lean_dec(v_val_460_);
                        v___x_462_ = lean_unsigned_to_nat(0);
                        v___x_463_ = lean_nat_dec_eq(v_snd_461_, v___x_462_);
                        lean_dec(v_snd_461_);
                        if v___x_463_ == 0 {
                            lean_dec(v_updateCnstr_437_);
                            lean_dec_ref(v_getPoly_436_);
                            if v_isShared_454_ == 0 {
                                lean_ctor_set(v___x_453_, 0, v_c_435_);
                                v___x_465_ = v___x_453_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_466_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_466_, 0, v_c_435_);
                                v___x_465_ = v_reuseFailAlloc_466_;
                                state = 3;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_453_);
                            v___x_467_ = lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Den_0__Lean_Meta_Grind_Arith_Linear_cleanupDenominators_x27_go___boxed as *mut core::ffi::c_void, 16, 4);
                            lean_closure_set(v___x_467_, 0, lean_box(0));
                            lean_closure_set(v___x_467_, 1, v_getPoly_436_);
                            lean_closure_set(v___x_467_, 2, v_updateCnstr_437_);
                            lean_closure_set(v___x_467_, 3, v_c_435_);
                            v___x_468_ = l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(
                                v___x_467_, v_a_438_, v_a_439_, v_a_440_, v_a_441_, v_a_442_,
                                v_a_443_, v_a_444_, v_a_445_, v_a_446_, v_a_447_, v_a_448_,
                            );
                            return v___x_468_;
                        }
                    } else {
                        lean_dec(v_charInst_x3f_459_);
                        lean_dec(v_updateCnstr_437_);
                        lean_dec_ref(v_getPoly_436_);
                        if v_isShared_454_ == 0 {
                            lean_ctor_set(v___x_453_, 0, v_c_435_);
                            v___x_470_ = v___x_453_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_471_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_471_, 0, v_c_435_);
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
                    v_reuseFailAlloc_479_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_479_, 0, v_a_473_);
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
    mut v_c_481_: *mut LeanObject,
    mut v_getPoly_482_: *mut LeanObject,
    mut v_updateCnstr_483_: *mut LeanObject,
    mut v_a_484_: *mut LeanObject,
    mut v_a_485_: *mut LeanObject,
    mut v_a_486_: *mut LeanObject,
    mut v_a_487_: *mut LeanObject,
    mut v_a_488_: *mut LeanObject,
    mut v_a_489_: *mut LeanObject,
    mut v_a_490_: *mut LeanObject,
    mut v_a_491_: *mut LeanObject,
    mut v_a_492_: *mut LeanObject,
    mut v_a_493_: *mut LeanObject,
    mut v_a_494_: *mut LeanObject,
    mut v_a_495_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_496_: *mut LeanObject = core::ptr::null_mut();
    v_res_496_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Den_0__Lean_Meta_Grind_Arith_Linear_cleanupDenominators_x27___redArg(v_c_481_, v_getPoly_482_, v_updateCnstr_483_, v_a_484_, v_a_485_, v_a_486_, v_a_487_, v_a_488_, v_a_489_, v_a_490_, v_a_491_, v_a_492_, v_a_493_, v_a_494_);
    lean_dec(v_a_494_);
    lean_dec_ref(v_a_493_);
    lean_dec(v_a_492_);
    lean_dec_ref(v_a_491_);
    lean_dec(v_a_490_);
    lean_dec_ref(v_a_489_);
    lean_dec(v_a_488_);
    lean_dec_ref(v_a_487_);
    lean_dec(v_a_486_);
    lean_dec(v_a_485_);
    lean_dec(v_a_484_);
    return v_res_496_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Den_0__Lean_Meta_Grind_Arith_Linear_cleanupDenominators_x27(
    mut v_00_u03b1_497_: *mut LeanObject,
    mut v_c_498_: *mut LeanObject,
    mut v_getPoly_499_: *mut LeanObject,
    mut v_updateCnstr_500_: *mut LeanObject,
    mut v_a_501_: *mut LeanObject,
    mut v_a_502_: *mut LeanObject,
    mut v_a_503_: *mut LeanObject,
    mut v_a_504_: *mut LeanObject,
    mut v_a_505_: *mut LeanObject,
    mut v_a_506_: *mut LeanObject,
    mut v_a_507_: *mut LeanObject,
    mut v_a_508_: *mut LeanObject,
    mut v_a_509_: *mut LeanObject,
    mut v_a_510_: *mut LeanObject,
    mut v_a_511_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_513_: *mut LeanObject = core::ptr::null_mut();
    v___x_513_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Den_0__Lean_Meta_Grind_Arith_Linear_cleanupDenominators_x27___redArg(v_c_498_, v_getPoly_499_, v_updateCnstr_500_, v_a_501_, v_a_502_, v_a_503_, v_a_504_, v_a_505_, v_a_506_, v_a_507_, v_a_508_, v_a_509_, v_a_510_, v_a_511_);
    return v___x_513_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Den_0__Lean_Meta_Grind_Arith_Linear_cleanupDenominators_x27___boxed(
    mut v_00_u03b1_514_: *mut LeanObject,
    mut v_c_515_: *mut LeanObject,
    mut v_getPoly_516_: *mut LeanObject,
    mut v_updateCnstr_517_: *mut LeanObject,
    mut v_a_518_: *mut LeanObject,
    mut v_a_519_: *mut LeanObject,
    mut v_a_520_: *mut LeanObject,
    mut v_a_521_: *mut LeanObject,
    mut v_a_522_: *mut LeanObject,
    mut v_a_523_: *mut LeanObject,
    mut v_a_524_: *mut LeanObject,
    mut v_a_525_: *mut LeanObject,
    mut v_a_526_: *mut LeanObject,
    mut v_a_527_: *mut LeanObject,
    mut v_a_528_: *mut LeanObject,
    mut v_a_529_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_530_: *mut LeanObject = core::ptr::null_mut();
    v_res_530_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Den_0__Lean_Meta_Grind_Arith_Linear_cleanupDenominators_x27(v_00_u03b1_514_, v_c_515_, v_getPoly_516_, v_updateCnstr_517_, v_a_518_, v_a_519_, v_a_520_, v_a_521_, v_a_522_, v_a_523_, v_a_524_, v_a_525_, v_a_526_, v_a_527_, v_a_528_);
    lean_dec(v_a_528_);
    lean_dec_ref(v_a_527_);
    lean_dec(v_a_526_);
    lean_dec_ref(v_a_525_);
    lean_dec(v_a_524_);
    lean_dec_ref(v_a_523_);
    lean_dec(v_a_522_);
    lean_dec_ref(v_a_521_);
    lean_dec(v_a_520_);
    lean_dec(v_a_519_);
    lean_dec(v_a_518_);
    return v_res_530_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstr_cleanupDenominators___lam__0(
    mut v_x_531_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_p_532_: *mut LeanObject = core::ptr::null_mut();
    v_p_532_ = lean_ctor_get(v_x_531_, 0);
    lean_inc_ref(v_p_532_);
    return v_p_532_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstr_cleanupDenominators___lam__0___boxed(
    mut v_x_533_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_534_: *mut LeanObject = core::ptr::null_mut();
    v_res_534_ =
        l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstr_cleanupDenominators___lam__0(v_x_533_);
    lean_dec_ref(v_x_533_);
    return v_res_534_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstr_cleanupDenominators___lam__1(
    mut v_c_535_: *mut LeanObject,
    mut v_p_536_: *mut LeanObject,
    mut v_val_537_: *mut LeanObject,
    mut v_x_538_: *mut LeanObject,
    mut v_n_539_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_strict_540_: u8 = 0;
    let mut v___x_541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_542_: *mut LeanObject = core::ptr::null_mut();
    v_strict_540_ = lean_ctor_get_uint8(
        v_c_535_,
        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
    );
    v___x_541_ = lean_alloc_ctor(2, 4, (0) as u32);
    lean_ctor_set(v___x_541_, 0, v_c_535_);
    lean_ctor_set(v___x_541_, 1, v_val_537_);
    lean_ctor_set(v___x_541_, 2, v_x_538_);
    lean_ctor_set(v___x_541_, 3, v_n_539_);
    v___x_542_ = lean_alloc_ctor(0, 2, (1) as u32);
    lean_ctor_set(v___x_542_, 0, v_p_536_);
    lean_ctor_set(v___x_542_, 1, v___x_541_);
    lean_ctor_set_uint8(
        v___x_542_,
        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
        v_strict_540_,
    );
    return v___x_542_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstr_cleanupDenominators(
    mut v_c_545_: *mut LeanObject,
    mut v_a_546_: *mut LeanObject,
    mut v_a_547_: *mut LeanObject,
    mut v_a_548_: *mut LeanObject,
    mut v_a_549_: *mut LeanObject,
    mut v_a_550_: *mut LeanObject,
    mut v_a_551_: *mut LeanObject,
    mut v_a_552_: *mut LeanObject,
    mut v_a_553_: *mut LeanObject,
    mut v_a_554_: *mut LeanObject,
    mut v_a_555_: *mut LeanObject,
    mut v_a_556_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_560_: *mut LeanObject = core::ptr::null_mut();
    v___f_558_ = l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstr_cleanupDenominators___closed__0;
    v___f_559_ = l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstr_cleanupDenominators___closed__1;
    v___x_560_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Den_0__Lean_Meta_Grind_Arith_Linear_cleanupDenominators_x27___redArg(v_c_545_, v___f_558_, v___f_559_, v_a_546_, v_a_547_, v_a_548_, v_a_549_, v_a_550_, v_a_551_, v_a_552_, v_a_553_, v_a_554_, v_a_555_, v_a_556_);
    return v___x_560_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstr_cleanupDenominators___boxed(
    mut v_c_561_: *mut LeanObject,
    mut v_a_562_: *mut LeanObject,
    mut v_a_563_: *mut LeanObject,
    mut v_a_564_: *mut LeanObject,
    mut v_a_565_: *mut LeanObject,
    mut v_a_566_: *mut LeanObject,
    mut v_a_567_: *mut LeanObject,
    mut v_a_568_: *mut LeanObject,
    mut v_a_569_: *mut LeanObject,
    mut v_a_570_: *mut LeanObject,
    mut v_a_571_: *mut LeanObject,
    mut v_a_572_: *mut LeanObject,
    mut v_a_573_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_574_: *mut LeanObject = core::ptr::null_mut();
    v_res_574_ = l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstr_cleanupDenominators(
        v_c_561_, v_a_562_, v_a_563_, v_a_564_, v_a_565_, v_a_566_, v_a_567_, v_a_568_, v_a_569_,
        v_a_570_, v_a_571_, v_a_572_,
    );
    lean_dec(v_a_572_);
    lean_dec_ref(v_a_571_);
    lean_dec(v_a_570_);
    lean_dec_ref(v_a_569_);
    lean_dec(v_a_568_);
    lean_dec_ref(v_a_567_);
    lean_dec(v_a_566_);
    lean_dec_ref(v_a_565_);
    lean_dec(v_a_564_);
    lean_dec(v_a_563_);
    lean_dec(v_a_562_);
    return v_res_574_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_RingEqCnstr_cleanupDenominators___lam__0(
    mut v_x_575_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_p_576_: *mut LeanObject = core::ptr::null_mut();
    v_p_576_ = lean_ctor_get(v_x_575_, 0);
    lean_inc_ref(v_p_576_);
    return v_p_576_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_RingEqCnstr_cleanupDenominators___lam__0___boxed(
    mut v_x_577_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_578_: *mut LeanObject = core::ptr::null_mut();
    v_res_578_ = l_Lean_Meta_Grind_Arith_Linear_RingEqCnstr_cleanupDenominators___lam__0(v_x_577_);
    lean_dec_ref(v_x_577_);
    return v_res_578_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_RingEqCnstr_cleanupDenominators___lam__1(
    mut v_c_579_: *mut LeanObject,
    mut v_p_580_: *mut LeanObject,
    mut v_val_581_: *mut LeanObject,
    mut v_x_582_: *mut LeanObject,
    mut v_n_583_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_585_: *mut LeanObject = core::ptr::null_mut();
    v___x_584_ = lean_alloc_ctor(2, 4, (0) as u32);
    lean_ctor_set(v___x_584_, 0, v_c_579_);
    lean_ctor_set(v___x_584_, 1, v_val_581_);
    lean_ctor_set(v___x_584_, 2, v_x_582_);
    lean_ctor_set(v___x_584_, 3, v_n_583_);
    v___x_585_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_585_, 0, v_p_580_);
    lean_ctor_set(v___x_585_, 1, v___x_584_);
    return v___x_585_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_RingEqCnstr_cleanupDenominators(
    mut v_c_588_: *mut LeanObject,
    mut v_a_589_: *mut LeanObject,
    mut v_a_590_: *mut LeanObject,
    mut v_a_591_: *mut LeanObject,
    mut v_a_592_: *mut LeanObject,
    mut v_a_593_: *mut LeanObject,
    mut v_a_594_: *mut LeanObject,
    mut v_a_595_: *mut LeanObject,
    mut v_a_596_: *mut LeanObject,
    mut v_a_597_: *mut LeanObject,
    mut v_a_598_: *mut LeanObject,
    mut v_a_599_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_603_: *mut LeanObject = core::ptr::null_mut();
    v___f_601_ = l_Lean_Meta_Grind_Arith_Linear_RingEqCnstr_cleanupDenominators___closed__0;
    v___f_602_ = l_Lean_Meta_Grind_Arith_Linear_RingEqCnstr_cleanupDenominators___closed__1;
    v___x_603_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Den_0__Lean_Meta_Grind_Arith_Linear_cleanupDenominators_x27___redArg(v_c_588_, v___f_601_, v___f_602_, v_a_589_, v_a_590_, v_a_591_, v_a_592_, v_a_593_, v_a_594_, v_a_595_, v_a_596_, v_a_597_, v_a_598_, v_a_599_);
    return v___x_603_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_RingEqCnstr_cleanupDenominators___boxed(
    mut v_c_604_: *mut LeanObject,
    mut v_a_605_: *mut LeanObject,
    mut v_a_606_: *mut LeanObject,
    mut v_a_607_: *mut LeanObject,
    mut v_a_608_: *mut LeanObject,
    mut v_a_609_: *mut LeanObject,
    mut v_a_610_: *mut LeanObject,
    mut v_a_611_: *mut LeanObject,
    mut v_a_612_: *mut LeanObject,
    mut v_a_613_: *mut LeanObject,
    mut v_a_614_: *mut LeanObject,
    mut v_a_615_: *mut LeanObject,
    mut v_a_616_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_617_: *mut LeanObject = core::ptr::null_mut();
    v_res_617_ = l_Lean_Meta_Grind_Arith_Linear_RingEqCnstr_cleanupDenominators(
        v_c_604_, v_a_605_, v_a_606_, v_a_607_, v_a_608_, v_a_609_, v_a_610_, v_a_611_, v_a_612_,
        v_a_613_, v_a_614_, v_a_615_,
    );
    lean_dec(v_a_615_);
    lean_dec_ref(v_a_614_);
    lean_dec(v_a_613_);
    lean_dec_ref(v_a_612_);
    lean_dec(v_a_611_);
    lean_dec_ref(v_a_610_);
    lean_dec(v_a_609_);
    lean_dec_ref(v_a_608_);
    lean_dec(v_a_607_);
    lean_dec(v_a_606_);
    lean_dec(v_a_605_);
    return v_res_617_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstr_cleanupDenominators___lam__0(
    mut v_x_618_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_p_619_: *mut LeanObject = core::ptr::null_mut();
    v_p_619_ = lean_ctor_get(v_x_618_, 0);
    lean_inc_ref(v_p_619_);
    return v_p_619_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstr_cleanupDenominators___lam__0___boxed(
    mut v_x_620_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_621_: *mut LeanObject = core::ptr::null_mut();
    v_res_621_ =
        l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstr_cleanupDenominators___lam__0(v_x_620_);
    lean_dec_ref(v_x_620_);
    return v_res_621_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstr_cleanupDenominators___lam__1(
    mut v_c_622_: *mut LeanObject,
    mut v_p_623_: *mut LeanObject,
    mut v_val_624_: *mut LeanObject,
    mut v_x_625_: *mut LeanObject,
    mut v_n_626_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_628_: *mut LeanObject = core::ptr::null_mut();
    v___x_627_ = lean_alloc_ctor(1, 4, (0) as u32);
    lean_ctor_set(v___x_627_, 0, v_c_622_);
    lean_ctor_set(v___x_627_, 1, v_val_624_);
    lean_ctor_set(v___x_627_, 2, v_x_625_);
    lean_ctor_set(v___x_627_, 3, v_n_626_);
    v___x_628_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_628_, 0, v_p_623_);
    lean_ctor_set(v___x_628_, 1, v___x_627_);
    return v___x_628_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstr_cleanupDenominators(
    mut v_c_631_: *mut LeanObject,
    mut v_a_632_: *mut LeanObject,
    mut v_a_633_: *mut LeanObject,
    mut v_a_634_: *mut LeanObject,
    mut v_a_635_: *mut LeanObject,
    mut v_a_636_: *mut LeanObject,
    mut v_a_637_: *mut LeanObject,
    mut v_a_638_: *mut LeanObject,
    mut v_a_639_: *mut LeanObject,
    mut v_a_640_: *mut LeanObject,
    mut v_a_641_: *mut LeanObject,
    mut v_a_642_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_644_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_648_: u8 = 0;
    let mut v_noNatDivInst_x3f_649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_655_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_656_: u8 = 0;
    let mut v_a_657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_660_: u8 = 0;
    let mut v___x_662_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_664_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_644_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(
                    v_a_632_, v_a_633_, v_a_634_, v_a_635_, v_a_636_, v_a_637_, v_a_638_, v_a_639_,
                    v_a_640_, v_a_641_, v_a_642_,
                );
                if lean_obj_tag(v___x_644_) == 0 {
                    v_a_645_ = lean_ctor_get(v___x_644_, 0);
                    v_isSharedCheck_656_ = (!lean_is_exclusive(v___x_644_)) as u8;
                    if v_isSharedCheck_656_ == 0 {
                        v___x_647_ = v___x_644_;
                        v_isShared_648_ = v_isSharedCheck_656_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_645_);
                        lean_dec(v___x_644_);
                        v___x_647_ = lean_box(0);
                        v_isShared_648_ = v_isSharedCheck_656_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_c_631_);
                    v_a_657_ = lean_ctor_get(v___x_644_, 0);
                    v_isSharedCheck_664_ = (!lean_is_exclusive(v___x_644_)) as u8;
                    if v_isSharedCheck_664_ == 0 {
                        v___x_659_ = v___x_644_;
                        v_isShared_660_ = v_isSharedCheck_664_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_657_);
                        lean_dec(v___x_644_);
                        v___x_659_ = lean_box(0);
                        v_isShared_660_ = v_isSharedCheck_664_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_noNatDivInst_x3f_649_ = lean_ctor_get(v_a_645_, 11);
                lean_inc(v_noNatDivInst_x3f_649_);
                lean_dec(v_a_645_);
                if lean_obj_tag(v_noNatDivInst_x3f_649_) == 0 {
                    if v_isShared_648_ == 0 {
                        lean_ctor_set(v___x_647_, 0, v_c_631_);
                        v___x_651_ = v___x_647_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_652_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_652_, 0, v_c_631_);
                        v___x_651_ = v_reuseFailAlloc_652_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec_ref_known(v_noNatDivInst_x3f_649_, 1);
                    lean_del_object(v___x_647_);
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
                    v_reuseFailAlloc_663_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_663_, 0, v_a_657_);
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
    mut v_c_665_: *mut LeanObject,
    mut v_a_666_: *mut LeanObject,
    mut v_a_667_: *mut LeanObject,
    mut v_a_668_: *mut LeanObject,
    mut v_a_669_: *mut LeanObject,
    mut v_a_670_: *mut LeanObject,
    mut v_a_671_: *mut LeanObject,
    mut v_a_672_: *mut LeanObject,
    mut v_a_673_: *mut LeanObject,
    mut v_a_674_: *mut LeanObject,
    mut v_a_675_: *mut LeanObject,
    mut v_a_676_: *mut LeanObject,
    mut v_a_677_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_678_: *mut LeanObject = core::ptr::null_mut();
    v_res_678_ = l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstr_cleanupDenominators(
        v_c_665_, v_a_666_, v_a_667_, v_a_668_, v_a_669_, v_a_670_, v_a_671_, v_a_672_, v_a_673_,
        v_a_674_, v_a_675_, v_a_676_,
    );
    lean_dec(v_a_676_);
    lean_dec_ref(v_a_675_);
    lean_dec(v_a_674_);
    lean_dec_ref(v_a_673_);
    lean_dec(v_a_672_);
    lean_dec_ref(v_a_671_);
    lean_dec(v_a_670_);
    lean_dec_ref(v_a_669_);
    lean_dec(v_a_668_);
    lean_dec(v_a_667_);
    lean_dec(v_a_666_);
    return v_res_678_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Den(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Den(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Den(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Den(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Den(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Den(builtin);
}
