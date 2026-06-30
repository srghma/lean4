// Lean compiler output
// Module: Init.Data.Iterators.Combinators.Monadic.Append
// Imports: Init.Data.Iterators.Consumers.Monadic.Loop Init.Classical Init.Data.Option.Lemmas Init.ByCases Init.Omega
use crate::r#gen::Init::ByCases::{initialize_Init_ByCases, runtime_initialize_Init_ByCases};
use crate::r#gen::Init::Classical::{initialize_Init_Classical, runtime_initialize_Init_Classical};
use crate::r#gen::Init::Data::Iterators::Consumers::Monadic::Loop::{
    initialize_Init_Data_Iterators_Consumers_Monadic_Loop,
    runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Loop,
};
use crate::r#gen::Init::Data::Option::Lemmas::{
    initialize_Init_Data_Option_Lemmas, runtime_initialize_Init_Data_Option_Lemmas,
};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::WFExtrinsicFix::l_WellFounded_opaqueFix_u2083___redArg;
pub unsafe fn l_Std_Iterators_Types_Append_ctorIdx___redArg(
    mut v_x_310_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_310_) == 0 {
        let mut v___x_311_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_311_ = leanh::lean_unsigned_to_nat(0);
        return v___x_311_;
    } else {
        let mut v___x_312_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_312_ = leanh::lean_unsigned_to_nat(1);
        return v___x_312_;
    }
}
pub unsafe fn l_Std_Iterators_Types_Append_ctorIdx___redArg___boxed(
    mut v_x_313_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_314_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_314_ = l_Std_Iterators_Types_Append_ctorIdx___redArg(v_x_313_);
    leanh::lean_dec_ref(v_x_313_);
    return v_res_314_;
}
pub unsafe fn l_Std_Iterators_Types_Append_ctorIdx(
    mut v_00_u03b1_u2081_315_: *mut leanh::LeanObject,
    mut v_00_u03b1_u2082_316_: *mut leanh::LeanObject,
    mut v_m_317_: *mut leanh::LeanObject,
    mut v_00_u03b2_318_: *mut leanh::LeanObject,
    mut v_x_319_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_320_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_320_ = l_Std_Iterators_Types_Append_ctorIdx___redArg(v_x_319_);
    return v___x_320_;
}
pub unsafe fn l_Std_Iterators_Types_Append_ctorIdx___boxed(
    mut v_00_u03b1_u2081_321_: *mut leanh::LeanObject,
    mut v_00_u03b1_u2082_322_: *mut leanh::LeanObject,
    mut v_m_323_: *mut leanh::LeanObject,
    mut v_00_u03b2_324_: *mut leanh::LeanObject,
    mut v_x_325_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_326_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_326_ = l_Std_Iterators_Types_Append_ctorIdx(
        v_00_u03b1_u2081_321_,
        v_00_u03b1_u2082_322_,
        v_m_323_,
        v_00_u03b2_324_,
        v_x_325_,
    );
    leanh::lean_dec_ref(v_x_325_);
    return v_res_326_;
}
pub unsafe fn l_Std_Iterators_Types_Append_ctorElim___redArg(
    mut v_t_327_: *mut leanh::LeanObject,
    mut v_k_328_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_t_327_) == 0 {
        let mut v_a_329_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_330_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_331_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_a_329_ = leanh::lean_ctor_get(v_t_327_, 0);
        leanh::lean_inc(v_a_329_);
        v_a_330_ = leanh::lean_ctor_get(v_t_327_, 1);
        leanh::lean_inc(v_a_330_);
        leanh::lean_dec_ref_known(v_t_327_, 2);
        v___x_331_ = leanh::lean_apply_2(v_k_328_, v_a_329_, v_a_330_);
        return v___x_331_;
    } else {
        let mut v_a_332_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_333_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_a_332_ = leanh::lean_ctor_get(v_t_327_, 0);
        leanh::lean_inc(v_a_332_);
        leanh::lean_dec_ref_known(v_t_327_, 1);
        v___x_333_ = leanh::lean_apply_1(v_k_328_, v_a_332_);
        return v___x_333_;
    }
}
pub unsafe fn l_Std_Iterators_Types_Append_ctorElim(
    mut v_00_u03b1_u2081_334_: *mut leanh::LeanObject,
    mut v_00_u03b1_u2082_335_: *mut leanh::LeanObject,
    mut v_m_336_: *mut leanh::LeanObject,
    mut v_00_u03b2_337_: *mut leanh::LeanObject,
    mut v_motive_338_: *mut leanh::LeanObject,
    mut v_ctorIdx_339_: *mut leanh::LeanObject,
    mut v_t_340_: *mut leanh::LeanObject,
    mut v_h_341_: *mut leanh::LeanObject,
    mut v_k_342_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_343_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_343_ = l_Std_Iterators_Types_Append_ctorElim___redArg(v_t_340_, v_k_342_);
    return v___x_343_;
}
pub unsafe fn l_Std_Iterators_Types_Append_ctorElim___boxed(
    mut v_00_u03b1_u2081_344_: *mut leanh::LeanObject,
    mut v_00_u03b1_u2082_345_: *mut leanh::LeanObject,
    mut v_m_346_: *mut leanh::LeanObject,
    mut v_00_u03b2_347_: *mut leanh::LeanObject,
    mut v_motive_348_: *mut leanh::LeanObject,
    mut v_ctorIdx_349_: *mut leanh::LeanObject,
    mut v_t_350_: *mut leanh::LeanObject,
    mut v_h_351_: *mut leanh::LeanObject,
    mut v_k_352_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_353_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_353_ = l_Std_Iterators_Types_Append_ctorElim(
        v_00_u03b1_u2081_344_,
        v_00_u03b1_u2082_345_,
        v_m_346_,
        v_00_u03b2_347_,
        v_motive_348_,
        v_ctorIdx_349_,
        v_t_350_,
        v_h_351_,
        v_k_352_,
    );
    leanh::lean_dec(v_ctorIdx_349_);
    return v_res_353_;
}
pub unsafe fn l_Std_Iterators_Types_Append_fst_elim___redArg(
    mut v_t_354_: *mut leanh::LeanObject,
    mut v_fst_355_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_356_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_356_ = l_Std_Iterators_Types_Append_ctorElim___redArg(v_t_354_, v_fst_355_);
    return v___x_356_;
}
pub unsafe fn l_Std_Iterators_Types_Append_fst_elim(
    mut v_00_u03b1_u2081_357_: *mut leanh::LeanObject,
    mut v_00_u03b1_u2082_358_: *mut leanh::LeanObject,
    mut v_m_359_: *mut leanh::LeanObject,
    mut v_00_u03b2_360_: *mut leanh::LeanObject,
    mut v_motive_361_: *mut leanh::LeanObject,
    mut v_t_362_: *mut leanh::LeanObject,
    mut v_h_363_: *mut leanh::LeanObject,
    mut v_fst_364_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_365_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_365_ = l_Std_Iterators_Types_Append_ctorElim___redArg(v_t_362_, v_fst_364_);
    return v___x_365_;
}
pub unsafe fn l_Std_Iterators_Types_Append_snd_elim___redArg(
    mut v_t_366_: *mut leanh::LeanObject,
    mut v_snd_367_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_368_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_368_ = l_Std_Iterators_Types_Append_ctorElim___redArg(v_t_366_, v_snd_367_);
    return v___x_368_;
}
pub unsafe fn l_Std_Iterators_Types_Append_snd_elim(
    mut v_00_u03b1_u2081_369_: *mut leanh::LeanObject,
    mut v_00_u03b1_u2082_370_: *mut leanh::LeanObject,
    mut v_m_371_: *mut leanh::LeanObject,
    mut v_00_u03b2_372_: *mut leanh::LeanObject,
    mut v_motive_373_: *mut leanh::LeanObject,
    mut v_t_374_: *mut leanh::LeanObject,
    mut v_h_375_: *mut leanh::LeanObject,
    mut v_snd_376_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_377_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_377_ = l_Std_Iterators_Types_Append_ctorElim___redArg(v_t_374_, v_snd_376_);
    return v___x_377_;
}
pub unsafe fn l_Std_IterM_append___redArg(
    mut v_it_u2081_378_: *mut leanh::LeanObject,
    mut v_it_u2082_379_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_380_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_380_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_380_, 0, v_it_u2081_378_);
    leanh::lean_ctor_set(v___x_380_, 1, v_it_u2082_379_);
    return v___x_380_;
}
pub unsafe fn l_Std_IterM_append(
    mut v_m_381_: *mut leanh::LeanObject,
    mut v_00_u03b2_382_: *mut leanh::LeanObject,
    mut v_00_u03b1_u2081_383_: *mut leanh::LeanObject,
    mut v_00_u03b1_u2082_384_: *mut leanh::LeanObject,
    mut v_inst_385_: *mut leanh::LeanObject,
    mut v_inst_386_: *mut leanh::LeanObject,
    mut v_it_u2081_387_: *mut leanh::LeanObject,
    mut v_it_u2082_388_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_389_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_389_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_389_, 0, v_it_u2081_387_);
    leanh::lean_ctor_set(v___x_389_, 1, v_it_u2082_388_);
    return v___x_389_;
}
pub unsafe fn l_Std_IterM_append___boxed(
    mut v_m_390_: *mut leanh::LeanObject,
    mut v_00_u03b2_391_: *mut leanh::LeanObject,
    mut v_00_u03b1_u2081_392_: *mut leanh::LeanObject,
    mut v_00_u03b1_u2082_393_: *mut leanh::LeanObject,
    mut v_inst_394_: *mut leanh::LeanObject,
    mut v_inst_395_: *mut leanh::LeanObject,
    mut v_it_u2081_396_: *mut leanh::LeanObject,
    mut v_it_u2082_397_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_398_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_398_ = l_Std_IterM_append(
        v_m_390_,
        v_00_u03b2_391_,
        v_00_u03b1_u2081_392_,
        v_00_u03b1_u2082_393_,
        v_inst_394_,
        v_inst_395_,
        v_it_u2081_396_,
        v_it_u2082_397_,
    );
    leanh::lean_dec(v_inst_395_);
    leanh::lean_dec(v_inst_394_);
    return v_res_398_;
}
pub unsafe fn l_Std_IterM_Intermediate_appendSnd___redArg(
    mut v_it_u2082_399_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_400_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_400_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_400_, 0, v_it_u2082_399_);
    return v___x_400_;
}
pub unsafe fn l_Std_IterM_Intermediate_appendSnd(
    mut v_m_401_: *mut leanh::LeanObject,
    mut v_00_u03b2_402_: *mut leanh::LeanObject,
    mut v_00_u03b1_u2082_403_: *mut leanh::LeanObject,
    mut v_inst_404_: *mut leanh::LeanObject,
    mut v_00_u03b1_u2081_405_: *mut leanh::LeanObject,
    mut v_it_u2082_406_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_407_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_407_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_407_, 0, v_it_u2082_406_);
    return v___x_407_;
}
pub unsafe fn l_Std_IterM_Intermediate_appendSnd___boxed(
    mut v_m_408_: *mut leanh::LeanObject,
    mut v_00_u03b2_409_: *mut leanh::LeanObject,
    mut v_00_u03b1_u2082_410_: *mut leanh::LeanObject,
    mut v_inst_411_: *mut leanh::LeanObject,
    mut v_00_u03b1_u2081_412_: *mut leanh::LeanObject,
    mut v_it_u2082_413_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_414_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_414_ = l_Std_IterM_Intermediate_appendSnd(
        v_m_408_,
        v_00_u03b2_409_,
        v_00_u03b1_u2082_410_,
        v_inst_411_,
        v_00_u03b1_u2081_412_,
        v_it_u2082_413_,
    );
    leanh::lean_dec(v_inst_411_);
    return v_res_414_;
}
pub unsafe fn l_Std_Iterators_Types_Append_instIterator___redArg___lam__0(
    mut v_toPure_415_: *mut leanh::LeanObject,
    mut v_____do__lift_416_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_it_417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_out_418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_421_: u8 = 0;
    let mut v___x_422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_427_: u8 = 0;
    let mut v_it_428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_431_: u8 = 0;
    let mut v___x_432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_437_: u8 = 0;
    let mut v___x_438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_____do__lift_416_) {
                0 => {
                    v_it_417_ = leanh::lean_ctor_get(v_____do__lift_416_, 0);
                    v_out_418_ = leanh::lean_ctor_get(v_____do__lift_416_, 1);
                    v_isSharedCheck_427_ =
                        (!leanh::lean_is_exclusive(v_____do__lift_416_)) as u8;
                    if v_isSharedCheck_427_ == 0 {
                        v___x_420_ = v_____do__lift_416_;
                        v_isShared_421_ = v_isSharedCheck_427_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_out_418_);
                        leanh::lean_inc(v_it_417_);
                        leanh::lean_dec(v_____do__lift_416_);
                        v___x_420_ = leanh::lean_box(0);
                        v_isShared_421_ = v_isSharedCheck_427_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_it_428_ = leanh::lean_ctor_get(v_____do__lift_416_, 0);
                    v_isSharedCheck_437_ =
                        (!leanh::lean_is_exclusive(v_____do__lift_416_)) as u8;
                    if v_isSharedCheck_437_ == 0 {
                        v___x_430_ = v_____do__lift_416_;
                        v_isShared_431_ = v_isSharedCheck_437_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_it_428_);
                        leanh::lean_dec(v_____do__lift_416_);
                        v___x_430_ = leanh::lean_box(0);
                        v_isShared_431_ = v_isSharedCheck_437_;
                        state = 3;
                        continue;
                    }
                }
                _ => {
                    v___x_438_ = leanh::lean_box(2);
                    v___x_439_ = leanh::lean_apply_2(
                        v_toPure_415_,
                        leanh::lean_box(0),
                        v___x_438_,
                    );
                    return v___x_439_;
                }
            },
            1 => {
                v___x_422_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_422_, 0, v_it_417_);
                if v_isShared_421_ == 0 {
                    leanh::lean_ctor_set(v___x_420_, 0, v___x_422_);
                    v___x_424_ = v___x_420_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_426_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_426_, 0, v___x_422_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_426_, 1, v_out_418_);
                    v___x_424_ = v_reuseFailAlloc_426_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_425_ = leanh::lean_apply_2(
                    v_toPure_415_,
                    leanh::lean_box(0),
                    v___x_424_,
                );
                return v___x_425_;
            }
            3 => {
                v___x_432_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_432_, 0, v_it_428_);
                if v_isShared_431_ == 0 {
                    leanh::lean_ctor_set(v___x_430_, 0, v___x_432_);
                    v___x_434_ = v___x_430_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_436_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_436_, 0, v___x_432_);
                    v___x_434_ = v_reuseFailAlloc_436_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_435_ = leanh::lean_apply_2(
                    v_toPure_415_,
                    leanh::lean_box(0),
                    v___x_434_,
                );
                return v___x_435_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Iterators_Types_Append_instIterator___redArg___lam__1(
    mut v_a_440_: *mut leanh::LeanObject,
    mut v_toPure_441_: *mut leanh::LeanObject,
    mut v_____do__lift_442_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_it_443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_out_444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_447_: u8 = 0;
    let mut v___x_448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_453_: u8 = 0;
    let mut v_it_454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_457_: u8 = 0;
    let mut v___x_458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_463_: u8 = 0;
    let mut v___x_464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_____do__lift_442_) {
                0 => {
                    v_it_443_ = leanh::lean_ctor_get(v_____do__lift_442_, 0);
                    v_out_444_ = leanh::lean_ctor_get(v_____do__lift_442_, 1);
                    v_isSharedCheck_453_ =
                        (!leanh::lean_is_exclusive(v_____do__lift_442_)) as u8;
                    if v_isSharedCheck_453_ == 0 {
                        v___x_446_ = v_____do__lift_442_;
                        v_isShared_447_ = v_isSharedCheck_453_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_out_444_);
                        leanh::lean_inc(v_it_443_);
                        leanh::lean_dec(v_____do__lift_442_);
                        v___x_446_ = leanh::lean_box(0);
                        v_isShared_447_ = v_isSharedCheck_453_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_it_454_ = leanh::lean_ctor_get(v_____do__lift_442_, 0);
                    v_isSharedCheck_463_ =
                        (!leanh::lean_is_exclusive(v_____do__lift_442_)) as u8;
                    if v_isSharedCheck_463_ == 0 {
                        v___x_456_ = v_____do__lift_442_;
                        v_isShared_457_ = v_isSharedCheck_463_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_it_454_);
                        leanh::lean_dec(v_____do__lift_442_);
                        v___x_456_ = leanh::lean_box(0);
                        v_isShared_457_ = v_isSharedCheck_463_;
                        state = 3;
                        continue;
                    }
                }
                _ => {
                    v___x_464_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_464_, 0, v_a_440_);
                    v___x_465_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_465_, 0, v___x_464_);
                    v___x_466_ = leanh::lean_apply_2(
                        v_toPure_441_,
                        leanh::lean_box(0),
                        v___x_465_,
                    );
                    return v___x_466_;
                }
            },
            1 => {
                v___x_448_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_448_, 0, v_it_443_);
                leanh::lean_ctor_set(v___x_448_, 1, v_a_440_);
                if v_isShared_447_ == 0 {
                    leanh::lean_ctor_set(v___x_446_, 0, v___x_448_);
                    v___x_450_ = v___x_446_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_452_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_452_, 0, v___x_448_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_452_, 1, v_out_444_);
                    v___x_450_ = v_reuseFailAlloc_452_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_451_ = leanh::lean_apply_2(
                    v_toPure_441_,
                    leanh::lean_box(0),
                    v___x_450_,
                );
                return v___x_451_;
            }
            3 => {
                v___x_458_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_458_, 0, v_it_454_);
                leanh::lean_ctor_set(v___x_458_, 1, v_a_440_);
                if v_isShared_457_ == 0 {
                    leanh::lean_ctor_set(v___x_456_, 0, v___x_458_);
                    v___x_460_ = v___x_456_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_462_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_462_, 0, v___x_458_);
                    v___x_460_ = v_reuseFailAlloc_462_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_461_ = leanh::lean_apply_2(
                    v_toPure_441_,
                    leanh::lean_box(0),
                    v___x_460_,
                );
                return v___x_461_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Iterators_Types_Append_instIterator___redArg___lam__2(
    mut v_toPure_467_: *mut leanh::LeanObject,
    mut v_inst_468_: *mut leanh::LeanObject,
    mut v_toBind_469_: *mut leanh::LeanObject,
    mut v_inst_470_: *mut leanh::LeanObject,
    mut v___f_471_: *mut leanh::LeanObject,
    mut v_x_472_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_472_) == 0 {
        let mut v_a_473_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_474_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_475_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_476_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_477_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v___f_471_);
        leanh::lean_dec(v_inst_470_);
        v_a_473_ = leanh::lean_ctor_get(v_x_472_, 0);
        leanh::lean_inc(v_a_473_);
        v_a_474_ = leanh::lean_ctor_get(v_x_472_, 1);
        leanh::lean_inc(v_a_474_);
        leanh::lean_dec_ref_known(v_x_472_, 2);
        v___f_475_ = leanh::lean_alloc_closure(
            l_Std_Iterators_Types_Append_instIterator___redArg___lam__1 as *mut core::ffi::c_void,
            3,
            2,
        );
        leanh::lean_closure_set(v___f_475_, 0, v_a_474_);
        leanh::lean_closure_set(v___f_475_, 1, v_toPure_467_);
        v___x_476_ = leanh::lean_apply_1(v_inst_468_, v_a_473_);
        v___x_477_ = leanh::lean_apply_4(
            v_toBind_469_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_476_,
            v___f_475_,
        );
        return v___x_477_;
    } else {
        let mut v_a_478_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_479_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_480_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_inst_468_);
        leanh::lean_dec(v_toPure_467_);
        v_a_478_ = leanh::lean_ctor_get(v_x_472_, 0);
        leanh::lean_inc(v_a_478_);
        leanh::lean_dec_ref_known(v_x_472_, 1);
        v___x_479_ = leanh::lean_apply_1(v_inst_470_, v_a_478_);
        v___x_480_ = leanh::lean_apply_4(
            v_toBind_469_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_479_,
            v___f_471_,
        );
        return v___x_480_;
    }
}
pub unsafe fn l_Std_Iterators_Types_Append_instIterator___redArg(
    mut v_inst_481_: *mut leanh::LeanObject,
    mut v_inst_482_: *mut leanh::LeanObject,
    mut v_inst_483_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_488_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_484_ = leanh::lean_ctor_get(v_inst_481_, 0);
    leanh::lean_inc_ref(v_toApplicative_484_);
    v_toBind_485_ = leanh::lean_ctor_get(v_inst_481_, 1);
    leanh::lean_inc(v_toBind_485_);
    leanh::lean_dec_ref(v_inst_481_);
    v_toPure_486_ = leanh::lean_ctor_get(v_toApplicative_484_, 1);
    leanh::lean_inc_n(v_toPure_486_, 2);
    leanh::lean_dec_ref(v_toApplicative_484_);
    v___f_487_ = leanh::lean_alloc_closure(
        l_Std_Iterators_Types_Append_instIterator___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_487_, 0, v_toPure_486_);
    v___f_488_ = leanh::lean_alloc_closure(
        l_Std_Iterators_Types_Append_instIterator___redArg___lam__2 as *mut core::ffi::c_void,
        6,
        5,
    );
    leanh::lean_closure_set(v___f_488_, 0, v_toPure_486_);
    leanh::lean_closure_set(v___f_488_, 1, v_inst_482_);
    leanh::lean_closure_set(v___f_488_, 2, v_toBind_485_);
    leanh::lean_closure_set(v___f_488_, 3, v_inst_483_);
    leanh::lean_closure_set(v___f_488_, 4, v___f_487_);
    return v___f_488_;
}
pub unsafe fn l_Std_Iterators_Types_Append_instIterator(
    mut v_m_489_: *mut leanh::LeanObject,
    mut v_00_u03b2_490_: *mut leanh::LeanObject,
    mut v_00_u03b1_u2081_491_: *mut leanh::LeanObject,
    mut v_00_u03b1_u2082_492_: *mut leanh::LeanObject,
    mut v_inst_493_: *mut leanh::LeanObject,
    mut v_inst_494_: *mut leanh::LeanObject,
    mut v_inst_495_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_500_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_496_ = leanh::lean_ctor_get(v_inst_493_, 0);
    leanh::lean_inc_ref(v_toApplicative_496_);
    v_toBind_497_ = leanh::lean_ctor_get(v_inst_493_, 1);
    leanh::lean_inc(v_toBind_497_);
    leanh::lean_dec_ref(v_inst_493_);
    v_toPure_498_ = leanh::lean_ctor_get(v_toApplicative_496_, 1);
    leanh::lean_inc_n(v_toPure_498_, 2);
    leanh::lean_dec_ref(v_toApplicative_496_);
    v___f_499_ = leanh::lean_alloc_closure(
        l_Std_Iterators_Types_Append_instIterator___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_499_, 0, v_toPure_498_);
    v___f_500_ = leanh::lean_alloc_closure(
        l_Std_Iterators_Types_Append_instIterator___redArg___lam__2 as *mut core::ffi::c_void,
        6,
        5,
    );
    leanh::lean_closure_set(v___f_500_, 0, v_toPure_498_);
    leanh::lean_closure_set(v___f_500_, 1, v_inst_494_);
    leanh::lean_closure_set(v___f_500_, 2, v_toBind_497_);
    leanh::lean_closure_set(v___f_500_, 3, v_inst_495_);
    leanh::lean_closure_set(v___f_500_, 4, v___f_499_);
    return v___f_500_;
}
pub unsafe fn l_Std_Iterators_Types_Append_instIteratorLoop___redArg___lam__0(
    mut v_toPure_501_: *mut leanh::LeanObject,
    mut v_recur_502_: *mut leanh::LeanObject,
    mut v_it_503_: *mut leanh::LeanObject,
    mut v_____do__lift_504_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_504_) == 0 {
        let mut v_a_505_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_506_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_it_503_);
        leanh::lean_dec(v_recur_502_);
        v_a_505_ = leanh::lean_ctor_get(v_____do__lift_504_, 0);
        leanh::lean_inc(v_a_505_);
        leanh::lean_dec_ref_known(v_____do__lift_504_, 1);
        v___x_506_ = leanh::lean_apply_2(v_toPure_501_, leanh::lean_box(0), v_a_505_);
        return v___x_506_;
    } else {
        let mut v_a_507_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_508_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_toPure_501_);
        v_a_507_ = leanh::lean_ctor_get(v_____do__lift_504_, 0);
        leanh::lean_inc(v_a_507_);
        leanh::lean_dec_ref_known(v_____do__lift_504_, 1);
        v___x_508_ = leanh::lean_apply_4(
            v_recur_502_,
            v_it_503_,
            v_a_507_,
            leanh::lean_box(0),
            leanh::lean_box(0),
        );
        return v___x_508_;
    }
}
pub unsafe fn l_Std_Iterators_Types_Append_instIteratorLoop___redArg___lam__1(
    mut v_toPure_509_: *mut leanh::LeanObject,
    mut v_recur_510_: *mut leanh::LeanObject,
    mut v___y_511_: *mut leanh::LeanObject,
    mut v_acc_512_: *mut leanh::LeanObject,
    mut v_toBind_513_: *mut leanh::LeanObject,
    mut v_s_514_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_s_514_) {
        0 => {
            let mut v_it_515_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_516_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_517_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_518_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_519_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_it_515_ = leanh::lean_ctor_get(v_s_514_, 0);
            leanh::lean_inc(v_it_515_);
            v_out_516_ = leanh::lean_ctor_get(v_s_514_, 1);
            leanh::lean_inc(v_out_516_);
            leanh::lean_dec_ref_known(v_s_514_, 2);
            v___f_517_ = leanh::lean_alloc_closure(
                l_Std_Iterators_Types_Append_instIteratorLoop___redArg___lam__0
                    as *mut core::ffi::c_void,
                4,
                3,
            );
            leanh::lean_closure_set(v___f_517_, 0, v_toPure_509_);
            leanh::lean_closure_set(v___f_517_, 1, v_recur_510_);
            leanh::lean_closure_set(v___f_517_, 2, v_it_515_);
            v___x_518_ = leanh::lean_apply_3(
                v___y_511_,
                v_out_516_,
                leanh::lean_box(0),
                v_acc_512_,
            );
            v___x_519_ = leanh::lean_apply_4(
                v_toBind_513_,
                leanh::lean_box(0),
                leanh::lean_box(0),
                v___x_518_,
                v___f_517_,
            );
            return v___x_519_;
        }
        1 => {
            let mut v_it_520_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_521_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_toBind_513_);
            leanh::lean_dec(v___y_511_);
            leanh::lean_dec(v_toPure_509_);
            v_it_520_ = leanh::lean_ctor_get(v_s_514_, 0);
            leanh::lean_inc(v_it_520_);
            leanh::lean_dec_ref_known(v_s_514_, 1);
            v___x_521_ = leanh::lean_apply_4(
                v_recur_510_,
                v_it_520_,
                v_acc_512_,
                leanh::lean_box(0),
                leanh::lean_box(0),
            );
            return v___x_521_;
        }
        _ => {
            let mut v___x_522_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_toBind_513_);
            leanh::lean_dec(v___y_511_);
            leanh::lean_dec(v_recur_510_);
            v___x_522_ =
                leanh::lean_apply_2(v_toPure_509_, leanh::lean_box(0), v_acc_512_);
            return v___x_522_;
        }
    }
}
pub unsafe fn l_Std_Iterators_Types_Append_instIteratorLoop___redArg___lam__4(
    mut v_inst_523_: *mut leanh::LeanObject,
    mut v_toPure_524_: *mut leanh::LeanObject,
    mut v___y_525_: *mut leanh::LeanObject,
    mut v_toBind_526_: *mut leanh::LeanObject,
    mut v_inst_527_: *mut leanh::LeanObject,
    mut v_lift_528_: *mut leanh::LeanObject,
    mut v_inst_529_: *mut leanh::LeanObject,
    mut v_it_530_: *mut leanh::LeanObject,
    mut v_acc_531_: *mut leanh::LeanObject,
    mut v_hP_532_: *mut leanh::LeanObject,
    mut v_recur_533_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_537_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_534_ = leanh::lean_ctor_get(v_inst_523_, 0);
    leanh::lean_inc_ref(v_toApplicative_534_);
    v_toBind_535_ = leanh::lean_ctor_get(v_inst_523_, 1);
    leanh::lean_inc(v_toBind_535_);
    leanh::lean_dec_ref(v_inst_523_);
    v_toPure_536_ = leanh::lean_ctor_get(v_toApplicative_534_, 1);
    leanh::lean_inc(v_toPure_536_);
    leanh::lean_dec_ref(v_toApplicative_534_);
    v___f_537_ = leanh::lean_alloc_closure(
        l_Std_Iterators_Types_Append_instIteratorLoop___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        5,
    );
    leanh::lean_closure_set(v___f_537_, 0, v_toPure_524_);
    leanh::lean_closure_set(v___f_537_, 1, v_recur_533_);
    leanh::lean_closure_set(v___f_537_, 2, v___y_525_);
    leanh::lean_closure_set(v___f_537_, 3, v_acc_531_);
    leanh::lean_closure_set(v___f_537_, 4, v_toBind_526_);
    if leanh::lean_obj_tag(v_it_530_) == 0 {
        let mut v_a_538_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_539_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_540_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_541_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_542_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_543_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_inst_529_);
        v_a_538_ = leanh::lean_ctor_get(v_it_530_, 0);
        leanh::lean_inc(v_a_538_);
        v_a_539_ = leanh::lean_ctor_get(v_it_530_, 1);
        leanh::lean_inc(v_a_539_);
        leanh::lean_dec_ref_known(v_it_530_, 2);
        v___f_540_ = leanh::lean_alloc_closure(
            l_Std_Iterators_Types_Append_instIterator___redArg___lam__1 as *mut core::ffi::c_void,
            3,
            2,
        );
        leanh::lean_closure_set(v___f_540_, 0, v_a_539_);
        leanh::lean_closure_set(v___f_540_, 1, v_toPure_536_);
        v___x_541_ = leanh::lean_apply_1(v_inst_527_, v_a_538_);
        v___x_542_ = leanh::lean_apply_4(
            v_toBind_535_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_541_,
            v___f_540_,
        );
        v___x_543_ = leanh::lean_apply_4(
            v_lift_528_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___f_537_,
            v___x_542_,
        );
        return v___x_543_;
    } else {
        let mut v_a_544_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_545_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_546_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_547_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_548_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_inst_527_);
        v_a_544_ = leanh::lean_ctor_get(v_it_530_, 0);
        leanh::lean_inc(v_a_544_);
        leanh::lean_dec_ref_known(v_it_530_, 1);
        v___f_545_ = leanh::lean_alloc_closure(
            l_Std_Iterators_Types_Append_instIterator___redArg___lam__0 as *mut core::ffi::c_void,
            2,
            1,
        );
        leanh::lean_closure_set(v___f_545_, 0, v_toPure_536_);
        v___x_546_ = leanh::lean_apply_1(v_inst_529_, v_a_544_);
        v___x_547_ = leanh::lean_apply_4(
            v_toBind_535_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_546_,
            v___f_545_,
        );
        v___x_548_ = leanh::lean_apply_4(
            v_lift_528_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___f_537_,
            v___x_547_,
        );
        return v___x_548_;
    }
}
pub unsafe fn l_Std_Iterators_Types_Append_instIteratorLoop___redArg___lam__2(
    mut v_inst_549_: *mut leanh::LeanObject,
    mut v_inst_550_: *mut leanh::LeanObject,
    mut v_inst_551_: *mut leanh::LeanObject,
    mut v_inst_552_: *mut leanh::LeanObject,
    mut v_lift_553_: *mut leanh::LeanObject,
    mut v_00_u03b3_554_: *mut leanh::LeanObject,
    mut v_Pl_555_: *mut leanh::LeanObject,
    mut v_it_556_: *mut leanh::LeanObject,
    mut v_init_557_: *mut leanh::LeanObject,
    mut v___y_558_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_563_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_559_ = leanh::lean_ctor_get(v_inst_549_, 0);
    leanh::lean_inc_ref(v_toApplicative_559_);
    v_toBind_560_ = leanh::lean_ctor_get(v_inst_549_, 1);
    leanh::lean_inc(v_toBind_560_);
    leanh::lean_dec_ref(v_inst_549_);
    v_toPure_561_ = leanh::lean_ctor_get(v_toApplicative_559_, 1);
    leanh::lean_inc(v_toPure_561_);
    leanh::lean_dec_ref(v_toApplicative_559_);
    v___f_562_ = leanh::lean_alloc_closure(
        l_Std_Iterators_Types_Append_instIteratorLoop___redArg___lam__4 as *mut core::ffi::c_void,
        11,
        7,
    );
    leanh::lean_closure_set(v___f_562_, 0, v_inst_550_);
    leanh::lean_closure_set(v___f_562_, 1, v_toPure_561_);
    leanh::lean_closure_set(v___f_562_, 2, v___y_558_);
    leanh::lean_closure_set(v___f_562_, 3, v_toBind_560_);
    leanh::lean_closure_set(v___f_562_, 4, v_inst_551_);
    leanh::lean_closure_set(v___f_562_, 5, v_lift_553_);
    leanh::lean_closure_set(v___f_562_, 6, v_inst_552_);
    v___x_563_ = l_WellFounded_opaqueFix_u2083___redArg(
        v___f_562_,
        v_it_556_,
        v_init_557_,
        leanh::lean_box(0),
    );
    return v___x_563_;
}
pub unsafe fn l_Std_Iterators_Types_Append_instIteratorLoop___redArg(
    mut v_inst_564_: *mut leanh::LeanObject,
    mut v_inst_565_: *mut leanh::LeanObject,
    mut v_inst_566_: *mut leanh::LeanObject,
    mut v_inst_567_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_568_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_568_ = leanh::lean_alloc_closure(
        l_Std_Iterators_Types_Append_instIteratorLoop___redArg___lam__2 as *mut core::ffi::c_void,
        10,
        4,
    );
    leanh::lean_closure_set(v___f_568_, 0, v_inst_565_);
    leanh::lean_closure_set(v___f_568_, 1, v_inst_564_);
    leanh::lean_closure_set(v___f_568_, 2, v_inst_566_);
    leanh::lean_closure_set(v___f_568_, 3, v_inst_567_);
    return v___f_568_;
}
pub unsafe fn l_Std_Iterators_Types_Append_instIteratorLoop(
    mut v_m_569_: *mut leanh::LeanObject,
    mut v_00_u03b2_570_: *mut leanh::LeanObject,
    mut v_00_u03b1_u2081_571_: *mut leanh::LeanObject,
    mut v_00_u03b1_u2082_572_: *mut leanh::LeanObject,
    mut v_n_573_: *mut leanh::LeanObject,
    mut v_inst_574_: *mut leanh::LeanObject,
    mut v_inst_575_: *mut leanh::LeanObject,
    mut v_inst_576_: *mut leanh::LeanObject,
    mut v_inst_577_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_578_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_578_ = leanh::lean_alloc_closure(
        l_Std_Iterators_Types_Append_instIteratorLoop___redArg___lam__2 as *mut core::ffi::c_void,
        10,
        4,
    );
    leanh::lean_closure_set(v___f_578_, 0, v_inst_575_);
    leanh::lean_closure_set(v___f_578_, 1, v_inst_574_);
    leanh::lean_closure_set(v___f_578_, 2, v_inst_576_);
    leanh::lean_closure_set(v___f_578_, 3, v_inst_577_);
    return v___f_578_;
}
pub unsafe fn l_Std_Iterators_Types_Append_instFinitenessRelation(
    mut v_00_u03b1_u2081_579_: *mut leanh::LeanObject,
    mut v_00_u03b1_u2082_580_: *mut leanh::LeanObject,
    mut v_m_581_: *mut leanh::LeanObject,
    mut v_00_u03b2_582_: *mut leanh::LeanObject,
    mut v_inst_583_: *mut leanh::LeanObject,
    mut v_inst_584_: *mut leanh::LeanObject,
    mut v_inst_585_: *mut leanh::LeanObject,
    mut v_inst_586_: *mut leanh::LeanObject,
    mut v_inst_587_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_588_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_588_ = leanh::lean_box(0);
    return v___x_588_;
}
pub unsafe fn l_Std_Iterators_Types_Append_instFinitenessRelation___boxed(
    mut v_00_u03b1_u2081_589_: *mut leanh::LeanObject,
    mut v_00_u03b1_u2082_590_: *mut leanh::LeanObject,
    mut v_m_591_: *mut leanh::LeanObject,
    mut v_00_u03b2_592_: *mut leanh::LeanObject,
    mut v_inst_593_: *mut leanh::LeanObject,
    mut v_inst_594_: *mut leanh::LeanObject,
    mut v_inst_595_: *mut leanh::LeanObject,
    mut v_inst_596_: *mut leanh::LeanObject,
    mut v_inst_597_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_598_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_598_ = l_Std_Iterators_Types_Append_instFinitenessRelation(
        v_00_u03b1_u2081_589_,
        v_00_u03b1_u2082_590_,
        v_m_591_,
        v_00_u03b2_592_,
        v_inst_593_,
        v_inst_594_,
        v_inst_595_,
        v_inst_596_,
        v_inst_597_,
    );
    leanh::lean_dec(v_inst_595_);
    leanh::lean_dec(v_inst_594_);
    leanh::lean_dec_ref(v_inst_593_);
    return v_res_598_;
}
pub unsafe fn l___private_Init_Data_Iterators_Combinators_Monadic_Append_0__Std_Iterators_Types_Append_instProductivenessRelation(
    mut v_00_u03b1_u2081_599_: *mut leanh::LeanObject,
    mut v_00_u03b1_u2082_600_: *mut leanh::LeanObject,
    mut v_m_601_: *mut leanh::LeanObject,
    mut v_00_u03b2_602_: *mut leanh::LeanObject,
    mut v_inst_603_: *mut leanh::LeanObject,
    mut v_inst_604_: *mut leanh::LeanObject,
    mut v_inst_605_: *mut leanh::LeanObject,
    mut v_inst_606_: *mut leanh::LeanObject,
    mut v_inst_607_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_608_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_608_ = leanh::lean_box(0);
    return v___x_608_;
}
pub unsafe fn l___private_Init_Data_Iterators_Combinators_Monadic_Append_0__Std_Iterators_Types_Append_instProductivenessRelation___boxed(
    mut v_00_u03b1_u2081_609_: *mut leanh::LeanObject,
    mut v_00_u03b1_u2082_610_: *mut leanh::LeanObject,
    mut v_m_611_: *mut leanh::LeanObject,
    mut v_00_u03b2_612_: *mut leanh::LeanObject,
    mut v_inst_613_: *mut leanh::LeanObject,
    mut v_inst_614_: *mut leanh::LeanObject,
    mut v_inst_615_: *mut leanh::LeanObject,
    mut v_inst_616_: *mut leanh::LeanObject,
    mut v_inst_617_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_618_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_618_ = l___private_Init_Data_Iterators_Combinators_Monadic_Append_0__Std_Iterators_Types_Append_instProductivenessRelation(v_00_u03b1_u2081_609_, v_00_u03b1_u2082_610_, v_m_611_, v_00_u03b2_612_, v_inst_613_, v_inst_614_, v_inst_615_, v_inst_616_, v_inst_617_);
    leanh::lean_dec(v_inst_615_);
    leanh::lean_dec(v_inst_614_);
    leanh::lean_dec_ref(v_inst_613_);
    return v_res_618_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Iterators_Combinators_Monadic_Append(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Loop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Classical(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_ByCases(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Iterators_Combinators_Monadic_Append(
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
pub unsafe fn initialize_Init_Data_Iterators_Combinators_Monadic_Append(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Iterators_Consumers_Monadic_Loop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Classical(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Option_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_ByCases(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Combinators_Monadic_Append(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Iterators_Combinators_Monadic_Append(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_Iterators_Combinators_Monadic_Append(builtin);
}