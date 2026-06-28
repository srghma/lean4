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
    mut v_x_310_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_310_) == 0 {
        let mut v___x_311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_311_ = crate::leanh::lean_unsigned_to_nat(0);
        return v___x_311_;
    } else {
        let mut v___x_312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_312_ = crate::leanh::lean_unsigned_to_nat(1);
        return v___x_312_;
    }
}
pub unsafe fn l_Std_Iterators_Types_Append_ctorIdx___redArg___boxed(
    mut v_x_313_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_314_ = l_Std_Iterators_Types_Append_ctorIdx___redArg(v_x_313_);
    crate::leanh::lean_dec_ref(v_x_313_);
    return v_res_314_;
}
pub unsafe fn l_Std_Iterators_Types_Append_ctorIdx(
    mut v_00_u03b1_u2081_315_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_u2082_316_: *mut crate::leanh::LeanObject,
    mut v_m_317_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_318_: *mut crate::leanh::LeanObject,
    mut v_x_319_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_320_ = l_Std_Iterators_Types_Append_ctorIdx___redArg(v_x_319_);
    return v___x_320_;
}
pub unsafe fn l_Std_Iterators_Types_Append_ctorIdx___boxed(
    mut v_00_u03b1_u2081_321_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_u2082_322_: *mut crate::leanh::LeanObject,
    mut v_m_323_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_324_: *mut crate::leanh::LeanObject,
    mut v_x_325_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_326_ = l_Std_Iterators_Types_Append_ctorIdx(
        v_00_u03b1_u2081_321_,
        v_00_u03b1_u2082_322_,
        v_m_323_,
        v_00_u03b2_324_,
        v_x_325_,
    );
    crate::leanh::lean_dec_ref(v_x_325_);
    return v_res_326_;
}
pub unsafe fn l_Std_Iterators_Types_Append_ctorElim___redArg(
    mut v_t_327_: *mut crate::leanh::LeanObject,
    mut v_k_328_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_t_327_) == 0 {
        let mut v_a_329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_329_ = crate::leanh::lean_ctor_get(v_t_327_, 0);
        crate::leanh::lean_inc(v_a_329_);
        v_a_330_ = crate::leanh::lean_ctor_get(v_t_327_, 1);
        crate::leanh::lean_inc(v_a_330_);
        crate::leanh::lean_dec_ref_known(v_t_327_, 2);
        v___x_331_ = crate::leanh::lean_apply_2(v_k_328_, v_a_329_, v_a_330_);
        return v___x_331_;
    } else {
        let mut v_a_332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_332_ = crate::leanh::lean_ctor_get(v_t_327_, 0);
        crate::leanh::lean_inc(v_a_332_);
        crate::leanh::lean_dec_ref_known(v_t_327_, 1);
        v___x_333_ = crate::leanh::lean_apply_1(v_k_328_, v_a_332_);
        return v___x_333_;
    }
}
pub unsafe fn l_Std_Iterators_Types_Append_ctorElim(
    mut v_00_u03b1_u2081_334_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_u2082_335_: *mut crate::leanh::LeanObject,
    mut v_m_336_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_337_: *mut crate::leanh::LeanObject,
    mut v_motive_338_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_339_: *mut crate::leanh::LeanObject,
    mut v_t_340_: *mut crate::leanh::LeanObject,
    mut v_h_341_: *mut crate::leanh::LeanObject,
    mut v_k_342_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_343_ = l_Std_Iterators_Types_Append_ctorElim___redArg(v_t_340_, v_k_342_);
    return v___x_343_;
}
pub unsafe fn l_Std_Iterators_Types_Append_ctorElim___boxed(
    mut v_00_u03b1_u2081_344_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_u2082_345_: *mut crate::leanh::LeanObject,
    mut v_m_346_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_347_: *mut crate::leanh::LeanObject,
    mut v_motive_348_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_349_: *mut crate::leanh::LeanObject,
    mut v_t_350_: *mut crate::leanh::LeanObject,
    mut v_h_351_: *mut crate::leanh::LeanObject,
    mut v_k_352_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v_ctorIdx_349_);
    return v_res_353_;
}
pub unsafe fn l_Std_Iterators_Types_Append_fst_elim___redArg(
    mut v_t_354_: *mut crate::leanh::LeanObject,
    mut v_fst_355_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_356_ = l_Std_Iterators_Types_Append_ctorElim___redArg(v_t_354_, v_fst_355_);
    return v___x_356_;
}
pub unsafe fn l_Std_Iterators_Types_Append_fst_elim(
    mut v_00_u03b1_u2081_357_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_u2082_358_: *mut crate::leanh::LeanObject,
    mut v_m_359_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_360_: *mut crate::leanh::LeanObject,
    mut v_motive_361_: *mut crate::leanh::LeanObject,
    mut v_t_362_: *mut crate::leanh::LeanObject,
    mut v_h_363_: *mut crate::leanh::LeanObject,
    mut v_fst_364_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_365_ = l_Std_Iterators_Types_Append_ctorElim___redArg(v_t_362_, v_fst_364_);
    return v___x_365_;
}
pub unsafe fn l_Std_Iterators_Types_Append_snd_elim___redArg(
    mut v_t_366_: *mut crate::leanh::LeanObject,
    mut v_snd_367_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_368_ = l_Std_Iterators_Types_Append_ctorElim___redArg(v_t_366_, v_snd_367_);
    return v___x_368_;
}
pub unsafe fn l_Std_Iterators_Types_Append_snd_elim(
    mut v_00_u03b1_u2081_369_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_u2082_370_: *mut crate::leanh::LeanObject,
    mut v_m_371_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_372_: *mut crate::leanh::LeanObject,
    mut v_motive_373_: *mut crate::leanh::LeanObject,
    mut v_t_374_: *mut crate::leanh::LeanObject,
    mut v_h_375_: *mut crate::leanh::LeanObject,
    mut v_snd_376_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_377_ = l_Std_Iterators_Types_Append_ctorElim___redArg(v_t_374_, v_snd_376_);
    return v___x_377_;
}
pub unsafe fn l_Std_IterM_append___redArg(
    mut v_it_u2081_378_: *mut crate::leanh::LeanObject,
    mut v_it_u2082_379_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_380_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_380_, 0, v_it_u2081_378_);
    crate::leanh::lean_ctor_set(v___x_380_, 1, v_it_u2082_379_);
    return v___x_380_;
}
pub unsafe fn l_Std_IterM_append(
    mut v_m_381_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_382_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_u2081_383_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_u2082_384_: *mut crate::leanh::LeanObject,
    mut v_inst_385_: *mut crate::leanh::LeanObject,
    mut v_inst_386_: *mut crate::leanh::LeanObject,
    mut v_it_u2081_387_: *mut crate::leanh::LeanObject,
    mut v_it_u2082_388_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_389_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_389_, 0, v_it_u2081_387_);
    crate::leanh::lean_ctor_set(v___x_389_, 1, v_it_u2082_388_);
    return v___x_389_;
}
pub unsafe fn l_Std_IterM_append___boxed(
    mut v_m_390_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_391_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_u2081_392_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_u2082_393_: *mut crate::leanh::LeanObject,
    mut v_inst_394_: *mut crate::leanh::LeanObject,
    mut v_inst_395_: *mut crate::leanh::LeanObject,
    mut v_it_u2081_396_: *mut crate::leanh::LeanObject,
    mut v_it_u2082_397_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v_inst_395_);
    crate::leanh::lean_dec(v_inst_394_);
    return v_res_398_;
}
pub unsafe fn l_Std_IterM_Intermediate_appendSnd___redArg(
    mut v_it_u2082_399_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_400_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_400_, 0, v_it_u2082_399_);
    return v___x_400_;
}
pub unsafe fn l_Std_IterM_Intermediate_appendSnd(
    mut v_m_401_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_402_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_u2082_403_: *mut crate::leanh::LeanObject,
    mut v_inst_404_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_u2081_405_: *mut crate::leanh::LeanObject,
    mut v_it_u2082_406_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_407_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_407_, 0, v_it_u2082_406_);
    return v___x_407_;
}
pub unsafe fn l_Std_IterM_Intermediate_appendSnd___boxed(
    mut v_m_408_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_409_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_u2082_410_: *mut crate::leanh::LeanObject,
    mut v_inst_411_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_u2081_412_: *mut crate::leanh::LeanObject,
    mut v_it_u2082_413_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_414_ = l_Std_IterM_Intermediate_appendSnd(
        v_m_408_,
        v_00_u03b2_409_,
        v_00_u03b1_u2082_410_,
        v_inst_411_,
        v_00_u03b1_u2081_412_,
        v_it_u2082_413_,
    );
    crate::leanh::lean_dec(v_inst_411_);
    return v_res_414_;
}
pub unsafe fn l_Std_Iterators_Types_Append_instIterator___redArg___lam__0(
    mut v_toPure_415_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_416_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_it_417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_out_418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_421_: u8 = 0;
    let mut v___x_422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_427_: u8 = 0;
    let mut v_it_428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_431_: u8 = 0;
    let mut v___x_432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_437_: u8 = 0;
    let mut v___x_438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_____do__lift_416_) {
                0 => {
                    v_it_417_ = crate::leanh::lean_ctor_get(v_____do__lift_416_, 0);
                    v_out_418_ = crate::leanh::lean_ctor_get(v_____do__lift_416_, 1);
                    v_isSharedCheck_427_ =
                        (!crate::leanh::lean_is_exclusive(v_____do__lift_416_)) as u8;
                    if v_isSharedCheck_427_ == 0 {
                        v___x_420_ = v_____do__lift_416_;
                        v_isShared_421_ = v_isSharedCheck_427_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_out_418_);
                        crate::leanh::lean_inc(v_it_417_);
                        crate::leanh::lean_dec(v_____do__lift_416_);
                        v___x_420_ = crate::leanh::lean_box(0);
                        v_isShared_421_ = v_isSharedCheck_427_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_it_428_ = crate::leanh::lean_ctor_get(v_____do__lift_416_, 0);
                    v_isSharedCheck_437_ =
                        (!crate::leanh::lean_is_exclusive(v_____do__lift_416_)) as u8;
                    if v_isSharedCheck_437_ == 0 {
                        v___x_430_ = v_____do__lift_416_;
                        v_isShared_431_ = v_isSharedCheck_437_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_it_428_);
                        crate::leanh::lean_dec(v_____do__lift_416_);
                        v___x_430_ = crate::leanh::lean_box(0);
                        v_isShared_431_ = v_isSharedCheck_437_;
                        state = 3;
                        continue;
                    }
                }
                _ => {
                    v___x_438_ = crate::leanh::lean_box(2);
                    v___x_439_ = crate::leanh::lean_apply_2(
                        v_toPure_415_,
                        crate::leanh::lean_box(0),
                        v___x_438_,
                    );
                    return v___x_439_;
                }
            },
            1 => {
                v___x_422_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_422_, 0, v_it_417_);
                if v_isShared_421_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_420_, 0, v___x_422_);
                    v___x_424_ = v___x_420_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_426_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_426_, 0, v___x_422_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_426_, 1, v_out_418_);
                    v___x_424_ = v_reuseFailAlloc_426_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_425_ = crate::leanh::lean_apply_2(
                    v_toPure_415_,
                    crate::leanh::lean_box(0),
                    v___x_424_,
                );
                return v___x_425_;
            }
            3 => {
                v___x_432_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_432_, 0, v_it_428_);
                if v_isShared_431_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_430_, 0, v___x_432_);
                    v___x_434_ = v___x_430_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_436_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_436_, 0, v___x_432_);
                    v___x_434_ = v_reuseFailAlloc_436_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_435_ = crate::leanh::lean_apply_2(
                    v_toPure_415_,
                    crate::leanh::lean_box(0),
                    v___x_434_,
                );
                return v___x_435_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Iterators_Types_Append_instIterator___redArg___lam__1(
    mut v_a_440_: *mut crate::leanh::LeanObject,
    mut v_toPure_441_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_442_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_it_443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_out_444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_447_: u8 = 0;
    let mut v___x_448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_453_: u8 = 0;
    let mut v_it_454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_457_: u8 = 0;
    let mut v___x_458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_463_: u8 = 0;
    let mut v___x_464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_____do__lift_442_) {
                0 => {
                    v_it_443_ = crate::leanh::lean_ctor_get(v_____do__lift_442_, 0);
                    v_out_444_ = crate::leanh::lean_ctor_get(v_____do__lift_442_, 1);
                    v_isSharedCheck_453_ =
                        (!crate::leanh::lean_is_exclusive(v_____do__lift_442_)) as u8;
                    if v_isSharedCheck_453_ == 0 {
                        v___x_446_ = v_____do__lift_442_;
                        v_isShared_447_ = v_isSharedCheck_453_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_out_444_);
                        crate::leanh::lean_inc(v_it_443_);
                        crate::leanh::lean_dec(v_____do__lift_442_);
                        v___x_446_ = crate::leanh::lean_box(0);
                        v_isShared_447_ = v_isSharedCheck_453_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_it_454_ = crate::leanh::lean_ctor_get(v_____do__lift_442_, 0);
                    v_isSharedCheck_463_ =
                        (!crate::leanh::lean_is_exclusive(v_____do__lift_442_)) as u8;
                    if v_isSharedCheck_463_ == 0 {
                        v___x_456_ = v_____do__lift_442_;
                        v_isShared_457_ = v_isSharedCheck_463_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_it_454_);
                        crate::leanh::lean_dec(v_____do__lift_442_);
                        v___x_456_ = crate::leanh::lean_box(0);
                        v_isShared_457_ = v_isSharedCheck_463_;
                        state = 3;
                        continue;
                    }
                }
                _ => {
                    v___x_464_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_464_, 0, v_a_440_);
                    v___x_465_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_465_, 0, v___x_464_);
                    v___x_466_ = crate::leanh::lean_apply_2(
                        v_toPure_441_,
                        crate::leanh::lean_box(0),
                        v___x_465_,
                    );
                    return v___x_466_;
                }
            },
            1 => {
                v___x_448_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_448_, 0, v_it_443_);
                crate::leanh::lean_ctor_set(v___x_448_, 1, v_a_440_);
                if v_isShared_447_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_446_, 0, v___x_448_);
                    v___x_450_ = v___x_446_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_452_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_452_, 0, v___x_448_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_452_, 1, v_out_444_);
                    v___x_450_ = v_reuseFailAlloc_452_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_451_ = crate::leanh::lean_apply_2(
                    v_toPure_441_,
                    crate::leanh::lean_box(0),
                    v___x_450_,
                );
                return v___x_451_;
            }
            3 => {
                v___x_458_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_458_, 0, v_it_454_);
                crate::leanh::lean_ctor_set(v___x_458_, 1, v_a_440_);
                if v_isShared_457_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_456_, 0, v___x_458_);
                    v___x_460_ = v___x_456_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_462_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_462_, 0, v___x_458_);
                    v___x_460_ = v_reuseFailAlloc_462_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_461_ = crate::leanh::lean_apply_2(
                    v_toPure_441_,
                    crate::leanh::lean_box(0),
                    v___x_460_,
                );
                return v___x_461_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Iterators_Types_Append_instIterator___redArg___lam__2(
    mut v_toPure_467_: *mut crate::leanh::LeanObject,
    mut v_inst_468_: *mut crate::leanh::LeanObject,
    mut v_toBind_469_: *mut crate::leanh::LeanObject,
    mut v_inst_470_: *mut crate::leanh::LeanObject,
    mut v___f_471_: *mut crate::leanh::LeanObject,
    mut v_x_472_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_472_) == 0 {
        let mut v_a_473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___f_471_);
        crate::leanh::lean_dec(v_inst_470_);
        v_a_473_ = crate::leanh::lean_ctor_get(v_x_472_, 0);
        crate::leanh::lean_inc(v_a_473_);
        v_a_474_ = crate::leanh::lean_ctor_get(v_x_472_, 1);
        crate::leanh::lean_inc(v_a_474_);
        crate::leanh::lean_dec_ref_known(v_x_472_, 2);
        v___f_475_ = crate::leanh::lean_alloc_closure(
            l_Std_Iterators_Types_Append_instIterator___redArg___lam__1 as *mut core::ffi::c_void,
            3,
            2,
        );
        crate::leanh::lean_closure_set(v___f_475_, 0, v_a_474_);
        crate::leanh::lean_closure_set(v___f_475_, 1, v_toPure_467_);
        v___x_476_ = crate::leanh::lean_apply_1(v_inst_468_, v_a_473_);
        v___x_477_ = crate::leanh::lean_apply_4(
            v_toBind_469_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_476_,
            v___f_475_,
        );
        return v___x_477_;
    } else {
        let mut v_a_478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_inst_468_);
        crate::leanh::lean_dec(v_toPure_467_);
        v_a_478_ = crate::leanh::lean_ctor_get(v_x_472_, 0);
        crate::leanh::lean_inc(v_a_478_);
        crate::leanh::lean_dec_ref_known(v_x_472_, 1);
        v___x_479_ = crate::leanh::lean_apply_1(v_inst_470_, v_a_478_);
        v___x_480_ = crate::leanh::lean_apply_4(
            v_toBind_469_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_479_,
            v___f_471_,
        );
        return v___x_480_;
    }
}
pub unsafe fn l_Std_Iterators_Types_Append_instIterator___redArg(
    mut v_inst_481_: *mut crate::leanh::LeanObject,
    mut v_inst_482_: *mut crate::leanh::LeanObject,
    mut v_inst_483_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_484_ = crate::leanh::lean_ctor_get(v_inst_481_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_484_);
    v_toBind_485_ = crate::leanh::lean_ctor_get(v_inst_481_, 1);
    crate::leanh::lean_inc(v_toBind_485_);
    crate::leanh::lean_dec_ref(v_inst_481_);
    v_toPure_486_ = crate::leanh::lean_ctor_get(v_toApplicative_484_, 1);
    crate::leanh::lean_inc_n(v_toPure_486_, 2);
    crate::leanh::lean_dec_ref(v_toApplicative_484_);
    v___f_487_ = crate::leanh::lean_alloc_closure(
        l_Std_Iterators_Types_Append_instIterator___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_487_, 0, v_toPure_486_);
    v___f_488_ = crate::leanh::lean_alloc_closure(
        l_Std_Iterators_Types_Append_instIterator___redArg___lam__2 as *mut core::ffi::c_void,
        6,
        5,
    );
    crate::leanh::lean_closure_set(v___f_488_, 0, v_toPure_486_);
    crate::leanh::lean_closure_set(v___f_488_, 1, v_inst_482_);
    crate::leanh::lean_closure_set(v___f_488_, 2, v_toBind_485_);
    crate::leanh::lean_closure_set(v___f_488_, 3, v_inst_483_);
    crate::leanh::lean_closure_set(v___f_488_, 4, v___f_487_);
    return v___f_488_;
}
pub unsafe fn l_Std_Iterators_Types_Append_instIterator(
    mut v_m_489_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_490_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_u2081_491_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_u2082_492_: *mut crate::leanh::LeanObject,
    mut v_inst_493_: *mut crate::leanh::LeanObject,
    mut v_inst_494_: *mut crate::leanh::LeanObject,
    mut v_inst_495_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_496_ = crate::leanh::lean_ctor_get(v_inst_493_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_496_);
    v_toBind_497_ = crate::leanh::lean_ctor_get(v_inst_493_, 1);
    crate::leanh::lean_inc(v_toBind_497_);
    crate::leanh::lean_dec_ref(v_inst_493_);
    v_toPure_498_ = crate::leanh::lean_ctor_get(v_toApplicative_496_, 1);
    crate::leanh::lean_inc_n(v_toPure_498_, 2);
    crate::leanh::lean_dec_ref(v_toApplicative_496_);
    v___f_499_ = crate::leanh::lean_alloc_closure(
        l_Std_Iterators_Types_Append_instIterator___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_499_, 0, v_toPure_498_);
    v___f_500_ = crate::leanh::lean_alloc_closure(
        l_Std_Iterators_Types_Append_instIterator___redArg___lam__2 as *mut core::ffi::c_void,
        6,
        5,
    );
    crate::leanh::lean_closure_set(v___f_500_, 0, v_toPure_498_);
    crate::leanh::lean_closure_set(v___f_500_, 1, v_inst_494_);
    crate::leanh::lean_closure_set(v___f_500_, 2, v_toBind_497_);
    crate::leanh::lean_closure_set(v___f_500_, 3, v_inst_495_);
    crate::leanh::lean_closure_set(v___f_500_, 4, v___f_499_);
    return v___f_500_;
}
pub unsafe fn l_Std_Iterators_Types_Append_instIteratorLoop___redArg___lam__0(
    mut v_toPure_501_: *mut crate::leanh::LeanObject,
    mut v_recur_502_: *mut crate::leanh::LeanObject,
    mut v_it_503_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_504_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_504_) == 0 {
        let mut v_a_505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_it_503_);
        crate::leanh::lean_dec(v_recur_502_);
        v_a_505_ = crate::leanh::lean_ctor_get(v_____do__lift_504_, 0);
        crate::leanh::lean_inc(v_a_505_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_504_, 1);
        v___x_506_ = crate::leanh::lean_apply_2(v_toPure_501_, crate::leanh::lean_box(0), v_a_505_);
        return v___x_506_;
    } else {
        let mut v_a_507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toPure_501_);
        v_a_507_ = crate::leanh::lean_ctor_get(v_____do__lift_504_, 0);
        crate::leanh::lean_inc(v_a_507_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_504_, 1);
        v___x_508_ = crate::leanh::lean_apply_4(
            v_recur_502_,
            v_it_503_,
            v_a_507_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
        );
        return v___x_508_;
    }
}
pub unsafe fn l_Std_Iterators_Types_Append_instIteratorLoop___redArg___lam__1(
    mut v_toPure_509_: *mut crate::leanh::LeanObject,
    mut v_recur_510_: *mut crate::leanh::LeanObject,
    mut v___y_511_: *mut crate::leanh::LeanObject,
    mut v_acc_512_: *mut crate::leanh::LeanObject,
    mut v_toBind_513_: *mut crate::leanh::LeanObject,
    mut v_s_514_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_s_514_) {
        0 => {
            let mut v_it_515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_it_515_ = crate::leanh::lean_ctor_get(v_s_514_, 0);
            crate::leanh::lean_inc(v_it_515_);
            v_out_516_ = crate::leanh::lean_ctor_get(v_s_514_, 1);
            crate::leanh::lean_inc(v_out_516_);
            crate::leanh::lean_dec_ref_known(v_s_514_, 2);
            v___f_517_ = crate::leanh::lean_alloc_closure(
                l_Std_Iterators_Types_Append_instIteratorLoop___redArg___lam__0
                    as *mut core::ffi::c_void,
                4,
                3,
            );
            crate::leanh::lean_closure_set(v___f_517_, 0, v_toPure_509_);
            crate::leanh::lean_closure_set(v___f_517_, 1, v_recur_510_);
            crate::leanh::lean_closure_set(v___f_517_, 2, v_it_515_);
            v___x_518_ = crate::leanh::lean_apply_3(
                v___y_511_,
                v_out_516_,
                crate::leanh::lean_box(0),
                v_acc_512_,
            );
            v___x_519_ = crate::leanh::lean_apply_4(
                v_toBind_513_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_518_,
                v___f_517_,
            );
            return v___x_519_;
        }
        1 => {
            let mut v_it_520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_toBind_513_);
            crate::leanh::lean_dec(v___y_511_);
            crate::leanh::lean_dec(v_toPure_509_);
            v_it_520_ = crate::leanh::lean_ctor_get(v_s_514_, 0);
            crate::leanh::lean_inc(v_it_520_);
            crate::leanh::lean_dec_ref_known(v_s_514_, 1);
            v___x_521_ = crate::leanh::lean_apply_4(
                v_recur_510_,
                v_it_520_,
                v_acc_512_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
            );
            return v___x_521_;
        }
        _ => {
            let mut v___x_522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_toBind_513_);
            crate::leanh::lean_dec(v___y_511_);
            crate::leanh::lean_dec(v_recur_510_);
            v___x_522_ =
                crate::leanh::lean_apply_2(v_toPure_509_, crate::leanh::lean_box(0), v_acc_512_);
            return v___x_522_;
        }
    }
}
pub unsafe fn l_Std_Iterators_Types_Append_instIteratorLoop___redArg___lam__4(
    mut v_inst_523_: *mut crate::leanh::LeanObject,
    mut v_toPure_524_: *mut crate::leanh::LeanObject,
    mut v___y_525_: *mut crate::leanh::LeanObject,
    mut v_toBind_526_: *mut crate::leanh::LeanObject,
    mut v_inst_527_: *mut crate::leanh::LeanObject,
    mut v_lift_528_: *mut crate::leanh::LeanObject,
    mut v_inst_529_: *mut crate::leanh::LeanObject,
    mut v_it_530_: *mut crate::leanh::LeanObject,
    mut v_acc_531_: *mut crate::leanh::LeanObject,
    mut v_hP_532_: *mut crate::leanh::LeanObject,
    mut v_recur_533_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_534_ = crate::leanh::lean_ctor_get(v_inst_523_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_534_);
    v_toBind_535_ = crate::leanh::lean_ctor_get(v_inst_523_, 1);
    crate::leanh::lean_inc(v_toBind_535_);
    crate::leanh::lean_dec_ref(v_inst_523_);
    v_toPure_536_ = crate::leanh::lean_ctor_get(v_toApplicative_534_, 1);
    crate::leanh::lean_inc(v_toPure_536_);
    crate::leanh::lean_dec_ref(v_toApplicative_534_);
    v___f_537_ = crate::leanh::lean_alloc_closure(
        l_Std_Iterators_Types_Append_instIteratorLoop___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        5,
    );
    crate::leanh::lean_closure_set(v___f_537_, 0, v_toPure_524_);
    crate::leanh::lean_closure_set(v___f_537_, 1, v_recur_533_);
    crate::leanh::lean_closure_set(v___f_537_, 2, v___y_525_);
    crate::leanh::lean_closure_set(v___f_537_, 3, v_acc_531_);
    crate::leanh::lean_closure_set(v___f_537_, 4, v_toBind_526_);
    if crate::leanh::lean_obj_tag(v_it_530_) == 0 {
        let mut v_a_538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_inst_529_);
        v_a_538_ = crate::leanh::lean_ctor_get(v_it_530_, 0);
        crate::leanh::lean_inc(v_a_538_);
        v_a_539_ = crate::leanh::lean_ctor_get(v_it_530_, 1);
        crate::leanh::lean_inc(v_a_539_);
        crate::leanh::lean_dec_ref_known(v_it_530_, 2);
        v___f_540_ = crate::leanh::lean_alloc_closure(
            l_Std_Iterators_Types_Append_instIterator___redArg___lam__1 as *mut core::ffi::c_void,
            3,
            2,
        );
        crate::leanh::lean_closure_set(v___f_540_, 0, v_a_539_);
        crate::leanh::lean_closure_set(v___f_540_, 1, v_toPure_536_);
        v___x_541_ = crate::leanh::lean_apply_1(v_inst_527_, v_a_538_);
        v___x_542_ = crate::leanh::lean_apply_4(
            v_toBind_535_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_541_,
            v___f_540_,
        );
        v___x_543_ = crate::leanh::lean_apply_4(
            v_lift_528_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___f_537_,
            v___x_542_,
        );
        return v___x_543_;
    } else {
        let mut v_a_544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_inst_527_);
        v_a_544_ = crate::leanh::lean_ctor_get(v_it_530_, 0);
        crate::leanh::lean_inc(v_a_544_);
        crate::leanh::lean_dec_ref_known(v_it_530_, 1);
        v___f_545_ = crate::leanh::lean_alloc_closure(
            l_Std_Iterators_Types_Append_instIterator___redArg___lam__0 as *mut core::ffi::c_void,
            2,
            1,
        );
        crate::leanh::lean_closure_set(v___f_545_, 0, v_toPure_536_);
        v___x_546_ = crate::leanh::lean_apply_1(v_inst_529_, v_a_544_);
        v___x_547_ = crate::leanh::lean_apply_4(
            v_toBind_535_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_546_,
            v___f_545_,
        );
        v___x_548_ = crate::leanh::lean_apply_4(
            v_lift_528_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___f_537_,
            v___x_547_,
        );
        return v___x_548_;
    }
}
pub unsafe fn l_Std_Iterators_Types_Append_instIteratorLoop___redArg___lam__2(
    mut v_inst_549_: *mut crate::leanh::LeanObject,
    mut v_inst_550_: *mut crate::leanh::LeanObject,
    mut v_inst_551_: *mut crate::leanh::LeanObject,
    mut v_inst_552_: *mut crate::leanh::LeanObject,
    mut v_lift_553_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_554_: *mut crate::leanh::LeanObject,
    mut v_Pl_555_: *mut crate::leanh::LeanObject,
    mut v_it_556_: *mut crate::leanh::LeanObject,
    mut v_init_557_: *mut crate::leanh::LeanObject,
    mut v___y_558_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_559_ = crate::leanh::lean_ctor_get(v_inst_549_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_559_);
    v_toBind_560_ = crate::leanh::lean_ctor_get(v_inst_549_, 1);
    crate::leanh::lean_inc(v_toBind_560_);
    crate::leanh::lean_dec_ref(v_inst_549_);
    v_toPure_561_ = crate::leanh::lean_ctor_get(v_toApplicative_559_, 1);
    crate::leanh::lean_inc(v_toPure_561_);
    crate::leanh::lean_dec_ref(v_toApplicative_559_);
    v___f_562_ = crate::leanh::lean_alloc_closure(
        l_Std_Iterators_Types_Append_instIteratorLoop___redArg___lam__4 as *mut core::ffi::c_void,
        11,
        7,
    );
    crate::leanh::lean_closure_set(v___f_562_, 0, v_inst_550_);
    crate::leanh::lean_closure_set(v___f_562_, 1, v_toPure_561_);
    crate::leanh::lean_closure_set(v___f_562_, 2, v___y_558_);
    crate::leanh::lean_closure_set(v___f_562_, 3, v_toBind_560_);
    crate::leanh::lean_closure_set(v___f_562_, 4, v_inst_551_);
    crate::leanh::lean_closure_set(v___f_562_, 5, v_lift_553_);
    crate::leanh::lean_closure_set(v___f_562_, 6, v_inst_552_);
    v___x_563_ = l_WellFounded_opaqueFix_u2083___redArg(
        v___f_562_,
        v_it_556_,
        v_init_557_,
        crate::leanh::lean_box(0),
    );
    return v___x_563_;
}
pub unsafe fn l_Std_Iterators_Types_Append_instIteratorLoop___redArg(
    mut v_inst_564_: *mut crate::leanh::LeanObject,
    mut v_inst_565_: *mut crate::leanh::LeanObject,
    mut v_inst_566_: *mut crate::leanh::LeanObject,
    mut v_inst_567_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_568_ = crate::leanh::lean_alloc_closure(
        l_Std_Iterators_Types_Append_instIteratorLoop___redArg___lam__2 as *mut core::ffi::c_void,
        10,
        4,
    );
    crate::leanh::lean_closure_set(v___f_568_, 0, v_inst_565_);
    crate::leanh::lean_closure_set(v___f_568_, 1, v_inst_564_);
    crate::leanh::lean_closure_set(v___f_568_, 2, v_inst_566_);
    crate::leanh::lean_closure_set(v___f_568_, 3, v_inst_567_);
    return v___f_568_;
}
pub unsafe fn l_Std_Iterators_Types_Append_instIteratorLoop(
    mut v_m_569_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_570_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_u2081_571_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_u2082_572_: *mut crate::leanh::LeanObject,
    mut v_n_573_: *mut crate::leanh::LeanObject,
    mut v_inst_574_: *mut crate::leanh::LeanObject,
    mut v_inst_575_: *mut crate::leanh::LeanObject,
    mut v_inst_576_: *mut crate::leanh::LeanObject,
    mut v_inst_577_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_578_ = crate::leanh::lean_alloc_closure(
        l_Std_Iterators_Types_Append_instIteratorLoop___redArg___lam__2 as *mut core::ffi::c_void,
        10,
        4,
    );
    crate::leanh::lean_closure_set(v___f_578_, 0, v_inst_575_);
    crate::leanh::lean_closure_set(v___f_578_, 1, v_inst_574_);
    crate::leanh::lean_closure_set(v___f_578_, 2, v_inst_576_);
    crate::leanh::lean_closure_set(v___f_578_, 3, v_inst_577_);
    return v___f_578_;
}
pub unsafe fn l_Std_Iterators_Types_Append_instFinitenessRelation(
    mut v_00_u03b1_u2081_579_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_u2082_580_: *mut crate::leanh::LeanObject,
    mut v_m_581_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_582_: *mut crate::leanh::LeanObject,
    mut v_inst_583_: *mut crate::leanh::LeanObject,
    mut v_inst_584_: *mut crate::leanh::LeanObject,
    mut v_inst_585_: *mut crate::leanh::LeanObject,
    mut v_inst_586_: *mut crate::leanh::LeanObject,
    mut v_inst_587_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_588_ = crate::leanh::lean_box(0);
    return v___x_588_;
}
pub unsafe fn l_Std_Iterators_Types_Append_instFinitenessRelation___boxed(
    mut v_00_u03b1_u2081_589_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_u2082_590_: *mut crate::leanh::LeanObject,
    mut v_m_591_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_592_: *mut crate::leanh::LeanObject,
    mut v_inst_593_: *mut crate::leanh::LeanObject,
    mut v_inst_594_: *mut crate::leanh::LeanObject,
    mut v_inst_595_: *mut crate::leanh::LeanObject,
    mut v_inst_596_: *mut crate::leanh::LeanObject,
    mut v_inst_597_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v_inst_595_);
    crate::leanh::lean_dec(v_inst_594_);
    crate::leanh::lean_dec_ref(v_inst_593_);
    return v_res_598_;
}
pub unsafe fn l___private_Init_Data_Iterators_Combinators_Monadic_Append_0__Std_Iterators_Types_Append_instProductivenessRelation(
    mut v_00_u03b1_u2081_599_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_u2082_600_: *mut crate::leanh::LeanObject,
    mut v_m_601_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_602_: *mut crate::leanh::LeanObject,
    mut v_inst_603_: *mut crate::leanh::LeanObject,
    mut v_inst_604_: *mut crate::leanh::LeanObject,
    mut v_inst_605_: *mut crate::leanh::LeanObject,
    mut v_inst_606_: *mut crate::leanh::LeanObject,
    mut v_inst_607_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_608_ = crate::leanh::lean_box(0);
    return v___x_608_;
}
pub unsafe fn l___private_Init_Data_Iterators_Combinators_Monadic_Append_0__Std_Iterators_Types_Append_instProductivenessRelation___boxed(
    mut v_00_u03b1_u2081_609_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_u2082_610_: *mut crate::leanh::LeanObject,
    mut v_m_611_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_612_: *mut crate::leanh::LeanObject,
    mut v_inst_613_: *mut crate::leanh::LeanObject,
    mut v_inst_614_: *mut crate::leanh::LeanObject,
    mut v_inst_615_: *mut crate::leanh::LeanObject,
    mut v_inst_616_: *mut crate::leanh::LeanObject,
    mut v_inst_617_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_618_ = l___private_Init_Data_Iterators_Combinators_Monadic_Append_0__Std_Iterators_Types_Append_instProductivenessRelation(v_00_u03b1_u2081_609_, v_00_u03b1_u2082_610_, v_m_611_, v_00_u03b2_612_, v_inst_613_, v_inst_614_, v_inst_615_, v_inst_616_, v_inst_617_);
    crate::leanh::lean_dec(v_inst_615_);
    crate::leanh::lean_dec(v_inst_614_);
    crate::leanh::lean_dec_ref(v_inst_613_);
    return v_res_618_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Iterators_Combinators_Monadic_Append(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Loop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Classical(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_ByCases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Iterators_Combinators_Monadic_Append(
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
pub unsafe fn initialize_Init_Data_Iterators_Combinators_Monadic_Append(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Iterators_Consumers_Monadic_Loop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Classical(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Option_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_ByCases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Combinators_Monadic_Append(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Iterators_Combinators_Monadic_Append(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_Iterators_Combinators_Monadic_Append(builtin);
}
