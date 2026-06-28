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
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_3, lean_apply_4, lean_box, lean_closure_set, lean_ctor_get,
    lean_ctor_set, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc, lean_inc_n, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_tag,
    lean_unsigned_to_nat,
};
pub unsafe fn l_Std_Iterators_Types_Append_ctorIdx___redArg(
    mut v_x_310_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_310_) == 0 {
        let mut v___x_311_: *mut LeanObject = core::ptr::null_mut();
        v___x_311_ = lean_unsigned_to_nat(0);
        return v___x_311_;
    } else {
        let mut v___x_312_: *mut LeanObject = core::ptr::null_mut();
        v___x_312_ = lean_unsigned_to_nat(1);
        return v___x_312_;
    }
}
pub unsafe fn l_Std_Iterators_Types_Append_ctorIdx___redArg___boxed(
    mut v_x_313_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_314_: *mut LeanObject = core::ptr::null_mut();
    v_res_314_ = l_Std_Iterators_Types_Append_ctorIdx___redArg(v_x_313_);
    lean_dec_ref(v_x_313_);
    return v_res_314_;
}
pub unsafe fn l_Std_Iterators_Types_Append_ctorIdx(
    mut v_00_u03b1_u2081_315_: *mut LeanObject,
    mut v_00_u03b1_u2082_316_: *mut LeanObject,
    mut v_m_317_: *mut LeanObject,
    mut v_00_u03b2_318_: *mut LeanObject,
    mut v_x_319_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_320_: *mut LeanObject = core::ptr::null_mut();
    v___x_320_ = l_Std_Iterators_Types_Append_ctorIdx___redArg(v_x_319_);
    return v___x_320_;
}
pub unsafe fn l_Std_Iterators_Types_Append_ctorIdx___boxed(
    mut v_00_u03b1_u2081_321_: *mut LeanObject,
    mut v_00_u03b1_u2082_322_: *mut LeanObject,
    mut v_m_323_: *mut LeanObject,
    mut v_00_u03b2_324_: *mut LeanObject,
    mut v_x_325_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_326_: *mut LeanObject = core::ptr::null_mut();
    v_res_326_ = l_Std_Iterators_Types_Append_ctorIdx(
        v_00_u03b1_u2081_321_,
        v_00_u03b1_u2082_322_,
        v_m_323_,
        v_00_u03b2_324_,
        v_x_325_,
    );
    lean_dec_ref(v_x_325_);
    return v_res_326_;
}
pub unsafe fn l_Std_Iterators_Types_Append_ctorElim___redArg(
    mut v_t_327_: *mut LeanObject,
    mut v_k_328_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_t_327_) == 0 {
        let mut v_a_329_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_330_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_331_: *mut LeanObject = core::ptr::null_mut();
        v_a_329_ = lean_ctor_get(v_t_327_, 0);
        lean_inc(v_a_329_);
        v_a_330_ = lean_ctor_get(v_t_327_, 1);
        lean_inc(v_a_330_);
        lean_dec_ref_known(v_t_327_, 2);
        v___x_331_ = lean_apply_2(v_k_328_, v_a_329_, v_a_330_);
        return v___x_331_;
    } else {
        let mut v_a_332_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_333_: *mut LeanObject = core::ptr::null_mut();
        v_a_332_ = lean_ctor_get(v_t_327_, 0);
        lean_inc(v_a_332_);
        lean_dec_ref_known(v_t_327_, 1);
        v___x_333_ = lean_apply_1(v_k_328_, v_a_332_);
        return v___x_333_;
    }
}
pub unsafe fn l_Std_Iterators_Types_Append_ctorElim(
    mut v_00_u03b1_u2081_334_: *mut LeanObject,
    mut v_00_u03b1_u2082_335_: *mut LeanObject,
    mut v_m_336_: *mut LeanObject,
    mut v_00_u03b2_337_: *mut LeanObject,
    mut v_motive_338_: *mut LeanObject,
    mut v_ctorIdx_339_: *mut LeanObject,
    mut v_t_340_: *mut LeanObject,
    mut v_h_341_: *mut LeanObject,
    mut v_k_342_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_343_: *mut LeanObject = core::ptr::null_mut();
    v___x_343_ = l_Std_Iterators_Types_Append_ctorElim___redArg(v_t_340_, v_k_342_);
    return v___x_343_;
}
pub unsafe fn l_Std_Iterators_Types_Append_ctorElim___boxed(
    mut v_00_u03b1_u2081_344_: *mut LeanObject,
    mut v_00_u03b1_u2082_345_: *mut LeanObject,
    mut v_m_346_: *mut LeanObject,
    mut v_00_u03b2_347_: *mut LeanObject,
    mut v_motive_348_: *mut LeanObject,
    mut v_ctorIdx_349_: *mut LeanObject,
    mut v_t_350_: *mut LeanObject,
    mut v_h_351_: *mut LeanObject,
    mut v_k_352_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_353_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_ctorIdx_349_);
    return v_res_353_;
}
pub unsafe fn l_Std_Iterators_Types_Append_fst_elim___redArg(
    mut v_t_354_: *mut LeanObject,
    mut v_fst_355_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_356_: *mut LeanObject = core::ptr::null_mut();
    v___x_356_ = l_Std_Iterators_Types_Append_ctorElim___redArg(v_t_354_, v_fst_355_);
    return v___x_356_;
}
pub unsafe fn l_Std_Iterators_Types_Append_fst_elim(
    mut v_00_u03b1_u2081_357_: *mut LeanObject,
    mut v_00_u03b1_u2082_358_: *mut LeanObject,
    mut v_m_359_: *mut LeanObject,
    mut v_00_u03b2_360_: *mut LeanObject,
    mut v_motive_361_: *mut LeanObject,
    mut v_t_362_: *mut LeanObject,
    mut v_h_363_: *mut LeanObject,
    mut v_fst_364_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_365_: *mut LeanObject = core::ptr::null_mut();
    v___x_365_ = l_Std_Iterators_Types_Append_ctorElim___redArg(v_t_362_, v_fst_364_);
    return v___x_365_;
}
pub unsafe fn l_Std_Iterators_Types_Append_snd_elim___redArg(
    mut v_t_366_: *mut LeanObject,
    mut v_snd_367_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_368_: *mut LeanObject = core::ptr::null_mut();
    v___x_368_ = l_Std_Iterators_Types_Append_ctorElim___redArg(v_t_366_, v_snd_367_);
    return v___x_368_;
}
pub unsafe fn l_Std_Iterators_Types_Append_snd_elim(
    mut v_00_u03b1_u2081_369_: *mut LeanObject,
    mut v_00_u03b1_u2082_370_: *mut LeanObject,
    mut v_m_371_: *mut LeanObject,
    mut v_00_u03b2_372_: *mut LeanObject,
    mut v_motive_373_: *mut LeanObject,
    mut v_t_374_: *mut LeanObject,
    mut v_h_375_: *mut LeanObject,
    mut v_snd_376_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_377_: *mut LeanObject = core::ptr::null_mut();
    v___x_377_ = l_Std_Iterators_Types_Append_ctorElim___redArg(v_t_374_, v_snd_376_);
    return v___x_377_;
}
pub unsafe fn l_Std_IterM_append___redArg(
    mut v_it_u2081_378_: *mut LeanObject,
    mut v_it_u2082_379_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_380_: *mut LeanObject = core::ptr::null_mut();
    v___x_380_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_380_, 0, v_it_u2081_378_);
    lean_ctor_set(v___x_380_, 1, v_it_u2082_379_);
    return v___x_380_;
}
pub unsafe fn l_Std_IterM_append(
    mut v_m_381_: *mut LeanObject,
    mut v_00_u03b2_382_: *mut LeanObject,
    mut v_00_u03b1_u2081_383_: *mut LeanObject,
    mut v_00_u03b1_u2082_384_: *mut LeanObject,
    mut v_inst_385_: *mut LeanObject,
    mut v_inst_386_: *mut LeanObject,
    mut v_it_u2081_387_: *mut LeanObject,
    mut v_it_u2082_388_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_389_: *mut LeanObject = core::ptr::null_mut();
    v___x_389_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_389_, 0, v_it_u2081_387_);
    lean_ctor_set(v___x_389_, 1, v_it_u2082_388_);
    return v___x_389_;
}
pub unsafe fn l_Std_IterM_append___boxed(
    mut v_m_390_: *mut LeanObject,
    mut v_00_u03b2_391_: *mut LeanObject,
    mut v_00_u03b1_u2081_392_: *mut LeanObject,
    mut v_00_u03b1_u2082_393_: *mut LeanObject,
    mut v_inst_394_: *mut LeanObject,
    mut v_inst_395_: *mut LeanObject,
    mut v_it_u2081_396_: *mut LeanObject,
    mut v_it_u2082_397_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_398_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_inst_395_);
    lean_dec(v_inst_394_);
    return v_res_398_;
}
pub unsafe fn l_Std_IterM_Intermediate_appendSnd___redArg(
    mut v_it_u2082_399_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_400_: *mut LeanObject = core::ptr::null_mut();
    v___x_400_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_400_, 0, v_it_u2082_399_);
    return v___x_400_;
}
pub unsafe fn l_Std_IterM_Intermediate_appendSnd(
    mut v_m_401_: *mut LeanObject,
    mut v_00_u03b2_402_: *mut LeanObject,
    mut v_00_u03b1_u2082_403_: *mut LeanObject,
    mut v_inst_404_: *mut LeanObject,
    mut v_00_u03b1_u2081_405_: *mut LeanObject,
    mut v_it_u2082_406_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_407_: *mut LeanObject = core::ptr::null_mut();
    v___x_407_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_407_, 0, v_it_u2082_406_);
    return v___x_407_;
}
pub unsafe fn l_Std_IterM_Intermediate_appendSnd___boxed(
    mut v_m_408_: *mut LeanObject,
    mut v_00_u03b2_409_: *mut LeanObject,
    mut v_00_u03b1_u2082_410_: *mut LeanObject,
    mut v_inst_411_: *mut LeanObject,
    mut v_00_u03b1_u2081_412_: *mut LeanObject,
    mut v_it_u2082_413_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_414_: *mut LeanObject = core::ptr::null_mut();
    v_res_414_ = l_Std_IterM_Intermediate_appendSnd(
        v_m_408_,
        v_00_u03b2_409_,
        v_00_u03b1_u2082_410_,
        v_inst_411_,
        v_00_u03b1_u2081_412_,
        v_it_u2082_413_,
    );
    lean_dec(v_inst_411_);
    return v_res_414_;
}
pub unsafe fn l_Std_Iterators_Types_Append_instIterator___redArg___lam__0(
    mut v_toPure_415_: *mut LeanObject,
    mut v_____do__lift_416_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_it_417_: *mut LeanObject = core::ptr::null_mut();
    let mut v_out_418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_420_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_421_: u8 = 0;
    let mut v___x_422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_425_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_427_: u8 = 0;
    let mut v_it_428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_430_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_431_: u8 = 0;
    let mut v___x_432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_435_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_437_: u8 = 0;
    let mut v___x_438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_439_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_____do__lift_416_) {
                0 => {
                    v_it_417_ = lean_ctor_get(v_____do__lift_416_, 0);
                    v_out_418_ = lean_ctor_get(v_____do__lift_416_, 1);
                    v_isSharedCheck_427_ = (!lean_is_exclusive(v_____do__lift_416_)) as u8;
                    if v_isSharedCheck_427_ == 0 {
                        v___x_420_ = v_____do__lift_416_;
                        v_isShared_421_ = v_isSharedCheck_427_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_out_418_);
                        lean_inc(v_it_417_);
                        lean_dec(v_____do__lift_416_);
                        v___x_420_ = lean_box(0);
                        v_isShared_421_ = v_isSharedCheck_427_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_it_428_ = lean_ctor_get(v_____do__lift_416_, 0);
                    v_isSharedCheck_437_ = (!lean_is_exclusive(v_____do__lift_416_)) as u8;
                    if v_isSharedCheck_437_ == 0 {
                        v___x_430_ = v_____do__lift_416_;
                        v_isShared_431_ = v_isSharedCheck_437_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_it_428_);
                        lean_dec(v_____do__lift_416_);
                        v___x_430_ = lean_box(0);
                        v_isShared_431_ = v_isSharedCheck_437_;
                        state = 3;
                        continue;
                    }
                }
                _ => {
                    v___x_438_ = lean_box(2);
                    v___x_439_ = lean_apply_2(v_toPure_415_, lean_box(0), v___x_438_);
                    return v___x_439_;
                }
            },
            1 => {
                v___x_422_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_422_, 0, v_it_417_);
                if v_isShared_421_ == 0 {
                    lean_ctor_set(v___x_420_, 0, v___x_422_);
                    v___x_424_ = v___x_420_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_426_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_426_, 0, v___x_422_);
                    lean_ctor_set(v_reuseFailAlloc_426_, 1, v_out_418_);
                    v___x_424_ = v_reuseFailAlloc_426_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_425_ = lean_apply_2(v_toPure_415_, lean_box(0), v___x_424_);
                return v___x_425_;
            }
            3 => {
                v___x_432_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_432_, 0, v_it_428_);
                if v_isShared_431_ == 0 {
                    lean_ctor_set(v___x_430_, 0, v___x_432_);
                    v___x_434_ = v___x_430_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_436_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_436_, 0, v___x_432_);
                    v___x_434_ = v_reuseFailAlloc_436_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_435_ = lean_apply_2(v_toPure_415_, lean_box(0), v___x_434_);
                return v___x_435_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Iterators_Types_Append_instIterator___redArg___lam__1(
    mut v_a_440_: *mut LeanObject,
    mut v_toPure_441_: *mut LeanObject,
    mut v_____do__lift_442_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_it_443_: *mut LeanObject = core::ptr::null_mut();
    let mut v_out_444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_446_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_447_: u8 = 0;
    let mut v___x_448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_451_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_452_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_453_: u8 = 0;
    let mut v_it_454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_456_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_457_: u8 = 0;
    let mut v___x_458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_461_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_463_: u8 = 0;
    let mut v___x_464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_466_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_____do__lift_442_) {
                0 => {
                    v_it_443_ = lean_ctor_get(v_____do__lift_442_, 0);
                    v_out_444_ = lean_ctor_get(v_____do__lift_442_, 1);
                    v_isSharedCheck_453_ = (!lean_is_exclusive(v_____do__lift_442_)) as u8;
                    if v_isSharedCheck_453_ == 0 {
                        v___x_446_ = v_____do__lift_442_;
                        v_isShared_447_ = v_isSharedCheck_453_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_out_444_);
                        lean_inc(v_it_443_);
                        lean_dec(v_____do__lift_442_);
                        v___x_446_ = lean_box(0);
                        v_isShared_447_ = v_isSharedCheck_453_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_it_454_ = lean_ctor_get(v_____do__lift_442_, 0);
                    v_isSharedCheck_463_ = (!lean_is_exclusive(v_____do__lift_442_)) as u8;
                    if v_isSharedCheck_463_ == 0 {
                        v___x_456_ = v_____do__lift_442_;
                        v_isShared_457_ = v_isSharedCheck_463_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_it_454_);
                        lean_dec(v_____do__lift_442_);
                        v___x_456_ = lean_box(0);
                        v_isShared_457_ = v_isSharedCheck_463_;
                        state = 3;
                        continue;
                    }
                }
                _ => {
                    v___x_464_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_464_, 0, v_a_440_);
                    v___x_465_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_465_, 0, v___x_464_);
                    v___x_466_ = lean_apply_2(v_toPure_441_, lean_box(0), v___x_465_);
                    return v___x_466_;
                }
            },
            1 => {
                v___x_448_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_448_, 0, v_it_443_);
                lean_ctor_set(v___x_448_, 1, v_a_440_);
                if v_isShared_447_ == 0 {
                    lean_ctor_set(v___x_446_, 0, v___x_448_);
                    v___x_450_ = v___x_446_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_452_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_452_, 0, v___x_448_);
                    lean_ctor_set(v_reuseFailAlloc_452_, 1, v_out_444_);
                    v___x_450_ = v_reuseFailAlloc_452_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_451_ = lean_apply_2(v_toPure_441_, lean_box(0), v___x_450_);
                return v___x_451_;
            }
            3 => {
                v___x_458_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_458_, 0, v_it_454_);
                lean_ctor_set(v___x_458_, 1, v_a_440_);
                if v_isShared_457_ == 0 {
                    lean_ctor_set(v___x_456_, 0, v___x_458_);
                    v___x_460_ = v___x_456_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_462_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_462_, 0, v___x_458_);
                    v___x_460_ = v_reuseFailAlloc_462_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_461_ = lean_apply_2(v_toPure_441_, lean_box(0), v___x_460_);
                return v___x_461_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Iterators_Types_Append_instIterator___redArg___lam__2(
    mut v_toPure_467_: *mut LeanObject,
    mut v_inst_468_: *mut LeanObject,
    mut v_toBind_469_: *mut LeanObject,
    mut v_inst_470_: *mut LeanObject,
    mut v___f_471_: *mut LeanObject,
    mut v_x_472_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_472_) == 0 {
        let mut v_a_473_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_474_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_475_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_476_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_477_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___f_471_);
        lean_dec(v_inst_470_);
        v_a_473_ = lean_ctor_get(v_x_472_, 0);
        lean_inc(v_a_473_);
        v_a_474_ = lean_ctor_get(v_x_472_, 1);
        lean_inc(v_a_474_);
        lean_dec_ref_known(v_x_472_, 2);
        v___f_475_ = lean_alloc_closure(
            l_Std_Iterators_Types_Append_instIterator___redArg___lam__1 as *mut core::ffi::c_void,
            3,
            2,
        );
        lean_closure_set(v___f_475_, 0, v_a_474_);
        lean_closure_set(v___f_475_, 1, v_toPure_467_);
        v___x_476_ = lean_apply_1(v_inst_468_, v_a_473_);
        v___x_477_ = lean_apply_4(
            v_toBind_469_,
            lean_box(0),
            lean_box(0),
            v___x_476_,
            v___f_475_,
        );
        return v___x_477_;
    } else {
        let mut v_a_478_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_479_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_480_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_inst_468_);
        lean_dec(v_toPure_467_);
        v_a_478_ = lean_ctor_get(v_x_472_, 0);
        lean_inc(v_a_478_);
        lean_dec_ref_known(v_x_472_, 1);
        v___x_479_ = lean_apply_1(v_inst_470_, v_a_478_);
        v___x_480_ = lean_apply_4(
            v_toBind_469_,
            lean_box(0),
            lean_box(0),
            v___x_479_,
            v___f_471_,
        );
        return v___x_480_;
    }
}
pub unsafe fn l_Std_Iterators_Types_Append_instIterator___redArg(
    mut v_inst_481_: *mut LeanObject,
    mut v_inst_482_: *mut LeanObject,
    mut v_inst_483_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_485_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_488_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_484_ = lean_ctor_get(v_inst_481_, 0);
    lean_inc_ref(v_toApplicative_484_);
    v_toBind_485_ = lean_ctor_get(v_inst_481_, 1);
    lean_inc(v_toBind_485_);
    lean_dec_ref(v_inst_481_);
    v_toPure_486_ = lean_ctor_get(v_toApplicative_484_, 1);
    lean_inc_n(v_toPure_486_, 2);
    lean_dec_ref(v_toApplicative_484_);
    v___f_487_ = lean_alloc_closure(
        l_Std_Iterators_Types_Append_instIterator___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_487_, 0, v_toPure_486_);
    v___f_488_ = lean_alloc_closure(
        l_Std_Iterators_Types_Append_instIterator___redArg___lam__2 as *mut core::ffi::c_void,
        6,
        5,
    );
    lean_closure_set(v___f_488_, 0, v_toPure_486_);
    lean_closure_set(v___f_488_, 1, v_inst_482_);
    lean_closure_set(v___f_488_, 2, v_toBind_485_);
    lean_closure_set(v___f_488_, 3, v_inst_483_);
    lean_closure_set(v___f_488_, 4, v___f_487_);
    return v___f_488_;
}
pub unsafe fn l_Std_Iterators_Types_Append_instIterator(
    mut v_m_489_: *mut LeanObject,
    mut v_00_u03b2_490_: *mut LeanObject,
    mut v_00_u03b1_u2081_491_: *mut LeanObject,
    mut v_00_u03b1_u2082_492_: *mut LeanObject,
    mut v_inst_493_: *mut LeanObject,
    mut v_inst_494_: *mut LeanObject,
    mut v_inst_495_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_496_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_497_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_500_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_496_ = lean_ctor_get(v_inst_493_, 0);
    lean_inc_ref(v_toApplicative_496_);
    v_toBind_497_ = lean_ctor_get(v_inst_493_, 1);
    lean_inc(v_toBind_497_);
    lean_dec_ref(v_inst_493_);
    v_toPure_498_ = lean_ctor_get(v_toApplicative_496_, 1);
    lean_inc_n(v_toPure_498_, 2);
    lean_dec_ref(v_toApplicative_496_);
    v___f_499_ = lean_alloc_closure(
        l_Std_Iterators_Types_Append_instIterator___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_499_, 0, v_toPure_498_);
    v___f_500_ = lean_alloc_closure(
        l_Std_Iterators_Types_Append_instIterator___redArg___lam__2 as *mut core::ffi::c_void,
        6,
        5,
    );
    lean_closure_set(v___f_500_, 0, v_toPure_498_);
    lean_closure_set(v___f_500_, 1, v_inst_494_);
    lean_closure_set(v___f_500_, 2, v_toBind_497_);
    lean_closure_set(v___f_500_, 3, v_inst_495_);
    lean_closure_set(v___f_500_, 4, v___f_499_);
    return v___f_500_;
}
pub unsafe fn l_Std_Iterators_Types_Append_instIteratorLoop___redArg___lam__0(
    mut v_toPure_501_: *mut LeanObject,
    mut v_recur_502_: *mut LeanObject,
    mut v_it_503_: *mut LeanObject,
    mut v_____do__lift_504_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_504_) == 0 {
        let mut v_a_505_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_506_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_it_503_);
        lean_dec(v_recur_502_);
        v_a_505_ = lean_ctor_get(v_____do__lift_504_, 0);
        lean_inc(v_a_505_);
        lean_dec_ref_known(v_____do__lift_504_, 1);
        v___x_506_ = lean_apply_2(v_toPure_501_, lean_box(0), v_a_505_);
        return v___x_506_;
    } else {
        let mut v_a_507_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_508_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_toPure_501_);
        v_a_507_ = lean_ctor_get(v_____do__lift_504_, 0);
        lean_inc(v_a_507_);
        lean_dec_ref_known(v_____do__lift_504_, 1);
        v___x_508_ = lean_apply_4(v_recur_502_, v_it_503_, v_a_507_, lean_box(0), lean_box(0));
        return v___x_508_;
    }
}
pub unsafe fn l_Std_Iterators_Types_Append_instIteratorLoop___redArg___lam__1(
    mut v_toPure_509_: *mut LeanObject,
    mut v_recur_510_: *mut LeanObject,
    mut v___y_511_: *mut LeanObject,
    mut v_acc_512_: *mut LeanObject,
    mut v_toBind_513_: *mut LeanObject,
    mut v_s_514_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_s_514_) {
        0 => {
            let mut v_it_515_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_516_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_517_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_518_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_519_: *mut LeanObject = core::ptr::null_mut();
            v_it_515_ = lean_ctor_get(v_s_514_, 0);
            lean_inc(v_it_515_);
            v_out_516_ = lean_ctor_get(v_s_514_, 1);
            lean_inc(v_out_516_);
            lean_dec_ref_known(v_s_514_, 2);
            v___f_517_ = lean_alloc_closure(
                l_Std_Iterators_Types_Append_instIteratorLoop___redArg___lam__0
                    as *mut core::ffi::c_void,
                4,
                3,
            );
            lean_closure_set(v___f_517_, 0, v_toPure_509_);
            lean_closure_set(v___f_517_, 1, v_recur_510_);
            lean_closure_set(v___f_517_, 2, v_it_515_);
            v___x_518_ = lean_apply_3(v___y_511_, v_out_516_, lean_box(0), v_acc_512_);
            v___x_519_ = lean_apply_4(
                v_toBind_513_,
                lean_box(0),
                lean_box(0),
                v___x_518_,
                v___f_517_,
            );
            return v___x_519_;
        }
        1 => {
            let mut v_it_520_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_521_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_toBind_513_);
            lean_dec(v___y_511_);
            lean_dec(v_toPure_509_);
            v_it_520_ = lean_ctor_get(v_s_514_, 0);
            lean_inc(v_it_520_);
            lean_dec_ref_known(v_s_514_, 1);
            v___x_521_ = lean_apply_4(
                v_recur_510_,
                v_it_520_,
                v_acc_512_,
                lean_box(0),
                lean_box(0),
            );
            return v___x_521_;
        }
        _ => {
            let mut v___x_522_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_toBind_513_);
            lean_dec(v___y_511_);
            lean_dec(v_recur_510_);
            v___x_522_ = lean_apply_2(v_toPure_509_, lean_box(0), v_acc_512_);
            return v___x_522_;
        }
    }
}
pub unsafe fn l_Std_Iterators_Types_Append_instIteratorLoop___redArg___lam__4(
    mut v_inst_523_: *mut LeanObject,
    mut v_toPure_524_: *mut LeanObject,
    mut v___y_525_: *mut LeanObject,
    mut v_toBind_526_: *mut LeanObject,
    mut v_inst_527_: *mut LeanObject,
    mut v_lift_528_: *mut LeanObject,
    mut v_inst_529_: *mut LeanObject,
    mut v_it_530_: *mut LeanObject,
    mut v_acc_531_: *mut LeanObject,
    mut v_hP_532_: *mut LeanObject,
    mut v_recur_533_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_537_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_534_ = lean_ctor_get(v_inst_523_, 0);
    lean_inc_ref(v_toApplicative_534_);
    v_toBind_535_ = lean_ctor_get(v_inst_523_, 1);
    lean_inc(v_toBind_535_);
    lean_dec_ref(v_inst_523_);
    v_toPure_536_ = lean_ctor_get(v_toApplicative_534_, 1);
    lean_inc(v_toPure_536_);
    lean_dec_ref(v_toApplicative_534_);
    v___f_537_ = lean_alloc_closure(
        l_Std_Iterators_Types_Append_instIteratorLoop___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        5,
    );
    lean_closure_set(v___f_537_, 0, v_toPure_524_);
    lean_closure_set(v___f_537_, 1, v_recur_533_);
    lean_closure_set(v___f_537_, 2, v___y_525_);
    lean_closure_set(v___f_537_, 3, v_acc_531_);
    lean_closure_set(v___f_537_, 4, v_toBind_526_);
    if lean_obj_tag(v_it_530_) == 0 {
        let mut v_a_538_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_539_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_540_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_541_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_542_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_543_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_inst_529_);
        v_a_538_ = lean_ctor_get(v_it_530_, 0);
        lean_inc(v_a_538_);
        v_a_539_ = lean_ctor_get(v_it_530_, 1);
        lean_inc(v_a_539_);
        lean_dec_ref_known(v_it_530_, 2);
        v___f_540_ = lean_alloc_closure(
            l_Std_Iterators_Types_Append_instIterator___redArg___lam__1 as *mut core::ffi::c_void,
            3,
            2,
        );
        lean_closure_set(v___f_540_, 0, v_a_539_);
        lean_closure_set(v___f_540_, 1, v_toPure_536_);
        v___x_541_ = lean_apply_1(v_inst_527_, v_a_538_);
        v___x_542_ = lean_apply_4(
            v_toBind_535_,
            lean_box(0),
            lean_box(0),
            v___x_541_,
            v___f_540_,
        );
        v___x_543_ = lean_apply_4(
            v_lift_528_,
            lean_box(0),
            lean_box(0),
            v___f_537_,
            v___x_542_,
        );
        return v___x_543_;
    } else {
        let mut v_a_544_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_545_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_546_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_547_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_548_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_inst_527_);
        v_a_544_ = lean_ctor_get(v_it_530_, 0);
        lean_inc(v_a_544_);
        lean_dec_ref_known(v_it_530_, 1);
        v___f_545_ = lean_alloc_closure(
            l_Std_Iterators_Types_Append_instIterator___redArg___lam__0 as *mut core::ffi::c_void,
            2,
            1,
        );
        lean_closure_set(v___f_545_, 0, v_toPure_536_);
        v___x_546_ = lean_apply_1(v_inst_529_, v_a_544_);
        v___x_547_ = lean_apply_4(
            v_toBind_535_,
            lean_box(0),
            lean_box(0),
            v___x_546_,
            v___f_545_,
        );
        v___x_548_ = lean_apply_4(
            v_lift_528_,
            lean_box(0),
            lean_box(0),
            v___f_537_,
            v___x_547_,
        );
        return v___x_548_;
    }
}
pub unsafe fn l_Std_Iterators_Types_Append_instIteratorLoop___redArg___lam__2(
    mut v_inst_549_: *mut LeanObject,
    mut v_inst_550_: *mut LeanObject,
    mut v_inst_551_: *mut LeanObject,
    mut v_inst_552_: *mut LeanObject,
    mut v_lift_553_: *mut LeanObject,
    mut v_00_u03b3_554_: *mut LeanObject,
    mut v_Pl_555_: *mut LeanObject,
    mut v_it_556_: *mut LeanObject,
    mut v_init_557_: *mut LeanObject,
    mut v___y_558_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_559_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_560_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_563_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_559_ = lean_ctor_get(v_inst_549_, 0);
    lean_inc_ref(v_toApplicative_559_);
    v_toBind_560_ = lean_ctor_get(v_inst_549_, 1);
    lean_inc(v_toBind_560_);
    lean_dec_ref(v_inst_549_);
    v_toPure_561_ = lean_ctor_get(v_toApplicative_559_, 1);
    lean_inc(v_toPure_561_);
    lean_dec_ref(v_toApplicative_559_);
    v___f_562_ = lean_alloc_closure(
        l_Std_Iterators_Types_Append_instIteratorLoop___redArg___lam__4 as *mut core::ffi::c_void,
        11,
        7,
    );
    lean_closure_set(v___f_562_, 0, v_inst_550_);
    lean_closure_set(v___f_562_, 1, v_toPure_561_);
    lean_closure_set(v___f_562_, 2, v___y_558_);
    lean_closure_set(v___f_562_, 3, v_toBind_560_);
    lean_closure_set(v___f_562_, 4, v_inst_551_);
    lean_closure_set(v___f_562_, 5, v_lift_553_);
    lean_closure_set(v___f_562_, 6, v_inst_552_);
    v___x_563_ =
        l_WellFounded_opaqueFix_u2083___redArg(v___f_562_, v_it_556_, v_init_557_, lean_box(0));
    return v___x_563_;
}
pub unsafe fn l_Std_Iterators_Types_Append_instIteratorLoop___redArg(
    mut v_inst_564_: *mut LeanObject,
    mut v_inst_565_: *mut LeanObject,
    mut v_inst_566_: *mut LeanObject,
    mut v_inst_567_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_568_: *mut LeanObject = core::ptr::null_mut();
    v___f_568_ = lean_alloc_closure(
        l_Std_Iterators_Types_Append_instIteratorLoop___redArg___lam__2 as *mut core::ffi::c_void,
        10,
        4,
    );
    lean_closure_set(v___f_568_, 0, v_inst_565_);
    lean_closure_set(v___f_568_, 1, v_inst_564_);
    lean_closure_set(v___f_568_, 2, v_inst_566_);
    lean_closure_set(v___f_568_, 3, v_inst_567_);
    return v___f_568_;
}
pub unsafe fn l_Std_Iterators_Types_Append_instIteratorLoop(
    mut v_m_569_: *mut LeanObject,
    mut v_00_u03b2_570_: *mut LeanObject,
    mut v_00_u03b1_u2081_571_: *mut LeanObject,
    mut v_00_u03b1_u2082_572_: *mut LeanObject,
    mut v_n_573_: *mut LeanObject,
    mut v_inst_574_: *mut LeanObject,
    mut v_inst_575_: *mut LeanObject,
    mut v_inst_576_: *mut LeanObject,
    mut v_inst_577_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_578_: *mut LeanObject = core::ptr::null_mut();
    v___f_578_ = lean_alloc_closure(
        l_Std_Iterators_Types_Append_instIteratorLoop___redArg___lam__2 as *mut core::ffi::c_void,
        10,
        4,
    );
    lean_closure_set(v___f_578_, 0, v_inst_575_);
    lean_closure_set(v___f_578_, 1, v_inst_574_);
    lean_closure_set(v___f_578_, 2, v_inst_576_);
    lean_closure_set(v___f_578_, 3, v_inst_577_);
    return v___f_578_;
}
pub unsafe fn l_Std_Iterators_Types_Append_instFinitenessRelation(
    mut v_00_u03b1_u2081_579_: *mut LeanObject,
    mut v_00_u03b1_u2082_580_: *mut LeanObject,
    mut v_m_581_: *mut LeanObject,
    mut v_00_u03b2_582_: *mut LeanObject,
    mut v_inst_583_: *mut LeanObject,
    mut v_inst_584_: *mut LeanObject,
    mut v_inst_585_: *mut LeanObject,
    mut v_inst_586_: *mut LeanObject,
    mut v_inst_587_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_588_: *mut LeanObject = core::ptr::null_mut();
    v___x_588_ = lean_box(0);
    return v___x_588_;
}
pub unsafe fn l_Std_Iterators_Types_Append_instFinitenessRelation___boxed(
    mut v_00_u03b1_u2081_589_: *mut LeanObject,
    mut v_00_u03b1_u2082_590_: *mut LeanObject,
    mut v_m_591_: *mut LeanObject,
    mut v_00_u03b2_592_: *mut LeanObject,
    mut v_inst_593_: *mut LeanObject,
    mut v_inst_594_: *mut LeanObject,
    mut v_inst_595_: *mut LeanObject,
    mut v_inst_596_: *mut LeanObject,
    mut v_inst_597_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_598_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_inst_595_);
    lean_dec(v_inst_594_);
    lean_dec_ref(v_inst_593_);
    return v_res_598_;
}
pub unsafe fn l___private_Init_Data_Iterators_Combinators_Monadic_Append_0__Std_Iterators_Types_Append_instProductivenessRelation(
    mut v_00_u03b1_u2081_599_: *mut LeanObject,
    mut v_00_u03b1_u2082_600_: *mut LeanObject,
    mut v_m_601_: *mut LeanObject,
    mut v_00_u03b2_602_: *mut LeanObject,
    mut v_inst_603_: *mut LeanObject,
    mut v_inst_604_: *mut LeanObject,
    mut v_inst_605_: *mut LeanObject,
    mut v_inst_606_: *mut LeanObject,
    mut v_inst_607_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_608_: *mut LeanObject = core::ptr::null_mut();
    v___x_608_ = lean_box(0);
    return v___x_608_;
}
pub unsafe fn l___private_Init_Data_Iterators_Combinators_Monadic_Append_0__Std_Iterators_Types_Append_instProductivenessRelation___boxed(
    mut v_00_u03b1_u2081_609_: *mut LeanObject,
    mut v_00_u03b1_u2082_610_: *mut LeanObject,
    mut v_m_611_: *mut LeanObject,
    mut v_00_u03b2_612_: *mut LeanObject,
    mut v_inst_613_: *mut LeanObject,
    mut v_inst_614_: *mut LeanObject,
    mut v_inst_615_: *mut LeanObject,
    mut v_inst_616_: *mut LeanObject,
    mut v_inst_617_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_618_: *mut LeanObject = core::ptr::null_mut();
    v_res_618_ = l___private_Init_Data_Iterators_Combinators_Monadic_Append_0__Std_Iterators_Types_Append_instProductivenessRelation(v_00_u03b1_u2081_609_, v_00_u03b1_u2082_610_, v_m_611_, v_00_u03b2_612_, v_inst_613_, v_inst_614_, v_inst_615_, v_inst_616_, v_inst_617_);
    lean_dec(v_inst_615_);
    lean_dec(v_inst_614_);
    lean_dec_ref(v_inst_613_);
    return v_res_618_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Iterators_Combinators_Monadic_Append(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Loop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Classical(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_ByCases(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Iterators_Combinators_Monadic_Append(
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
pub unsafe fn initialize_Init_Data_Iterators_Combinators_Monadic_Append(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Iterators_Consumers_Monadic_Loop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Classical(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Option_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_ByCases(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Combinators_Monadic_Append(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_Iterators_Combinators_Monadic_Append(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_Iterators_Combinators_Monadic_Append(builtin);
}
