// Lean compiler output
// Module: Init.Data.Iterators.Combinators.Monadic.FlatMap
// Imports: Init.Data.Iterators.Combinators.Monadic.FilterMap Init.Data.Option.Lemmas
use crate::r#gen::Init::Data::Iterators::Combinators::Monadic::FilterMap::{
    initialize_Init_Data_Iterators_Combinators_Monadic_FilterMap,
    runtime_initialize_Init_Data_Iterators_Combinators_Monadic_FilterMap,
};
use crate::r#gen::Init::Data::Option::Lemmas::{
    initialize_Init_Data_Option_Lemmas, runtime_initialize_Init_Data_Option_Lemmas,
};
use crate::r#gen::Init::WFExtrinsicFix::l_WellFounded_opaqueFix_u2083___redArg;
pub unsafe fn l___private_Init_Data_Iterators_Combinators_Monadic_FlatMap_0__Std_IterM_flattenAfter___redArg(
    mut v_it_u2081_333_: *mut leanh::LeanObject,
    mut v_it_u2082_334_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_335_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_335_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_335_, 0, v_it_u2081_333_);
    leanh::lean_ctor_set(v___x_335_, 1, v_it_u2082_334_);
    return v___x_335_;
}
pub unsafe fn l___private_Init_Data_Iterators_Combinators_Monadic_FlatMap_0__Std_IterM_flattenAfter(
    mut v_00_u03b1_336_: *mut leanh::LeanObject,
    mut v_00_u03b1_u2082_337_: *mut leanh::LeanObject,
    mut v_00_u03b2_338_: *mut leanh::LeanObject,
    mut v_m_339_: *mut leanh::LeanObject,
    mut v_inst_340_: *mut leanh::LeanObject,
    mut v_inst_341_: *mut leanh::LeanObject,
    mut v_inst_342_: *mut leanh::LeanObject,
    mut v_it_u2081_343_: *mut leanh::LeanObject,
    mut v_it_u2082_344_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_345_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_345_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_345_, 0, v_it_u2081_343_);
    leanh::lean_ctor_set(v___x_345_, 1, v_it_u2082_344_);
    return v___x_345_;
}
pub unsafe fn l___private_Init_Data_Iterators_Combinators_Monadic_FlatMap_0__Std_IterM_flattenAfter___boxed(
    mut v_00_u03b1_346_: *mut leanh::LeanObject,
    mut v_00_u03b1_u2082_347_: *mut leanh::LeanObject,
    mut v_00_u03b2_348_: *mut leanh::LeanObject,
    mut v_m_349_: *mut leanh::LeanObject,
    mut v_inst_350_: *mut leanh::LeanObject,
    mut v_inst_351_: *mut leanh::LeanObject,
    mut v_inst_352_: *mut leanh::LeanObject,
    mut v_it_u2081_353_: *mut leanh::LeanObject,
    mut v_it_u2082_354_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_355_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_355_ =
        l___private_Init_Data_Iterators_Combinators_Monadic_FlatMap_0__Std_IterM_flattenAfter(
            v_00_u03b1_346_,
            v_00_u03b1_u2082_347_,
            v_00_u03b2_348_,
            v_m_349_,
            v_inst_350_,
            v_inst_351_,
            v_inst_352_,
            v_it_u2081_353_,
            v_it_u2082_354_,
        );
    leanh::lean_dec(v_inst_352_);
    leanh::lean_dec(v_inst_351_);
    leanh::lean_dec_ref(v_inst_350_);
    return v_res_355_;
}
pub unsafe fn l_Std_IterM_flatMapAfterM___redArg(
    mut v_it_u2081_356_: *mut leanh::LeanObject,
    mut v_it_u2082_357_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_358_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_358_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_358_, 0, v_it_u2081_356_);
    leanh::lean_ctor_set(v___x_358_, 1, v_it_u2082_357_);
    return v___x_358_;
}
pub unsafe fn l_Std_IterM_flatMapAfterM(
    mut v_00_u03b1_359_: *mut leanh::LeanObject,
    mut v_00_u03b2_360_: *mut leanh::LeanObject,
    mut v_00_u03b1_u2082_361_: *mut leanh::LeanObject,
    mut v_00_u03b3_362_: *mut leanh::LeanObject,
    mut v_m_363_: *mut leanh::LeanObject,
    mut v_inst_364_: *mut leanh::LeanObject,
    mut v_inst_365_: *mut leanh::LeanObject,
    mut v_inst_366_: *mut leanh::LeanObject,
    mut v_inst_367_: *mut leanh::LeanObject,
    mut v_f_368_: *mut leanh::LeanObject,
    mut v_it_u2081_369_: *mut leanh::LeanObject,
    mut v_it_u2082_370_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_371_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_371_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_371_, 0, v_it_u2081_369_);
    leanh::lean_ctor_set(v___x_371_, 1, v_it_u2082_370_);
    return v___x_371_;
}
pub unsafe fn l_Std_IterM_flatMapAfterM___boxed(
    mut v_00_u03b1_372_: *mut leanh::LeanObject,
    mut v_00_u03b2_373_: *mut leanh::LeanObject,
    mut v_00_u03b1_u2082_374_: *mut leanh::LeanObject,
    mut v_00_u03b3_375_: *mut leanh::LeanObject,
    mut v_m_376_: *mut leanh::LeanObject,
    mut v_inst_377_: *mut leanh::LeanObject,
    mut v_inst_378_: *mut leanh::LeanObject,
    mut v_inst_379_: *mut leanh::LeanObject,
    mut v_inst_380_: *mut leanh::LeanObject,
    mut v_f_381_: *mut leanh::LeanObject,
    mut v_it_u2081_382_: *mut leanh::LeanObject,
    mut v_it_u2082_383_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_384_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_384_ = l_Std_IterM_flatMapAfterM(
        v_00_u03b1_372_,
        v_00_u03b2_373_,
        v_00_u03b1_u2082_374_,
        v_00_u03b3_375_,
        v_m_376_,
        v_inst_377_,
        v_inst_378_,
        v_inst_379_,
        v_inst_380_,
        v_f_381_,
        v_it_u2081_382_,
        v_it_u2082_383_,
    );
    leanh::lean_dec(v_f_381_);
    leanh::lean_dec(v_inst_380_);
    leanh::lean_dec(v_inst_379_);
    leanh::lean_dec(v_inst_378_);
    leanh::lean_dec_ref(v_inst_377_);
    return v_res_384_;
}
pub unsafe fn l_Std_IterM_flatMapM___redArg(
    mut v_it_385_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_387_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_386_ = leanh::lean_box(0);
    v___x_387_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_387_, 0, v_it_385_);
    leanh::lean_ctor_set(v___x_387_, 1, v___x_386_);
    return v___x_387_;
}
pub unsafe fn l_Std_IterM_flatMapM(
    mut v_00_u03b1_388_: *mut leanh::LeanObject,
    mut v_00_u03b2_389_: *mut leanh::LeanObject,
    mut v_00_u03b1_u2082_390_: *mut leanh::LeanObject,
    mut v_00_u03b3_391_: *mut leanh::LeanObject,
    mut v_m_392_: *mut leanh::LeanObject,
    mut v_inst_393_: *mut leanh::LeanObject,
    mut v_inst_394_: *mut leanh::LeanObject,
    mut v_inst_395_: *mut leanh::LeanObject,
    mut v_inst_396_: *mut leanh::LeanObject,
    mut v_f_397_: *mut leanh::LeanObject,
    mut v_it_398_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_400_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_399_ = leanh::lean_box(0);
    v___x_400_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_400_, 0, v_it_398_);
    leanh::lean_ctor_set(v___x_400_, 1, v___x_399_);
    return v___x_400_;
}
pub unsafe fn l_Std_IterM_flatMapM___boxed(
    mut v_00_u03b1_401_: *mut leanh::LeanObject,
    mut v_00_u03b2_402_: *mut leanh::LeanObject,
    mut v_00_u03b1_u2082_403_: *mut leanh::LeanObject,
    mut v_00_u03b3_404_: *mut leanh::LeanObject,
    mut v_m_405_: *mut leanh::LeanObject,
    mut v_inst_406_: *mut leanh::LeanObject,
    mut v_inst_407_: *mut leanh::LeanObject,
    mut v_inst_408_: *mut leanh::LeanObject,
    mut v_inst_409_: *mut leanh::LeanObject,
    mut v_f_410_: *mut leanh::LeanObject,
    mut v_it_411_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_412_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_412_ = l_Std_IterM_flatMapM(
        v_00_u03b1_401_,
        v_00_u03b2_402_,
        v_00_u03b1_u2082_403_,
        v_00_u03b3_404_,
        v_m_405_,
        v_inst_406_,
        v_inst_407_,
        v_inst_408_,
        v_inst_409_,
        v_f_410_,
        v_it_411_,
    );
    leanh::lean_dec(v_f_410_);
    leanh::lean_dec(v_inst_409_);
    leanh::lean_dec(v_inst_408_);
    leanh::lean_dec(v_inst_407_);
    leanh::lean_dec_ref(v_inst_406_);
    return v_res_412_;
}
pub unsafe fn l_Std_IterM_flatMapAfter___redArg(
    mut v_it_u2081_413_: *mut leanh::LeanObject,
    mut v_it_u2082_414_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_415_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_415_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_415_, 0, v_it_u2081_413_);
    leanh::lean_ctor_set(v___x_415_, 1, v_it_u2082_414_);
    return v___x_415_;
}
pub unsafe fn l_Std_IterM_flatMapAfter(
    mut v_00_u03b1_416_: *mut leanh::LeanObject,
    mut v_00_u03b2_417_: *mut leanh::LeanObject,
    mut v_00_u03b1_u2082_418_: *mut leanh::LeanObject,
    mut v_00_u03b3_419_: *mut leanh::LeanObject,
    mut v_m_420_: *mut leanh::LeanObject,
    mut v_inst_421_: *mut leanh::LeanObject,
    mut v_inst_422_: *mut leanh::LeanObject,
    mut v_inst_423_: *mut leanh::LeanObject,
    mut v_f_424_: *mut leanh::LeanObject,
    mut v_it_u2081_425_: *mut leanh::LeanObject,
    mut v_it_u2082_426_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_427_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_427_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_427_, 0, v_it_u2081_425_);
    leanh::lean_ctor_set(v___x_427_, 1, v_it_u2082_426_);
    return v___x_427_;
}
pub unsafe fn l_Std_IterM_flatMapAfter___boxed(
    mut v_00_u03b1_428_: *mut leanh::LeanObject,
    mut v_00_u03b2_429_: *mut leanh::LeanObject,
    mut v_00_u03b1_u2082_430_: *mut leanh::LeanObject,
    mut v_00_u03b3_431_: *mut leanh::LeanObject,
    mut v_m_432_: *mut leanh::LeanObject,
    mut v_inst_433_: *mut leanh::LeanObject,
    mut v_inst_434_: *mut leanh::LeanObject,
    mut v_inst_435_: *mut leanh::LeanObject,
    mut v_f_436_: *mut leanh::LeanObject,
    mut v_it_u2081_437_: *mut leanh::LeanObject,
    mut v_it_u2082_438_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_439_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_439_ = l_Std_IterM_flatMapAfter(
        v_00_u03b1_428_,
        v_00_u03b2_429_,
        v_00_u03b1_u2082_430_,
        v_00_u03b3_431_,
        v_m_432_,
        v_inst_433_,
        v_inst_434_,
        v_inst_435_,
        v_f_436_,
        v_it_u2081_437_,
        v_it_u2082_438_,
    );
    leanh::lean_dec(v_f_436_);
    leanh::lean_dec(v_inst_435_);
    leanh::lean_dec(v_inst_434_);
    leanh::lean_dec_ref(v_inst_433_);
    return v_res_439_;
}
pub unsafe fn l_Std_IterM_flatMap___redArg(
    mut v_it_440_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_442_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_441_ = leanh::lean_box(0);
    v___x_442_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_442_, 0, v_it_440_);
    leanh::lean_ctor_set(v___x_442_, 1, v___x_441_);
    return v___x_442_;
}
pub unsafe fn l_Std_IterM_flatMap(
    mut v_00_u03b1_443_: *mut leanh::LeanObject,
    mut v_00_u03b2_444_: *mut leanh::LeanObject,
    mut v_00_u03b1_u2082_445_: *mut leanh::LeanObject,
    mut v_00_u03b3_446_: *mut leanh::LeanObject,
    mut v_m_447_: *mut leanh::LeanObject,
    mut v_inst_448_: *mut leanh::LeanObject,
    mut v_inst_449_: *mut leanh::LeanObject,
    mut v_inst_450_: *mut leanh::LeanObject,
    mut v_f_451_: *mut leanh::LeanObject,
    mut v_it_452_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_454_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_453_ = leanh::lean_box(0);
    v___x_454_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_454_, 0, v_it_452_);
    leanh::lean_ctor_set(v___x_454_, 1, v___x_453_);
    return v___x_454_;
}
pub unsafe fn l_Std_IterM_flatMap___boxed(
    mut v_00_u03b1_455_: *mut leanh::LeanObject,
    mut v_00_u03b2_456_: *mut leanh::LeanObject,
    mut v_00_u03b1_u2082_457_: *mut leanh::LeanObject,
    mut v_00_u03b3_458_: *mut leanh::LeanObject,
    mut v_m_459_: *mut leanh::LeanObject,
    mut v_inst_460_: *mut leanh::LeanObject,
    mut v_inst_461_: *mut leanh::LeanObject,
    mut v_inst_462_: *mut leanh::LeanObject,
    mut v_f_463_: *mut leanh::LeanObject,
    mut v_it_464_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_465_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_465_ = l_Std_IterM_flatMap(
        v_00_u03b1_455_,
        v_00_u03b2_456_,
        v_00_u03b1_u2082_457_,
        v_00_u03b3_458_,
        v_m_459_,
        v_inst_460_,
        v_inst_461_,
        v_inst_462_,
        v_f_463_,
        v_it_464_,
    );
    leanh::lean_dec(v_f_463_);
    leanh::lean_dec(v_inst_462_);
    leanh::lean_dec(v_inst_461_);
    leanh::lean_dec_ref(v_inst_460_);
    return v_res_465_;
}
pub unsafe fn l_Std_Iterators_Types_Flatten_instIterator___redArg___lam__0(
    mut v_toPure_466_: *mut leanh::LeanObject,
    mut v_it_u2082_467_: *mut leanh::LeanObject,
    mut v_____do__lift_468_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_it_469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_out_470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_it_475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_478_: u8 = 0;
    let mut v___x_479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_484_: u8 = 0;
    let mut v___x_485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_____do__lift_468_) {
                0 => {
                    leanh::lean_dec(v_it_u2082_467_);
                    v_it_469_ = leanh::lean_ctor_get(v_____do__lift_468_, 0);
                    leanh::lean_inc(v_it_469_);
                    v_out_470_ = leanh::lean_ctor_get(v_____do__lift_468_, 1);
                    leanh::lean_inc(v_out_470_);
                    leanh::lean_dec_ref_known(v_____do__lift_468_, 2);
                    v___x_471_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_471_, 0, v_out_470_);
                    v___x_472_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_472_, 0, v_it_469_);
                    leanh::lean_ctor_set(v___x_472_, 1, v___x_471_);
                    v___x_473_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_473_, 0, v___x_472_);
                    v___x_474_ = leanh::lean_apply_2(
                        v_toPure_466_,
                        leanh::lean_box(0),
                        v___x_473_,
                    );
                    return v___x_474_;
                }
                1 => {
                    v_it_475_ = leanh::lean_ctor_get(v_____do__lift_468_, 0);
                    v_isSharedCheck_484_ =
                        (!leanh::lean_is_exclusive(v_____do__lift_468_)) as u8;
                    if v_isSharedCheck_484_ == 0 {
                        v___x_477_ = v_____do__lift_468_;
                        v_isShared_478_ = v_isSharedCheck_484_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_it_475_);
                        leanh::lean_dec(v_____do__lift_468_);
                        v___x_477_ = leanh::lean_box(0);
                        v_isShared_478_ = v_isSharedCheck_484_;
                        state = 1;
                        continue;
                    }
                }
                _ => {
                    leanh::lean_dec(v_it_u2082_467_);
                    v___x_485_ = leanh::lean_box(2);
                    v___x_486_ = leanh::lean_apply_2(
                        v_toPure_466_,
                        leanh::lean_box(0),
                        v___x_485_,
                    );
                    return v___x_486_;
                }
            },
            1 => {
                v___x_479_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_479_, 0, v_it_475_);
                leanh::lean_ctor_set(v___x_479_, 1, v_it_u2082_467_);
                if v_isShared_478_ == 0 {
                    leanh::lean_ctor_set(v___x_477_, 0, v___x_479_);
                    v___x_481_ = v___x_477_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_483_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_483_, 0, v___x_479_);
                    v___x_481_ = v_reuseFailAlloc_483_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_482_ = leanh::lean_apply_2(
                    v_toPure_466_,
                    leanh::lean_box(0),
                    v___x_481_,
                );
                return v___x_482_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Iterators_Types_Flatten_instIterator___redArg___lam__1(
    mut v_it_u2081_487_: *mut leanh::LeanObject,
    mut v_toPure_488_: *mut leanh::LeanObject,
    mut v_____do__lift_489_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_it_490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_out_491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_494_: u8 = 0;
    let mut v___x_495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_501_: u8 = 0;
    let mut v_it_502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_505_: u8 = 0;
    let mut v___x_506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_512_: u8 = 0;
    let mut v___x_513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_____do__lift_489_) {
                0 => {
                    v_it_490_ = leanh::lean_ctor_get(v_____do__lift_489_, 0);
                    v_out_491_ = leanh::lean_ctor_get(v_____do__lift_489_, 1);
                    v_isSharedCheck_501_ =
                        (!leanh::lean_is_exclusive(v_____do__lift_489_)) as u8;
                    if v_isSharedCheck_501_ == 0 {
                        v___x_493_ = v_____do__lift_489_;
                        v_isShared_494_ = v_isSharedCheck_501_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_out_491_);
                        leanh::lean_inc(v_it_490_);
                        leanh::lean_dec(v_____do__lift_489_);
                        v___x_493_ = leanh::lean_box(0);
                        v_isShared_494_ = v_isSharedCheck_501_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_it_502_ = leanh::lean_ctor_get(v_____do__lift_489_, 0);
                    v_isSharedCheck_512_ =
                        (!leanh::lean_is_exclusive(v_____do__lift_489_)) as u8;
                    if v_isSharedCheck_512_ == 0 {
                        v___x_504_ = v_____do__lift_489_;
                        v_isShared_505_ = v_isSharedCheck_512_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_it_502_);
                        leanh::lean_dec(v_____do__lift_489_);
                        v___x_504_ = leanh::lean_box(0);
                        v_isShared_505_ = v_isSharedCheck_512_;
                        state = 3;
                        continue;
                    }
                }
                _ => {
                    v___x_513_ = leanh::lean_box(0);
                    v___x_514_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_514_, 0, v_it_u2081_487_);
                    leanh::lean_ctor_set(v___x_514_, 1, v___x_513_);
                    v___x_515_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_515_, 0, v___x_514_);
                    v___x_516_ = leanh::lean_apply_2(
                        v_toPure_488_,
                        leanh::lean_box(0),
                        v___x_515_,
                    );
                    return v___x_516_;
                }
            },
            1 => {
                v___x_495_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_495_, 0, v_it_490_);
                v___x_496_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_496_, 0, v_it_u2081_487_);
                leanh::lean_ctor_set(v___x_496_, 1, v___x_495_);
                if v_isShared_494_ == 0 {
                    leanh::lean_ctor_set(v___x_493_, 0, v___x_496_);
                    v___x_498_ = v___x_493_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_500_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_500_, 0, v___x_496_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_500_, 1, v_out_491_);
                    v___x_498_ = v_reuseFailAlloc_500_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_499_ = leanh::lean_apply_2(
                    v_toPure_488_,
                    leanh::lean_box(0),
                    v___x_498_,
                );
                return v___x_499_;
            }
            3 => {
                v___x_506_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_506_, 0, v_it_502_);
                v___x_507_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_507_, 0, v_it_u2081_487_);
                leanh::lean_ctor_set(v___x_507_, 1, v___x_506_);
                if v_isShared_505_ == 0 {
                    leanh::lean_ctor_set(v___x_504_, 0, v___x_507_);
                    v___x_509_ = v___x_504_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_511_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_511_, 0, v___x_507_);
                    v___x_509_ = v_reuseFailAlloc_511_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_510_ = leanh::lean_apply_2(
                    v_toPure_488_,
                    leanh::lean_box(0),
                    v___x_509_,
                );
                return v___x_510_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Iterators_Types_Flatten_instIterator___redArg___lam__2(
    mut v_toPure_517_: *mut leanh::LeanObject,
    mut v_inst_518_: *mut leanh::LeanObject,
    mut v_toBind_519_: *mut leanh::LeanObject,
    mut v_inst_520_: *mut leanh::LeanObject,
    mut v_it_521_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_it_u2082_522_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_it_u2082_522_ = leanh::lean_ctor_get(v_it_521_, 1);
    leanh::lean_inc(v_it_u2082_522_);
    if leanh::lean_obj_tag(v_it_u2082_522_) == 0 {
        let mut v_it_u2081_523_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_524_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_525_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_526_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_inst_520_);
        v_it_u2081_523_ = leanh::lean_ctor_get(v_it_521_, 0);
        leanh::lean_inc(v_it_u2081_523_);
        leanh::lean_dec_ref(v_it_521_);
        v___f_524_ = leanh::lean_alloc_closure(
            l_Std_Iterators_Types_Flatten_instIterator___redArg___lam__0 as *mut core::ffi::c_void,
            3,
            2,
        );
        leanh::lean_closure_set(v___f_524_, 0, v_toPure_517_);
        leanh::lean_closure_set(v___f_524_, 1, v_it_u2082_522_);
        v___x_525_ = leanh::lean_apply_1(v_inst_518_, v_it_u2081_523_);
        v___x_526_ = leanh::lean_apply_4(
            v_toBind_519_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_525_,
            v___f_524_,
        );
        return v___x_526_;
    } else {
        let mut v_it_u2081_527_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_val_528_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_529_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_530_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_531_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_inst_518_);
        v_it_u2081_527_ = leanh::lean_ctor_get(v_it_521_, 0);
        leanh::lean_inc(v_it_u2081_527_);
        leanh::lean_dec_ref(v_it_521_);
        v_val_528_ = leanh::lean_ctor_get(v_it_u2082_522_, 0);
        leanh::lean_inc(v_val_528_);
        leanh::lean_dec_ref_known(v_it_u2082_522_, 1);
        v___f_529_ = leanh::lean_alloc_closure(
            l_Std_Iterators_Types_Flatten_instIterator___redArg___lam__1 as *mut core::ffi::c_void,
            3,
            2,
        );
        leanh::lean_closure_set(v___f_529_, 0, v_it_u2081_527_);
        leanh::lean_closure_set(v___f_529_, 1, v_toPure_517_);
        v___x_530_ = leanh::lean_apply_1(v_inst_520_, v_val_528_);
        v___x_531_ = leanh::lean_apply_4(
            v_toBind_519_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_530_,
            v___f_529_,
        );
        return v___x_531_;
    }
}
pub unsafe fn l_Std_Iterators_Types_Flatten_instIterator___redArg(
    mut v_inst_532_: *mut leanh::LeanObject,
    mut v_inst_533_: *mut leanh::LeanObject,
    mut v_inst_534_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_538_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_535_ = leanh::lean_ctor_get(v_inst_532_, 0);
    leanh::lean_inc_ref(v_toApplicative_535_);
    v_toBind_536_ = leanh::lean_ctor_get(v_inst_532_, 1);
    leanh::lean_inc(v_toBind_536_);
    leanh::lean_dec_ref(v_inst_532_);
    v_toPure_537_ = leanh::lean_ctor_get(v_toApplicative_535_, 1);
    leanh::lean_inc(v_toPure_537_);
    leanh::lean_dec_ref(v_toApplicative_535_);
    v___f_538_ = leanh::lean_alloc_closure(
        l_Std_Iterators_Types_Flatten_instIterator___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        4,
    );
    leanh::lean_closure_set(v___f_538_, 0, v_toPure_537_);
    leanh::lean_closure_set(v___f_538_, 1, v_inst_533_);
    leanh::lean_closure_set(v___f_538_, 2, v_toBind_536_);
    leanh::lean_closure_set(v___f_538_, 3, v_inst_534_);
    return v___f_538_;
}
pub unsafe fn l_Std_Iterators_Types_Flatten_instIterator(
    mut v_00_u03b1_539_: *mut leanh::LeanObject,
    mut v_00_u03b1_u2082_540_: *mut leanh::LeanObject,
    mut v_00_u03b2_541_: *mut leanh::LeanObject,
    mut v_m_542_: *mut leanh::LeanObject,
    mut v_inst_543_: *mut leanh::LeanObject,
    mut v_inst_544_: *mut leanh::LeanObject,
    mut v_inst_545_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_546_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_546_ =
        l_Std_Iterators_Types_Flatten_instIterator___redArg(v_inst_543_, v_inst_544_, v_inst_545_);
    return v___x_546_;
}
pub unsafe fn l___private_Init_Data_Iterators_Combinators_Monadic_FlatMap_0__Std_Iterators_Types_Flatten_instFinitenessRelation(
    mut v_00_u03b1_547_: *mut leanh::LeanObject,
    mut v_00_u03b1_u2082_548_: *mut leanh::LeanObject,
    mut v_00_u03b2_549_: *mut leanh::LeanObject,
    mut v_m_550_: *mut leanh::LeanObject,
    mut v_inst_551_: *mut leanh::LeanObject,
    mut v_inst_552_: *mut leanh::LeanObject,
    mut v_inst_553_: *mut leanh::LeanObject,
    mut v_inst_554_: *mut leanh::LeanObject,
    mut v_inst_555_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_556_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_556_ = leanh::lean_box(0);
    return v___x_556_;
}
pub unsafe fn l___private_Init_Data_Iterators_Combinators_Monadic_FlatMap_0__Std_Iterators_Types_Flatten_instFinitenessRelation___boxed(
    mut v_00_u03b1_557_: *mut leanh::LeanObject,
    mut v_00_u03b1_u2082_558_: *mut leanh::LeanObject,
    mut v_00_u03b2_559_: *mut leanh::LeanObject,
    mut v_m_560_: *mut leanh::LeanObject,
    mut v_inst_561_: *mut leanh::LeanObject,
    mut v_inst_562_: *mut leanh::LeanObject,
    mut v_inst_563_: *mut leanh::LeanObject,
    mut v_inst_564_: *mut leanh::LeanObject,
    mut v_inst_565_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_566_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_566_ = l___private_Init_Data_Iterators_Combinators_Monadic_FlatMap_0__Std_Iterators_Types_Flatten_instFinitenessRelation(v_00_u03b1_557_, v_00_u03b1_u2082_558_, v_00_u03b2_559_, v_m_560_, v_inst_561_, v_inst_562_, v_inst_563_, v_inst_564_, v_inst_565_);
    leanh::lean_dec(v_inst_563_);
    leanh::lean_dec(v_inst_562_);
    leanh::lean_dec_ref(v_inst_561_);
    return v_res_566_;
}
pub unsafe fn l___private_Init_Data_Iterators_Combinators_Monadic_FlatMap_0__Std_Iterators_Types_Flatten_instProductivenessRelation(
    mut v_00_u03b1_567_: *mut leanh::LeanObject,
    mut v_00_u03b1_u2082_568_: *mut leanh::LeanObject,
    mut v_00_u03b2_569_: *mut leanh::LeanObject,
    mut v_m_570_: *mut leanh::LeanObject,
    mut v_inst_571_: *mut leanh::LeanObject,
    mut v_inst_572_: *mut leanh::LeanObject,
    mut v_inst_573_: *mut leanh::LeanObject,
    mut v_inst_574_: *mut leanh::LeanObject,
    mut v_inst_575_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_576_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_576_ = leanh::lean_box(0);
    return v___x_576_;
}
pub unsafe fn l___private_Init_Data_Iterators_Combinators_Monadic_FlatMap_0__Std_Iterators_Types_Flatten_instProductivenessRelation___boxed(
    mut v_00_u03b1_577_: *mut leanh::LeanObject,
    mut v_00_u03b1_u2082_578_: *mut leanh::LeanObject,
    mut v_00_u03b2_579_: *mut leanh::LeanObject,
    mut v_m_580_: *mut leanh::LeanObject,
    mut v_inst_581_: *mut leanh::LeanObject,
    mut v_inst_582_: *mut leanh::LeanObject,
    mut v_inst_583_: *mut leanh::LeanObject,
    mut v_inst_584_: *mut leanh::LeanObject,
    mut v_inst_585_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_586_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_586_ = l___private_Init_Data_Iterators_Combinators_Monadic_FlatMap_0__Std_Iterators_Types_Flatten_instProductivenessRelation(v_00_u03b1_577_, v_00_u03b1_u2082_578_, v_00_u03b2_579_, v_m_580_, v_inst_581_, v_inst_582_, v_inst_583_, v_inst_584_, v_inst_585_);
    leanh::lean_dec(v_inst_583_);
    leanh::lean_dec(v_inst_582_);
    leanh::lean_dec_ref(v_inst_581_);
    return v_res_586_;
}
pub unsafe fn l_Std_Iterators_Types_Flatten_instIteratorLoop___redArg___lam__0(
    mut v_toPure_587_: *mut leanh::LeanObject,
    mut v_recur_588_: *mut leanh::LeanObject,
    mut v_it_589_: *mut leanh::LeanObject,
    mut v_____do__lift_590_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_590_) == 0 {
        let mut v_a_591_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_592_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_it_589_);
        leanh::lean_dec(v_recur_588_);
        v_a_591_ = leanh::lean_ctor_get(v_____do__lift_590_, 0);
        leanh::lean_inc(v_a_591_);
        leanh::lean_dec_ref_known(v_____do__lift_590_, 1);
        v___x_592_ = leanh::lean_apply_2(v_toPure_587_, leanh::lean_box(0), v_a_591_);
        return v___x_592_;
    } else {
        let mut v_a_593_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_594_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_toPure_587_);
        v_a_593_ = leanh::lean_ctor_get(v_____do__lift_590_, 0);
        leanh::lean_inc(v_a_593_);
        leanh::lean_dec_ref_known(v_____do__lift_590_, 1);
        v___x_594_ = leanh::lean_apply_4(
            v_recur_588_,
            v_it_589_,
            v_a_593_,
            leanh::lean_box(0),
            leanh::lean_box(0),
        );
        return v___x_594_;
    }
}
pub unsafe fn l_Std_Iterators_Types_Flatten_instIteratorLoop___redArg___lam__1(
    mut v_toPure_595_: *mut leanh::LeanObject,
    mut v_recur_596_: *mut leanh::LeanObject,
    mut v___y_597_: *mut leanh::LeanObject,
    mut v_acc_598_: *mut leanh::LeanObject,
    mut v_toBind_599_: *mut leanh::LeanObject,
    mut v_s_600_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_s_600_) {
        0 => {
            let mut v_it_601_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_602_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_603_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_604_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_605_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_it_601_ = leanh::lean_ctor_get(v_s_600_, 0);
            leanh::lean_inc(v_it_601_);
            v_out_602_ = leanh::lean_ctor_get(v_s_600_, 1);
            leanh::lean_inc(v_out_602_);
            leanh::lean_dec_ref_known(v_s_600_, 2);
            v___f_603_ = leanh::lean_alloc_closure(
                l_Std_Iterators_Types_Flatten_instIteratorLoop___redArg___lam__0
                    as *mut core::ffi::c_void,
                4,
                3,
            );
            leanh::lean_closure_set(v___f_603_, 0, v_toPure_595_);
            leanh::lean_closure_set(v___f_603_, 1, v_recur_596_);
            leanh::lean_closure_set(v___f_603_, 2, v_it_601_);
            v___x_604_ = leanh::lean_apply_3(
                v___y_597_,
                v_out_602_,
                leanh::lean_box(0),
                v_acc_598_,
            );
            v___x_605_ = leanh::lean_apply_4(
                v_toBind_599_,
                leanh::lean_box(0),
                leanh::lean_box(0),
                v___x_604_,
                v___f_603_,
            );
            return v___x_605_;
        }
        1 => {
            let mut v_it_606_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_607_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_toBind_599_);
            leanh::lean_dec(v___y_597_);
            leanh::lean_dec(v_toPure_595_);
            v_it_606_ = leanh::lean_ctor_get(v_s_600_, 0);
            leanh::lean_inc(v_it_606_);
            leanh::lean_dec_ref_known(v_s_600_, 1);
            v___x_607_ = leanh::lean_apply_4(
                v_recur_596_,
                v_it_606_,
                v_acc_598_,
                leanh::lean_box(0),
                leanh::lean_box(0),
            );
            return v___x_607_;
        }
        _ => {
            let mut v___x_608_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_toBind_599_);
            leanh::lean_dec(v___y_597_);
            leanh::lean_dec(v_recur_596_);
            v___x_608_ =
                leanh::lean_apply_2(v_toPure_595_, leanh::lean_box(0), v_acc_598_);
            return v___x_608_;
        }
    }
}
pub unsafe fn l_Std_Iterators_Types_Flatten_instIteratorLoop___redArg___lam__4(
    mut v_inst_609_: *mut leanh::LeanObject,
    mut v_toPure_610_: *mut leanh::LeanObject,
    mut v___y_611_: *mut leanh::LeanObject,
    mut v_toBind_612_: *mut leanh::LeanObject,
    mut v_inst_613_: *mut leanh::LeanObject,
    mut v_lift_614_: *mut leanh::LeanObject,
    mut v_inst_615_: *mut leanh::LeanObject,
    mut v_it_616_: *mut leanh::LeanObject,
    mut v_acc_617_: *mut leanh::LeanObject,
    mut v_hP_618_: *mut leanh::LeanObject,
    mut v_recur_619_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_it_u2081_623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_it_u2082_624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_625_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_620_ = leanh::lean_ctor_get(v_inst_609_, 0);
    leanh::lean_inc_ref(v_toApplicative_620_);
    v_toBind_621_ = leanh::lean_ctor_get(v_inst_609_, 1);
    leanh::lean_inc(v_toBind_621_);
    leanh::lean_dec_ref(v_inst_609_);
    v_toPure_622_ = leanh::lean_ctor_get(v_toApplicative_620_, 1);
    leanh::lean_inc(v_toPure_622_);
    leanh::lean_dec_ref(v_toApplicative_620_);
    v_it_u2081_623_ = leanh::lean_ctor_get(v_it_616_, 0);
    leanh::lean_inc(v_it_u2081_623_);
    v_it_u2082_624_ = leanh::lean_ctor_get(v_it_616_, 1);
    leanh::lean_inc(v_it_u2082_624_);
    leanh::lean_dec_ref(v_it_616_);
    v___f_625_ = leanh::lean_alloc_closure(
        l_Std_Iterators_Types_Flatten_instIteratorLoop___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        5,
    );
    leanh::lean_closure_set(v___f_625_, 0, v_toPure_610_);
    leanh::lean_closure_set(v___f_625_, 1, v_recur_619_);
    leanh::lean_closure_set(v___f_625_, 2, v___y_611_);
    leanh::lean_closure_set(v___f_625_, 3, v_acc_617_);
    leanh::lean_closure_set(v___f_625_, 4, v_toBind_612_);
    if leanh::lean_obj_tag(v_it_u2082_624_) == 0 {
        let mut v___f_626_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_627_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_628_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_629_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_inst_615_);
        v___f_626_ = leanh::lean_alloc_closure(
            l_Std_Iterators_Types_Flatten_instIterator___redArg___lam__0 as *mut core::ffi::c_void,
            3,
            2,
        );
        leanh::lean_closure_set(v___f_626_, 0, v_toPure_622_);
        leanh::lean_closure_set(v___f_626_, 1, v_it_u2082_624_);
        v___x_627_ = leanh::lean_apply_1(v_inst_613_, v_it_u2081_623_);
        v___x_628_ = leanh::lean_apply_4(
            v_toBind_621_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_627_,
            v___f_626_,
        );
        v___x_629_ = leanh::lean_apply_4(
            v_lift_614_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___f_625_,
            v___x_628_,
        );
        return v___x_629_;
    } else {
        let mut v_val_630_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_631_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_632_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_633_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_634_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_inst_613_);
        v_val_630_ = leanh::lean_ctor_get(v_it_u2082_624_, 0);
        leanh::lean_inc(v_val_630_);
        leanh::lean_dec_ref_known(v_it_u2082_624_, 1);
        v___f_631_ = leanh::lean_alloc_closure(
            l_Std_Iterators_Types_Flatten_instIterator___redArg___lam__1 as *mut core::ffi::c_void,
            3,
            2,
        );
        leanh::lean_closure_set(v___f_631_, 0, v_it_u2081_623_);
        leanh::lean_closure_set(v___f_631_, 1, v_toPure_622_);
        v___x_632_ = leanh::lean_apply_1(v_inst_615_, v_val_630_);
        v___x_633_ = leanh::lean_apply_4(
            v_toBind_621_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_632_,
            v___f_631_,
        );
        v___x_634_ = leanh::lean_apply_4(
            v_lift_614_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___f_625_,
            v___x_633_,
        );
        return v___x_634_;
    }
}
pub unsafe fn l_Std_Iterators_Types_Flatten_instIteratorLoop___redArg___lam__2(
    mut v_inst_635_: *mut leanh::LeanObject,
    mut v_inst_636_: *mut leanh::LeanObject,
    mut v_inst_637_: *mut leanh::LeanObject,
    mut v_inst_638_: *mut leanh::LeanObject,
    mut v_lift_639_: *mut leanh::LeanObject,
    mut v_00_u03b3_640_: *mut leanh::LeanObject,
    mut v_Pl_641_: *mut leanh::LeanObject,
    mut v_it_642_: *mut leanh::LeanObject,
    mut v_init_643_: *mut leanh::LeanObject,
    mut v___y_644_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_649_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_645_ = leanh::lean_ctor_get(v_inst_635_, 0);
    leanh::lean_inc_ref(v_toApplicative_645_);
    v_toBind_646_ = leanh::lean_ctor_get(v_inst_635_, 1);
    leanh::lean_inc(v_toBind_646_);
    leanh::lean_dec_ref(v_inst_635_);
    v_toPure_647_ = leanh::lean_ctor_get(v_toApplicative_645_, 1);
    leanh::lean_inc(v_toPure_647_);
    leanh::lean_dec_ref(v_toApplicative_645_);
    v___f_648_ = leanh::lean_alloc_closure(
        l_Std_Iterators_Types_Flatten_instIteratorLoop___redArg___lam__4 as *mut core::ffi::c_void,
        11,
        7,
    );
    leanh::lean_closure_set(v___f_648_, 0, v_inst_636_);
    leanh::lean_closure_set(v___f_648_, 1, v_toPure_647_);
    leanh::lean_closure_set(v___f_648_, 2, v___y_644_);
    leanh::lean_closure_set(v___f_648_, 3, v_toBind_646_);
    leanh::lean_closure_set(v___f_648_, 4, v_inst_637_);
    leanh::lean_closure_set(v___f_648_, 5, v_lift_639_);
    leanh::lean_closure_set(v___f_648_, 6, v_inst_638_);
    v___x_649_ = l_WellFounded_opaqueFix_u2083___redArg(
        v___f_648_,
        v_it_642_,
        v_init_643_,
        leanh::lean_box(0),
    );
    return v___x_649_;
}
pub unsafe fn l_Std_Iterators_Types_Flatten_instIteratorLoop___redArg(
    mut v_inst_650_: *mut leanh::LeanObject,
    mut v_inst_651_: *mut leanh::LeanObject,
    mut v_inst_652_: *mut leanh::LeanObject,
    mut v_inst_653_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_654_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_654_ = leanh::lean_alloc_closure(
        l_Std_Iterators_Types_Flatten_instIteratorLoop___redArg___lam__2 as *mut core::ffi::c_void,
        10,
        4,
    );
    leanh::lean_closure_set(v___f_654_, 0, v_inst_651_);
    leanh::lean_closure_set(v___f_654_, 1, v_inst_650_);
    leanh::lean_closure_set(v___f_654_, 2, v_inst_652_);
    leanh::lean_closure_set(v___f_654_, 3, v_inst_653_);
    return v___f_654_;
}
pub unsafe fn l_Std_Iterators_Types_Flatten_instIteratorLoop(
    mut v_00_u03b1_655_: *mut leanh::LeanObject,
    mut v_00_u03b1_u2082_656_: *mut leanh::LeanObject,
    mut v_00_u03b2_657_: *mut leanh::LeanObject,
    mut v_m_658_: *mut leanh::LeanObject,
    mut v_n_659_: *mut leanh::LeanObject,
    mut v_inst_660_: *mut leanh::LeanObject,
    mut v_inst_661_: *mut leanh::LeanObject,
    mut v_inst_662_: *mut leanh::LeanObject,
    mut v_inst_663_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_664_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_664_ = leanh::lean_alloc_closure(
        l_Std_Iterators_Types_Flatten_instIteratorLoop___redArg___lam__2 as *mut core::ffi::c_void,
        10,
        4,
    );
    leanh::lean_closure_set(v___f_664_, 0, v_inst_661_);
    leanh::lean_closure_set(v___f_664_, 1, v_inst_660_);
    leanh::lean_closure_set(v___f_664_, 2, v_inst_662_);
    leanh::lean_closure_set(v___f_664_, 3, v_inst_663_);
    return v___f_664_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Iterators_Combinators_Monadic_FlatMap(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Iterators_Combinators_Monadic_FilterMap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Iterators_Combinators_Monadic_FlatMap(
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
pub unsafe fn initialize_Init_Data_Iterators_Combinators_Monadic_FlatMap(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Iterators_Combinators_Monadic_FilterMap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Option_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Combinators_Monadic_FlatMap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Iterators_Combinators_Monadic_FlatMap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_Iterators_Combinators_Monadic_FlatMap(builtin);
}