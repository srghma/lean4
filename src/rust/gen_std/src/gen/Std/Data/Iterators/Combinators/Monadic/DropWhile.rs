// Lean compiler output
// Module: Std.Data.Iterators.Combinators.Monadic.DropWhile
// Imports: Init.Data.Nat.Lemmas Init.Data.Iterators.Consumers.Monadic.Collect Init.Data.Iterators.Consumers.Monadic.Loop Init.Data.Iterators.PostconditionMonad
use crate::r#gen::Init::Data::Iterators::Consumers::Monadic::Collect::{
    initialize_Init_Data_Iterators_Consumers_Monadic_Collect,
    runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Collect,
};
use crate::r#gen::Init::Data::Iterators::Consumers::Monadic::Loop::{
    initialize_Init_Data_Iterators_Consumers_Monadic_Loop,
    runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Loop,
};
use crate::r#gen::Init::Data::Iterators::PostconditionMonad::{
    initialize_Init_Data_Iterators_PostconditionMonad,
    runtime_initialize_Init_Data_Iterators_PostconditionMonad,
};
use crate::r#gen::Init::Data::Nat::Lemmas::{
    initialize_Init_Data_Nat_Lemmas, runtime_initialize_Init_Data_Nat_Lemmas,
};
use crate::r#gen::Init::WFExtrinsicFix::l_WellFounded_opaqueFix_u2083___redArg;
pub unsafe fn l_Std_IterM_Intermediate_dropWhileWithPostcondition___redArg(
    mut v_dropping_304_: u8,
    mut v_it_305_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_306_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_306_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_306_, 0, v_it_305_);
    leanh::lean_ctor_set_uint8(
        v___x_306_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v_dropping_304_,
    );
    return v___x_306_;
}
pub unsafe fn l_Std_IterM_Intermediate_dropWhileWithPostcondition___redArg___boxed(
    mut v_dropping_307_: *mut leanh::LeanObject,
    mut v_it_308_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_dropping_boxed_309_: u8 = 0;
    let mut v_res_310_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_dropping_boxed_309_ = (leanh::lean_unbox(v_dropping_307_) as u8);
    v_res_310_ = l_Std_IterM_Intermediate_dropWhileWithPostcondition___redArg(
        v_dropping_boxed_309_,
        v_it_308_,
    );
    return v_res_310_;
}
pub unsafe fn l_Std_IterM_Intermediate_dropWhileWithPostcondition(
    mut v_00_u03b1_311_: *mut leanh::LeanObject,
    mut v_m_312_: *mut leanh::LeanObject,
    mut v_00_u03b2_313_: *mut leanh::LeanObject,
    mut v_P_314_: *mut leanh::LeanObject,
    mut v_dropping_315_: u8,
    mut v_it_316_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_317_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_317_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_317_, 0, v_it_316_);
    leanh::lean_ctor_set_uint8(
        v___x_317_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v_dropping_315_,
    );
    return v___x_317_;
}
pub unsafe fn l_Std_IterM_Intermediate_dropWhileWithPostcondition___boxed(
    mut v_00_u03b1_318_: *mut leanh::LeanObject,
    mut v_m_319_: *mut leanh::LeanObject,
    mut v_00_u03b2_320_: *mut leanh::LeanObject,
    mut v_P_321_: *mut leanh::LeanObject,
    mut v_dropping_322_: *mut leanh::LeanObject,
    mut v_it_323_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_dropping_boxed_324_: u8 = 0;
    let mut v_res_325_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_dropping_boxed_324_ = (leanh::lean_unbox(v_dropping_322_) as u8);
    v_res_325_ = l_Std_IterM_Intermediate_dropWhileWithPostcondition(
        v_00_u03b1_318_,
        v_m_319_,
        v_00_u03b2_320_,
        v_P_321_,
        v_dropping_boxed_324_,
        v_it_323_,
    );
    leanh::lean_dec(v_P_321_);
    return v_res_325_;
}
pub unsafe fn l_Std_IterM_Intermediate_dropWhileM___redArg(
    mut v_dropping_326_: u8,
    mut v_it_327_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_328_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_328_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_328_, 0, v_it_327_);
    leanh::lean_ctor_set_uint8(
        v___x_328_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v_dropping_326_,
    );
    return v___x_328_;
}
pub unsafe fn l_Std_IterM_Intermediate_dropWhileM___redArg___boxed(
    mut v_dropping_329_: *mut leanh::LeanObject,
    mut v_it_330_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_dropping_boxed_331_: u8 = 0;
    let mut v_res_332_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_dropping_boxed_331_ = (leanh::lean_unbox(v_dropping_329_) as u8);
    v_res_332_ = l_Std_IterM_Intermediate_dropWhileM___redArg(v_dropping_boxed_331_, v_it_330_);
    return v_res_332_;
}
pub unsafe fn l_Std_IterM_Intermediate_dropWhileM(
    mut v_00_u03b1_333_: *mut leanh::LeanObject,
    mut v_m_334_: *mut leanh::LeanObject,
    mut v_00_u03b2_335_: *mut leanh::LeanObject,
    mut v_inst_336_: *mut leanh::LeanObject,
    mut v_inst_337_: *mut leanh::LeanObject,
    mut v_P_338_: *mut leanh::LeanObject,
    mut v_dropping_339_: u8,
    mut v_it_340_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_341_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_341_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_341_, 0, v_it_340_);
    leanh::lean_ctor_set_uint8(
        v___x_341_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v_dropping_339_,
    );
    return v___x_341_;
}
pub unsafe fn l_Std_IterM_Intermediate_dropWhileM___boxed(
    mut v_00_u03b1_342_: *mut leanh::LeanObject,
    mut v_m_343_: *mut leanh::LeanObject,
    mut v_00_u03b2_344_: *mut leanh::LeanObject,
    mut v_inst_345_: *mut leanh::LeanObject,
    mut v_inst_346_: *mut leanh::LeanObject,
    mut v_P_347_: *mut leanh::LeanObject,
    mut v_dropping_348_: *mut leanh::LeanObject,
    mut v_it_349_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_dropping_boxed_350_: u8 = 0;
    let mut v_res_351_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_dropping_boxed_350_ = (leanh::lean_unbox(v_dropping_348_) as u8);
    v_res_351_ = l_Std_IterM_Intermediate_dropWhileM(
        v_00_u03b1_342_,
        v_m_343_,
        v_00_u03b2_344_,
        v_inst_345_,
        v_inst_346_,
        v_P_347_,
        v_dropping_boxed_350_,
        v_it_349_,
    );
    leanh::lean_dec(v_P_347_);
    leanh::lean_dec(v_inst_346_);
    leanh::lean_dec_ref(v_inst_345_);
    return v_res_351_;
}
pub unsafe fn l_Std_IterM_Intermediate_dropWhile___redArg(
    mut v_dropping_352_: u8,
    mut v_it_353_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_354_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_354_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_354_, 0, v_it_353_);
    leanh::lean_ctor_set_uint8(
        v___x_354_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v_dropping_352_,
    );
    return v___x_354_;
}
pub unsafe fn l_Std_IterM_Intermediate_dropWhile___redArg___boxed(
    mut v_dropping_355_: *mut leanh::LeanObject,
    mut v_it_356_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_dropping_boxed_357_: u8 = 0;
    let mut v_res_358_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_dropping_boxed_357_ = (leanh::lean_unbox(v_dropping_355_) as u8);
    v_res_358_ = l_Std_IterM_Intermediate_dropWhile___redArg(v_dropping_boxed_357_, v_it_356_);
    return v_res_358_;
}
pub unsafe fn l_Std_IterM_Intermediate_dropWhile(
    mut v_00_u03b1_359_: *mut leanh::LeanObject,
    mut v_m_360_: *mut leanh::LeanObject,
    mut v_00_u03b2_361_: *mut leanh::LeanObject,
    mut v_inst_362_: *mut leanh::LeanObject,
    mut v_P_363_: *mut leanh::LeanObject,
    mut v_dropping_364_: u8,
    mut v_it_365_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_366_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_366_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_366_, 0, v_it_365_);
    leanh::lean_ctor_set_uint8(
        v___x_366_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v_dropping_364_,
    );
    return v___x_366_;
}
pub unsafe fn l_Std_IterM_Intermediate_dropWhile___boxed(
    mut v_00_u03b1_367_: *mut leanh::LeanObject,
    mut v_m_368_: *mut leanh::LeanObject,
    mut v_00_u03b2_369_: *mut leanh::LeanObject,
    mut v_inst_370_: *mut leanh::LeanObject,
    mut v_P_371_: *mut leanh::LeanObject,
    mut v_dropping_372_: *mut leanh::LeanObject,
    mut v_it_373_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_dropping_boxed_374_: u8 = 0;
    let mut v_res_375_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_dropping_boxed_374_ = (leanh::lean_unbox(v_dropping_372_) as u8);
    v_res_375_ = l_Std_IterM_Intermediate_dropWhile(
        v_00_u03b1_367_,
        v_m_368_,
        v_00_u03b2_369_,
        v_inst_370_,
        v_P_371_,
        v_dropping_boxed_374_,
        v_it_373_,
    );
    leanh::lean_dec_ref(v_P_371_);
    leanh::lean_dec_ref(v_inst_370_);
    return v_res_375_;
}
pub unsafe fn l_Std_IterM_dropWhileWithPostcondition___redArg(
    mut v_it_376_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_377_: u8 = 0;
    let mut v___x_378_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_377_ = 1;
    v___x_378_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_378_, 0, v_it_376_);
    leanh::lean_ctor_set_uint8(
        v___x_378_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_377_,
    );
    return v___x_378_;
}
pub unsafe fn l_Std_IterM_dropWhileWithPostcondition(
    mut v_00_u03b1_379_: *mut leanh::LeanObject,
    mut v_m_380_: *mut leanh::LeanObject,
    mut v_00_u03b2_381_: *mut leanh::LeanObject,
    mut v_P_382_: *mut leanh::LeanObject,
    mut v_it_383_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_384_: u8 = 0;
    let mut v___x_385_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_384_ = 1;
    v___x_385_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_385_, 0, v_it_383_);
    leanh::lean_ctor_set_uint8(
        v___x_385_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_384_,
    );
    return v___x_385_;
}
pub unsafe fn l_Std_IterM_dropWhileWithPostcondition___boxed(
    mut v_00_u03b1_386_: *mut leanh::LeanObject,
    mut v_m_387_: *mut leanh::LeanObject,
    mut v_00_u03b2_388_: *mut leanh::LeanObject,
    mut v_P_389_: *mut leanh::LeanObject,
    mut v_it_390_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_391_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_391_ = l_Std_IterM_dropWhileWithPostcondition(
        v_00_u03b1_386_,
        v_m_387_,
        v_00_u03b2_388_,
        v_P_389_,
        v_it_390_,
    );
    leanh::lean_dec(v_P_389_);
    return v_res_391_;
}
pub unsafe fn l_Std_IterM_dropWhileM___redArg(
    mut v_it_392_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_393_: u8 = 0;
    let mut v___x_394_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_393_ = 1;
    v___x_394_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_394_, 0, v_it_392_);
    leanh::lean_ctor_set_uint8(
        v___x_394_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_393_,
    );
    return v___x_394_;
}
pub unsafe fn l_Std_IterM_dropWhileM(
    mut v_00_u03b1_395_: *mut leanh::LeanObject,
    mut v_m_396_: *mut leanh::LeanObject,
    mut v_00_u03b2_397_: *mut leanh::LeanObject,
    mut v_inst_398_: *mut leanh::LeanObject,
    mut v_inst_399_: *mut leanh::LeanObject,
    mut v_P_400_: *mut leanh::LeanObject,
    mut v_it_401_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_402_: u8 = 0;
    let mut v___x_403_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_402_ = 1;
    v___x_403_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_403_, 0, v_it_401_);
    leanh::lean_ctor_set_uint8(
        v___x_403_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_402_,
    );
    return v___x_403_;
}
pub unsafe fn l_Std_IterM_dropWhileM___boxed(
    mut v_00_u03b1_404_: *mut leanh::LeanObject,
    mut v_m_405_: *mut leanh::LeanObject,
    mut v_00_u03b2_406_: *mut leanh::LeanObject,
    mut v_inst_407_: *mut leanh::LeanObject,
    mut v_inst_408_: *mut leanh::LeanObject,
    mut v_P_409_: *mut leanh::LeanObject,
    mut v_it_410_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_411_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_411_ = l_Std_IterM_dropWhileM(
        v_00_u03b1_404_,
        v_m_405_,
        v_00_u03b2_406_,
        v_inst_407_,
        v_inst_408_,
        v_P_409_,
        v_it_410_,
    );
    leanh::lean_dec(v_P_409_);
    leanh::lean_dec(v_inst_408_);
    leanh::lean_dec_ref(v_inst_407_);
    return v_res_411_;
}
pub unsafe fn l_Std_IterM_dropWhile___redArg(
    mut v_it_412_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_413_: u8 = 0;
    let mut v___x_414_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_413_ = 1;
    v___x_414_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_414_, 0, v_it_412_);
    leanh::lean_ctor_set_uint8(
        v___x_414_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_413_,
    );
    return v___x_414_;
}
pub unsafe fn l_Std_IterM_dropWhile(
    mut v_00_u03b1_415_: *mut leanh::LeanObject,
    mut v_m_416_: *mut leanh::LeanObject,
    mut v_00_u03b2_417_: *mut leanh::LeanObject,
    mut v_inst_418_: *mut leanh::LeanObject,
    mut v_P_419_: *mut leanh::LeanObject,
    mut v_it_420_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_421_: u8 = 0;
    let mut v___x_422_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_421_ = 1;
    v___x_422_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_422_, 0, v_it_420_);
    leanh::lean_ctor_set_uint8(
        v___x_422_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_421_,
    );
    return v___x_422_;
}
pub unsafe fn l_Std_IterM_dropWhile___boxed(
    mut v_00_u03b1_423_: *mut leanh::LeanObject,
    mut v_m_424_: *mut leanh::LeanObject,
    mut v_00_u03b2_425_: *mut leanh::LeanObject,
    mut v_inst_426_: *mut leanh::LeanObject,
    mut v_P_427_: *mut leanh::LeanObject,
    mut v_it_428_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_429_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_429_ = l_Std_IterM_dropWhile(
        v_00_u03b1_423_,
        v_m_424_,
        v_00_u03b2_425_,
        v_inst_426_,
        v_P_427_,
        v_it_428_,
    );
    leanh::lean_dec_ref(v_P_427_);
    leanh::lean_dec_ref(v_inst_426_);
    return v_res_429_;
}
pub unsafe fn l_Std_Iterators_Types_DropWhile_instIterator___redArg___lam__0(
    mut v_it_430_: *mut leanh::LeanObject,
    mut v_out_431_: *mut leanh::LeanObject,
    mut v_toPure_432_: *mut leanh::LeanObject,
    mut v_dropping_433_: u8,
    mut v_____do__lift_434_: u8,
) -> *mut leanh::LeanObject {
    if v_____do__lift_434_ == 0 {
        let mut v___x_435_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_436_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_437_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_435_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
        leanh::lean_ctor_set(v___x_435_, 0, v_it_430_);
        leanh::lean_ctor_set_uint8(
            v___x_435_,
            (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
            v_____do__lift_434_,
        );
        v___x_436_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_436_, 0, v___x_435_);
        leanh::lean_ctor_set(v___x_436_, 1, v_out_431_);
        v___x_437_ =
            leanh::lean_apply_2(v_toPure_432_, leanh::lean_box(0), v___x_436_);
        return v___x_437_;
    } else {
        let mut v___x_438_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_439_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_440_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_out_431_);
        v___x_438_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
        leanh::lean_ctor_set(v___x_438_, 0, v_it_430_);
        leanh::lean_ctor_set_uint8(
            v___x_438_,
            (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
            v_dropping_433_,
        );
        v___x_439_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_439_, 0, v___x_438_);
        v___x_440_ =
            leanh::lean_apply_2(v_toPure_432_, leanh::lean_box(0), v___x_439_);
        return v___x_440_;
    }
}
pub unsafe fn l_Std_Iterators_Types_DropWhile_instIterator___redArg___lam__0___boxed(
    mut v_it_441_: *mut leanh::LeanObject,
    mut v_out_442_: *mut leanh::LeanObject,
    mut v_toPure_443_: *mut leanh::LeanObject,
    mut v_dropping_444_: *mut leanh::LeanObject,
    mut v_____do__lift_445_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_dropping_boxed_446_: u8 = 0;
    let mut v_____do__lift_387__boxed_447_: u8 = 0;
    let mut v_res_448_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_dropping_boxed_446_ = (leanh::lean_unbox(v_dropping_444_) as u8);
    v_____do__lift_387__boxed_447_ = (leanh::lean_unbox(v_____do__lift_445_) as u8);
    v_res_448_ = l_Std_Iterators_Types_DropWhile_instIterator___redArg___lam__0(
        v_it_441_,
        v_out_442_,
        v_toPure_443_,
        v_dropping_boxed_446_,
        v_____do__lift_387__boxed_447_,
    );
    return v_res_448_;
}
pub unsafe fn l_Std_Iterators_Types_DropWhile_instIterator___redArg___lam__1(
    mut v_dropping_449_: u8,
    mut v_toPure_450_: *mut leanh::LeanObject,
    mut v_P_451_: *mut leanh::LeanObject,
    mut v_toBind_452_: *mut leanh::LeanObject,
    mut v_____do__lift_453_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_it_454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_out_455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_458_: u8 = 0;
    let mut v___x_459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_464_: u8 = 0;
    let mut v_it_465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_out_466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_it_471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_474_: u8 = 0;
    let mut v___x_475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_480_: u8 = 0;
    let mut v___x_481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                match leanh::lean_obj_tag(v_____do__lift_453_) {
                    0 => {
                        if v_dropping_449_ == 0 {
                            leanh::lean_dec(v_toBind_452_);
                            leanh::lean_dec(v_P_451_);
                            v_it_454_ = leanh::lean_ctor_get(v_____do__lift_453_, 0);
                            v_out_455_ = leanh::lean_ctor_get(v_____do__lift_453_, 1);
                            v_isSharedCheck_464_ =
                                (!leanh::lean_is_exclusive(v_____do__lift_453_)) as u8;
                            if v_isSharedCheck_464_ == 0 {
                                v___x_457_ = v_____do__lift_453_;
                                v_isShared_458_ = v_isSharedCheck_464_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_out_455_);
                                leanh::lean_inc(v_it_454_);
                                leanh::lean_dec(v_____do__lift_453_);
                                v___x_457_ = leanh::lean_box(0);
                                v_isShared_458_ = v_isSharedCheck_464_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v_it_465_ = leanh::lean_ctor_get(v_____do__lift_453_, 0);
                            leanh::lean_inc(v_it_465_);
                            v_out_466_ = leanh::lean_ctor_get(v_____do__lift_453_, 1);
                            leanh::lean_inc_n(v_out_466_, 2);
                            leanh::lean_dec_ref_known(v_____do__lift_453_, 2);
                            v___x_467_ = leanh::lean_box((v_dropping_449_) as usize);
                            v___f_468_ = leanh::lean_alloc_closure(l_Std_Iterators_Types_DropWhile_instIterator___redArg___lam__0___boxed as *mut core::ffi::c_void, 5, 4);
                            leanh::lean_closure_set(v___f_468_, 0, v_it_465_);
                            leanh::lean_closure_set(v___f_468_, 1, v_out_466_);
                            leanh::lean_closure_set(v___f_468_, 2, v_toPure_450_);
                            leanh::lean_closure_set(v___f_468_, 3, v___x_467_);
                            v___x_469_ = leanh::lean_apply_1(v_P_451_, v_out_466_);
                            v___x_470_ = leanh::lean_apply_4(
                                v_toBind_452_,
                                leanh::lean_box(0),
                                leanh::lean_box(0),
                                v___x_469_,
                                v___f_468_,
                            );
                            return v___x_470_;
                        }
                    }
                    1 => {
                        leanh::lean_dec(v_toBind_452_);
                        leanh::lean_dec(v_P_451_);
                        v_it_471_ = leanh::lean_ctor_get(v_____do__lift_453_, 0);
                        v_isSharedCheck_480_ =
                            (!leanh::lean_is_exclusive(v_____do__lift_453_)) as u8;
                        if v_isSharedCheck_480_ == 0 {
                            v___x_473_ = v_____do__lift_453_;
                            v_isShared_474_ = v_isSharedCheck_480_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_it_471_);
                            leanh::lean_dec(v_____do__lift_453_);
                            v___x_473_ = leanh::lean_box(0);
                            v_isShared_474_ = v_isSharedCheck_480_;
                            state = 3;
                            continue;
                        }
                    }
                    _ => {
                        leanh::lean_dec(v_toBind_452_);
                        leanh::lean_dec(v_P_451_);
                        v___x_481_ = leanh::lean_box(2);
                        v___x_482_ = leanh::lean_apply_2(
                            v_toPure_450_,
                            leanh::lean_box(0),
                            v___x_481_,
                        );
                        return v___x_482_;
                    }
                }
            }
            1 => {
                v___x_459_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_459_, 0, v_it_454_);
                leanh::lean_ctor_set_uint8(
                    v___x_459_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v_dropping_449_,
                );
                if v_isShared_458_ == 0 {
                    leanh::lean_ctor_set(v___x_457_, 0, v___x_459_);
                    v___x_461_ = v___x_457_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_463_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_463_, 0, v___x_459_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_463_, 1, v_out_455_);
                    v___x_461_ = v_reuseFailAlloc_463_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_462_ = leanh::lean_apply_2(
                    v_toPure_450_,
                    leanh::lean_box(0),
                    v___x_461_,
                );
                return v___x_462_;
            }
            3 => {
                v___x_475_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_475_, 0, v_it_471_);
                leanh::lean_ctor_set_uint8(
                    v___x_475_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v_dropping_449_,
                );
                if v_isShared_474_ == 0 {
                    leanh::lean_ctor_set(v___x_473_, 0, v___x_475_);
                    v___x_477_ = v___x_473_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_479_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_479_, 0, v___x_475_);
                    v___x_477_ = v_reuseFailAlloc_479_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_478_ = leanh::lean_apply_2(
                    v_toPure_450_,
                    leanh::lean_box(0),
                    v___x_477_,
                );
                return v___x_478_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Iterators_Types_DropWhile_instIterator___redArg___lam__1___boxed(
    mut v_dropping_483_: *mut leanh::LeanObject,
    mut v_toPure_484_: *mut leanh::LeanObject,
    mut v_P_485_: *mut leanh::LeanObject,
    mut v_toBind_486_: *mut leanh::LeanObject,
    mut v_____do__lift_487_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_dropping_boxed_488_: u8 = 0;
    let mut v_res_489_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_dropping_boxed_488_ = (leanh::lean_unbox(v_dropping_483_) as u8);
    v_res_489_ = l_Std_Iterators_Types_DropWhile_instIterator___redArg___lam__1(
        v_dropping_boxed_488_,
        v_toPure_484_,
        v_P_485_,
        v_toBind_486_,
        v_____do__lift_487_,
    );
    return v_res_489_;
}
pub unsafe fn l_Std_Iterators_Types_DropWhile_instIterator___redArg___lam__2(
    mut v_toPure_490_: *mut leanh::LeanObject,
    mut v_P_491_: *mut leanh::LeanObject,
    mut v_toBind_492_: *mut leanh::LeanObject,
    mut v_inst_493_: *mut leanh::LeanObject,
    mut v_it_494_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_dropping_495_: u8 = 0;
    let mut v_inner_496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_500_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_dropping_495_ = leanh::lean_ctor_get_uint8(
        v_it_494_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
    );
    v_inner_496_ = leanh::lean_ctor_get(v_it_494_, 0);
    leanh::lean_inc(v_inner_496_);
    leanh::lean_dec_ref(v_it_494_);
    v___x_497_ = leanh::lean_box((v_dropping_495_) as usize);
    leanh::lean_inc(v_toBind_492_);
    v___f_498_ = leanh::lean_alloc_closure(
        l_Std_Iterators_Types_DropWhile_instIterator___redArg___lam__1___boxed
            as *mut core::ffi::c_void,
        5,
        4,
    );
    leanh::lean_closure_set(v___f_498_, 0, v___x_497_);
    leanh::lean_closure_set(v___f_498_, 1, v_toPure_490_);
    leanh::lean_closure_set(v___f_498_, 2, v_P_491_);
    leanh::lean_closure_set(v___f_498_, 3, v_toBind_492_);
    v___x_499_ = leanh::lean_apply_1(v_inst_493_, v_inner_496_);
    v___x_500_ = leanh::lean_apply_4(
        v_toBind_492_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_499_,
        v___f_498_,
    );
    return v___x_500_;
}
pub unsafe fn l_Std_Iterators_Types_DropWhile_instIterator___redArg(
    mut v_inst_501_: *mut leanh::LeanObject,
    mut v_inst_502_: *mut leanh::LeanObject,
    mut v_P_503_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_507_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_504_ = leanh::lean_ctor_get(v_inst_501_, 0);
    leanh::lean_inc_ref(v_toApplicative_504_);
    v_toBind_505_ = leanh::lean_ctor_get(v_inst_501_, 1);
    leanh::lean_inc(v_toBind_505_);
    leanh::lean_dec_ref(v_inst_501_);
    v_toPure_506_ = leanh::lean_ctor_get(v_toApplicative_504_, 1);
    leanh::lean_inc(v_toPure_506_);
    leanh::lean_dec_ref(v_toApplicative_504_);
    v___f_507_ = leanh::lean_alloc_closure(
        l_Std_Iterators_Types_DropWhile_instIterator___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        4,
    );
    leanh::lean_closure_set(v___f_507_, 0, v_toPure_506_);
    leanh::lean_closure_set(v___f_507_, 1, v_P_503_);
    leanh::lean_closure_set(v___f_507_, 2, v_toBind_505_);
    leanh::lean_closure_set(v___f_507_, 3, v_inst_502_);
    return v___f_507_;
}
pub unsafe fn l_Std_Iterators_Types_DropWhile_instIterator(
    mut v_00_u03b1_508_: *mut leanh::LeanObject,
    mut v_m_509_: *mut leanh::LeanObject,
    mut v_00_u03b2_510_: *mut leanh::LeanObject,
    mut v_inst_511_: *mut leanh::LeanObject,
    mut v_inst_512_: *mut leanh::LeanObject,
    mut v_P_513_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_517_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_514_ = leanh::lean_ctor_get(v_inst_511_, 0);
    leanh::lean_inc_ref(v_toApplicative_514_);
    v_toBind_515_ = leanh::lean_ctor_get(v_inst_511_, 1);
    leanh::lean_inc(v_toBind_515_);
    leanh::lean_dec_ref(v_inst_511_);
    v_toPure_516_ = leanh::lean_ctor_get(v_toApplicative_514_, 1);
    leanh::lean_inc(v_toPure_516_);
    leanh::lean_dec_ref(v_toApplicative_514_);
    v___f_517_ = leanh::lean_alloc_closure(
        l_Std_Iterators_Types_DropWhile_instIterator___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        4,
    );
    leanh::lean_closure_set(v___f_517_, 0, v_toPure_516_);
    leanh::lean_closure_set(v___f_517_, 1, v_P_513_);
    leanh::lean_closure_set(v___f_517_, 2, v_toBind_515_);
    leanh::lean_closure_set(v___f_517_, 3, v_inst_512_);
    return v___f_517_;
}
pub unsafe fn l___private_Std_Data_Iterators_Combinators_Monadic_DropWhile_0__Std_Iterators_Types_DropWhile_instFinitenessRelation(
    mut v_00_u03b1_518_: *mut leanh::LeanObject,
    mut v_m_519_: *mut leanh::LeanObject,
    mut v_00_u03b2_520_: *mut leanh::LeanObject,
    mut v_inst_521_: *mut leanh::LeanObject,
    mut v_inst_522_: *mut leanh::LeanObject,
    mut v_inst_523_: *mut leanh::LeanObject,
    mut v_P_524_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_525_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_525_ = leanh::lean_box(0);
    return v___x_525_;
}
pub unsafe fn l___private_Std_Data_Iterators_Combinators_Monadic_DropWhile_0__Std_Iterators_Types_DropWhile_instFinitenessRelation___boxed(
    mut v_00_u03b1_526_: *mut leanh::LeanObject,
    mut v_m_527_: *mut leanh::LeanObject,
    mut v_00_u03b2_528_: *mut leanh::LeanObject,
    mut v_inst_529_: *mut leanh::LeanObject,
    mut v_inst_530_: *mut leanh::LeanObject,
    mut v_inst_531_: *mut leanh::LeanObject,
    mut v_P_532_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_533_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_533_ = l___private_Std_Data_Iterators_Combinators_Monadic_DropWhile_0__Std_Iterators_Types_DropWhile_instFinitenessRelation(v_00_u03b1_526_, v_m_527_, v_00_u03b2_528_, v_inst_529_, v_inst_530_, v_inst_531_, v_P_532_);
    leanh::lean_dec(v_P_532_);
    leanh::lean_dec(v_inst_530_);
    leanh::lean_dec_ref(v_inst_529_);
    return v_res_533_;
}
pub unsafe fn l_Std_Iterators_Types_DropWhile_instIteratorLoop___redArg___lam__0(
    mut v_toPure_534_: *mut leanh::LeanObject,
    mut v_recur_535_: *mut leanh::LeanObject,
    mut v_it_536_: *mut leanh::LeanObject,
    mut v_____do__lift_537_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_537_) == 0 {
        let mut v_a_538_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_539_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_it_536_);
        leanh::lean_dec(v_recur_535_);
        v_a_538_ = leanh::lean_ctor_get(v_____do__lift_537_, 0);
        leanh::lean_inc(v_a_538_);
        leanh::lean_dec_ref_known(v_____do__lift_537_, 1);
        v___x_539_ = leanh::lean_apply_2(v_toPure_534_, leanh::lean_box(0), v_a_538_);
        return v___x_539_;
    } else {
        let mut v_a_540_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_541_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_toPure_534_);
        v_a_540_ = leanh::lean_ctor_get(v_____do__lift_537_, 0);
        leanh::lean_inc(v_a_540_);
        leanh::lean_dec_ref_known(v_____do__lift_537_, 1);
        v___x_541_ = leanh::lean_apply_4(
            v_recur_535_,
            v_it_536_,
            v_a_540_,
            leanh::lean_box(0),
            leanh::lean_box(0),
        );
        return v___x_541_;
    }
}
pub unsafe fn l_Std_Iterators_Types_DropWhile_instIteratorLoop___redArg___lam__1(
    mut v_toPure_542_: *mut leanh::LeanObject,
    mut v_recur_543_: *mut leanh::LeanObject,
    mut v___y_544_: *mut leanh::LeanObject,
    mut v_acc_545_: *mut leanh::LeanObject,
    mut v_toBind_546_: *mut leanh::LeanObject,
    mut v_s_547_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_s_547_) {
        0 => {
            let mut v_it_548_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_549_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_550_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_551_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_552_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_it_548_ = leanh::lean_ctor_get(v_s_547_, 0);
            leanh::lean_inc(v_it_548_);
            v_out_549_ = leanh::lean_ctor_get(v_s_547_, 1);
            leanh::lean_inc(v_out_549_);
            leanh::lean_dec_ref_known(v_s_547_, 2);
            v___f_550_ = leanh::lean_alloc_closure(
                l_Std_Iterators_Types_DropWhile_instIteratorLoop___redArg___lam__0
                    as *mut core::ffi::c_void,
                4,
                3,
            );
            leanh::lean_closure_set(v___f_550_, 0, v_toPure_542_);
            leanh::lean_closure_set(v___f_550_, 1, v_recur_543_);
            leanh::lean_closure_set(v___f_550_, 2, v_it_548_);
            v___x_551_ = leanh::lean_apply_3(
                v___y_544_,
                v_out_549_,
                leanh::lean_box(0),
                v_acc_545_,
            );
            v___x_552_ = leanh::lean_apply_4(
                v_toBind_546_,
                leanh::lean_box(0),
                leanh::lean_box(0),
                v___x_551_,
                v___f_550_,
            );
            return v___x_552_;
        }
        1 => {
            let mut v_it_553_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_554_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_toBind_546_);
            leanh::lean_dec(v___y_544_);
            leanh::lean_dec(v_toPure_542_);
            v_it_553_ = leanh::lean_ctor_get(v_s_547_, 0);
            leanh::lean_inc(v_it_553_);
            leanh::lean_dec_ref_known(v_s_547_, 1);
            v___x_554_ = leanh::lean_apply_4(
                v_recur_543_,
                v_it_553_,
                v_acc_545_,
                leanh::lean_box(0),
                leanh::lean_box(0),
            );
            return v___x_554_;
        }
        _ => {
            let mut v___x_555_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_toBind_546_);
            leanh::lean_dec(v___y_544_);
            leanh::lean_dec(v_recur_543_);
            v___x_555_ =
                leanh::lean_apply_2(v_toPure_542_, leanh::lean_box(0), v_acc_545_);
            return v___x_555_;
        }
    }
}
pub unsafe fn l_Std_Iterators_Types_DropWhile_instIteratorLoop___redArg___lam__4(
    mut v_inst_556_: *mut leanh::LeanObject,
    mut v_toPure_557_: *mut leanh::LeanObject,
    mut v___y_558_: *mut leanh::LeanObject,
    mut v_toBind_559_: *mut leanh::LeanObject,
    mut v_P_560_: *mut leanh::LeanObject,
    mut v_inst_561_: *mut leanh::LeanObject,
    mut v_lift_562_: *mut leanh::LeanObject,
    mut v_it_563_: *mut leanh::LeanObject,
    mut v_acc_564_: *mut leanh::LeanObject,
    mut v_hP_565_: *mut leanh::LeanObject,
    mut v_recur_566_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dropping_570_: u8 = 0;
    let mut v_inner_571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_577_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_567_ = leanh::lean_ctor_get(v_inst_556_, 0);
    leanh::lean_inc_ref(v_toApplicative_567_);
    v_toBind_568_ = leanh::lean_ctor_get(v_inst_556_, 1);
    leanh::lean_inc_n(v_toBind_568_, 2);
    leanh::lean_dec_ref(v_inst_556_);
    v_toPure_569_ = leanh::lean_ctor_get(v_toApplicative_567_, 1);
    leanh::lean_inc(v_toPure_569_);
    leanh::lean_dec_ref(v_toApplicative_567_);
    v_dropping_570_ = leanh::lean_ctor_get_uint8(
        v_it_563_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
    );
    v_inner_571_ = leanh::lean_ctor_get(v_it_563_, 0);
    leanh::lean_inc(v_inner_571_);
    leanh::lean_dec_ref(v_it_563_);
    v___f_572_ = leanh::lean_alloc_closure(
        l_Std_Iterators_Types_DropWhile_instIteratorLoop___redArg___lam__1
            as *mut core::ffi::c_void,
        6,
        5,
    );
    leanh::lean_closure_set(v___f_572_, 0, v_toPure_557_);
    leanh::lean_closure_set(v___f_572_, 1, v_recur_566_);
    leanh::lean_closure_set(v___f_572_, 2, v___y_558_);
    leanh::lean_closure_set(v___f_572_, 3, v_acc_564_);
    leanh::lean_closure_set(v___f_572_, 4, v_toBind_559_);
    v___x_573_ = leanh::lean_box((v_dropping_570_) as usize);
    v___f_574_ = leanh::lean_alloc_closure(
        l_Std_Iterators_Types_DropWhile_instIterator___redArg___lam__1___boxed
            as *mut core::ffi::c_void,
        5,
        4,
    );
    leanh::lean_closure_set(v___f_574_, 0, v___x_573_);
    leanh::lean_closure_set(v___f_574_, 1, v_toPure_569_);
    leanh::lean_closure_set(v___f_574_, 2, v_P_560_);
    leanh::lean_closure_set(v___f_574_, 3, v_toBind_568_);
    v___x_575_ = leanh::lean_apply_1(v_inst_561_, v_inner_571_);
    v___x_576_ = leanh::lean_apply_4(
        v_toBind_568_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_575_,
        v___f_574_,
    );
    v___x_577_ = leanh::lean_apply_4(
        v_lift_562_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___f_572_,
        v___x_576_,
    );
    return v___x_577_;
}
pub unsafe fn l_Std_Iterators_Types_DropWhile_instIteratorLoop___redArg___lam__2(
    mut v_inst_578_: *mut leanh::LeanObject,
    mut v_inst_579_: *mut leanh::LeanObject,
    mut v_P_580_: *mut leanh::LeanObject,
    mut v_inst_581_: *mut leanh::LeanObject,
    mut v_lift_582_: *mut leanh::LeanObject,
    mut v_00_u03b3_583_: *mut leanh::LeanObject,
    mut v_Pl_584_: *mut leanh::LeanObject,
    mut v_it_585_: *mut leanh::LeanObject,
    mut v_init_586_: *mut leanh::LeanObject,
    mut v___y_587_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_592_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_588_ = leanh::lean_ctor_get(v_inst_578_, 0);
    leanh::lean_inc_ref(v_toApplicative_588_);
    v_toBind_589_ = leanh::lean_ctor_get(v_inst_578_, 1);
    leanh::lean_inc(v_toBind_589_);
    leanh::lean_dec_ref(v_inst_578_);
    v_toPure_590_ = leanh::lean_ctor_get(v_toApplicative_588_, 1);
    leanh::lean_inc(v_toPure_590_);
    leanh::lean_dec_ref(v_toApplicative_588_);
    v___f_591_ = leanh::lean_alloc_closure(
        l_Std_Iterators_Types_DropWhile_instIteratorLoop___redArg___lam__4
            as *mut core::ffi::c_void,
        11,
        7,
    );
    leanh::lean_closure_set(v___f_591_, 0, v_inst_579_);
    leanh::lean_closure_set(v___f_591_, 1, v_toPure_590_);
    leanh::lean_closure_set(v___f_591_, 2, v___y_587_);
    leanh::lean_closure_set(v___f_591_, 3, v_toBind_589_);
    leanh::lean_closure_set(v___f_591_, 4, v_P_580_);
    leanh::lean_closure_set(v___f_591_, 5, v_inst_581_);
    leanh::lean_closure_set(v___f_591_, 6, v_lift_582_);
    v___x_592_ = l_WellFounded_opaqueFix_u2083___redArg(
        v___f_591_,
        v_it_585_,
        v_init_586_,
        leanh::lean_box(0),
    );
    return v___x_592_;
}
pub unsafe fn l_Std_Iterators_Types_DropWhile_instIteratorLoop___redArg(
    mut v_P_593_: *mut leanh::LeanObject,
    mut v_inst_594_: *mut leanh::LeanObject,
    mut v_inst_595_: *mut leanh::LeanObject,
    mut v_inst_596_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_597_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_597_ = leanh::lean_alloc_closure(
        l_Std_Iterators_Types_DropWhile_instIteratorLoop___redArg___lam__2
            as *mut core::ffi::c_void,
        10,
        4,
    );
    leanh::lean_closure_set(v___f_597_, 0, v_inst_595_);
    leanh::lean_closure_set(v___f_597_, 1, v_inst_594_);
    leanh::lean_closure_set(v___f_597_, 2, v_P_593_);
    leanh::lean_closure_set(v___f_597_, 3, v_inst_596_);
    return v___f_597_;
}
pub unsafe fn l_Std_Iterators_Types_DropWhile_instIteratorLoop(
    mut v_00_u03b1_598_: *mut leanh::LeanObject,
    mut v_m_599_: *mut leanh::LeanObject,
    mut v_00_u03b2_600_: *mut leanh::LeanObject,
    mut v_n_601_: *mut leanh::LeanObject,
    mut v_P_602_: *mut leanh::LeanObject,
    mut v_inst_603_: *mut leanh::LeanObject,
    mut v_inst_604_: *mut leanh::LeanObject,
    mut v_inst_605_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_606_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_606_ = leanh::lean_alloc_closure(
        l_Std_Iterators_Types_DropWhile_instIteratorLoop___redArg___lam__2
            as *mut core::ffi::c_void,
        10,
        4,
    );
    leanh::lean_closure_set(v___f_606_, 0, v_inst_604_);
    leanh::lean_closure_set(v___f_606_, 1, v_inst_603_);
    leanh::lean_closure_set(v___f_606_, 2, v_P_602_);
    leanh::lean_closure_set(v___f_606_, 3, v_inst_605_);
    return v___f_606_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_Iterators_Combinators_Monadic_DropWhile(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Nat_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Collect(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Loop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_PostconditionMonad(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_Iterators_Combinators_Monadic_DropWhile(
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
pub unsafe fn initialize_Std_Data_Iterators_Combinators_Monadic_DropWhile(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Nat_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers_Monadic_Collect(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers_Monadic_Loop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_PostconditionMonad(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Combinators_Monadic_DropWhile(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Data_Iterators_Combinators_Monadic_DropWhile(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Data_Iterators_Combinators_Monadic_DropWhile(builtin);
}