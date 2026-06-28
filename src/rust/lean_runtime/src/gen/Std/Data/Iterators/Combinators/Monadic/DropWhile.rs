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
    mut v_it_305_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_306_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_306_, 0, v_it_305_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_306_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v_dropping_304_,
    );
    return v___x_306_;
}
pub unsafe fn l_Std_IterM_Intermediate_dropWhileWithPostcondition___redArg___boxed(
    mut v_dropping_307_: *mut crate::leanh::LeanObject,
    mut v_it_308_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_dropping_boxed_309_: u8 = 0;
    let mut v_res_310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_dropping_boxed_309_ = (crate::leanh::lean_unbox(v_dropping_307_) as u8);
    v_res_310_ = l_Std_IterM_Intermediate_dropWhileWithPostcondition___redArg(
        v_dropping_boxed_309_,
        v_it_308_,
    );
    return v_res_310_;
}
pub unsafe fn l_Std_IterM_Intermediate_dropWhileWithPostcondition(
    mut v_00_u03b1_311_: *mut crate::leanh::LeanObject,
    mut v_m_312_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_313_: *mut crate::leanh::LeanObject,
    mut v_P_314_: *mut crate::leanh::LeanObject,
    mut v_dropping_315_: u8,
    mut v_it_316_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_317_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_317_, 0, v_it_316_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_317_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v_dropping_315_,
    );
    return v___x_317_;
}
pub unsafe fn l_Std_IterM_Intermediate_dropWhileWithPostcondition___boxed(
    mut v_00_u03b1_318_: *mut crate::leanh::LeanObject,
    mut v_m_319_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_320_: *mut crate::leanh::LeanObject,
    mut v_P_321_: *mut crate::leanh::LeanObject,
    mut v_dropping_322_: *mut crate::leanh::LeanObject,
    mut v_it_323_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_dropping_boxed_324_: u8 = 0;
    let mut v_res_325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_dropping_boxed_324_ = (crate::leanh::lean_unbox(v_dropping_322_) as u8);
    v_res_325_ = l_Std_IterM_Intermediate_dropWhileWithPostcondition(
        v_00_u03b1_318_,
        v_m_319_,
        v_00_u03b2_320_,
        v_P_321_,
        v_dropping_boxed_324_,
        v_it_323_,
    );
    crate::leanh::lean_dec(v_P_321_);
    return v_res_325_;
}
pub unsafe fn l_Std_IterM_Intermediate_dropWhileM___redArg(
    mut v_dropping_326_: u8,
    mut v_it_327_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_328_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_328_, 0, v_it_327_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_328_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v_dropping_326_,
    );
    return v___x_328_;
}
pub unsafe fn l_Std_IterM_Intermediate_dropWhileM___redArg___boxed(
    mut v_dropping_329_: *mut crate::leanh::LeanObject,
    mut v_it_330_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_dropping_boxed_331_: u8 = 0;
    let mut v_res_332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_dropping_boxed_331_ = (crate::leanh::lean_unbox(v_dropping_329_) as u8);
    v_res_332_ = l_Std_IterM_Intermediate_dropWhileM___redArg(v_dropping_boxed_331_, v_it_330_);
    return v_res_332_;
}
pub unsafe fn l_Std_IterM_Intermediate_dropWhileM(
    mut v_00_u03b1_333_: *mut crate::leanh::LeanObject,
    mut v_m_334_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_335_: *mut crate::leanh::LeanObject,
    mut v_inst_336_: *mut crate::leanh::LeanObject,
    mut v_inst_337_: *mut crate::leanh::LeanObject,
    mut v_P_338_: *mut crate::leanh::LeanObject,
    mut v_dropping_339_: u8,
    mut v_it_340_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_341_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_341_, 0, v_it_340_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_341_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v_dropping_339_,
    );
    return v___x_341_;
}
pub unsafe fn l_Std_IterM_Intermediate_dropWhileM___boxed(
    mut v_00_u03b1_342_: *mut crate::leanh::LeanObject,
    mut v_m_343_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_344_: *mut crate::leanh::LeanObject,
    mut v_inst_345_: *mut crate::leanh::LeanObject,
    mut v_inst_346_: *mut crate::leanh::LeanObject,
    mut v_P_347_: *mut crate::leanh::LeanObject,
    mut v_dropping_348_: *mut crate::leanh::LeanObject,
    mut v_it_349_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_dropping_boxed_350_: u8 = 0;
    let mut v_res_351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_dropping_boxed_350_ = (crate::leanh::lean_unbox(v_dropping_348_) as u8);
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
    crate::leanh::lean_dec(v_P_347_);
    crate::leanh::lean_dec(v_inst_346_);
    crate::leanh::lean_dec_ref(v_inst_345_);
    return v_res_351_;
}
pub unsafe fn l_Std_IterM_Intermediate_dropWhile___redArg(
    mut v_dropping_352_: u8,
    mut v_it_353_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_354_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_354_, 0, v_it_353_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_354_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v_dropping_352_,
    );
    return v___x_354_;
}
pub unsafe fn l_Std_IterM_Intermediate_dropWhile___redArg___boxed(
    mut v_dropping_355_: *mut crate::leanh::LeanObject,
    mut v_it_356_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_dropping_boxed_357_: u8 = 0;
    let mut v_res_358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_dropping_boxed_357_ = (crate::leanh::lean_unbox(v_dropping_355_) as u8);
    v_res_358_ = l_Std_IterM_Intermediate_dropWhile___redArg(v_dropping_boxed_357_, v_it_356_);
    return v_res_358_;
}
pub unsafe fn l_Std_IterM_Intermediate_dropWhile(
    mut v_00_u03b1_359_: *mut crate::leanh::LeanObject,
    mut v_m_360_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_361_: *mut crate::leanh::LeanObject,
    mut v_inst_362_: *mut crate::leanh::LeanObject,
    mut v_P_363_: *mut crate::leanh::LeanObject,
    mut v_dropping_364_: u8,
    mut v_it_365_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_366_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_366_, 0, v_it_365_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_366_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v_dropping_364_,
    );
    return v___x_366_;
}
pub unsafe fn l_Std_IterM_Intermediate_dropWhile___boxed(
    mut v_00_u03b1_367_: *mut crate::leanh::LeanObject,
    mut v_m_368_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_369_: *mut crate::leanh::LeanObject,
    mut v_inst_370_: *mut crate::leanh::LeanObject,
    mut v_P_371_: *mut crate::leanh::LeanObject,
    mut v_dropping_372_: *mut crate::leanh::LeanObject,
    mut v_it_373_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_dropping_boxed_374_: u8 = 0;
    let mut v_res_375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_dropping_boxed_374_ = (crate::leanh::lean_unbox(v_dropping_372_) as u8);
    v_res_375_ = l_Std_IterM_Intermediate_dropWhile(
        v_00_u03b1_367_,
        v_m_368_,
        v_00_u03b2_369_,
        v_inst_370_,
        v_P_371_,
        v_dropping_boxed_374_,
        v_it_373_,
    );
    crate::leanh::lean_dec_ref(v_P_371_);
    crate::leanh::lean_dec_ref(v_inst_370_);
    return v_res_375_;
}
pub unsafe fn l_Std_IterM_dropWhileWithPostcondition___redArg(
    mut v_it_376_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_377_: u8 = 0;
    let mut v___x_378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_377_ = 1;
    v___x_378_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_378_, 0, v_it_376_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_378_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_377_,
    );
    return v___x_378_;
}
pub unsafe fn l_Std_IterM_dropWhileWithPostcondition(
    mut v_00_u03b1_379_: *mut crate::leanh::LeanObject,
    mut v_m_380_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_381_: *mut crate::leanh::LeanObject,
    mut v_P_382_: *mut crate::leanh::LeanObject,
    mut v_it_383_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_384_: u8 = 0;
    let mut v___x_385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_384_ = 1;
    v___x_385_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_385_, 0, v_it_383_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_385_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_384_,
    );
    return v___x_385_;
}
pub unsafe fn l_Std_IterM_dropWhileWithPostcondition___boxed(
    mut v_00_u03b1_386_: *mut crate::leanh::LeanObject,
    mut v_m_387_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_388_: *mut crate::leanh::LeanObject,
    mut v_P_389_: *mut crate::leanh::LeanObject,
    mut v_it_390_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_391_ = l_Std_IterM_dropWhileWithPostcondition(
        v_00_u03b1_386_,
        v_m_387_,
        v_00_u03b2_388_,
        v_P_389_,
        v_it_390_,
    );
    crate::leanh::lean_dec(v_P_389_);
    return v_res_391_;
}
pub unsafe fn l_Std_IterM_dropWhileM___redArg(
    mut v_it_392_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_393_: u8 = 0;
    let mut v___x_394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_393_ = 1;
    v___x_394_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_394_, 0, v_it_392_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_394_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_393_,
    );
    return v___x_394_;
}
pub unsafe fn l_Std_IterM_dropWhileM(
    mut v_00_u03b1_395_: *mut crate::leanh::LeanObject,
    mut v_m_396_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_397_: *mut crate::leanh::LeanObject,
    mut v_inst_398_: *mut crate::leanh::LeanObject,
    mut v_inst_399_: *mut crate::leanh::LeanObject,
    mut v_P_400_: *mut crate::leanh::LeanObject,
    mut v_it_401_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_402_: u8 = 0;
    let mut v___x_403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_402_ = 1;
    v___x_403_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_403_, 0, v_it_401_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_403_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_402_,
    );
    return v___x_403_;
}
pub unsafe fn l_Std_IterM_dropWhileM___boxed(
    mut v_00_u03b1_404_: *mut crate::leanh::LeanObject,
    mut v_m_405_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_406_: *mut crate::leanh::LeanObject,
    mut v_inst_407_: *mut crate::leanh::LeanObject,
    mut v_inst_408_: *mut crate::leanh::LeanObject,
    mut v_P_409_: *mut crate::leanh::LeanObject,
    mut v_it_410_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_411_ = l_Std_IterM_dropWhileM(
        v_00_u03b1_404_,
        v_m_405_,
        v_00_u03b2_406_,
        v_inst_407_,
        v_inst_408_,
        v_P_409_,
        v_it_410_,
    );
    crate::leanh::lean_dec(v_P_409_);
    crate::leanh::lean_dec(v_inst_408_);
    crate::leanh::lean_dec_ref(v_inst_407_);
    return v_res_411_;
}
pub unsafe fn l_Std_IterM_dropWhile___redArg(
    mut v_it_412_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_413_: u8 = 0;
    let mut v___x_414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_413_ = 1;
    v___x_414_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_414_, 0, v_it_412_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_414_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_413_,
    );
    return v___x_414_;
}
pub unsafe fn l_Std_IterM_dropWhile(
    mut v_00_u03b1_415_: *mut crate::leanh::LeanObject,
    mut v_m_416_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_417_: *mut crate::leanh::LeanObject,
    mut v_inst_418_: *mut crate::leanh::LeanObject,
    mut v_P_419_: *mut crate::leanh::LeanObject,
    mut v_it_420_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_421_: u8 = 0;
    let mut v___x_422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_421_ = 1;
    v___x_422_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_422_, 0, v_it_420_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_422_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_421_,
    );
    return v___x_422_;
}
pub unsafe fn l_Std_IterM_dropWhile___boxed(
    mut v_00_u03b1_423_: *mut crate::leanh::LeanObject,
    mut v_m_424_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_425_: *mut crate::leanh::LeanObject,
    mut v_inst_426_: *mut crate::leanh::LeanObject,
    mut v_P_427_: *mut crate::leanh::LeanObject,
    mut v_it_428_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_429_ = l_Std_IterM_dropWhile(
        v_00_u03b1_423_,
        v_m_424_,
        v_00_u03b2_425_,
        v_inst_426_,
        v_P_427_,
        v_it_428_,
    );
    crate::leanh::lean_dec_ref(v_P_427_);
    crate::leanh::lean_dec_ref(v_inst_426_);
    return v_res_429_;
}
pub unsafe fn l_Std_Iterators_Types_DropWhile_instIterator___redArg___lam__0(
    mut v_it_430_: *mut crate::leanh::LeanObject,
    mut v_out_431_: *mut crate::leanh::LeanObject,
    mut v_toPure_432_: *mut crate::leanh::LeanObject,
    mut v_dropping_433_: u8,
    mut v_____do__lift_434_: u8,
) -> *mut crate::leanh::LeanObject {
    if v_____do__lift_434_ == 0 {
        let mut v___x_435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_435_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
        crate::leanh::lean_ctor_set(v___x_435_, 0, v_it_430_);
        crate::leanh::lean_ctor_set_uint8(
            v___x_435_,
            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
            v_____do__lift_434_,
        );
        v___x_436_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_436_, 0, v___x_435_);
        crate::leanh::lean_ctor_set(v___x_436_, 1, v_out_431_);
        v___x_437_ =
            crate::leanh::lean_apply_2(v_toPure_432_, crate::leanh::lean_box(0), v___x_436_);
        return v___x_437_;
    } else {
        let mut v___x_438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_out_431_);
        v___x_438_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
        crate::leanh::lean_ctor_set(v___x_438_, 0, v_it_430_);
        crate::leanh::lean_ctor_set_uint8(
            v___x_438_,
            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
            v_dropping_433_,
        );
        v___x_439_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_439_, 0, v___x_438_);
        v___x_440_ =
            crate::leanh::lean_apply_2(v_toPure_432_, crate::leanh::lean_box(0), v___x_439_);
        return v___x_440_;
    }
}
pub unsafe fn l_Std_Iterators_Types_DropWhile_instIterator___redArg___lam__0___boxed(
    mut v_it_441_: *mut crate::leanh::LeanObject,
    mut v_out_442_: *mut crate::leanh::LeanObject,
    mut v_toPure_443_: *mut crate::leanh::LeanObject,
    mut v_dropping_444_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_445_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_dropping_boxed_446_: u8 = 0;
    let mut v_____do__lift_387__boxed_447_: u8 = 0;
    let mut v_res_448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_dropping_boxed_446_ = (crate::leanh::lean_unbox(v_dropping_444_) as u8);
    v_____do__lift_387__boxed_447_ = (crate::leanh::lean_unbox(v_____do__lift_445_) as u8);
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
    mut v_toPure_450_: *mut crate::leanh::LeanObject,
    mut v_P_451_: *mut crate::leanh::LeanObject,
    mut v_toBind_452_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_453_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_it_454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_out_455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_458_: u8 = 0;
    let mut v___x_459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_464_: u8 = 0;
    let mut v_it_465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_out_466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_it_471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_474_: u8 = 0;
    let mut v___x_475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_480_: u8 = 0;
    let mut v___x_481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                match crate::leanh::lean_obj_tag(v_____do__lift_453_) {
                    0 => {
                        if v_dropping_449_ == 0 {
                            crate::leanh::lean_dec(v_toBind_452_);
                            crate::leanh::lean_dec(v_P_451_);
                            v_it_454_ = crate::leanh::lean_ctor_get(v_____do__lift_453_, 0);
                            v_out_455_ = crate::leanh::lean_ctor_get(v_____do__lift_453_, 1);
                            v_isSharedCheck_464_ =
                                (!crate::leanh::lean_is_exclusive(v_____do__lift_453_)) as u8;
                            if v_isSharedCheck_464_ == 0 {
                                v___x_457_ = v_____do__lift_453_;
                                v_isShared_458_ = v_isSharedCheck_464_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_out_455_);
                                crate::leanh::lean_inc(v_it_454_);
                                crate::leanh::lean_dec(v_____do__lift_453_);
                                v___x_457_ = crate::leanh::lean_box(0);
                                v_isShared_458_ = v_isSharedCheck_464_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v_it_465_ = crate::leanh::lean_ctor_get(v_____do__lift_453_, 0);
                            crate::leanh::lean_inc(v_it_465_);
                            v_out_466_ = crate::leanh::lean_ctor_get(v_____do__lift_453_, 1);
                            crate::leanh::lean_inc_n(v_out_466_, 2);
                            crate::leanh::lean_dec_ref_known(v_____do__lift_453_, 2);
                            v___x_467_ = crate::leanh::lean_box((v_dropping_449_) as usize);
                            v___f_468_ = crate::leanh::lean_alloc_closure(l_Std_Iterators_Types_DropWhile_instIterator___redArg___lam__0___boxed as *mut core::ffi::c_void, 5, 4);
                            crate::leanh::lean_closure_set(v___f_468_, 0, v_it_465_);
                            crate::leanh::lean_closure_set(v___f_468_, 1, v_out_466_);
                            crate::leanh::lean_closure_set(v___f_468_, 2, v_toPure_450_);
                            crate::leanh::lean_closure_set(v___f_468_, 3, v___x_467_);
                            v___x_469_ = crate::leanh::lean_apply_1(v_P_451_, v_out_466_);
                            v___x_470_ = crate::leanh::lean_apply_4(
                                v_toBind_452_,
                                crate::leanh::lean_box(0),
                                crate::leanh::lean_box(0),
                                v___x_469_,
                                v___f_468_,
                            );
                            return v___x_470_;
                        }
                    }
                    1 => {
                        crate::leanh::lean_dec(v_toBind_452_);
                        crate::leanh::lean_dec(v_P_451_);
                        v_it_471_ = crate::leanh::lean_ctor_get(v_____do__lift_453_, 0);
                        v_isSharedCheck_480_ =
                            (!crate::leanh::lean_is_exclusive(v_____do__lift_453_)) as u8;
                        if v_isSharedCheck_480_ == 0 {
                            v___x_473_ = v_____do__lift_453_;
                            v_isShared_474_ = v_isSharedCheck_480_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_it_471_);
                            crate::leanh::lean_dec(v_____do__lift_453_);
                            v___x_473_ = crate::leanh::lean_box(0);
                            v_isShared_474_ = v_isSharedCheck_480_;
                            state = 3;
                            continue;
                        }
                    }
                    _ => {
                        crate::leanh::lean_dec(v_toBind_452_);
                        crate::leanh::lean_dec(v_P_451_);
                        v___x_481_ = crate::leanh::lean_box(2);
                        v___x_482_ = crate::leanh::lean_apply_2(
                            v_toPure_450_,
                            crate::leanh::lean_box(0),
                            v___x_481_,
                        );
                        return v___x_482_;
                    }
                }
            }
            1 => {
                v___x_459_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_459_, 0, v_it_454_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_459_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v_dropping_449_,
                );
                if v_isShared_458_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_457_, 0, v___x_459_);
                    v___x_461_ = v___x_457_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_463_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_463_, 0, v___x_459_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_463_, 1, v_out_455_);
                    v___x_461_ = v_reuseFailAlloc_463_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_462_ = crate::leanh::lean_apply_2(
                    v_toPure_450_,
                    crate::leanh::lean_box(0),
                    v___x_461_,
                );
                return v___x_462_;
            }
            3 => {
                v___x_475_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_475_, 0, v_it_471_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_475_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v_dropping_449_,
                );
                if v_isShared_474_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_473_, 0, v___x_475_);
                    v___x_477_ = v___x_473_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_479_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_479_, 0, v___x_475_);
                    v___x_477_ = v_reuseFailAlloc_479_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_478_ = crate::leanh::lean_apply_2(
                    v_toPure_450_,
                    crate::leanh::lean_box(0),
                    v___x_477_,
                );
                return v___x_478_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Iterators_Types_DropWhile_instIterator___redArg___lam__1___boxed(
    mut v_dropping_483_: *mut crate::leanh::LeanObject,
    mut v_toPure_484_: *mut crate::leanh::LeanObject,
    mut v_P_485_: *mut crate::leanh::LeanObject,
    mut v_toBind_486_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_487_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_dropping_boxed_488_: u8 = 0;
    let mut v_res_489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_dropping_boxed_488_ = (crate::leanh::lean_unbox(v_dropping_483_) as u8);
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
    mut v_toPure_490_: *mut crate::leanh::LeanObject,
    mut v_P_491_: *mut crate::leanh::LeanObject,
    mut v_toBind_492_: *mut crate::leanh::LeanObject,
    mut v_inst_493_: *mut crate::leanh::LeanObject,
    mut v_it_494_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_dropping_495_: u8 = 0;
    let mut v_inner_496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_dropping_495_ = crate::leanh::lean_ctor_get_uint8(
        v_it_494_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
    );
    v_inner_496_ = crate::leanh::lean_ctor_get(v_it_494_, 0);
    crate::leanh::lean_inc(v_inner_496_);
    crate::leanh::lean_dec_ref(v_it_494_);
    v___x_497_ = crate::leanh::lean_box((v_dropping_495_) as usize);
    crate::leanh::lean_inc(v_toBind_492_);
    v___f_498_ = crate::leanh::lean_alloc_closure(
        l_Std_Iterators_Types_DropWhile_instIterator___redArg___lam__1___boxed
            as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_498_, 0, v___x_497_);
    crate::leanh::lean_closure_set(v___f_498_, 1, v_toPure_490_);
    crate::leanh::lean_closure_set(v___f_498_, 2, v_P_491_);
    crate::leanh::lean_closure_set(v___f_498_, 3, v_toBind_492_);
    v___x_499_ = crate::leanh::lean_apply_1(v_inst_493_, v_inner_496_);
    v___x_500_ = crate::leanh::lean_apply_4(
        v_toBind_492_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_499_,
        v___f_498_,
    );
    return v___x_500_;
}
pub unsafe fn l_Std_Iterators_Types_DropWhile_instIterator___redArg(
    mut v_inst_501_: *mut crate::leanh::LeanObject,
    mut v_inst_502_: *mut crate::leanh::LeanObject,
    mut v_P_503_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_504_ = crate::leanh::lean_ctor_get(v_inst_501_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_504_);
    v_toBind_505_ = crate::leanh::lean_ctor_get(v_inst_501_, 1);
    crate::leanh::lean_inc(v_toBind_505_);
    crate::leanh::lean_dec_ref(v_inst_501_);
    v_toPure_506_ = crate::leanh::lean_ctor_get(v_toApplicative_504_, 1);
    crate::leanh::lean_inc(v_toPure_506_);
    crate::leanh::lean_dec_ref(v_toApplicative_504_);
    v___f_507_ = crate::leanh::lean_alloc_closure(
        l_Std_Iterators_Types_DropWhile_instIterator___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_507_, 0, v_toPure_506_);
    crate::leanh::lean_closure_set(v___f_507_, 1, v_P_503_);
    crate::leanh::lean_closure_set(v___f_507_, 2, v_toBind_505_);
    crate::leanh::lean_closure_set(v___f_507_, 3, v_inst_502_);
    return v___f_507_;
}
pub unsafe fn l_Std_Iterators_Types_DropWhile_instIterator(
    mut v_00_u03b1_508_: *mut crate::leanh::LeanObject,
    mut v_m_509_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_510_: *mut crate::leanh::LeanObject,
    mut v_inst_511_: *mut crate::leanh::LeanObject,
    mut v_inst_512_: *mut crate::leanh::LeanObject,
    mut v_P_513_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_514_ = crate::leanh::lean_ctor_get(v_inst_511_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_514_);
    v_toBind_515_ = crate::leanh::lean_ctor_get(v_inst_511_, 1);
    crate::leanh::lean_inc(v_toBind_515_);
    crate::leanh::lean_dec_ref(v_inst_511_);
    v_toPure_516_ = crate::leanh::lean_ctor_get(v_toApplicative_514_, 1);
    crate::leanh::lean_inc(v_toPure_516_);
    crate::leanh::lean_dec_ref(v_toApplicative_514_);
    v___f_517_ = crate::leanh::lean_alloc_closure(
        l_Std_Iterators_Types_DropWhile_instIterator___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_517_, 0, v_toPure_516_);
    crate::leanh::lean_closure_set(v___f_517_, 1, v_P_513_);
    crate::leanh::lean_closure_set(v___f_517_, 2, v_toBind_515_);
    crate::leanh::lean_closure_set(v___f_517_, 3, v_inst_512_);
    return v___f_517_;
}
pub unsafe fn l___private_Std_Data_Iterators_Combinators_Monadic_DropWhile_0__Std_Iterators_Types_DropWhile_instFinitenessRelation(
    mut v_00_u03b1_518_: *mut crate::leanh::LeanObject,
    mut v_m_519_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_520_: *mut crate::leanh::LeanObject,
    mut v_inst_521_: *mut crate::leanh::LeanObject,
    mut v_inst_522_: *mut crate::leanh::LeanObject,
    mut v_inst_523_: *mut crate::leanh::LeanObject,
    mut v_P_524_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_525_ = crate::leanh::lean_box(0);
    return v___x_525_;
}
pub unsafe fn l___private_Std_Data_Iterators_Combinators_Monadic_DropWhile_0__Std_Iterators_Types_DropWhile_instFinitenessRelation___boxed(
    mut v_00_u03b1_526_: *mut crate::leanh::LeanObject,
    mut v_m_527_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_528_: *mut crate::leanh::LeanObject,
    mut v_inst_529_: *mut crate::leanh::LeanObject,
    mut v_inst_530_: *mut crate::leanh::LeanObject,
    mut v_inst_531_: *mut crate::leanh::LeanObject,
    mut v_P_532_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_533_ = l___private_Std_Data_Iterators_Combinators_Monadic_DropWhile_0__Std_Iterators_Types_DropWhile_instFinitenessRelation(v_00_u03b1_526_, v_m_527_, v_00_u03b2_528_, v_inst_529_, v_inst_530_, v_inst_531_, v_P_532_);
    crate::leanh::lean_dec(v_P_532_);
    crate::leanh::lean_dec(v_inst_530_);
    crate::leanh::lean_dec_ref(v_inst_529_);
    return v_res_533_;
}
pub unsafe fn l_Std_Iterators_Types_DropWhile_instIteratorLoop___redArg___lam__0(
    mut v_toPure_534_: *mut crate::leanh::LeanObject,
    mut v_recur_535_: *mut crate::leanh::LeanObject,
    mut v_it_536_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_537_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_537_) == 0 {
        let mut v_a_538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_it_536_);
        crate::leanh::lean_dec(v_recur_535_);
        v_a_538_ = crate::leanh::lean_ctor_get(v_____do__lift_537_, 0);
        crate::leanh::lean_inc(v_a_538_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_537_, 1);
        v___x_539_ = crate::leanh::lean_apply_2(v_toPure_534_, crate::leanh::lean_box(0), v_a_538_);
        return v___x_539_;
    } else {
        let mut v_a_540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toPure_534_);
        v_a_540_ = crate::leanh::lean_ctor_get(v_____do__lift_537_, 0);
        crate::leanh::lean_inc(v_a_540_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_537_, 1);
        v___x_541_ = crate::leanh::lean_apply_4(
            v_recur_535_,
            v_it_536_,
            v_a_540_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
        );
        return v___x_541_;
    }
}
pub unsafe fn l_Std_Iterators_Types_DropWhile_instIteratorLoop___redArg___lam__1(
    mut v_toPure_542_: *mut crate::leanh::LeanObject,
    mut v_recur_543_: *mut crate::leanh::LeanObject,
    mut v___y_544_: *mut crate::leanh::LeanObject,
    mut v_acc_545_: *mut crate::leanh::LeanObject,
    mut v_toBind_546_: *mut crate::leanh::LeanObject,
    mut v_s_547_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_s_547_) {
        0 => {
            let mut v_it_548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_it_548_ = crate::leanh::lean_ctor_get(v_s_547_, 0);
            crate::leanh::lean_inc(v_it_548_);
            v_out_549_ = crate::leanh::lean_ctor_get(v_s_547_, 1);
            crate::leanh::lean_inc(v_out_549_);
            crate::leanh::lean_dec_ref_known(v_s_547_, 2);
            v___f_550_ = crate::leanh::lean_alloc_closure(
                l_Std_Iterators_Types_DropWhile_instIteratorLoop___redArg___lam__0
                    as *mut core::ffi::c_void,
                4,
                3,
            );
            crate::leanh::lean_closure_set(v___f_550_, 0, v_toPure_542_);
            crate::leanh::lean_closure_set(v___f_550_, 1, v_recur_543_);
            crate::leanh::lean_closure_set(v___f_550_, 2, v_it_548_);
            v___x_551_ = crate::leanh::lean_apply_3(
                v___y_544_,
                v_out_549_,
                crate::leanh::lean_box(0),
                v_acc_545_,
            );
            v___x_552_ = crate::leanh::lean_apply_4(
                v_toBind_546_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_551_,
                v___f_550_,
            );
            return v___x_552_;
        }
        1 => {
            let mut v_it_553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_toBind_546_);
            crate::leanh::lean_dec(v___y_544_);
            crate::leanh::lean_dec(v_toPure_542_);
            v_it_553_ = crate::leanh::lean_ctor_get(v_s_547_, 0);
            crate::leanh::lean_inc(v_it_553_);
            crate::leanh::lean_dec_ref_known(v_s_547_, 1);
            v___x_554_ = crate::leanh::lean_apply_4(
                v_recur_543_,
                v_it_553_,
                v_acc_545_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
            );
            return v___x_554_;
        }
        _ => {
            let mut v___x_555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_toBind_546_);
            crate::leanh::lean_dec(v___y_544_);
            crate::leanh::lean_dec(v_recur_543_);
            v___x_555_ =
                crate::leanh::lean_apply_2(v_toPure_542_, crate::leanh::lean_box(0), v_acc_545_);
            return v___x_555_;
        }
    }
}
pub unsafe fn l_Std_Iterators_Types_DropWhile_instIteratorLoop___redArg___lam__4(
    mut v_inst_556_: *mut crate::leanh::LeanObject,
    mut v_toPure_557_: *mut crate::leanh::LeanObject,
    mut v___y_558_: *mut crate::leanh::LeanObject,
    mut v_toBind_559_: *mut crate::leanh::LeanObject,
    mut v_P_560_: *mut crate::leanh::LeanObject,
    mut v_inst_561_: *mut crate::leanh::LeanObject,
    mut v_lift_562_: *mut crate::leanh::LeanObject,
    mut v_it_563_: *mut crate::leanh::LeanObject,
    mut v_acc_564_: *mut crate::leanh::LeanObject,
    mut v_hP_565_: *mut crate::leanh::LeanObject,
    mut v_recur_566_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dropping_570_: u8 = 0;
    let mut v_inner_571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_567_ = crate::leanh::lean_ctor_get(v_inst_556_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_567_);
    v_toBind_568_ = crate::leanh::lean_ctor_get(v_inst_556_, 1);
    crate::leanh::lean_inc_n(v_toBind_568_, 2);
    crate::leanh::lean_dec_ref(v_inst_556_);
    v_toPure_569_ = crate::leanh::lean_ctor_get(v_toApplicative_567_, 1);
    crate::leanh::lean_inc(v_toPure_569_);
    crate::leanh::lean_dec_ref(v_toApplicative_567_);
    v_dropping_570_ = crate::leanh::lean_ctor_get_uint8(
        v_it_563_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
    );
    v_inner_571_ = crate::leanh::lean_ctor_get(v_it_563_, 0);
    crate::leanh::lean_inc(v_inner_571_);
    crate::leanh::lean_dec_ref(v_it_563_);
    v___f_572_ = crate::leanh::lean_alloc_closure(
        l_Std_Iterators_Types_DropWhile_instIteratorLoop___redArg___lam__1
            as *mut core::ffi::c_void,
        6,
        5,
    );
    crate::leanh::lean_closure_set(v___f_572_, 0, v_toPure_557_);
    crate::leanh::lean_closure_set(v___f_572_, 1, v_recur_566_);
    crate::leanh::lean_closure_set(v___f_572_, 2, v___y_558_);
    crate::leanh::lean_closure_set(v___f_572_, 3, v_acc_564_);
    crate::leanh::lean_closure_set(v___f_572_, 4, v_toBind_559_);
    v___x_573_ = crate::leanh::lean_box((v_dropping_570_) as usize);
    v___f_574_ = crate::leanh::lean_alloc_closure(
        l_Std_Iterators_Types_DropWhile_instIterator___redArg___lam__1___boxed
            as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_574_, 0, v___x_573_);
    crate::leanh::lean_closure_set(v___f_574_, 1, v_toPure_569_);
    crate::leanh::lean_closure_set(v___f_574_, 2, v_P_560_);
    crate::leanh::lean_closure_set(v___f_574_, 3, v_toBind_568_);
    v___x_575_ = crate::leanh::lean_apply_1(v_inst_561_, v_inner_571_);
    v___x_576_ = crate::leanh::lean_apply_4(
        v_toBind_568_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_575_,
        v___f_574_,
    );
    v___x_577_ = crate::leanh::lean_apply_4(
        v_lift_562_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_572_,
        v___x_576_,
    );
    return v___x_577_;
}
pub unsafe fn l_Std_Iterators_Types_DropWhile_instIteratorLoop___redArg___lam__2(
    mut v_inst_578_: *mut crate::leanh::LeanObject,
    mut v_inst_579_: *mut crate::leanh::LeanObject,
    mut v_P_580_: *mut crate::leanh::LeanObject,
    mut v_inst_581_: *mut crate::leanh::LeanObject,
    mut v_lift_582_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_583_: *mut crate::leanh::LeanObject,
    mut v_Pl_584_: *mut crate::leanh::LeanObject,
    mut v_it_585_: *mut crate::leanh::LeanObject,
    mut v_init_586_: *mut crate::leanh::LeanObject,
    mut v___y_587_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_588_ = crate::leanh::lean_ctor_get(v_inst_578_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_588_);
    v_toBind_589_ = crate::leanh::lean_ctor_get(v_inst_578_, 1);
    crate::leanh::lean_inc(v_toBind_589_);
    crate::leanh::lean_dec_ref(v_inst_578_);
    v_toPure_590_ = crate::leanh::lean_ctor_get(v_toApplicative_588_, 1);
    crate::leanh::lean_inc(v_toPure_590_);
    crate::leanh::lean_dec_ref(v_toApplicative_588_);
    v___f_591_ = crate::leanh::lean_alloc_closure(
        l_Std_Iterators_Types_DropWhile_instIteratorLoop___redArg___lam__4
            as *mut core::ffi::c_void,
        11,
        7,
    );
    crate::leanh::lean_closure_set(v___f_591_, 0, v_inst_579_);
    crate::leanh::lean_closure_set(v___f_591_, 1, v_toPure_590_);
    crate::leanh::lean_closure_set(v___f_591_, 2, v___y_587_);
    crate::leanh::lean_closure_set(v___f_591_, 3, v_toBind_589_);
    crate::leanh::lean_closure_set(v___f_591_, 4, v_P_580_);
    crate::leanh::lean_closure_set(v___f_591_, 5, v_inst_581_);
    crate::leanh::lean_closure_set(v___f_591_, 6, v_lift_582_);
    v___x_592_ = l_WellFounded_opaqueFix_u2083___redArg(
        v___f_591_,
        v_it_585_,
        v_init_586_,
        crate::leanh::lean_box(0),
    );
    return v___x_592_;
}
pub unsafe fn l_Std_Iterators_Types_DropWhile_instIteratorLoop___redArg(
    mut v_P_593_: *mut crate::leanh::LeanObject,
    mut v_inst_594_: *mut crate::leanh::LeanObject,
    mut v_inst_595_: *mut crate::leanh::LeanObject,
    mut v_inst_596_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_597_ = crate::leanh::lean_alloc_closure(
        l_Std_Iterators_Types_DropWhile_instIteratorLoop___redArg___lam__2
            as *mut core::ffi::c_void,
        10,
        4,
    );
    crate::leanh::lean_closure_set(v___f_597_, 0, v_inst_595_);
    crate::leanh::lean_closure_set(v___f_597_, 1, v_inst_594_);
    crate::leanh::lean_closure_set(v___f_597_, 2, v_P_593_);
    crate::leanh::lean_closure_set(v___f_597_, 3, v_inst_596_);
    return v___f_597_;
}
pub unsafe fn l_Std_Iterators_Types_DropWhile_instIteratorLoop(
    mut v_00_u03b1_598_: *mut crate::leanh::LeanObject,
    mut v_m_599_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_600_: *mut crate::leanh::LeanObject,
    mut v_n_601_: *mut crate::leanh::LeanObject,
    mut v_P_602_: *mut crate::leanh::LeanObject,
    mut v_inst_603_: *mut crate::leanh::LeanObject,
    mut v_inst_604_: *mut crate::leanh::LeanObject,
    mut v_inst_605_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_606_ = crate::leanh::lean_alloc_closure(
        l_Std_Iterators_Types_DropWhile_instIteratorLoop___redArg___lam__2
            as *mut core::ffi::c_void,
        10,
        4,
    );
    crate::leanh::lean_closure_set(v___f_606_, 0, v_inst_604_);
    crate::leanh::lean_closure_set(v___f_606_, 1, v_inst_603_);
    crate::leanh::lean_closure_set(v___f_606_, 2, v_P_602_);
    crate::leanh::lean_closure_set(v___f_606_, 3, v_inst_605_);
    return v___f_606_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_Iterators_Combinators_Monadic_DropWhile(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Nat_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Collect(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Loop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_PostconditionMonad(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_Iterators_Combinators_Monadic_DropWhile(
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
pub unsafe fn initialize_Std_Data_Iterators_Combinators_Monadic_DropWhile(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Nat_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers_Monadic_Collect(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers_Monadic_Loop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_PostconditionMonad(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Combinators_Monadic_DropWhile(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Data_Iterators_Combinators_Monadic_DropWhile(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Data_Iterators_Combinators_Monadic_DropWhile(builtin);
}
