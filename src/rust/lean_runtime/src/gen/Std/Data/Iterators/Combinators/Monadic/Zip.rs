// Lean compiler output
// Module: Std.Data.Iterators.Combinators.Monadic.Zip
// Imports: Init.Data.Option.Lemmas Init.Data.Iterators.Consumers.Loop
use crate::r#gen::Init::Data::Iterators::Consumers::Loop::{
    initialize_Init_Data_Iterators_Consumers_Loop,
    runtime_initialize_Init_Data_Iterators_Consumers_Loop,
};
use crate::r#gen::Init::Data::Option::Lemmas::{
    initialize_Init_Data_Option_Lemmas, runtime_initialize_Init_Data_Option_Lemmas,
};
use crate::r#gen::Init::WFExtrinsicFix::l_WellFounded_opaqueFix_u2083___redArg;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_3, lean_apply_4, lean_box, lean_closure_set, lean_ctor_get,
    lean_ctor_set, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_tag,
};
pub unsafe fn l_Std_IterM_zip___redArg(
    mut v_left_280_: *mut LeanObject,
    mut v_right_281_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_283_: *mut LeanObject = core::ptr::null_mut();
    v___x_282_ = lean_box(0);
    v___x_283_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_283_, 0, v_left_280_);
    lean_ctor_set(v___x_283_, 1, v___x_282_);
    lean_ctor_set(v___x_283_, 2, v_right_281_);
    return v___x_283_;
}
pub unsafe fn l_Std_IterM_zip(
    mut v_m_284_: *mut LeanObject,
    mut v_00_u03b1_u2081_285_: *mut LeanObject,
    mut v_00_u03b2_u2081_286_: *mut LeanObject,
    mut v_inst_287_: *mut LeanObject,
    mut v_00_u03b1_u2082_288_: *mut LeanObject,
    mut v_00_u03b2_u2082_289_: *mut LeanObject,
    mut v_left_290_: *mut LeanObject,
    mut v_right_291_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_293_: *mut LeanObject = core::ptr::null_mut();
    v___x_292_ = lean_box(0);
    v___x_293_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_293_, 0, v_left_290_);
    lean_ctor_set(v___x_293_, 1, v___x_292_);
    lean_ctor_set(v___x_293_, 2, v_right_291_);
    return v___x_293_;
}
pub unsafe fn l_Std_IterM_zip___boxed(
    mut v_m_294_: *mut LeanObject,
    mut v_00_u03b1_u2081_295_: *mut LeanObject,
    mut v_00_u03b2_u2081_296_: *mut LeanObject,
    mut v_inst_297_: *mut LeanObject,
    mut v_00_u03b1_u2082_298_: *mut LeanObject,
    mut v_00_u03b2_u2082_299_: *mut LeanObject,
    mut v_left_300_: *mut LeanObject,
    mut v_right_301_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_302_: *mut LeanObject = core::ptr::null_mut();
    v_res_302_ = l_Std_IterM_zip(
        v_m_294_,
        v_00_u03b1_u2081_295_,
        v_00_u03b2_u2081_296_,
        v_inst_297_,
        v_00_u03b1_u2082_298_,
        v_00_u03b2_u2082_299_,
        v_left_300_,
        v_right_301_,
    );
    lean_dec(v_inst_297_);
    return v_res_302_;
}
pub unsafe fn l_Std_Iterators_Types_Zip_instIterator___redArg___lam__0(
    mut v_right_303_: *mut LeanObject,
    mut v_toPure_304_: *mut LeanObject,
    mut v_memoizedLeft_305_: *mut LeanObject,
    mut v_____do__lift_306_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_it_307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_out_308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_312_: *mut LeanObject = core::ptr::null_mut();
    let mut v_it_313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_315_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_316_: u8 = 0;
    let mut v___x_317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_320_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_321_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_322_: u8 = 0;
    let mut v___x_323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_324_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_____do__lift_306_) {
                0 => {
                    lean_dec(v_memoizedLeft_305_);
                    v_it_307_ = lean_ctor_get(v_____do__lift_306_, 0);
                    lean_inc(v_it_307_);
                    v_out_308_ = lean_ctor_get(v_____do__lift_306_, 1);
                    lean_inc(v_out_308_);
                    lean_dec_ref_known(v_____do__lift_306_, 2);
                    v___x_309_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_309_, 0, v_out_308_);
                    v___x_310_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v___x_310_, 0, v_it_307_);
                    lean_ctor_set(v___x_310_, 1, v___x_309_);
                    lean_ctor_set(v___x_310_, 2, v_right_303_);
                    v___x_311_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_311_, 0, v___x_310_);
                    v___x_312_ = lean_apply_2(v_toPure_304_, lean_box(0), v___x_311_);
                    return v___x_312_;
                }
                1 => {
                    v_it_313_ = lean_ctor_get(v_____do__lift_306_, 0);
                    v_isSharedCheck_322_ = (!lean_is_exclusive(v_____do__lift_306_)) as u8;
                    if v_isSharedCheck_322_ == 0 {
                        v___x_315_ = v_____do__lift_306_;
                        v_isShared_316_ = v_isSharedCheck_322_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_it_313_);
                        lean_dec(v_____do__lift_306_);
                        v___x_315_ = lean_box(0);
                        v_isShared_316_ = v_isSharedCheck_322_;
                        state = 1;
                        continue;
                    }
                }
                _ => {
                    lean_dec(v_memoizedLeft_305_);
                    lean_dec(v_right_303_);
                    v___x_323_ = lean_box(2);
                    v___x_324_ = lean_apply_2(v_toPure_304_, lean_box(0), v___x_323_);
                    return v___x_324_;
                }
            },
            1 => {
                v___x_317_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_317_, 0, v_it_313_);
                lean_ctor_set(v___x_317_, 1, v_memoizedLeft_305_);
                lean_ctor_set(v___x_317_, 2, v_right_303_);
                if v_isShared_316_ == 0 {
                    lean_ctor_set(v___x_315_, 0, v___x_317_);
                    v___x_319_ = v___x_315_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_321_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_321_, 0, v___x_317_);
                    v___x_319_ = v_reuseFailAlloc_321_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_320_ = lean_apply_2(v_toPure_304_, lean_box(0), v___x_319_);
                return v___x_320_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Iterators_Types_Zip_instIterator___redArg___lam__1(
    mut v_left_325_: *mut LeanObject,
    mut v_val_326_: *mut LeanObject,
    mut v_toPure_327_: *mut LeanObject,
    mut v_memoizedLeft_328_: *mut LeanObject,
    mut v_____do__lift_329_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_it_330_: *mut LeanObject = core::ptr::null_mut();
    let mut v_out_331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_333_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_334_: u8 = 0;
    let mut v___x_335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_340_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_342_: u8 = 0;
    let mut v_it_343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_345_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_346_: u8 = 0;
    let mut v___x_347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_350_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_352_: u8 = 0;
    let mut v___x_353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_354_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_____do__lift_329_) {
                0 => {
                    lean_dec(v_memoizedLeft_328_);
                    v_it_330_ = lean_ctor_get(v_____do__lift_329_, 0);
                    v_out_331_ = lean_ctor_get(v_____do__lift_329_, 1);
                    v_isSharedCheck_342_ = (!lean_is_exclusive(v_____do__lift_329_)) as u8;
                    if v_isSharedCheck_342_ == 0 {
                        v___x_333_ = v_____do__lift_329_;
                        v_isShared_334_ = v_isSharedCheck_342_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_out_331_);
                        lean_inc(v_it_330_);
                        lean_dec(v_____do__lift_329_);
                        v___x_333_ = lean_box(0);
                        v_isShared_334_ = v_isSharedCheck_342_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    lean_dec(v_val_326_);
                    v_it_343_ = lean_ctor_get(v_____do__lift_329_, 0);
                    v_isSharedCheck_352_ = (!lean_is_exclusive(v_____do__lift_329_)) as u8;
                    if v_isSharedCheck_352_ == 0 {
                        v___x_345_ = v_____do__lift_329_;
                        v_isShared_346_ = v_isSharedCheck_352_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_it_343_);
                        lean_dec(v_____do__lift_329_);
                        v___x_345_ = lean_box(0);
                        v_isShared_346_ = v_isSharedCheck_352_;
                        state = 3;
                        continue;
                    }
                }
                _ => {
                    lean_dec(v_memoizedLeft_328_);
                    lean_dec(v_val_326_);
                    lean_dec(v_left_325_);
                    v___x_353_ = lean_box(2);
                    v___x_354_ = lean_apply_2(v_toPure_327_, lean_box(0), v___x_353_);
                    return v___x_354_;
                }
            },
            1 => {
                v___x_335_ = lean_box(0);
                v___x_336_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_336_, 0, v_left_325_);
                lean_ctor_set(v___x_336_, 1, v___x_335_);
                lean_ctor_set(v___x_336_, 2, v_it_330_);
                v___x_337_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_337_, 0, v_val_326_);
                lean_ctor_set(v___x_337_, 1, v_out_331_);
                if v_isShared_334_ == 0 {
                    lean_ctor_set(v___x_333_, 1, v___x_337_);
                    lean_ctor_set(v___x_333_, 0, v___x_336_);
                    v___x_339_ = v___x_333_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_341_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_341_, 0, v___x_336_);
                    lean_ctor_set(v_reuseFailAlloc_341_, 1, v___x_337_);
                    v___x_339_ = v_reuseFailAlloc_341_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_340_ = lean_apply_2(v_toPure_327_, lean_box(0), v___x_339_);
                return v___x_340_;
            }
            3 => {
                v___x_347_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_347_, 0, v_left_325_);
                lean_ctor_set(v___x_347_, 1, v_memoizedLeft_328_);
                lean_ctor_set(v___x_347_, 2, v_it_343_);
                if v_isShared_346_ == 0 {
                    lean_ctor_set(v___x_345_, 0, v___x_347_);
                    v___x_349_ = v___x_345_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_351_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_351_, 0, v___x_347_);
                    v___x_349_ = v_reuseFailAlloc_351_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_350_ = lean_apply_2(v_toPure_327_, lean_box(0), v___x_349_);
                return v___x_350_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Iterators_Types_Zip_instIterator___redArg___lam__2(
    mut v_toPure_355_: *mut LeanObject,
    mut v_inst_356_: *mut LeanObject,
    mut v_toBind_357_: *mut LeanObject,
    mut v_inst_358_: *mut LeanObject,
    mut v_it_359_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_memoizedLeft_360_: *mut LeanObject = core::ptr::null_mut();
    v_memoizedLeft_360_ = lean_ctor_get(v_it_359_, 1);
    lean_inc(v_memoizedLeft_360_);
    if lean_obj_tag(v_memoizedLeft_360_) == 0 {
        let mut v_left_361_: *mut LeanObject = core::ptr::null_mut();
        let mut v_right_362_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_363_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_364_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_365_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_inst_358_);
        v_left_361_ = lean_ctor_get(v_it_359_, 0);
        lean_inc(v_left_361_);
        v_right_362_ = lean_ctor_get(v_it_359_, 2);
        lean_inc(v_right_362_);
        lean_dec_ref(v_it_359_);
        v___f_363_ = lean_alloc_closure(
            l_Std_Iterators_Types_Zip_instIterator___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            3,
        );
        lean_closure_set(v___f_363_, 0, v_right_362_);
        lean_closure_set(v___f_363_, 1, v_toPure_355_);
        lean_closure_set(v___f_363_, 2, v_memoizedLeft_360_);
        v___x_364_ = lean_apply_1(v_inst_356_, v_left_361_);
        v___x_365_ = lean_apply_4(
            v_toBind_357_,
            lean_box(0),
            lean_box(0),
            v___x_364_,
            v___f_363_,
        );
        return v___x_365_;
    } else {
        let mut v_left_366_: *mut LeanObject = core::ptr::null_mut();
        let mut v_right_367_: *mut LeanObject = core::ptr::null_mut();
        let mut v_val_368_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_369_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_370_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_371_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_inst_356_);
        v_left_366_ = lean_ctor_get(v_it_359_, 0);
        lean_inc(v_left_366_);
        v_right_367_ = lean_ctor_get(v_it_359_, 2);
        lean_inc(v_right_367_);
        lean_dec_ref(v_it_359_);
        v_val_368_ = lean_ctor_get(v_memoizedLeft_360_, 0);
        lean_inc(v_val_368_);
        v___f_369_ = lean_alloc_closure(
            l_Std_Iterators_Types_Zip_instIterator___redArg___lam__1 as *mut core::ffi::c_void,
            5,
            4,
        );
        lean_closure_set(v___f_369_, 0, v_left_366_);
        lean_closure_set(v___f_369_, 1, v_val_368_);
        lean_closure_set(v___f_369_, 2, v_toPure_355_);
        lean_closure_set(v___f_369_, 3, v_memoizedLeft_360_);
        v___x_370_ = lean_apply_1(v_inst_358_, v_right_367_);
        v___x_371_ = lean_apply_4(
            v_toBind_357_,
            lean_box(0),
            lean_box(0),
            v___x_370_,
            v___f_369_,
        );
        return v___x_371_;
    }
}
pub unsafe fn l_Std_Iterators_Types_Zip_instIterator___redArg(
    mut v_inst_372_: *mut LeanObject,
    mut v_inst_373_: *mut LeanObject,
    mut v_inst_374_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_376_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_378_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_375_ = lean_ctor_get(v_inst_374_, 0);
    lean_inc_ref(v_toApplicative_375_);
    v_toBind_376_ = lean_ctor_get(v_inst_374_, 1);
    lean_inc(v_toBind_376_);
    lean_dec_ref(v_inst_374_);
    v_toPure_377_ = lean_ctor_get(v_toApplicative_375_, 1);
    lean_inc(v_toPure_377_);
    lean_dec_ref(v_toApplicative_375_);
    v___f_378_ = lean_alloc_closure(
        l_Std_Iterators_Types_Zip_instIterator___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_378_, 0, v_toPure_377_);
    lean_closure_set(v___f_378_, 1, v_inst_372_);
    lean_closure_set(v___f_378_, 2, v_toBind_376_);
    lean_closure_set(v___f_378_, 3, v_inst_373_);
    return v___f_378_;
}
pub unsafe fn l_Std_Iterators_Types_Zip_instIterator(
    mut v_m_379_: *mut LeanObject,
    mut v_00_u03b1_u2081_380_: *mut LeanObject,
    mut v_00_u03b2_u2081_381_: *mut LeanObject,
    mut v_inst_382_: *mut LeanObject,
    mut v_00_u03b1_u2082_383_: *mut LeanObject,
    mut v_00_u03b2_u2082_384_: *mut LeanObject,
    mut v_inst_385_: *mut LeanObject,
    mut v_inst_386_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_387_: *mut LeanObject = core::ptr::null_mut();
    v___x_387_ =
        l_Std_Iterators_Types_Zip_instIterator___redArg(v_inst_382_, v_inst_385_, v_inst_386_);
    return v___x_387_;
}
pub unsafe fn l_Std_Iterators_Types_Zip_instFinitenessRelation_u2081(
    mut v_m_388_: *mut LeanObject,
    mut v_00_u03b1_u2081_389_: *mut LeanObject,
    mut v_00_u03b2_u2081_390_: *mut LeanObject,
    mut v_inst_391_: *mut LeanObject,
    mut v_00_u03b1_u2082_392_: *mut LeanObject,
    mut v_00_u03b2_u2082_393_: *mut LeanObject,
    mut v_inst_394_: *mut LeanObject,
    mut v_inst_395_: *mut LeanObject,
    mut v_inst_396_: *mut LeanObject,
    mut v_inst_397_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_398_: *mut LeanObject = core::ptr::null_mut();
    v___x_398_ = lean_box(0);
    return v___x_398_;
}
pub unsafe fn l_Std_Iterators_Types_Zip_instFinitenessRelation_u2081___boxed(
    mut v_m_399_: *mut LeanObject,
    mut v_00_u03b1_u2081_400_: *mut LeanObject,
    mut v_00_u03b2_u2081_401_: *mut LeanObject,
    mut v_inst_402_: *mut LeanObject,
    mut v_00_u03b1_u2082_403_: *mut LeanObject,
    mut v_00_u03b2_u2082_404_: *mut LeanObject,
    mut v_inst_405_: *mut LeanObject,
    mut v_inst_406_: *mut LeanObject,
    mut v_inst_407_: *mut LeanObject,
    mut v_inst_408_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_409_: *mut LeanObject = core::ptr::null_mut();
    v_res_409_ = l_Std_Iterators_Types_Zip_instFinitenessRelation_u2081(
        v_m_399_,
        v_00_u03b1_u2081_400_,
        v_00_u03b2_u2081_401_,
        v_inst_402_,
        v_00_u03b1_u2082_403_,
        v_00_u03b2_u2082_404_,
        v_inst_405_,
        v_inst_406_,
        v_inst_407_,
        v_inst_408_,
    );
    lean_dec_ref(v_inst_406_);
    lean_dec(v_inst_405_);
    lean_dec(v_inst_402_);
    return v_res_409_;
}
pub unsafe fn l___private_Std_Data_Iterators_Combinators_Monadic_Zip_0__Option_SomeLtNone_lt_match__1_splitter___redArg(
    mut v_x_410_: *mut LeanObject,
    mut v_x_411_: *mut LeanObject,
    mut v_h__1_412_: *mut LeanObject,
    mut v_h__2_413_: *mut LeanObject,
    mut v_h__3_414_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_410_) == 0 {
        let mut v___x_415_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__3_414_);
        lean_dec(v_h__2_413_);
        v___x_415_ = lean_apply_1(v_h__1_412_, v_x_411_);
        return v___x_415_;
    } else {
        lean_dec(v_h__1_412_);
        if lean_obj_tag(v_x_411_) == 0 {
            let mut v_val_416_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_417_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_414_);
            v_val_416_ = lean_ctor_get(v_x_410_, 0);
            lean_inc(v_val_416_);
            lean_dec_ref_known(v_x_410_, 1);
            v___x_417_ = lean_apply_1(v_h__2_413_, v_val_416_);
            return v___x_417_;
        } else {
            let mut v_val_418_: *mut LeanObject = core::ptr::null_mut();
            let mut v_val_419_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_420_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_413_);
            v_val_418_ = lean_ctor_get(v_x_410_, 0);
            lean_inc(v_val_418_);
            lean_dec_ref_known(v_x_410_, 1);
            v_val_419_ = lean_ctor_get(v_x_411_, 0);
            lean_inc(v_val_419_);
            lean_dec_ref_known(v_x_411_, 1);
            v___x_420_ = lean_apply_2(v_h__3_414_, v_val_418_, v_val_419_);
            return v___x_420_;
        }
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Combinators_Monadic_Zip_0__Option_SomeLtNone_lt_match__1_splitter(
    mut v_00_u03b2_421_: *mut LeanObject,
    mut v_00_u03b1_422_: *mut LeanObject,
    mut v_motive_423_: *mut LeanObject,
    mut v_x_424_: *mut LeanObject,
    mut v_x_425_: *mut LeanObject,
    mut v_h__1_426_: *mut LeanObject,
    mut v_h__2_427_: *mut LeanObject,
    mut v_h__3_428_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_424_) == 0 {
        let mut v___x_429_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__3_428_);
        lean_dec(v_h__2_427_);
        v___x_429_ = lean_apply_1(v_h__1_426_, v_x_425_);
        return v___x_429_;
    } else {
        lean_dec(v_h__1_426_);
        if lean_obj_tag(v_x_425_) == 0 {
            let mut v_val_430_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_431_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_428_);
            v_val_430_ = lean_ctor_get(v_x_424_, 0);
            lean_inc(v_val_430_);
            lean_dec_ref_known(v_x_424_, 1);
            v___x_431_ = lean_apply_1(v_h__2_427_, v_val_430_);
            return v___x_431_;
        } else {
            let mut v_val_432_: *mut LeanObject = core::ptr::null_mut();
            let mut v_val_433_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_434_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_427_);
            v_val_432_ = lean_ctor_get(v_x_424_, 0);
            lean_inc(v_val_432_);
            lean_dec_ref_known(v_x_424_, 1);
            v_val_433_ = lean_ctor_get(v_x_425_, 0);
            lean_inc(v_val_433_);
            lean_dec_ref_known(v_x_425_, 1);
            v___x_434_ = lean_apply_2(v_h__3_428_, v_val_432_, v_val_433_);
            return v___x_434_;
        }
    }
}
pub unsafe fn l_Std_Iterators_Types_Zip_instFinitenessRelation_u2082(
    mut v_m_435_: *mut LeanObject,
    mut v_00_u03b1_u2081_436_: *mut LeanObject,
    mut v_00_u03b2_u2081_437_: *mut LeanObject,
    mut v_inst_438_: *mut LeanObject,
    mut v_00_u03b1_u2082_439_: *mut LeanObject,
    mut v_00_u03b2_u2082_440_: *mut LeanObject,
    mut v_inst_441_: *mut LeanObject,
    mut v_inst_442_: *mut LeanObject,
    mut v_inst_443_: *mut LeanObject,
    mut v_inst_444_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_445_: *mut LeanObject = core::ptr::null_mut();
    v___x_445_ = lean_box(0);
    return v___x_445_;
}
pub unsafe fn l_Std_Iterators_Types_Zip_instFinitenessRelation_u2082___boxed(
    mut v_m_446_: *mut LeanObject,
    mut v_00_u03b1_u2081_447_: *mut LeanObject,
    mut v_00_u03b2_u2081_448_: *mut LeanObject,
    mut v_inst_449_: *mut LeanObject,
    mut v_00_u03b1_u2082_450_: *mut LeanObject,
    mut v_00_u03b2_u2082_451_: *mut LeanObject,
    mut v_inst_452_: *mut LeanObject,
    mut v_inst_453_: *mut LeanObject,
    mut v_inst_454_: *mut LeanObject,
    mut v_inst_455_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_456_: *mut LeanObject = core::ptr::null_mut();
    v_res_456_ = l_Std_Iterators_Types_Zip_instFinitenessRelation_u2082(
        v_m_446_,
        v_00_u03b1_u2081_447_,
        v_00_u03b2_u2081_448_,
        v_inst_449_,
        v_00_u03b1_u2082_450_,
        v_00_u03b2_u2082_451_,
        v_inst_452_,
        v_inst_453_,
        v_inst_454_,
        v_inst_455_,
    );
    lean_dec_ref(v_inst_453_);
    lean_dec(v_inst_452_);
    lean_dec(v_inst_449_);
    return v_res_456_;
}
pub unsafe fn l_Std_Iterators_Types_Zip_instProductivenessRelation(
    mut v_m_457_: *mut LeanObject,
    mut v_00_u03b1_u2081_458_: *mut LeanObject,
    mut v_00_u03b2_u2081_459_: *mut LeanObject,
    mut v_inst_460_: *mut LeanObject,
    mut v_00_u03b1_u2082_461_: *mut LeanObject,
    mut v_00_u03b2_u2082_462_: *mut LeanObject,
    mut v_inst_463_: *mut LeanObject,
    mut v_inst_464_: *mut LeanObject,
    mut v_inst_465_: *mut LeanObject,
    mut v_inst_466_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_467_: *mut LeanObject = core::ptr::null_mut();
    v___x_467_ = lean_box(0);
    return v___x_467_;
}
pub unsafe fn l_Std_Iterators_Types_Zip_instProductivenessRelation___boxed(
    mut v_m_468_: *mut LeanObject,
    mut v_00_u03b1_u2081_469_: *mut LeanObject,
    mut v_00_u03b2_u2081_470_: *mut LeanObject,
    mut v_inst_471_: *mut LeanObject,
    mut v_00_u03b1_u2082_472_: *mut LeanObject,
    mut v_00_u03b2_u2082_473_: *mut LeanObject,
    mut v_inst_474_: *mut LeanObject,
    mut v_inst_475_: *mut LeanObject,
    mut v_inst_476_: *mut LeanObject,
    mut v_inst_477_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_478_: *mut LeanObject = core::ptr::null_mut();
    v_res_478_ = l_Std_Iterators_Types_Zip_instProductivenessRelation(
        v_m_468_,
        v_00_u03b1_u2081_469_,
        v_00_u03b2_u2081_470_,
        v_inst_471_,
        v_00_u03b1_u2082_472_,
        v_00_u03b2_u2082_473_,
        v_inst_474_,
        v_inst_475_,
        v_inst_476_,
        v_inst_477_,
    );
    lean_dec_ref(v_inst_475_);
    lean_dec(v_inst_474_);
    lean_dec(v_inst_471_);
    return v_res_478_;
}
pub unsafe fn l_Std_Iterators_Types_Zip_instIteratorLoop___redArg___lam__0(
    mut v_toPure_479_: *mut LeanObject,
    mut v_recur_480_: *mut LeanObject,
    mut v_it_481_: *mut LeanObject,
    mut v_____do__lift_482_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_482_) == 0 {
        let mut v_a_483_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_484_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_it_481_);
        lean_dec(v_recur_480_);
        v_a_483_ = lean_ctor_get(v_____do__lift_482_, 0);
        lean_inc(v_a_483_);
        lean_dec_ref_known(v_____do__lift_482_, 1);
        v___x_484_ = lean_apply_2(v_toPure_479_, lean_box(0), v_a_483_);
        return v___x_484_;
    } else {
        let mut v_a_485_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_486_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_toPure_479_);
        v_a_485_ = lean_ctor_get(v_____do__lift_482_, 0);
        lean_inc(v_a_485_);
        lean_dec_ref_known(v_____do__lift_482_, 1);
        v___x_486_ = lean_apply_4(v_recur_480_, v_it_481_, v_a_485_, lean_box(0), lean_box(0));
        return v___x_486_;
    }
}
pub unsafe fn l_Std_Iterators_Types_Zip_instIteratorLoop___redArg___lam__1(
    mut v_toPure_487_: *mut LeanObject,
    mut v_recur_488_: *mut LeanObject,
    mut v___y_489_: *mut LeanObject,
    mut v_acc_490_: *mut LeanObject,
    mut v_toBind_491_: *mut LeanObject,
    mut v_s_492_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_s_492_) {
        0 => {
            let mut v_it_493_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_494_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_495_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_496_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_497_: *mut LeanObject = core::ptr::null_mut();
            v_it_493_ = lean_ctor_get(v_s_492_, 0);
            lean_inc(v_it_493_);
            v_out_494_ = lean_ctor_get(v_s_492_, 1);
            lean_inc(v_out_494_);
            lean_dec_ref_known(v_s_492_, 2);
            v___f_495_ = lean_alloc_closure(
                l_Std_Iterators_Types_Zip_instIteratorLoop___redArg___lam__0
                    as *mut core::ffi::c_void,
                4,
                3,
            );
            lean_closure_set(v___f_495_, 0, v_toPure_487_);
            lean_closure_set(v___f_495_, 1, v_recur_488_);
            lean_closure_set(v___f_495_, 2, v_it_493_);
            v___x_496_ = lean_apply_3(v___y_489_, v_out_494_, lean_box(0), v_acc_490_);
            v___x_497_ = lean_apply_4(
                v_toBind_491_,
                lean_box(0),
                lean_box(0),
                v___x_496_,
                v___f_495_,
            );
            return v___x_497_;
        }
        1 => {
            let mut v_it_498_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_499_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_toBind_491_);
            lean_dec(v___y_489_);
            lean_dec(v_toPure_487_);
            v_it_498_ = lean_ctor_get(v_s_492_, 0);
            lean_inc(v_it_498_);
            lean_dec_ref_known(v_s_492_, 1);
            v___x_499_ = lean_apply_4(
                v_recur_488_,
                v_it_498_,
                v_acc_490_,
                lean_box(0),
                lean_box(0),
            );
            return v___x_499_;
        }
        _ => {
            let mut v___x_500_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_toBind_491_);
            lean_dec(v___y_489_);
            lean_dec(v_recur_488_);
            v___x_500_ = lean_apply_2(v_toPure_487_, lean_box(0), v_acc_490_);
            return v___x_500_;
        }
    }
}
pub unsafe fn l_Std_Iterators_Types_Zip_instIteratorLoop___redArg___lam__4(
    mut v_inst_501_: *mut LeanObject,
    mut v_toPure_502_: *mut LeanObject,
    mut v___y_503_: *mut LeanObject,
    mut v_toBind_504_: *mut LeanObject,
    mut v_inst_505_: *mut LeanObject,
    mut v_lift_506_: *mut LeanObject,
    mut v_inst_507_: *mut LeanObject,
    mut v_it_508_: *mut LeanObject,
    mut v_acc_509_: *mut LeanObject,
    mut v_hP_510_: *mut LeanObject,
    mut v_recur_511_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_513_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_514_: *mut LeanObject = core::ptr::null_mut();
    let mut v_left_515_: *mut LeanObject = core::ptr::null_mut();
    let mut v_memoizedLeft_516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_right_517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_518_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_512_ = lean_ctor_get(v_inst_501_, 0);
    lean_inc_ref(v_toApplicative_512_);
    v_toBind_513_ = lean_ctor_get(v_inst_501_, 1);
    lean_inc(v_toBind_513_);
    lean_dec_ref(v_inst_501_);
    v_toPure_514_ = lean_ctor_get(v_toApplicative_512_, 1);
    lean_inc(v_toPure_514_);
    lean_dec_ref(v_toApplicative_512_);
    v_left_515_ = lean_ctor_get(v_it_508_, 0);
    lean_inc(v_left_515_);
    v_memoizedLeft_516_ = lean_ctor_get(v_it_508_, 1);
    lean_inc(v_memoizedLeft_516_);
    v_right_517_ = lean_ctor_get(v_it_508_, 2);
    lean_inc(v_right_517_);
    lean_dec_ref(v_it_508_);
    v___f_518_ = lean_alloc_closure(
        l_Std_Iterators_Types_Zip_instIteratorLoop___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        5,
    );
    lean_closure_set(v___f_518_, 0, v_toPure_502_);
    lean_closure_set(v___f_518_, 1, v_recur_511_);
    lean_closure_set(v___f_518_, 2, v___y_503_);
    lean_closure_set(v___f_518_, 3, v_acc_509_);
    lean_closure_set(v___f_518_, 4, v_toBind_504_);
    if lean_obj_tag(v_memoizedLeft_516_) == 0 {
        let mut v___f_519_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_520_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_521_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_522_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_inst_507_);
        v___f_519_ = lean_alloc_closure(
            l_Std_Iterators_Types_Zip_instIterator___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            3,
        );
        lean_closure_set(v___f_519_, 0, v_right_517_);
        lean_closure_set(v___f_519_, 1, v_toPure_514_);
        lean_closure_set(v___f_519_, 2, v_memoizedLeft_516_);
        v___x_520_ = lean_apply_1(v_inst_505_, v_left_515_);
        v___x_521_ = lean_apply_4(
            v_toBind_513_,
            lean_box(0),
            lean_box(0),
            v___x_520_,
            v___f_519_,
        );
        v___x_522_ = lean_apply_4(
            v_lift_506_,
            lean_box(0),
            lean_box(0),
            v___f_518_,
            v___x_521_,
        );
        return v___x_522_;
    } else {
        let mut v_val_523_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_524_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_525_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_526_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_527_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_inst_505_);
        v_val_523_ = lean_ctor_get(v_memoizedLeft_516_, 0);
        lean_inc(v_val_523_);
        v___f_524_ = lean_alloc_closure(
            l_Std_Iterators_Types_Zip_instIterator___redArg___lam__1 as *mut core::ffi::c_void,
            5,
            4,
        );
        lean_closure_set(v___f_524_, 0, v_left_515_);
        lean_closure_set(v___f_524_, 1, v_val_523_);
        lean_closure_set(v___f_524_, 2, v_toPure_514_);
        lean_closure_set(v___f_524_, 3, v_memoizedLeft_516_);
        v___x_525_ = lean_apply_1(v_inst_507_, v_right_517_);
        v___x_526_ = lean_apply_4(
            v_toBind_513_,
            lean_box(0),
            lean_box(0),
            v___x_525_,
            v___f_524_,
        );
        v___x_527_ = lean_apply_4(
            v_lift_506_,
            lean_box(0),
            lean_box(0),
            v___f_518_,
            v___x_526_,
        );
        return v___x_527_;
    }
}
pub unsafe fn l_Std_Iterators_Types_Zip_instIteratorLoop___redArg___lam__2(
    mut v_inst_528_: *mut LeanObject,
    mut v_inst_529_: *mut LeanObject,
    mut v_inst_530_: *mut LeanObject,
    mut v_inst_531_: *mut LeanObject,
    mut v_lift_532_: *mut LeanObject,
    mut v_00_u03b3_533_: *mut LeanObject,
    mut v_Pl_534_: *mut LeanObject,
    mut v_it_535_: *mut LeanObject,
    mut v_init_536_: *mut LeanObject,
    mut v___y_537_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_542_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_538_ = lean_ctor_get(v_inst_528_, 0);
    lean_inc_ref(v_toApplicative_538_);
    v_toBind_539_ = lean_ctor_get(v_inst_528_, 1);
    lean_inc(v_toBind_539_);
    lean_dec_ref(v_inst_528_);
    v_toPure_540_ = lean_ctor_get(v_toApplicative_538_, 1);
    lean_inc(v_toPure_540_);
    lean_dec_ref(v_toApplicative_538_);
    v___f_541_ = lean_alloc_closure(
        l_Std_Iterators_Types_Zip_instIteratorLoop___redArg___lam__4 as *mut core::ffi::c_void,
        11,
        7,
    );
    lean_closure_set(v___f_541_, 0, v_inst_529_);
    lean_closure_set(v___f_541_, 1, v_toPure_540_);
    lean_closure_set(v___f_541_, 2, v___y_537_);
    lean_closure_set(v___f_541_, 3, v_toBind_539_);
    lean_closure_set(v___f_541_, 4, v_inst_530_);
    lean_closure_set(v___f_541_, 5, v_lift_532_);
    lean_closure_set(v___f_541_, 6, v_inst_531_);
    v___x_542_ =
        l_WellFounded_opaqueFix_u2083___redArg(v___f_541_, v_it_535_, v_init_536_, lean_box(0));
    return v___x_542_;
}
pub unsafe fn l_Std_Iterators_Types_Zip_instIteratorLoop___redArg(
    mut v_inst_543_: *mut LeanObject,
    mut v_inst_544_: *mut LeanObject,
    mut v_inst_545_: *mut LeanObject,
    mut v_inst_546_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_547_: *mut LeanObject = core::ptr::null_mut();
    v___f_547_ = lean_alloc_closure(
        l_Std_Iterators_Types_Zip_instIteratorLoop___redArg___lam__2 as *mut core::ffi::c_void,
        10,
        4,
    );
    lean_closure_set(v___f_547_, 0, v_inst_546_);
    lean_closure_set(v___f_547_, 1, v_inst_545_);
    lean_closure_set(v___f_547_, 2, v_inst_543_);
    lean_closure_set(v___f_547_, 3, v_inst_544_);
    return v___f_547_;
}
pub unsafe fn l_Std_Iterators_Types_Zip_instIteratorLoop(
    mut v_m_548_: *mut LeanObject,
    mut v_00_u03b1_u2081_549_: *mut LeanObject,
    mut v_00_u03b2_u2081_550_: *mut LeanObject,
    mut v_inst_551_: *mut LeanObject,
    mut v_00_u03b1_u2082_552_: *mut LeanObject,
    mut v_00_u03b2_u2082_553_: *mut LeanObject,
    mut v_inst_554_: *mut LeanObject,
    mut v_n_555_: *mut LeanObject,
    mut v_inst_556_: *mut LeanObject,
    mut v_inst_557_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_558_: *mut LeanObject = core::ptr::null_mut();
    v___f_558_ = lean_alloc_closure(
        l_Std_Iterators_Types_Zip_instIteratorLoop___redArg___lam__2 as *mut core::ffi::c_void,
        10,
        4,
    );
    lean_closure_set(v___f_558_, 0, v_inst_557_);
    lean_closure_set(v___f_558_, 1, v_inst_556_);
    lean_closure_set(v___f_558_, 2, v_inst_551_);
    lean_closure_set(v___f_558_, 3, v_inst_554_);
    return v___f_558_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_Iterators_Combinators_Monadic_Zip(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Loop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_Iterators_Combinators_Monadic_Zip(
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
pub unsafe fn initialize_Std_Data_Iterators_Combinators_Monadic_Zip(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Option_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers_Loop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Combinators_Monadic_Zip(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Data_Iterators_Combinators_Monadic_Zip(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Data_Iterators_Combinators_Monadic_Zip(builtin);
}
