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
pub unsafe fn l_Std_IterM_zip___redArg(
    mut v_left_280_: *mut leanh::LeanObject,
    mut v_right_281_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_283_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_282_ = leanh::lean_box(0);
    v___x_283_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_283_, 0, v_left_280_);
    leanh::lean_ctor_set(v___x_283_, 1, v___x_282_);
    leanh::lean_ctor_set(v___x_283_, 2, v_right_281_);
    return v___x_283_;
}
pub unsafe fn l_Std_IterM_zip(
    mut v_m_284_: *mut leanh::LeanObject,
    mut v_00_u03b1_u2081_285_: *mut leanh::LeanObject,
    mut v_00_u03b2_u2081_286_: *mut leanh::LeanObject,
    mut v_inst_287_: *mut leanh::LeanObject,
    mut v_00_u03b1_u2082_288_: *mut leanh::LeanObject,
    mut v_00_u03b2_u2082_289_: *mut leanh::LeanObject,
    mut v_left_290_: *mut leanh::LeanObject,
    mut v_right_291_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_293_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_292_ = leanh::lean_box(0);
    v___x_293_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_293_, 0, v_left_290_);
    leanh::lean_ctor_set(v___x_293_, 1, v___x_292_);
    leanh::lean_ctor_set(v___x_293_, 2, v_right_291_);
    return v___x_293_;
}
pub unsafe fn l_Std_IterM_zip___boxed(
    mut v_m_294_: *mut leanh::LeanObject,
    mut v_00_u03b1_u2081_295_: *mut leanh::LeanObject,
    mut v_00_u03b2_u2081_296_: *mut leanh::LeanObject,
    mut v_inst_297_: *mut leanh::LeanObject,
    mut v_00_u03b1_u2082_298_: *mut leanh::LeanObject,
    mut v_00_u03b2_u2082_299_: *mut leanh::LeanObject,
    mut v_left_300_: *mut leanh::LeanObject,
    mut v_right_301_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_302_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_inst_297_);
    return v_res_302_;
}
pub unsafe fn l_Std_Iterators_Types_Zip_instIterator___redArg___lam__0(
    mut v_right_303_: *mut leanh::LeanObject,
    mut v_toPure_304_: *mut leanh::LeanObject,
    mut v_memoizedLeft_305_: *mut leanh::LeanObject,
    mut v_____do__lift_306_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_it_307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_out_308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_it_313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_316_: u8 = 0;
    let mut v___x_317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_322_: u8 = 0;
    let mut v___x_323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_____do__lift_306_) {
                0 => {
                    leanh::lean_dec(v_memoizedLeft_305_);
                    v_it_307_ = leanh::lean_ctor_get(v_____do__lift_306_, 0);
                    leanh::lean_inc(v_it_307_);
                    v_out_308_ = leanh::lean_ctor_get(v_____do__lift_306_, 1);
                    leanh::lean_inc(v_out_308_);
                    leanh::lean_dec_ref_known(v_____do__lift_306_, 2);
                    v___x_309_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_309_, 0, v_out_308_);
                    v___x_310_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_310_, 0, v_it_307_);
                    leanh::lean_ctor_set(v___x_310_, 1, v___x_309_);
                    leanh::lean_ctor_set(v___x_310_, 2, v_right_303_);
                    v___x_311_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_311_, 0, v___x_310_);
                    v___x_312_ = leanh::lean_apply_2(
                        v_toPure_304_,
                        leanh::lean_box(0),
                        v___x_311_,
                    );
                    return v___x_312_;
                }
                1 => {
                    v_it_313_ = leanh::lean_ctor_get(v_____do__lift_306_, 0);
                    v_isSharedCheck_322_ =
                        (!leanh::lean_is_exclusive(v_____do__lift_306_)) as u8;
                    if v_isSharedCheck_322_ == 0 {
                        v___x_315_ = v_____do__lift_306_;
                        v_isShared_316_ = v_isSharedCheck_322_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_it_313_);
                        leanh::lean_dec(v_____do__lift_306_);
                        v___x_315_ = leanh::lean_box(0);
                        v_isShared_316_ = v_isSharedCheck_322_;
                        state = 1;
                        continue;
                    }
                }
                _ => {
                    leanh::lean_dec(v_memoizedLeft_305_);
                    leanh::lean_dec(v_right_303_);
                    v___x_323_ = leanh::lean_box(2);
                    v___x_324_ = leanh::lean_apply_2(
                        v_toPure_304_,
                        leanh::lean_box(0),
                        v___x_323_,
                    );
                    return v___x_324_;
                }
            },
            1 => {
                v___x_317_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_317_, 0, v_it_313_);
                leanh::lean_ctor_set(v___x_317_, 1, v_memoizedLeft_305_);
                leanh::lean_ctor_set(v___x_317_, 2, v_right_303_);
                if v_isShared_316_ == 0 {
                    leanh::lean_ctor_set(v___x_315_, 0, v___x_317_);
                    v___x_319_ = v___x_315_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_321_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_321_, 0, v___x_317_);
                    v___x_319_ = v_reuseFailAlloc_321_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_320_ = leanh::lean_apply_2(
                    v_toPure_304_,
                    leanh::lean_box(0),
                    v___x_319_,
                );
                return v___x_320_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Iterators_Types_Zip_instIterator___redArg___lam__1(
    mut v_left_325_: *mut leanh::LeanObject,
    mut v_val_326_: *mut leanh::LeanObject,
    mut v_toPure_327_: *mut leanh::LeanObject,
    mut v_memoizedLeft_328_: *mut leanh::LeanObject,
    mut v_____do__lift_329_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_it_330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_out_331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_334_: u8 = 0;
    let mut v___x_335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_342_: u8 = 0;
    let mut v_it_343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_346_: u8 = 0;
    let mut v___x_347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_352_: u8 = 0;
    let mut v___x_353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_____do__lift_329_) {
                0 => {
                    leanh::lean_dec(v_memoizedLeft_328_);
                    v_it_330_ = leanh::lean_ctor_get(v_____do__lift_329_, 0);
                    v_out_331_ = leanh::lean_ctor_get(v_____do__lift_329_, 1);
                    v_isSharedCheck_342_ =
                        (!leanh::lean_is_exclusive(v_____do__lift_329_)) as u8;
                    if v_isSharedCheck_342_ == 0 {
                        v___x_333_ = v_____do__lift_329_;
                        v_isShared_334_ = v_isSharedCheck_342_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_out_331_);
                        leanh::lean_inc(v_it_330_);
                        leanh::lean_dec(v_____do__lift_329_);
                        v___x_333_ = leanh::lean_box(0);
                        v_isShared_334_ = v_isSharedCheck_342_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    leanh::lean_dec(v_val_326_);
                    v_it_343_ = leanh::lean_ctor_get(v_____do__lift_329_, 0);
                    v_isSharedCheck_352_ =
                        (!leanh::lean_is_exclusive(v_____do__lift_329_)) as u8;
                    if v_isSharedCheck_352_ == 0 {
                        v___x_345_ = v_____do__lift_329_;
                        v_isShared_346_ = v_isSharedCheck_352_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_it_343_);
                        leanh::lean_dec(v_____do__lift_329_);
                        v___x_345_ = leanh::lean_box(0);
                        v_isShared_346_ = v_isSharedCheck_352_;
                        state = 3;
                        continue;
                    }
                }
                _ => {
                    leanh::lean_dec(v_memoizedLeft_328_);
                    leanh::lean_dec(v_val_326_);
                    leanh::lean_dec(v_left_325_);
                    v___x_353_ = leanh::lean_box(2);
                    v___x_354_ = leanh::lean_apply_2(
                        v_toPure_327_,
                        leanh::lean_box(0),
                        v___x_353_,
                    );
                    return v___x_354_;
                }
            },
            1 => {
                v___x_335_ = leanh::lean_box(0);
                v___x_336_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_336_, 0, v_left_325_);
                leanh::lean_ctor_set(v___x_336_, 1, v___x_335_);
                leanh::lean_ctor_set(v___x_336_, 2, v_it_330_);
                v___x_337_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_337_, 0, v_val_326_);
                leanh::lean_ctor_set(v___x_337_, 1, v_out_331_);
                if v_isShared_334_ == 0 {
                    leanh::lean_ctor_set(v___x_333_, 1, v___x_337_);
                    leanh::lean_ctor_set(v___x_333_, 0, v___x_336_);
                    v___x_339_ = v___x_333_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_341_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_341_, 0, v___x_336_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_341_, 1, v___x_337_);
                    v___x_339_ = v_reuseFailAlloc_341_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_340_ = leanh::lean_apply_2(
                    v_toPure_327_,
                    leanh::lean_box(0),
                    v___x_339_,
                );
                return v___x_340_;
            }
            3 => {
                v___x_347_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_347_, 0, v_left_325_);
                leanh::lean_ctor_set(v___x_347_, 1, v_memoizedLeft_328_);
                leanh::lean_ctor_set(v___x_347_, 2, v_it_343_);
                if v_isShared_346_ == 0 {
                    leanh::lean_ctor_set(v___x_345_, 0, v___x_347_);
                    v___x_349_ = v___x_345_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_351_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_351_, 0, v___x_347_);
                    v___x_349_ = v_reuseFailAlloc_351_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_350_ = leanh::lean_apply_2(
                    v_toPure_327_,
                    leanh::lean_box(0),
                    v___x_349_,
                );
                return v___x_350_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Iterators_Types_Zip_instIterator___redArg___lam__2(
    mut v_toPure_355_: *mut leanh::LeanObject,
    mut v_inst_356_: *mut leanh::LeanObject,
    mut v_toBind_357_: *mut leanh::LeanObject,
    mut v_inst_358_: *mut leanh::LeanObject,
    mut v_it_359_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_memoizedLeft_360_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_memoizedLeft_360_ = leanh::lean_ctor_get(v_it_359_, 1);
    leanh::lean_inc(v_memoizedLeft_360_);
    if leanh::lean_obj_tag(v_memoizedLeft_360_) == 0 {
        let mut v_left_361_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_right_362_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_363_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_364_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_365_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_inst_358_);
        v_left_361_ = leanh::lean_ctor_get(v_it_359_, 0);
        leanh::lean_inc(v_left_361_);
        v_right_362_ = leanh::lean_ctor_get(v_it_359_, 2);
        leanh::lean_inc(v_right_362_);
        leanh::lean_dec_ref(v_it_359_);
        v___f_363_ = leanh::lean_alloc_closure(
            l_Std_Iterators_Types_Zip_instIterator___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            3,
        );
        leanh::lean_closure_set(v___f_363_, 0, v_right_362_);
        leanh::lean_closure_set(v___f_363_, 1, v_toPure_355_);
        leanh::lean_closure_set(v___f_363_, 2, v_memoizedLeft_360_);
        v___x_364_ = leanh::lean_apply_1(v_inst_356_, v_left_361_);
        v___x_365_ = leanh::lean_apply_4(
            v_toBind_357_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_364_,
            v___f_363_,
        );
        return v___x_365_;
    } else {
        let mut v_left_366_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_right_367_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_val_368_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_369_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_370_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_371_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_inst_356_);
        v_left_366_ = leanh::lean_ctor_get(v_it_359_, 0);
        leanh::lean_inc(v_left_366_);
        v_right_367_ = leanh::lean_ctor_get(v_it_359_, 2);
        leanh::lean_inc(v_right_367_);
        leanh::lean_dec_ref(v_it_359_);
        v_val_368_ = leanh::lean_ctor_get(v_memoizedLeft_360_, 0);
        leanh::lean_inc(v_val_368_);
        v___f_369_ = leanh::lean_alloc_closure(
            l_Std_Iterators_Types_Zip_instIterator___redArg___lam__1 as *mut core::ffi::c_void,
            5,
            4,
        );
        leanh::lean_closure_set(v___f_369_, 0, v_left_366_);
        leanh::lean_closure_set(v___f_369_, 1, v_val_368_);
        leanh::lean_closure_set(v___f_369_, 2, v_toPure_355_);
        leanh::lean_closure_set(v___f_369_, 3, v_memoizedLeft_360_);
        v___x_370_ = leanh::lean_apply_1(v_inst_358_, v_right_367_);
        v___x_371_ = leanh::lean_apply_4(
            v_toBind_357_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_370_,
            v___f_369_,
        );
        return v___x_371_;
    }
}
pub unsafe fn l_Std_Iterators_Types_Zip_instIterator___redArg(
    mut v_inst_372_: *mut leanh::LeanObject,
    mut v_inst_373_: *mut leanh::LeanObject,
    mut v_inst_374_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_378_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_375_ = leanh::lean_ctor_get(v_inst_374_, 0);
    leanh::lean_inc_ref(v_toApplicative_375_);
    v_toBind_376_ = leanh::lean_ctor_get(v_inst_374_, 1);
    leanh::lean_inc(v_toBind_376_);
    leanh::lean_dec_ref(v_inst_374_);
    v_toPure_377_ = leanh::lean_ctor_get(v_toApplicative_375_, 1);
    leanh::lean_inc(v_toPure_377_);
    leanh::lean_dec_ref(v_toApplicative_375_);
    v___f_378_ = leanh::lean_alloc_closure(
        l_Std_Iterators_Types_Zip_instIterator___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        4,
    );
    leanh::lean_closure_set(v___f_378_, 0, v_toPure_377_);
    leanh::lean_closure_set(v___f_378_, 1, v_inst_372_);
    leanh::lean_closure_set(v___f_378_, 2, v_toBind_376_);
    leanh::lean_closure_set(v___f_378_, 3, v_inst_373_);
    return v___f_378_;
}
pub unsafe fn l_Std_Iterators_Types_Zip_instIterator(
    mut v_m_379_: *mut leanh::LeanObject,
    mut v_00_u03b1_u2081_380_: *mut leanh::LeanObject,
    mut v_00_u03b2_u2081_381_: *mut leanh::LeanObject,
    mut v_inst_382_: *mut leanh::LeanObject,
    mut v_00_u03b1_u2082_383_: *mut leanh::LeanObject,
    mut v_00_u03b2_u2082_384_: *mut leanh::LeanObject,
    mut v_inst_385_: *mut leanh::LeanObject,
    mut v_inst_386_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_387_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_387_ =
        l_Std_Iterators_Types_Zip_instIterator___redArg(v_inst_382_, v_inst_385_, v_inst_386_);
    return v___x_387_;
}
pub unsafe fn l_Std_Iterators_Types_Zip_instFinitenessRelation_u2081(
    mut v_m_388_: *mut leanh::LeanObject,
    mut v_00_u03b1_u2081_389_: *mut leanh::LeanObject,
    mut v_00_u03b2_u2081_390_: *mut leanh::LeanObject,
    mut v_inst_391_: *mut leanh::LeanObject,
    mut v_00_u03b1_u2082_392_: *mut leanh::LeanObject,
    mut v_00_u03b2_u2082_393_: *mut leanh::LeanObject,
    mut v_inst_394_: *mut leanh::LeanObject,
    mut v_inst_395_: *mut leanh::LeanObject,
    mut v_inst_396_: *mut leanh::LeanObject,
    mut v_inst_397_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_398_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_398_ = leanh::lean_box(0);
    return v___x_398_;
}
pub unsafe fn l_Std_Iterators_Types_Zip_instFinitenessRelation_u2081___boxed(
    mut v_m_399_: *mut leanh::LeanObject,
    mut v_00_u03b1_u2081_400_: *mut leanh::LeanObject,
    mut v_00_u03b2_u2081_401_: *mut leanh::LeanObject,
    mut v_inst_402_: *mut leanh::LeanObject,
    mut v_00_u03b1_u2082_403_: *mut leanh::LeanObject,
    mut v_00_u03b2_u2082_404_: *mut leanh::LeanObject,
    mut v_inst_405_: *mut leanh::LeanObject,
    mut v_inst_406_: *mut leanh::LeanObject,
    mut v_inst_407_: *mut leanh::LeanObject,
    mut v_inst_408_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_409_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec_ref(v_inst_406_);
    leanh::lean_dec(v_inst_405_);
    leanh::lean_dec(v_inst_402_);
    return v_res_409_;
}
pub unsafe fn l___private_Std_Data_Iterators_Combinators_Monadic_Zip_0__Option_SomeLtNone_lt_match__1_splitter___redArg(
    mut v_x_410_: *mut leanh::LeanObject,
    mut v_x_411_: *mut leanh::LeanObject,
    mut v_h__1_412_: *mut leanh::LeanObject,
    mut v_h__2_413_: *mut leanh::LeanObject,
    mut v_h__3_414_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_410_) == 0 {
        let mut v___x_415_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__3_414_);
        leanh::lean_dec(v_h__2_413_);
        v___x_415_ = leanh::lean_apply_1(v_h__1_412_, v_x_411_);
        return v___x_415_;
    } else {
        leanh::lean_dec(v_h__1_412_);
        if leanh::lean_obj_tag(v_x_411_) == 0 {
            let mut v_val_416_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_417_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_414_);
            v_val_416_ = leanh::lean_ctor_get(v_x_410_, 0);
            leanh::lean_inc(v_val_416_);
            leanh::lean_dec_ref_known(v_x_410_, 1);
            v___x_417_ = leanh::lean_apply_1(v_h__2_413_, v_val_416_);
            return v___x_417_;
        } else {
            let mut v_val_418_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_419_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_420_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_413_);
            v_val_418_ = leanh::lean_ctor_get(v_x_410_, 0);
            leanh::lean_inc(v_val_418_);
            leanh::lean_dec_ref_known(v_x_410_, 1);
            v_val_419_ = leanh::lean_ctor_get(v_x_411_, 0);
            leanh::lean_inc(v_val_419_);
            leanh::lean_dec_ref_known(v_x_411_, 1);
            v___x_420_ = leanh::lean_apply_2(v_h__3_414_, v_val_418_, v_val_419_);
            return v___x_420_;
        }
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Combinators_Monadic_Zip_0__Option_SomeLtNone_lt_match__1_splitter(
    mut v_00_u03b2_421_: *mut leanh::LeanObject,
    mut v_00_u03b1_422_: *mut leanh::LeanObject,
    mut v_motive_423_: *mut leanh::LeanObject,
    mut v_x_424_: *mut leanh::LeanObject,
    mut v_x_425_: *mut leanh::LeanObject,
    mut v_h__1_426_: *mut leanh::LeanObject,
    mut v_h__2_427_: *mut leanh::LeanObject,
    mut v_h__3_428_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_424_) == 0 {
        let mut v___x_429_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__3_428_);
        leanh::lean_dec(v_h__2_427_);
        v___x_429_ = leanh::lean_apply_1(v_h__1_426_, v_x_425_);
        return v___x_429_;
    } else {
        leanh::lean_dec(v_h__1_426_);
        if leanh::lean_obj_tag(v_x_425_) == 0 {
            let mut v_val_430_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_431_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_428_);
            v_val_430_ = leanh::lean_ctor_get(v_x_424_, 0);
            leanh::lean_inc(v_val_430_);
            leanh::lean_dec_ref_known(v_x_424_, 1);
            v___x_431_ = leanh::lean_apply_1(v_h__2_427_, v_val_430_);
            return v___x_431_;
        } else {
            let mut v_val_432_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_433_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_434_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_427_);
            v_val_432_ = leanh::lean_ctor_get(v_x_424_, 0);
            leanh::lean_inc(v_val_432_);
            leanh::lean_dec_ref_known(v_x_424_, 1);
            v_val_433_ = leanh::lean_ctor_get(v_x_425_, 0);
            leanh::lean_inc(v_val_433_);
            leanh::lean_dec_ref_known(v_x_425_, 1);
            v___x_434_ = leanh::lean_apply_2(v_h__3_428_, v_val_432_, v_val_433_);
            return v___x_434_;
        }
    }
}
pub unsafe fn l_Std_Iterators_Types_Zip_instFinitenessRelation_u2082(
    mut v_m_435_: *mut leanh::LeanObject,
    mut v_00_u03b1_u2081_436_: *mut leanh::LeanObject,
    mut v_00_u03b2_u2081_437_: *mut leanh::LeanObject,
    mut v_inst_438_: *mut leanh::LeanObject,
    mut v_00_u03b1_u2082_439_: *mut leanh::LeanObject,
    mut v_00_u03b2_u2082_440_: *mut leanh::LeanObject,
    mut v_inst_441_: *mut leanh::LeanObject,
    mut v_inst_442_: *mut leanh::LeanObject,
    mut v_inst_443_: *mut leanh::LeanObject,
    mut v_inst_444_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_445_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_445_ = leanh::lean_box(0);
    return v___x_445_;
}
pub unsafe fn l_Std_Iterators_Types_Zip_instFinitenessRelation_u2082___boxed(
    mut v_m_446_: *mut leanh::LeanObject,
    mut v_00_u03b1_u2081_447_: *mut leanh::LeanObject,
    mut v_00_u03b2_u2081_448_: *mut leanh::LeanObject,
    mut v_inst_449_: *mut leanh::LeanObject,
    mut v_00_u03b1_u2082_450_: *mut leanh::LeanObject,
    mut v_00_u03b2_u2082_451_: *mut leanh::LeanObject,
    mut v_inst_452_: *mut leanh::LeanObject,
    mut v_inst_453_: *mut leanh::LeanObject,
    mut v_inst_454_: *mut leanh::LeanObject,
    mut v_inst_455_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_456_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec_ref(v_inst_453_);
    leanh::lean_dec(v_inst_452_);
    leanh::lean_dec(v_inst_449_);
    return v_res_456_;
}
pub unsafe fn l_Std_Iterators_Types_Zip_instProductivenessRelation(
    mut v_m_457_: *mut leanh::LeanObject,
    mut v_00_u03b1_u2081_458_: *mut leanh::LeanObject,
    mut v_00_u03b2_u2081_459_: *mut leanh::LeanObject,
    mut v_inst_460_: *mut leanh::LeanObject,
    mut v_00_u03b1_u2082_461_: *mut leanh::LeanObject,
    mut v_00_u03b2_u2082_462_: *mut leanh::LeanObject,
    mut v_inst_463_: *mut leanh::LeanObject,
    mut v_inst_464_: *mut leanh::LeanObject,
    mut v_inst_465_: *mut leanh::LeanObject,
    mut v_inst_466_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_467_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_467_ = leanh::lean_box(0);
    return v___x_467_;
}
pub unsafe fn l_Std_Iterators_Types_Zip_instProductivenessRelation___boxed(
    mut v_m_468_: *mut leanh::LeanObject,
    mut v_00_u03b1_u2081_469_: *mut leanh::LeanObject,
    mut v_00_u03b2_u2081_470_: *mut leanh::LeanObject,
    mut v_inst_471_: *mut leanh::LeanObject,
    mut v_00_u03b1_u2082_472_: *mut leanh::LeanObject,
    mut v_00_u03b2_u2082_473_: *mut leanh::LeanObject,
    mut v_inst_474_: *mut leanh::LeanObject,
    mut v_inst_475_: *mut leanh::LeanObject,
    mut v_inst_476_: *mut leanh::LeanObject,
    mut v_inst_477_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_478_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec_ref(v_inst_475_);
    leanh::lean_dec(v_inst_474_);
    leanh::lean_dec(v_inst_471_);
    return v_res_478_;
}
pub unsafe fn l_Std_Iterators_Types_Zip_instIteratorLoop___redArg___lam__0(
    mut v_toPure_479_: *mut leanh::LeanObject,
    mut v_recur_480_: *mut leanh::LeanObject,
    mut v_it_481_: *mut leanh::LeanObject,
    mut v_____do__lift_482_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_482_) == 0 {
        let mut v_a_483_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_484_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_it_481_);
        leanh::lean_dec(v_recur_480_);
        v_a_483_ = leanh::lean_ctor_get(v_____do__lift_482_, 0);
        leanh::lean_inc(v_a_483_);
        leanh::lean_dec_ref_known(v_____do__lift_482_, 1);
        v___x_484_ = leanh::lean_apply_2(v_toPure_479_, leanh::lean_box(0), v_a_483_);
        return v___x_484_;
    } else {
        let mut v_a_485_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_486_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_toPure_479_);
        v_a_485_ = leanh::lean_ctor_get(v_____do__lift_482_, 0);
        leanh::lean_inc(v_a_485_);
        leanh::lean_dec_ref_known(v_____do__lift_482_, 1);
        v___x_486_ = leanh::lean_apply_4(
            v_recur_480_,
            v_it_481_,
            v_a_485_,
            leanh::lean_box(0),
            leanh::lean_box(0),
        );
        return v___x_486_;
    }
}
pub unsafe fn l_Std_Iterators_Types_Zip_instIteratorLoop___redArg___lam__1(
    mut v_toPure_487_: *mut leanh::LeanObject,
    mut v_recur_488_: *mut leanh::LeanObject,
    mut v___y_489_: *mut leanh::LeanObject,
    mut v_acc_490_: *mut leanh::LeanObject,
    mut v_toBind_491_: *mut leanh::LeanObject,
    mut v_s_492_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_s_492_) {
        0 => {
            let mut v_it_493_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_494_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_495_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_496_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_497_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_it_493_ = leanh::lean_ctor_get(v_s_492_, 0);
            leanh::lean_inc(v_it_493_);
            v_out_494_ = leanh::lean_ctor_get(v_s_492_, 1);
            leanh::lean_inc(v_out_494_);
            leanh::lean_dec_ref_known(v_s_492_, 2);
            v___f_495_ = leanh::lean_alloc_closure(
                l_Std_Iterators_Types_Zip_instIteratorLoop___redArg___lam__0
                    as *mut core::ffi::c_void,
                4,
                3,
            );
            leanh::lean_closure_set(v___f_495_, 0, v_toPure_487_);
            leanh::lean_closure_set(v___f_495_, 1, v_recur_488_);
            leanh::lean_closure_set(v___f_495_, 2, v_it_493_);
            v___x_496_ = leanh::lean_apply_3(
                v___y_489_,
                v_out_494_,
                leanh::lean_box(0),
                v_acc_490_,
            );
            v___x_497_ = leanh::lean_apply_4(
                v_toBind_491_,
                leanh::lean_box(0),
                leanh::lean_box(0),
                v___x_496_,
                v___f_495_,
            );
            return v___x_497_;
        }
        1 => {
            let mut v_it_498_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_499_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_toBind_491_);
            leanh::lean_dec(v___y_489_);
            leanh::lean_dec(v_toPure_487_);
            v_it_498_ = leanh::lean_ctor_get(v_s_492_, 0);
            leanh::lean_inc(v_it_498_);
            leanh::lean_dec_ref_known(v_s_492_, 1);
            v___x_499_ = leanh::lean_apply_4(
                v_recur_488_,
                v_it_498_,
                v_acc_490_,
                leanh::lean_box(0),
                leanh::lean_box(0),
            );
            return v___x_499_;
        }
        _ => {
            let mut v___x_500_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_toBind_491_);
            leanh::lean_dec(v___y_489_);
            leanh::lean_dec(v_recur_488_);
            v___x_500_ =
                leanh::lean_apply_2(v_toPure_487_, leanh::lean_box(0), v_acc_490_);
            return v___x_500_;
        }
    }
}
pub unsafe fn l_Std_Iterators_Types_Zip_instIteratorLoop___redArg___lam__4(
    mut v_inst_501_: *mut leanh::LeanObject,
    mut v_toPure_502_: *mut leanh::LeanObject,
    mut v___y_503_: *mut leanh::LeanObject,
    mut v_toBind_504_: *mut leanh::LeanObject,
    mut v_inst_505_: *mut leanh::LeanObject,
    mut v_lift_506_: *mut leanh::LeanObject,
    mut v_inst_507_: *mut leanh::LeanObject,
    mut v_it_508_: *mut leanh::LeanObject,
    mut v_acc_509_: *mut leanh::LeanObject,
    mut v_hP_510_: *mut leanh::LeanObject,
    mut v_recur_511_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_left_515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_memoizedLeft_516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_right_517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_518_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_512_ = leanh::lean_ctor_get(v_inst_501_, 0);
    leanh::lean_inc_ref(v_toApplicative_512_);
    v_toBind_513_ = leanh::lean_ctor_get(v_inst_501_, 1);
    leanh::lean_inc(v_toBind_513_);
    leanh::lean_dec_ref(v_inst_501_);
    v_toPure_514_ = leanh::lean_ctor_get(v_toApplicative_512_, 1);
    leanh::lean_inc(v_toPure_514_);
    leanh::lean_dec_ref(v_toApplicative_512_);
    v_left_515_ = leanh::lean_ctor_get(v_it_508_, 0);
    leanh::lean_inc(v_left_515_);
    v_memoizedLeft_516_ = leanh::lean_ctor_get(v_it_508_, 1);
    leanh::lean_inc(v_memoizedLeft_516_);
    v_right_517_ = leanh::lean_ctor_get(v_it_508_, 2);
    leanh::lean_inc(v_right_517_);
    leanh::lean_dec_ref(v_it_508_);
    v___f_518_ = leanh::lean_alloc_closure(
        l_Std_Iterators_Types_Zip_instIteratorLoop___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        5,
    );
    leanh::lean_closure_set(v___f_518_, 0, v_toPure_502_);
    leanh::lean_closure_set(v___f_518_, 1, v_recur_511_);
    leanh::lean_closure_set(v___f_518_, 2, v___y_503_);
    leanh::lean_closure_set(v___f_518_, 3, v_acc_509_);
    leanh::lean_closure_set(v___f_518_, 4, v_toBind_504_);
    if leanh::lean_obj_tag(v_memoizedLeft_516_) == 0 {
        let mut v___f_519_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_520_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_521_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_522_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_inst_507_);
        v___f_519_ = leanh::lean_alloc_closure(
            l_Std_Iterators_Types_Zip_instIterator___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            3,
        );
        leanh::lean_closure_set(v___f_519_, 0, v_right_517_);
        leanh::lean_closure_set(v___f_519_, 1, v_toPure_514_);
        leanh::lean_closure_set(v___f_519_, 2, v_memoizedLeft_516_);
        v___x_520_ = leanh::lean_apply_1(v_inst_505_, v_left_515_);
        v___x_521_ = leanh::lean_apply_4(
            v_toBind_513_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_520_,
            v___f_519_,
        );
        v___x_522_ = leanh::lean_apply_4(
            v_lift_506_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___f_518_,
            v___x_521_,
        );
        return v___x_522_;
    } else {
        let mut v_val_523_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_524_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_525_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_526_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_527_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_inst_505_);
        v_val_523_ = leanh::lean_ctor_get(v_memoizedLeft_516_, 0);
        leanh::lean_inc(v_val_523_);
        v___f_524_ = leanh::lean_alloc_closure(
            l_Std_Iterators_Types_Zip_instIterator___redArg___lam__1 as *mut core::ffi::c_void,
            5,
            4,
        );
        leanh::lean_closure_set(v___f_524_, 0, v_left_515_);
        leanh::lean_closure_set(v___f_524_, 1, v_val_523_);
        leanh::lean_closure_set(v___f_524_, 2, v_toPure_514_);
        leanh::lean_closure_set(v___f_524_, 3, v_memoizedLeft_516_);
        v___x_525_ = leanh::lean_apply_1(v_inst_507_, v_right_517_);
        v___x_526_ = leanh::lean_apply_4(
            v_toBind_513_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_525_,
            v___f_524_,
        );
        v___x_527_ = leanh::lean_apply_4(
            v_lift_506_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___f_518_,
            v___x_526_,
        );
        return v___x_527_;
    }
}
pub unsafe fn l_Std_Iterators_Types_Zip_instIteratorLoop___redArg___lam__2(
    mut v_inst_528_: *mut leanh::LeanObject,
    mut v_inst_529_: *mut leanh::LeanObject,
    mut v_inst_530_: *mut leanh::LeanObject,
    mut v_inst_531_: *mut leanh::LeanObject,
    mut v_lift_532_: *mut leanh::LeanObject,
    mut v_00_u03b3_533_: *mut leanh::LeanObject,
    mut v_Pl_534_: *mut leanh::LeanObject,
    mut v_it_535_: *mut leanh::LeanObject,
    mut v_init_536_: *mut leanh::LeanObject,
    mut v___y_537_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_542_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_538_ = leanh::lean_ctor_get(v_inst_528_, 0);
    leanh::lean_inc_ref(v_toApplicative_538_);
    v_toBind_539_ = leanh::lean_ctor_get(v_inst_528_, 1);
    leanh::lean_inc(v_toBind_539_);
    leanh::lean_dec_ref(v_inst_528_);
    v_toPure_540_ = leanh::lean_ctor_get(v_toApplicative_538_, 1);
    leanh::lean_inc(v_toPure_540_);
    leanh::lean_dec_ref(v_toApplicative_538_);
    v___f_541_ = leanh::lean_alloc_closure(
        l_Std_Iterators_Types_Zip_instIteratorLoop___redArg___lam__4 as *mut core::ffi::c_void,
        11,
        7,
    );
    leanh::lean_closure_set(v___f_541_, 0, v_inst_529_);
    leanh::lean_closure_set(v___f_541_, 1, v_toPure_540_);
    leanh::lean_closure_set(v___f_541_, 2, v___y_537_);
    leanh::lean_closure_set(v___f_541_, 3, v_toBind_539_);
    leanh::lean_closure_set(v___f_541_, 4, v_inst_530_);
    leanh::lean_closure_set(v___f_541_, 5, v_lift_532_);
    leanh::lean_closure_set(v___f_541_, 6, v_inst_531_);
    v___x_542_ = l_WellFounded_opaqueFix_u2083___redArg(
        v___f_541_,
        v_it_535_,
        v_init_536_,
        leanh::lean_box(0),
    );
    return v___x_542_;
}
pub unsafe fn l_Std_Iterators_Types_Zip_instIteratorLoop___redArg(
    mut v_inst_543_: *mut leanh::LeanObject,
    mut v_inst_544_: *mut leanh::LeanObject,
    mut v_inst_545_: *mut leanh::LeanObject,
    mut v_inst_546_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_547_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_547_ = leanh::lean_alloc_closure(
        l_Std_Iterators_Types_Zip_instIteratorLoop___redArg___lam__2 as *mut core::ffi::c_void,
        10,
        4,
    );
    leanh::lean_closure_set(v___f_547_, 0, v_inst_546_);
    leanh::lean_closure_set(v___f_547_, 1, v_inst_545_);
    leanh::lean_closure_set(v___f_547_, 2, v_inst_543_);
    leanh::lean_closure_set(v___f_547_, 3, v_inst_544_);
    return v___f_547_;
}
pub unsafe fn l_Std_Iterators_Types_Zip_instIteratorLoop(
    mut v_m_548_: *mut leanh::LeanObject,
    mut v_00_u03b1_u2081_549_: *mut leanh::LeanObject,
    mut v_00_u03b2_u2081_550_: *mut leanh::LeanObject,
    mut v_inst_551_: *mut leanh::LeanObject,
    mut v_00_u03b1_u2082_552_: *mut leanh::LeanObject,
    mut v_00_u03b2_u2082_553_: *mut leanh::LeanObject,
    mut v_inst_554_: *mut leanh::LeanObject,
    mut v_n_555_: *mut leanh::LeanObject,
    mut v_inst_556_: *mut leanh::LeanObject,
    mut v_inst_557_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_558_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_558_ = leanh::lean_alloc_closure(
        l_Std_Iterators_Types_Zip_instIteratorLoop___redArg___lam__2 as *mut core::ffi::c_void,
        10,
        4,
    );
    leanh::lean_closure_set(v___f_558_, 0, v_inst_557_);
    leanh::lean_closure_set(v___f_558_, 1, v_inst_556_);
    leanh::lean_closure_set(v___f_558_, 2, v_inst_551_);
    leanh::lean_closure_set(v___f_558_, 3, v_inst_554_);
    return v___f_558_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_Iterators_Combinators_Monadic_Zip(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Loop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_Iterators_Combinators_Monadic_Zip(
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
pub unsafe fn initialize_Std_Data_Iterators_Combinators_Monadic_Zip(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Option_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers_Loop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Combinators_Monadic_Zip(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Data_Iterators_Combinators_Monadic_Zip(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Data_Iterators_Combinators_Monadic_Zip(builtin);
}