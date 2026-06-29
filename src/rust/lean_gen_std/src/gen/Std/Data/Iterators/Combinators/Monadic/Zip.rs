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
    mut v_left_280_: *mut crate::leanh::LeanObject,
    mut v_right_281_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_282_ = crate::leanh::lean_box(0);
    v___x_283_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_283_, 0, v_left_280_);
    crate::leanh::lean_ctor_set(v___x_283_, 1, v___x_282_);
    crate::leanh::lean_ctor_set(v___x_283_, 2, v_right_281_);
    return v___x_283_;
}
pub unsafe fn l_Std_IterM_zip(
    mut v_m_284_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_u2081_285_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_u2081_286_: *mut crate::leanh::LeanObject,
    mut v_inst_287_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_u2082_288_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_u2082_289_: *mut crate::leanh::LeanObject,
    mut v_left_290_: *mut crate::leanh::LeanObject,
    mut v_right_291_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_292_ = crate::leanh::lean_box(0);
    v___x_293_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_293_, 0, v_left_290_);
    crate::leanh::lean_ctor_set(v___x_293_, 1, v___x_292_);
    crate::leanh::lean_ctor_set(v___x_293_, 2, v_right_291_);
    return v___x_293_;
}
pub unsafe fn l_Std_IterM_zip___boxed(
    mut v_m_294_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_u2081_295_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_u2081_296_: *mut crate::leanh::LeanObject,
    mut v_inst_297_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_u2082_298_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_u2082_299_: *mut crate::leanh::LeanObject,
    mut v_left_300_: *mut crate::leanh::LeanObject,
    mut v_right_301_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v_inst_297_);
    return v_res_302_;
}
pub unsafe fn l_Std_Iterators_Types_Zip_instIterator___redArg___lam__0(
    mut v_right_303_: *mut crate::leanh::LeanObject,
    mut v_toPure_304_: *mut crate::leanh::LeanObject,
    mut v_memoizedLeft_305_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_306_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_it_307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_out_308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_it_313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_316_: u8 = 0;
    let mut v___x_317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_322_: u8 = 0;
    let mut v___x_323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_____do__lift_306_) {
                0 => {
                    crate::leanh::lean_dec(v_memoizedLeft_305_);
                    v_it_307_ = crate::leanh::lean_ctor_get(v_____do__lift_306_, 0);
                    crate::leanh::lean_inc(v_it_307_);
                    v_out_308_ = crate::leanh::lean_ctor_get(v_____do__lift_306_, 1);
                    crate::leanh::lean_inc(v_out_308_);
                    crate::leanh::lean_dec_ref_known(v_____do__lift_306_, 2);
                    v___x_309_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_309_, 0, v_out_308_);
                    v___x_310_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_310_, 0, v_it_307_);
                    crate::leanh::lean_ctor_set(v___x_310_, 1, v___x_309_);
                    crate::leanh::lean_ctor_set(v___x_310_, 2, v_right_303_);
                    v___x_311_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_311_, 0, v___x_310_);
                    v___x_312_ = crate::leanh::lean_apply_2(
                        v_toPure_304_,
                        crate::leanh::lean_box(0),
                        v___x_311_,
                    );
                    return v___x_312_;
                }
                1 => {
                    v_it_313_ = crate::leanh::lean_ctor_get(v_____do__lift_306_, 0);
                    v_isSharedCheck_322_ =
                        (!crate::leanh::lean_is_exclusive(v_____do__lift_306_)) as u8;
                    if v_isSharedCheck_322_ == 0 {
                        v___x_315_ = v_____do__lift_306_;
                        v_isShared_316_ = v_isSharedCheck_322_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_it_313_);
                        crate::leanh::lean_dec(v_____do__lift_306_);
                        v___x_315_ = crate::leanh::lean_box(0);
                        v_isShared_316_ = v_isSharedCheck_322_;
                        state = 1;
                        continue;
                    }
                }
                _ => {
                    crate::leanh::lean_dec(v_memoizedLeft_305_);
                    crate::leanh::lean_dec(v_right_303_);
                    v___x_323_ = crate::leanh::lean_box(2);
                    v___x_324_ = crate::leanh::lean_apply_2(
                        v_toPure_304_,
                        crate::leanh::lean_box(0),
                        v___x_323_,
                    );
                    return v___x_324_;
                }
            },
            1 => {
                v___x_317_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_317_, 0, v_it_313_);
                crate::leanh::lean_ctor_set(v___x_317_, 1, v_memoizedLeft_305_);
                crate::leanh::lean_ctor_set(v___x_317_, 2, v_right_303_);
                if v_isShared_316_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_315_, 0, v___x_317_);
                    v___x_319_ = v___x_315_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_321_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_321_, 0, v___x_317_);
                    v___x_319_ = v_reuseFailAlloc_321_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_320_ = crate::leanh::lean_apply_2(
                    v_toPure_304_,
                    crate::leanh::lean_box(0),
                    v___x_319_,
                );
                return v___x_320_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Iterators_Types_Zip_instIterator___redArg___lam__1(
    mut v_left_325_: *mut crate::leanh::LeanObject,
    mut v_val_326_: *mut crate::leanh::LeanObject,
    mut v_toPure_327_: *mut crate::leanh::LeanObject,
    mut v_memoizedLeft_328_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_329_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_it_330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_out_331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_334_: u8 = 0;
    let mut v___x_335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_342_: u8 = 0;
    let mut v_it_343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_346_: u8 = 0;
    let mut v___x_347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_352_: u8 = 0;
    let mut v___x_353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_____do__lift_329_) {
                0 => {
                    crate::leanh::lean_dec(v_memoizedLeft_328_);
                    v_it_330_ = crate::leanh::lean_ctor_get(v_____do__lift_329_, 0);
                    v_out_331_ = crate::leanh::lean_ctor_get(v_____do__lift_329_, 1);
                    v_isSharedCheck_342_ =
                        (!crate::leanh::lean_is_exclusive(v_____do__lift_329_)) as u8;
                    if v_isSharedCheck_342_ == 0 {
                        v___x_333_ = v_____do__lift_329_;
                        v_isShared_334_ = v_isSharedCheck_342_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_out_331_);
                        crate::leanh::lean_inc(v_it_330_);
                        crate::leanh::lean_dec(v_____do__lift_329_);
                        v___x_333_ = crate::leanh::lean_box(0);
                        v_isShared_334_ = v_isSharedCheck_342_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    crate::leanh::lean_dec(v_val_326_);
                    v_it_343_ = crate::leanh::lean_ctor_get(v_____do__lift_329_, 0);
                    v_isSharedCheck_352_ =
                        (!crate::leanh::lean_is_exclusive(v_____do__lift_329_)) as u8;
                    if v_isSharedCheck_352_ == 0 {
                        v___x_345_ = v_____do__lift_329_;
                        v_isShared_346_ = v_isSharedCheck_352_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_it_343_);
                        crate::leanh::lean_dec(v_____do__lift_329_);
                        v___x_345_ = crate::leanh::lean_box(0);
                        v_isShared_346_ = v_isSharedCheck_352_;
                        state = 3;
                        continue;
                    }
                }
                _ => {
                    crate::leanh::lean_dec(v_memoizedLeft_328_);
                    crate::leanh::lean_dec(v_val_326_);
                    crate::leanh::lean_dec(v_left_325_);
                    v___x_353_ = crate::leanh::lean_box(2);
                    v___x_354_ = crate::leanh::lean_apply_2(
                        v_toPure_327_,
                        crate::leanh::lean_box(0),
                        v___x_353_,
                    );
                    return v___x_354_;
                }
            },
            1 => {
                v___x_335_ = crate::leanh::lean_box(0);
                v___x_336_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_336_, 0, v_left_325_);
                crate::leanh::lean_ctor_set(v___x_336_, 1, v___x_335_);
                crate::leanh::lean_ctor_set(v___x_336_, 2, v_it_330_);
                v___x_337_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_337_, 0, v_val_326_);
                crate::leanh::lean_ctor_set(v___x_337_, 1, v_out_331_);
                if v_isShared_334_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_333_, 1, v___x_337_);
                    crate::leanh::lean_ctor_set(v___x_333_, 0, v___x_336_);
                    v___x_339_ = v___x_333_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_341_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_341_, 0, v___x_336_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_341_, 1, v___x_337_);
                    v___x_339_ = v_reuseFailAlloc_341_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_340_ = crate::leanh::lean_apply_2(
                    v_toPure_327_,
                    crate::leanh::lean_box(0),
                    v___x_339_,
                );
                return v___x_340_;
            }
            3 => {
                v___x_347_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_347_, 0, v_left_325_);
                crate::leanh::lean_ctor_set(v___x_347_, 1, v_memoizedLeft_328_);
                crate::leanh::lean_ctor_set(v___x_347_, 2, v_it_343_);
                if v_isShared_346_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_345_, 0, v___x_347_);
                    v___x_349_ = v___x_345_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_351_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_351_, 0, v___x_347_);
                    v___x_349_ = v_reuseFailAlloc_351_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_350_ = crate::leanh::lean_apply_2(
                    v_toPure_327_,
                    crate::leanh::lean_box(0),
                    v___x_349_,
                );
                return v___x_350_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Iterators_Types_Zip_instIterator___redArg___lam__2(
    mut v_toPure_355_: *mut crate::leanh::LeanObject,
    mut v_inst_356_: *mut crate::leanh::LeanObject,
    mut v_toBind_357_: *mut crate::leanh::LeanObject,
    mut v_inst_358_: *mut crate::leanh::LeanObject,
    mut v_it_359_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_memoizedLeft_360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_memoizedLeft_360_ = crate::leanh::lean_ctor_get(v_it_359_, 1);
    crate::leanh::lean_inc(v_memoizedLeft_360_);
    if crate::leanh::lean_obj_tag(v_memoizedLeft_360_) == 0 {
        let mut v_left_361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_right_362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_inst_358_);
        v_left_361_ = crate::leanh::lean_ctor_get(v_it_359_, 0);
        crate::leanh::lean_inc(v_left_361_);
        v_right_362_ = crate::leanh::lean_ctor_get(v_it_359_, 2);
        crate::leanh::lean_inc(v_right_362_);
        crate::leanh::lean_dec_ref(v_it_359_);
        v___f_363_ = crate::leanh::lean_alloc_closure(
            l_Std_Iterators_Types_Zip_instIterator___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            3,
        );
        crate::leanh::lean_closure_set(v___f_363_, 0, v_right_362_);
        crate::leanh::lean_closure_set(v___f_363_, 1, v_toPure_355_);
        crate::leanh::lean_closure_set(v___f_363_, 2, v_memoizedLeft_360_);
        v___x_364_ = crate::leanh::lean_apply_1(v_inst_356_, v_left_361_);
        v___x_365_ = crate::leanh::lean_apply_4(
            v_toBind_357_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_364_,
            v___f_363_,
        );
        return v___x_365_;
    } else {
        let mut v_left_366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_right_367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_val_368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_inst_356_);
        v_left_366_ = crate::leanh::lean_ctor_get(v_it_359_, 0);
        crate::leanh::lean_inc(v_left_366_);
        v_right_367_ = crate::leanh::lean_ctor_get(v_it_359_, 2);
        crate::leanh::lean_inc(v_right_367_);
        crate::leanh::lean_dec_ref(v_it_359_);
        v_val_368_ = crate::leanh::lean_ctor_get(v_memoizedLeft_360_, 0);
        crate::leanh::lean_inc(v_val_368_);
        v___f_369_ = crate::leanh::lean_alloc_closure(
            l_Std_Iterators_Types_Zip_instIterator___redArg___lam__1 as *mut core::ffi::c_void,
            5,
            4,
        );
        crate::leanh::lean_closure_set(v___f_369_, 0, v_left_366_);
        crate::leanh::lean_closure_set(v___f_369_, 1, v_val_368_);
        crate::leanh::lean_closure_set(v___f_369_, 2, v_toPure_355_);
        crate::leanh::lean_closure_set(v___f_369_, 3, v_memoizedLeft_360_);
        v___x_370_ = crate::leanh::lean_apply_1(v_inst_358_, v_right_367_);
        v___x_371_ = crate::leanh::lean_apply_4(
            v_toBind_357_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_370_,
            v___f_369_,
        );
        return v___x_371_;
    }
}
pub unsafe fn l_Std_Iterators_Types_Zip_instIterator___redArg(
    mut v_inst_372_: *mut crate::leanh::LeanObject,
    mut v_inst_373_: *mut crate::leanh::LeanObject,
    mut v_inst_374_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_375_ = crate::leanh::lean_ctor_get(v_inst_374_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_375_);
    v_toBind_376_ = crate::leanh::lean_ctor_get(v_inst_374_, 1);
    crate::leanh::lean_inc(v_toBind_376_);
    crate::leanh::lean_dec_ref(v_inst_374_);
    v_toPure_377_ = crate::leanh::lean_ctor_get(v_toApplicative_375_, 1);
    crate::leanh::lean_inc(v_toPure_377_);
    crate::leanh::lean_dec_ref(v_toApplicative_375_);
    v___f_378_ = crate::leanh::lean_alloc_closure(
        l_Std_Iterators_Types_Zip_instIterator___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_378_, 0, v_toPure_377_);
    crate::leanh::lean_closure_set(v___f_378_, 1, v_inst_372_);
    crate::leanh::lean_closure_set(v___f_378_, 2, v_toBind_376_);
    crate::leanh::lean_closure_set(v___f_378_, 3, v_inst_373_);
    return v___f_378_;
}
pub unsafe fn l_Std_Iterators_Types_Zip_instIterator(
    mut v_m_379_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_u2081_380_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_u2081_381_: *mut crate::leanh::LeanObject,
    mut v_inst_382_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_u2082_383_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_u2082_384_: *mut crate::leanh::LeanObject,
    mut v_inst_385_: *mut crate::leanh::LeanObject,
    mut v_inst_386_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_387_ =
        l_Std_Iterators_Types_Zip_instIterator___redArg(v_inst_382_, v_inst_385_, v_inst_386_);
    return v___x_387_;
}
pub unsafe fn l_Std_Iterators_Types_Zip_instFinitenessRelation_u2081(
    mut v_m_388_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_u2081_389_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_u2081_390_: *mut crate::leanh::LeanObject,
    mut v_inst_391_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_u2082_392_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_u2082_393_: *mut crate::leanh::LeanObject,
    mut v_inst_394_: *mut crate::leanh::LeanObject,
    mut v_inst_395_: *mut crate::leanh::LeanObject,
    mut v_inst_396_: *mut crate::leanh::LeanObject,
    mut v_inst_397_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_398_ = crate::leanh::lean_box(0);
    return v___x_398_;
}
pub unsafe fn l_Std_Iterators_Types_Zip_instFinitenessRelation_u2081___boxed(
    mut v_m_399_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_u2081_400_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_u2081_401_: *mut crate::leanh::LeanObject,
    mut v_inst_402_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_u2082_403_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_u2082_404_: *mut crate::leanh::LeanObject,
    mut v_inst_405_: *mut crate::leanh::LeanObject,
    mut v_inst_406_: *mut crate::leanh::LeanObject,
    mut v_inst_407_: *mut crate::leanh::LeanObject,
    mut v_inst_408_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec_ref(v_inst_406_);
    crate::leanh::lean_dec(v_inst_405_);
    crate::leanh::lean_dec(v_inst_402_);
    return v_res_409_;
}
pub unsafe fn l___private_Std_Data_Iterators_Combinators_Monadic_Zip_0__Option_SomeLtNone_lt_match__1_splitter___redArg(
    mut v_x_410_: *mut crate::leanh::LeanObject,
    mut v_x_411_: *mut crate::leanh::LeanObject,
    mut v_h__1_412_: *mut crate::leanh::LeanObject,
    mut v_h__2_413_: *mut crate::leanh::LeanObject,
    mut v_h__3_414_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_410_) == 0 {
        let mut v___x_415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__3_414_);
        crate::leanh::lean_dec(v_h__2_413_);
        v___x_415_ = crate::leanh::lean_apply_1(v_h__1_412_, v_x_411_);
        return v___x_415_;
    } else {
        crate::leanh::lean_dec(v_h__1_412_);
        if crate::leanh::lean_obj_tag(v_x_411_) == 0 {
            let mut v_val_416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_414_);
            v_val_416_ = crate::leanh::lean_ctor_get(v_x_410_, 0);
            crate::leanh::lean_inc(v_val_416_);
            crate::leanh::lean_dec_ref_known(v_x_410_, 1);
            v___x_417_ = crate::leanh::lean_apply_1(v_h__2_413_, v_val_416_);
            return v___x_417_;
        } else {
            let mut v_val_418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_413_);
            v_val_418_ = crate::leanh::lean_ctor_get(v_x_410_, 0);
            crate::leanh::lean_inc(v_val_418_);
            crate::leanh::lean_dec_ref_known(v_x_410_, 1);
            v_val_419_ = crate::leanh::lean_ctor_get(v_x_411_, 0);
            crate::leanh::lean_inc(v_val_419_);
            crate::leanh::lean_dec_ref_known(v_x_411_, 1);
            v___x_420_ = crate::leanh::lean_apply_2(v_h__3_414_, v_val_418_, v_val_419_);
            return v___x_420_;
        }
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Combinators_Monadic_Zip_0__Option_SomeLtNone_lt_match__1_splitter(
    mut v_00_u03b2_421_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_422_: *mut crate::leanh::LeanObject,
    mut v_motive_423_: *mut crate::leanh::LeanObject,
    mut v_x_424_: *mut crate::leanh::LeanObject,
    mut v_x_425_: *mut crate::leanh::LeanObject,
    mut v_h__1_426_: *mut crate::leanh::LeanObject,
    mut v_h__2_427_: *mut crate::leanh::LeanObject,
    mut v_h__3_428_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_424_) == 0 {
        let mut v___x_429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__3_428_);
        crate::leanh::lean_dec(v_h__2_427_);
        v___x_429_ = crate::leanh::lean_apply_1(v_h__1_426_, v_x_425_);
        return v___x_429_;
    } else {
        crate::leanh::lean_dec(v_h__1_426_);
        if crate::leanh::lean_obj_tag(v_x_425_) == 0 {
            let mut v_val_430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_428_);
            v_val_430_ = crate::leanh::lean_ctor_get(v_x_424_, 0);
            crate::leanh::lean_inc(v_val_430_);
            crate::leanh::lean_dec_ref_known(v_x_424_, 1);
            v___x_431_ = crate::leanh::lean_apply_1(v_h__2_427_, v_val_430_);
            return v___x_431_;
        } else {
            let mut v_val_432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_427_);
            v_val_432_ = crate::leanh::lean_ctor_get(v_x_424_, 0);
            crate::leanh::lean_inc(v_val_432_);
            crate::leanh::lean_dec_ref_known(v_x_424_, 1);
            v_val_433_ = crate::leanh::lean_ctor_get(v_x_425_, 0);
            crate::leanh::lean_inc(v_val_433_);
            crate::leanh::lean_dec_ref_known(v_x_425_, 1);
            v___x_434_ = crate::leanh::lean_apply_2(v_h__3_428_, v_val_432_, v_val_433_);
            return v___x_434_;
        }
    }
}
pub unsafe fn l_Std_Iterators_Types_Zip_instFinitenessRelation_u2082(
    mut v_m_435_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_u2081_436_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_u2081_437_: *mut crate::leanh::LeanObject,
    mut v_inst_438_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_u2082_439_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_u2082_440_: *mut crate::leanh::LeanObject,
    mut v_inst_441_: *mut crate::leanh::LeanObject,
    mut v_inst_442_: *mut crate::leanh::LeanObject,
    mut v_inst_443_: *mut crate::leanh::LeanObject,
    mut v_inst_444_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_445_ = crate::leanh::lean_box(0);
    return v___x_445_;
}
pub unsafe fn l_Std_Iterators_Types_Zip_instFinitenessRelation_u2082___boxed(
    mut v_m_446_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_u2081_447_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_u2081_448_: *mut crate::leanh::LeanObject,
    mut v_inst_449_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_u2082_450_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_u2082_451_: *mut crate::leanh::LeanObject,
    mut v_inst_452_: *mut crate::leanh::LeanObject,
    mut v_inst_453_: *mut crate::leanh::LeanObject,
    mut v_inst_454_: *mut crate::leanh::LeanObject,
    mut v_inst_455_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec_ref(v_inst_453_);
    crate::leanh::lean_dec(v_inst_452_);
    crate::leanh::lean_dec(v_inst_449_);
    return v_res_456_;
}
pub unsafe fn l_Std_Iterators_Types_Zip_instProductivenessRelation(
    mut v_m_457_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_u2081_458_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_u2081_459_: *mut crate::leanh::LeanObject,
    mut v_inst_460_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_u2082_461_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_u2082_462_: *mut crate::leanh::LeanObject,
    mut v_inst_463_: *mut crate::leanh::LeanObject,
    mut v_inst_464_: *mut crate::leanh::LeanObject,
    mut v_inst_465_: *mut crate::leanh::LeanObject,
    mut v_inst_466_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_467_ = crate::leanh::lean_box(0);
    return v___x_467_;
}
pub unsafe fn l_Std_Iterators_Types_Zip_instProductivenessRelation___boxed(
    mut v_m_468_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_u2081_469_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_u2081_470_: *mut crate::leanh::LeanObject,
    mut v_inst_471_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_u2082_472_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_u2082_473_: *mut crate::leanh::LeanObject,
    mut v_inst_474_: *mut crate::leanh::LeanObject,
    mut v_inst_475_: *mut crate::leanh::LeanObject,
    mut v_inst_476_: *mut crate::leanh::LeanObject,
    mut v_inst_477_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec_ref(v_inst_475_);
    crate::leanh::lean_dec(v_inst_474_);
    crate::leanh::lean_dec(v_inst_471_);
    return v_res_478_;
}
pub unsafe fn l_Std_Iterators_Types_Zip_instIteratorLoop___redArg___lam__0(
    mut v_toPure_479_: *mut crate::leanh::LeanObject,
    mut v_recur_480_: *mut crate::leanh::LeanObject,
    mut v_it_481_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_482_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_482_) == 0 {
        let mut v_a_483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_it_481_);
        crate::leanh::lean_dec(v_recur_480_);
        v_a_483_ = crate::leanh::lean_ctor_get(v_____do__lift_482_, 0);
        crate::leanh::lean_inc(v_a_483_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_482_, 1);
        v___x_484_ = crate::leanh::lean_apply_2(v_toPure_479_, crate::leanh::lean_box(0), v_a_483_);
        return v___x_484_;
    } else {
        let mut v_a_485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toPure_479_);
        v_a_485_ = crate::leanh::lean_ctor_get(v_____do__lift_482_, 0);
        crate::leanh::lean_inc(v_a_485_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_482_, 1);
        v___x_486_ = crate::leanh::lean_apply_4(
            v_recur_480_,
            v_it_481_,
            v_a_485_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
        );
        return v___x_486_;
    }
}
pub unsafe fn l_Std_Iterators_Types_Zip_instIteratorLoop___redArg___lam__1(
    mut v_toPure_487_: *mut crate::leanh::LeanObject,
    mut v_recur_488_: *mut crate::leanh::LeanObject,
    mut v___y_489_: *mut crate::leanh::LeanObject,
    mut v_acc_490_: *mut crate::leanh::LeanObject,
    mut v_toBind_491_: *mut crate::leanh::LeanObject,
    mut v_s_492_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_s_492_) {
        0 => {
            let mut v_it_493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_it_493_ = crate::leanh::lean_ctor_get(v_s_492_, 0);
            crate::leanh::lean_inc(v_it_493_);
            v_out_494_ = crate::leanh::lean_ctor_get(v_s_492_, 1);
            crate::leanh::lean_inc(v_out_494_);
            crate::leanh::lean_dec_ref_known(v_s_492_, 2);
            v___f_495_ = crate::leanh::lean_alloc_closure(
                l_Std_Iterators_Types_Zip_instIteratorLoop___redArg___lam__0
                    as *mut core::ffi::c_void,
                4,
                3,
            );
            crate::leanh::lean_closure_set(v___f_495_, 0, v_toPure_487_);
            crate::leanh::lean_closure_set(v___f_495_, 1, v_recur_488_);
            crate::leanh::lean_closure_set(v___f_495_, 2, v_it_493_);
            v___x_496_ = crate::leanh::lean_apply_3(
                v___y_489_,
                v_out_494_,
                crate::leanh::lean_box(0),
                v_acc_490_,
            );
            v___x_497_ = crate::leanh::lean_apply_4(
                v_toBind_491_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_496_,
                v___f_495_,
            );
            return v___x_497_;
        }
        1 => {
            let mut v_it_498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_toBind_491_);
            crate::leanh::lean_dec(v___y_489_);
            crate::leanh::lean_dec(v_toPure_487_);
            v_it_498_ = crate::leanh::lean_ctor_get(v_s_492_, 0);
            crate::leanh::lean_inc(v_it_498_);
            crate::leanh::lean_dec_ref_known(v_s_492_, 1);
            v___x_499_ = crate::leanh::lean_apply_4(
                v_recur_488_,
                v_it_498_,
                v_acc_490_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
            );
            return v___x_499_;
        }
        _ => {
            let mut v___x_500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_toBind_491_);
            crate::leanh::lean_dec(v___y_489_);
            crate::leanh::lean_dec(v_recur_488_);
            v___x_500_ =
                crate::leanh::lean_apply_2(v_toPure_487_, crate::leanh::lean_box(0), v_acc_490_);
            return v___x_500_;
        }
    }
}
pub unsafe fn l_Std_Iterators_Types_Zip_instIteratorLoop___redArg___lam__4(
    mut v_inst_501_: *mut crate::leanh::LeanObject,
    mut v_toPure_502_: *mut crate::leanh::LeanObject,
    mut v___y_503_: *mut crate::leanh::LeanObject,
    mut v_toBind_504_: *mut crate::leanh::LeanObject,
    mut v_inst_505_: *mut crate::leanh::LeanObject,
    mut v_lift_506_: *mut crate::leanh::LeanObject,
    mut v_inst_507_: *mut crate::leanh::LeanObject,
    mut v_it_508_: *mut crate::leanh::LeanObject,
    mut v_acc_509_: *mut crate::leanh::LeanObject,
    mut v_hP_510_: *mut crate::leanh::LeanObject,
    mut v_recur_511_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_left_515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_memoizedLeft_516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_right_517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_512_ = crate::leanh::lean_ctor_get(v_inst_501_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_512_);
    v_toBind_513_ = crate::leanh::lean_ctor_get(v_inst_501_, 1);
    crate::leanh::lean_inc(v_toBind_513_);
    crate::leanh::lean_dec_ref(v_inst_501_);
    v_toPure_514_ = crate::leanh::lean_ctor_get(v_toApplicative_512_, 1);
    crate::leanh::lean_inc(v_toPure_514_);
    crate::leanh::lean_dec_ref(v_toApplicative_512_);
    v_left_515_ = crate::leanh::lean_ctor_get(v_it_508_, 0);
    crate::leanh::lean_inc(v_left_515_);
    v_memoizedLeft_516_ = crate::leanh::lean_ctor_get(v_it_508_, 1);
    crate::leanh::lean_inc(v_memoizedLeft_516_);
    v_right_517_ = crate::leanh::lean_ctor_get(v_it_508_, 2);
    crate::leanh::lean_inc(v_right_517_);
    crate::leanh::lean_dec_ref(v_it_508_);
    v___f_518_ = crate::leanh::lean_alloc_closure(
        l_Std_Iterators_Types_Zip_instIteratorLoop___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        5,
    );
    crate::leanh::lean_closure_set(v___f_518_, 0, v_toPure_502_);
    crate::leanh::lean_closure_set(v___f_518_, 1, v_recur_511_);
    crate::leanh::lean_closure_set(v___f_518_, 2, v___y_503_);
    crate::leanh::lean_closure_set(v___f_518_, 3, v_acc_509_);
    crate::leanh::lean_closure_set(v___f_518_, 4, v_toBind_504_);
    if crate::leanh::lean_obj_tag(v_memoizedLeft_516_) == 0 {
        let mut v___f_519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_inst_507_);
        v___f_519_ = crate::leanh::lean_alloc_closure(
            l_Std_Iterators_Types_Zip_instIterator___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            3,
        );
        crate::leanh::lean_closure_set(v___f_519_, 0, v_right_517_);
        crate::leanh::lean_closure_set(v___f_519_, 1, v_toPure_514_);
        crate::leanh::lean_closure_set(v___f_519_, 2, v_memoizedLeft_516_);
        v___x_520_ = crate::leanh::lean_apply_1(v_inst_505_, v_left_515_);
        v___x_521_ = crate::leanh::lean_apply_4(
            v_toBind_513_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_520_,
            v___f_519_,
        );
        v___x_522_ = crate::leanh::lean_apply_4(
            v_lift_506_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___f_518_,
            v___x_521_,
        );
        return v___x_522_;
    } else {
        let mut v_val_523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_inst_505_);
        v_val_523_ = crate::leanh::lean_ctor_get(v_memoizedLeft_516_, 0);
        crate::leanh::lean_inc(v_val_523_);
        v___f_524_ = crate::leanh::lean_alloc_closure(
            l_Std_Iterators_Types_Zip_instIterator___redArg___lam__1 as *mut core::ffi::c_void,
            5,
            4,
        );
        crate::leanh::lean_closure_set(v___f_524_, 0, v_left_515_);
        crate::leanh::lean_closure_set(v___f_524_, 1, v_val_523_);
        crate::leanh::lean_closure_set(v___f_524_, 2, v_toPure_514_);
        crate::leanh::lean_closure_set(v___f_524_, 3, v_memoizedLeft_516_);
        v___x_525_ = crate::leanh::lean_apply_1(v_inst_507_, v_right_517_);
        v___x_526_ = crate::leanh::lean_apply_4(
            v_toBind_513_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_525_,
            v___f_524_,
        );
        v___x_527_ = crate::leanh::lean_apply_4(
            v_lift_506_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___f_518_,
            v___x_526_,
        );
        return v___x_527_;
    }
}
pub unsafe fn l_Std_Iterators_Types_Zip_instIteratorLoop___redArg___lam__2(
    mut v_inst_528_: *mut crate::leanh::LeanObject,
    mut v_inst_529_: *mut crate::leanh::LeanObject,
    mut v_inst_530_: *mut crate::leanh::LeanObject,
    mut v_inst_531_: *mut crate::leanh::LeanObject,
    mut v_lift_532_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_533_: *mut crate::leanh::LeanObject,
    mut v_Pl_534_: *mut crate::leanh::LeanObject,
    mut v_it_535_: *mut crate::leanh::LeanObject,
    mut v_init_536_: *mut crate::leanh::LeanObject,
    mut v___y_537_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_538_ = crate::leanh::lean_ctor_get(v_inst_528_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_538_);
    v_toBind_539_ = crate::leanh::lean_ctor_get(v_inst_528_, 1);
    crate::leanh::lean_inc(v_toBind_539_);
    crate::leanh::lean_dec_ref(v_inst_528_);
    v_toPure_540_ = crate::leanh::lean_ctor_get(v_toApplicative_538_, 1);
    crate::leanh::lean_inc(v_toPure_540_);
    crate::leanh::lean_dec_ref(v_toApplicative_538_);
    v___f_541_ = crate::leanh::lean_alloc_closure(
        l_Std_Iterators_Types_Zip_instIteratorLoop___redArg___lam__4 as *mut core::ffi::c_void,
        11,
        7,
    );
    crate::leanh::lean_closure_set(v___f_541_, 0, v_inst_529_);
    crate::leanh::lean_closure_set(v___f_541_, 1, v_toPure_540_);
    crate::leanh::lean_closure_set(v___f_541_, 2, v___y_537_);
    crate::leanh::lean_closure_set(v___f_541_, 3, v_toBind_539_);
    crate::leanh::lean_closure_set(v___f_541_, 4, v_inst_530_);
    crate::leanh::lean_closure_set(v___f_541_, 5, v_lift_532_);
    crate::leanh::lean_closure_set(v___f_541_, 6, v_inst_531_);
    v___x_542_ = l_WellFounded_opaqueFix_u2083___redArg(
        v___f_541_,
        v_it_535_,
        v_init_536_,
        crate::leanh::lean_box(0),
    );
    return v___x_542_;
}
pub unsafe fn l_Std_Iterators_Types_Zip_instIteratorLoop___redArg(
    mut v_inst_543_: *mut crate::leanh::LeanObject,
    mut v_inst_544_: *mut crate::leanh::LeanObject,
    mut v_inst_545_: *mut crate::leanh::LeanObject,
    mut v_inst_546_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_547_ = crate::leanh::lean_alloc_closure(
        l_Std_Iterators_Types_Zip_instIteratorLoop___redArg___lam__2 as *mut core::ffi::c_void,
        10,
        4,
    );
    crate::leanh::lean_closure_set(v___f_547_, 0, v_inst_546_);
    crate::leanh::lean_closure_set(v___f_547_, 1, v_inst_545_);
    crate::leanh::lean_closure_set(v___f_547_, 2, v_inst_543_);
    crate::leanh::lean_closure_set(v___f_547_, 3, v_inst_544_);
    return v___f_547_;
}
pub unsafe fn l_Std_Iterators_Types_Zip_instIteratorLoop(
    mut v_m_548_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_u2081_549_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_u2081_550_: *mut crate::leanh::LeanObject,
    mut v_inst_551_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_u2082_552_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_u2082_553_: *mut crate::leanh::LeanObject,
    mut v_inst_554_: *mut crate::leanh::LeanObject,
    mut v_n_555_: *mut crate::leanh::LeanObject,
    mut v_inst_556_: *mut crate::leanh::LeanObject,
    mut v_inst_557_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_558_ = crate::leanh::lean_alloc_closure(
        l_Std_Iterators_Types_Zip_instIteratorLoop___redArg___lam__2 as *mut core::ffi::c_void,
        10,
        4,
    );
    crate::leanh::lean_closure_set(v___f_558_, 0, v_inst_557_);
    crate::leanh::lean_closure_set(v___f_558_, 1, v_inst_556_);
    crate::leanh::lean_closure_set(v___f_558_, 2, v_inst_551_);
    crate::leanh::lean_closure_set(v___f_558_, 3, v_inst_554_);
    return v___f_558_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_Iterators_Combinators_Monadic_Zip(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Loop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_Iterators_Combinators_Monadic_Zip(
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
pub unsafe fn initialize_Std_Data_Iterators_Combinators_Monadic_Zip(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Option_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers_Loop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Combinators_Monadic_Zip(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Data_Iterators_Combinators_Monadic_Zip(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Data_Iterators_Combinators_Monadic_Zip(builtin);
}
