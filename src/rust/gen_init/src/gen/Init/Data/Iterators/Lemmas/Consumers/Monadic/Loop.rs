// Lean compiler output
// Module: Init.Data.Iterators.Lemmas.Consumers.Monadic.Loop
// Imports: Init.Data.Iterators.Consumers.Monadic.Loop Init.Data.Iterators.Consumers.Monadic.Loop Init.Data.Iterators.Consumers.Monadic.Collect Init.Data.List.Control Init.Data.Array.Lemmas Init.Data.Bool Init.Data.Iterators.Lemmas.Consumers.Monadic.Collect Init.Data.Iterators.Lemmas.Monadic.Basic Init.Omega
use crate::r#gen::Init::Data::Array::Lemmas::{
    initialize_Init_Data_Array_Lemmas, runtime_initialize_Init_Data_Array_Lemmas,
};
use crate::r#gen::Init::Data::Bool::{
    initialize_Init_Data_Bool, runtime_initialize_Init_Data_Bool,
};
use crate::r#gen::Init::Data::Iterators::Consumers::Monadic::Collect::{
    initialize_Init_Data_Iterators_Consumers_Monadic_Collect,
    runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Collect,
};
use crate::r#gen::Init::Data::Iterators::Consumers::Monadic::Loop::{
    initialize_Init_Data_Iterators_Consumers_Monadic_Loop,
    runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Loop,
};
use crate::r#gen::Init::Data::Iterators::Lemmas::Consumers::Monadic::Collect::{
    initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect,
    runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect,
};
use crate::r#gen::Init::Data::Iterators::Lemmas::Monadic::Basic::{
    initialize_Init_Data_Iterators_Lemmas_Monadic_Basic,
    runtime_initialize_Init_Data_Iterators_Lemmas_Monadic_Basic,
};
use crate::r#gen::Init::Data::List::Control::{
    initialize_Init_Data_List_Control, runtime_initialize_Init_Data_List_Control,
};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop_0__Std_IterM_DefaultConsumers_forIn_x27_match__1_splitter___redArg(
    mut v_____do__lift_265_: *mut leanh::LeanObject,
    mut v_h__1_266_: *mut leanh::LeanObject,
    mut v_h__2_267_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_265_) == 0 {
        let mut v_a_268_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_269_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_266_);
        v_a_268_ = leanh::lean_ctor_get(v_____do__lift_265_, 0);
        leanh::lean_inc(v_a_268_);
        leanh::lean_dec_ref_known(v_____do__lift_265_, 1);
        v___x_269_ = leanh::lean_apply_2(v_h__2_267_, v_a_268_, leanh::lean_box(0));
        return v___x_269_;
    } else {
        let mut v_a_270_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_271_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_267_);
        v_a_270_ = leanh::lean_ctor_get(v_____do__lift_265_, 0);
        leanh::lean_inc(v_a_270_);
        leanh::lean_dec_ref_known(v_____do__lift_265_, 1);
        v___x_271_ = leanh::lean_apply_2(v_h__1_266_, v_a_270_, leanh::lean_box(0));
        return v___x_271_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop_0__Std_IterM_DefaultConsumers_forIn_x27_match__1_splitter(
    mut v_00_u03b2_272_: *mut leanh::LeanObject,
    mut v_00_u03b3_273_: *mut leanh::LeanObject,
    mut v_PlausibleForInStep_274_: *mut leanh::LeanObject,
    mut v_acc_275_: *mut leanh::LeanObject,
    mut v_out_276_: *mut leanh::LeanObject,
    mut v_motive_277_: *mut leanh::LeanObject,
    mut v_____do__lift_278_: *mut leanh::LeanObject,
    mut v_h__1_279_: *mut leanh::LeanObject,
    mut v_h__2_280_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_278_) == 0 {
        let mut v_a_281_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_282_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_279_);
        v_a_281_ = leanh::lean_ctor_get(v_____do__lift_278_, 0);
        leanh::lean_inc(v_a_281_);
        leanh::lean_dec_ref_known(v_____do__lift_278_, 1);
        v___x_282_ = leanh::lean_apply_2(v_h__2_280_, v_a_281_, leanh::lean_box(0));
        return v___x_282_;
    } else {
        let mut v_a_283_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_284_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_280_);
        v_a_283_ = leanh::lean_ctor_get(v_____do__lift_278_, 0);
        leanh::lean_inc(v_a_283_);
        leanh::lean_dec_ref_known(v_____do__lift_278_, 1);
        v___x_284_ = leanh::lean_apply_2(v_h__1_279_, v_a_283_, leanh::lean_box(0));
        return v___x_284_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop_0__Std_IterM_DefaultConsumers_forIn_x27_match__1_splitter___boxed(
    mut v_00_u03b2_285_: *mut leanh::LeanObject,
    mut v_00_u03b3_286_: *mut leanh::LeanObject,
    mut v_PlausibleForInStep_287_: *mut leanh::LeanObject,
    mut v_acc_288_: *mut leanh::LeanObject,
    mut v_out_289_: *mut leanh::LeanObject,
    mut v_motive_290_: *mut leanh::LeanObject,
    mut v_____do__lift_291_: *mut leanh::LeanObject,
    mut v_h__1_292_: *mut leanh::LeanObject,
    mut v_h__2_293_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_294_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_294_ = l___private_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop_0__Std_IterM_DefaultConsumers_forIn_x27_match__1_splitter(v_00_u03b2_285_, v_00_u03b3_286_, v_PlausibleForInStep_287_, v_acc_288_, v_out_289_, v_motive_290_, v_____do__lift_291_, v_h__1_292_, v_h__2_293_);
    leanh::lean_dec(v_out_289_);
    leanh::lean_dec(v_acc_288_);
    return v_res_294_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop_0__Std_IterM_DefaultConsumers_forIn_x27_match__3_splitter___redArg(
    mut v_x_295_: *mut leanh::LeanObject,
    mut v_h__1_296_: *mut leanh::LeanObject,
    mut v_h__2_297_: *mut leanh::LeanObject,
    mut v_h__3_298_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_295_) {
        0 => {
            let mut v_it_299_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_300_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_301_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_298_);
            leanh::lean_dec(v_h__2_297_);
            v_it_299_ = leanh::lean_ctor_get(v_x_295_, 0);
            leanh::lean_inc(v_it_299_);
            v_out_300_ = leanh::lean_ctor_get(v_x_295_, 1);
            leanh::lean_inc(v_out_300_);
            leanh::lean_dec_ref_known(v_x_295_, 2);
            v___x_301_ = leanh::lean_apply_3(
                v_h__1_296_,
                v_it_299_,
                v_out_300_,
                leanh::lean_box(0),
            );
            return v___x_301_;
        }
        1 => {
            let mut v_it_302_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_303_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_298_);
            leanh::lean_dec(v_h__1_296_);
            v_it_302_ = leanh::lean_ctor_get(v_x_295_, 0);
            leanh::lean_inc(v_it_302_);
            leanh::lean_dec_ref_known(v_x_295_, 1);
            v___x_303_ =
                leanh::lean_apply_2(v_h__2_297_, v_it_302_, leanh::lean_box(0));
            return v___x_303_;
        }
        _ => {
            let mut v___x_304_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_297_);
            leanh::lean_dec(v_h__1_296_);
            v___x_304_ = leanh::lean_apply_1(v_h__3_298_, leanh::lean_box(0));
            return v___x_304_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop_0__Std_IterM_DefaultConsumers_forIn_x27_match__3_splitter(
    mut v_m_305_: *mut leanh::LeanObject,
    mut v_00_u03b1_306_: *mut leanh::LeanObject,
    mut v_00_u03b2_307_: *mut leanh::LeanObject,
    mut v_inst_308_: *mut leanh::LeanObject,
    mut v_it_309_: *mut leanh::LeanObject,
    mut v_motive_310_: *mut leanh::LeanObject,
    mut v_x_311_: *mut leanh::LeanObject,
    mut v_h__1_312_: *mut leanh::LeanObject,
    mut v_h__2_313_: *mut leanh::LeanObject,
    mut v_h__3_314_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_311_) {
        0 => {
            let mut v_it_315_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_316_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_317_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_314_);
            leanh::lean_dec(v_h__2_313_);
            v_it_315_ = leanh::lean_ctor_get(v_x_311_, 0);
            leanh::lean_inc(v_it_315_);
            v_out_316_ = leanh::lean_ctor_get(v_x_311_, 1);
            leanh::lean_inc(v_out_316_);
            leanh::lean_dec_ref_known(v_x_311_, 2);
            v___x_317_ = leanh::lean_apply_3(
                v_h__1_312_,
                v_it_315_,
                v_out_316_,
                leanh::lean_box(0),
            );
            return v___x_317_;
        }
        1 => {
            let mut v_it_318_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_319_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_314_);
            leanh::lean_dec(v_h__1_312_);
            v_it_318_ = leanh::lean_ctor_get(v_x_311_, 0);
            leanh::lean_inc(v_it_318_);
            leanh::lean_dec_ref_known(v_x_311_, 1);
            v___x_319_ =
                leanh::lean_apply_2(v_h__2_313_, v_it_318_, leanh::lean_box(0));
            return v___x_319_;
        }
        _ => {
            let mut v___x_320_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_313_);
            leanh::lean_dec(v_h__1_312_);
            v___x_320_ = leanh::lean_apply_1(v_h__3_314_, leanh::lean_box(0));
            return v___x_320_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop_0__Std_IterM_DefaultConsumers_forIn_x27_match__3_splitter___boxed(
    mut v_m_321_: *mut leanh::LeanObject,
    mut v_00_u03b1_322_: *mut leanh::LeanObject,
    mut v_00_u03b2_323_: *mut leanh::LeanObject,
    mut v_inst_324_: *mut leanh::LeanObject,
    mut v_it_325_: *mut leanh::LeanObject,
    mut v_motive_326_: *mut leanh::LeanObject,
    mut v_x_327_: *mut leanh::LeanObject,
    mut v_h__1_328_: *mut leanh::LeanObject,
    mut v_h__2_329_: *mut leanh::LeanObject,
    mut v_h__3_330_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_331_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_331_ = l___private_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop_0__Std_IterM_DefaultConsumers_forIn_x27_match__3_splitter(v_m_321_, v_00_u03b1_322_, v_00_u03b2_323_, v_inst_324_, v_it_325_, v_motive_326_, v_x_327_, v_h__1_328_, v_h__2_329_, v_h__3_330_);
    leanh::lean_dec(v_it_325_);
    leanh::lean_dec(v_inst_324_);
    return v_res_331_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__1_splitter___redArg(
    mut v_____do__lift_332_: *mut leanh::LeanObject,
    mut v_h__1_333_: *mut leanh::LeanObject,
    mut v_h__2_334_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_332_) == 0 {
        let mut v_a_335_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_336_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_333_);
        v_a_335_ = leanh::lean_ctor_get(v_____do__lift_332_, 0);
        leanh::lean_inc(v_a_335_);
        leanh::lean_dec_ref_known(v_____do__lift_332_, 1);
        v___x_336_ = leanh::lean_apply_2(v_h__2_334_, v_a_335_, leanh::lean_box(0));
        return v___x_336_;
    } else {
        let mut v_a_337_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_338_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_334_);
        v_a_337_ = leanh::lean_ctor_get(v_____do__lift_332_, 0);
        leanh::lean_inc(v_a_337_);
        leanh::lean_dec_ref_known(v_____do__lift_332_, 1);
        v___x_338_ = leanh::lean_apply_2(v_h__1_333_, v_a_337_, leanh::lean_box(0));
        return v___x_338_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__1_splitter(
    mut v_00_u03b2_339_: *mut leanh::LeanObject,
    mut v_00_u03b3_340_: *mut leanh::LeanObject,
    mut v_init_341_: *mut leanh::LeanObject,
    mut v_PlausibleForInStep_342_: *mut leanh::LeanObject,
    mut v_out_343_: *mut leanh::LeanObject,
    mut v_motive_344_: *mut leanh::LeanObject,
    mut v_____do__lift_345_: *mut leanh::LeanObject,
    mut v_h__1_346_: *mut leanh::LeanObject,
    mut v_h__2_347_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_345_) == 0 {
        let mut v_a_348_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_349_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_346_);
        v_a_348_ = leanh::lean_ctor_get(v_____do__lift_345_, 0);
        leanh::lean_inc(v_a_348_);
        leanh::lean_dec_ref_known(v_____do__lift_345_, 1);
        v___x_349_ = leanh::lean_apply_2(v_h__2_347_, v_a_348_, leanh::lean_box(0));
        return v___x_349_;
    } else {
        let mut v_a_350_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_351_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_347_);
        v_a_350_ = leanh::lean_ctor_get(v_____do__lift_345_, 0);
        leanh::lean_inc(v_a_350_);
        leanh::lean_dec_ref_known(v_____do__lift_345_, 1);
        v___x_351_ = leanh::lean_apply_2(v_h__1_346_, v_a_350_, leanh::lean_box(0));
        return v___x_351_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__1_splitter___boxed(
    mut v_00_u03b2_352_: *mut leanh::LeanObject,
    mut v_00_u03b3_353_: *mut leanh::LeanObject,
    mut v_init_354_: *mut leanh::LeanObject,
    mut v_PlausibleForInStep_355_: *mut leanh::LeanObject,
    mut v_out_356_: *mut leanh::LeanObject,
    mut v_motive_357_: *mut leanh::LeanObject,
    mut v_____do__lift_358_: *mut leanh::LeanObject,
    mut v_h__1_359_: *mut leanh::LeanObject,
    mut v_h__2_360_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_361_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_361_ = l___private_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__1_splitter(v_00_u03b2_352_, v_00_u03b3_353_, v_init_354_, v_PlausibleForInStep_355_, v_out_356_, v_motive_357_, v_____do__lift_358_, v_h__1_359_, v_h__2_360_);
    leanh::lean_dec(v_out_356_);
    leanh::lean_dec(v_init_354_);
    return v_res_361_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter___redArg(
    mut v_x_362_: *mut leanh::LeanObject,
    mut v_h__1_363_: *mut leanh::LeanObject,
    mut v_h__2_364_: *mut leanh::LeanObject,
    mut v_h__3_365_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_362_) {
        0 => {
            let mut v_it_366_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_367_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_368_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_365_);
            leanh::lean_dec(v_h__2_364_);
            v_it_366_ = leanh::lean_ctor_get(v_x_362_, 0);
            leanh::lean_inc(v_it_366_);
            v_out_367_ = leanh::lean_ctor_get(v_x_362_, 1);
            leanh::lean_inc(v_out_367_);
            leanh::lean_dec_ref_known(v_x_362_, 2);
            v___x_368_ = leanh::lean_apply_3(
                v_h__1_363_,
                v_it_366_,
                v_out_367_,
                leanh::lean_box(0),
            );
            return v___x_368_;
        }
        1 => {
            let mut v_it_369_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_370_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_365_);
            leanh::lean_dec(v_h__1_363_);
            v_it_369_ = leanh::lean_ctor_get(v_x_362_, 0);
            leanh::lean_inc(v_it_369_);
            leanh::lean_dec_ref_known(v_x_362_, 1);
            v___x_370_ =
                leanh::lean_apply_2(v_h__2_364_, v_it_369_, leanh::lean_box(0));
            return v___x_370_;
        }
        _ => {
            let mut v___x_371_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_364_);
            leanh::lean_dec(v_h__1_363_);
            v___x_371_ = leanh::lean_apply_1(v_h__3_365_, leanh::lean_box(0));
            return v___x_371_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter(
    mut v_00_u03b1_372_: *mut leanh::LeanObject,
    mut v_00_u03b2_373_: *mut leanh::LeanObject,
    mut v_m_374_: *mut leanh::LeanObject,
    mut v_inst_375_: *mut leanh::LeanObject,
    mut v_it_376_: *mut leanh::LeanObject,
    mut v_motive_377_: *mut leanh::LeanObject,
    mut v_x_378_: *mut leanh::LeanObject,
    mut v_h__1_379_: *mut leanh::LeanObject,
    mut v_h__2_380_: *mut leanh::LeanObject,
    mut v_h__3_381_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_378_) {
        0 => {
            let mut v_it_382_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_383_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_384_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_381_);
            leanh::lean_dec(v_h__2_380_);
            v_it_382_ = leanh::lean_ctor_get(v_x_378_, 0);
            leanh::lean_inc(v_it_382_);
            v_out_383_ = leanh::lean_ctor_get(v_x_378_, 1);
            leanh::lean_inc(v_out_383_);
            leanh::lean_dec_ref_known(v_x_378_, 2);
            v___x_384_ = leanh::lean_apply_3(
                v_h__1_379_,
                v_it_382_,
                v_out_383_,
                leanh::lean_box(0),
            );
            return v___x_384_;
        }
        1 => {
            let mut v_it_385_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_386_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_381_);
            leanh::lean_dec(v_h__1_379_);
            v_it_385_ = leanh::lean_ctor_get(v_x_378_, 0);
            leanh::lean_inc(v_it_385_);
            leanh::lean_dec_ref_known(v_x_378_, 1);
            v___x_386_ =
                leanh::lean_apply_2(v_h__2_380_, v_it_385_, leanh::lean_box(0));
            return v___x_386_;
        }
        _ => {
            let mut v___x_387_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_380_);
            leanh::lean_dec(v_h__1_379_);
            v___x_387_ = leanh::lean_apply_1(v_h__3_381_, leanh::lean_box(0));
            return v___x_387_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter___boxed(
    mut v_00_u03b1_388_: *mut leanh::LeanObject,
    mut v_00_u03b2_389_: *mut leanh::LeanObject,
    mut v_m_390_: *mut leanh::LeanObject,
    mut v_inst_391_: *mut leanh::LeanObject,
    mut v_it_392_: *mut leanh::LeanObject,
    mut v_motive_393_: *mut leanh::LeanObject,
    mut v_x_394_: *mut leanh::LeanObject,
    mut v_h__1_395_: *mut leanh::LeanObject,
    mut v_h__2_396_: *mut leanh::LeanObject,
    mut v_h__3_397_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_398_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_398_ = l___private_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter(v_00_u03b1_388_, v_00_u03b2_389_, v_m_390_, v_inst_391_, v_it_392_, v_motive_393_, v_x_394_, v_h__1_395_, v_h__2_396_, v_h__3_397_);
    leanh::lean_dec(v_it_392_);
    leanh::lean_dec(v_inst_391_);
    return v_res_398_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop_0__Std_IterM_forIn_x27__eq__match__step_match__1_splitter___redArg(
    mut v_____do__lift_399_: *mut leanh::LeanObject,
    mut v_h__1_400_: *mut leanh::LeanObject,
    mut v_h__2_401_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_399_) == 0 {
        let mut v_a_402_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_403_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_400_);
        v_a_402_ = leanh::lean_ctor_get(v_____do__lift_399_, 0);
        leanh::lean_inc(v_a_402_);
        leanh::lean_dec_ref_known(v_____do__lift_399_, 1);
        v___x_403_ = leanh::lean_apply_1(v_h__2_401_, v_a_402_);
        return v___x_403_;
    } else {
        let mut v_a_404_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_405_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_401_);
        v_a_404_ = leanh::lean_ctor_get(v_____do__lift_399_, 0);
        leanh::lean_inc(v_a_404_);
        leanh::lean_dec_ref_known(v_____do__lift_399_, 1);
        v___x_405_ = leanh::lean_apply_1(v_h__1_400_, v_a_404_);
        return v___x_405_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop_0__Std_IterM_forIn_x27__eq__match__step_match__1_splitter(
    mut v_00_u03b3_406_: *mut leanh::LeanObject,
    mut v_motive_407_: *mut leanh::LeanObject,
    mut v_____do__lift_408_: *mut leanh::LeanObject,
    mut v_h__1_409_: *mut leanh::LeanObject,
    mut v_h__2_410_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_408_) == 0 {
        let mut v_a_411_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_412_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_409_);
        v_a_411_ = leanh::lean_ctor_get(v_____do__lift_408_, 0);
        leanh::lean_inc(v_a_411_);
        leanh::lean_dec_ref_known(v_____do__lift_408_, 1);
        v___x_412_ = leanh::lean_apply_1(v_h__2_410_, v_a_411_);
        return v___x_412_;
    } else {
        let mut v_a_413_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_414_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_410_);
        v_a_413_ = leanh::lean_ctor_get(v_____do__lift_408_, 0);
        leanh::lean_inc(v_a_413_);
        leanh::lean_dec_ref_known(v_____do__lift_408_, 1);
        v___x_414_ = leanh::lean_apply_1(v_h__1_409_, v_a_413_);
        return v___x_414_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop_0__List_forIn_x27__eq__foldlM_match__1_splitter___redArg(
    mut v_b_415_: *mut leanh::LeanObject,
    mut v_h__1_416_: *mut leanh::LeanObject,
    mut v_h__2_417_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_b_415_) == 0 {
        let mut v_a_418_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_419_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_416_);
        v_a_418_ = leanh::lean_ctor_get(v_b_415_, 0);
        leanh::lean_inc(v_a_418_);
        leanh::lean_dec_ref_known(v_b_415_, 1);
        v___x_419_ = leanh::lean_apply_1(v_h__2_417_, v_a_418_);
        return v___x_419_;
    } else {
        let mut v_a_420_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_421_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_417_);
        v_a_420_ = leanh::lean_ctor_get(v_b_415_, 0);
        leanh::lean_inc(v_a_420_);
        leanh::lean_dec_ref_known(v_b_415_, 1);
        v___x_421_ = leanh::lean_apply_1(v_h__1_416_, v_a_420_);
        return v___x_421_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop_0__List_forIn_x27__eq__foldlM_match__1_splitter(
    mut v_00_u03b2_422_: *mut leanh::LeanObject,
    mut v_motive_423_: *mut leanh::LeanObject,
    mut v_b_424_: *mut leanh::LeanObject,
    mut v_h__1_425_: *mut leanh::LeanObject,
    mut v_h__2_426_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_b_424_) == 0 {
        let mut v_a_427_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_428_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_425_);
        v_a_427_ = leanh::lean_ctor_get(v_b_424_, 0);
        leanh::lean_inc(v_a_427_);
        leanh::lean_dec_ref_known(v_b_424_, 1);
        v___x_428_ = leanh::lean_apply_1(v_h__2_426_, v_a_427_);
        return v___x_428_;
    } else {
        let mut v_a_429_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_430_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_426_);
        v_a_429_ = leanh::lean_ctor_get(v_b_424_, 0);
        leanh::lean_inc(v_a_429_);
        leanh::lean_dec_ref_known(v_b_424_, 1);
        v___x_430_ = leanh::lean_apply_1(v_h__1_425_, v_a_429_);
        return v___x_430_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop_0__Std_IterM_toArray__eq__match__step_match__1_splitter___redArg(
    mut v_x_431_: *mut leanh::LeanObject,
    mut v_h__1_432_: *mut leanh::LeanObject,
    mut v_h__2_433_: *mut leanh::LeanObject,
    mut v_h__3_434_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_431_) {
        0 => {
            let mut v_it_435_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_436_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_437_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_434_);
            leanh::lean_dec(v_h__2_433_);
            v_it_435_ = leanh::lean_ctor_get(v_x_431_, 0);
            leanh::lean_inc(v_it_435_);
            v_out_436_ = leanh::lean_ctor_get(v_x_431_, 1);
            leanh::lean_inc(v_out_436_);
            leanh::lean_dec_ref_known(v_x_431_, 2);
            v___x_437_ = leanh::lean_apply_2(v_h__1_432_, v_it_435_, v_out_436_);
            return v___x_437_;
        }
        1 => {
            let mut v_it_438_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_439_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_434_);
            leanh::lean_dec(v_h__1_432_);
            v_it_438_ = leanh::lean_ctor_get(v_x_431_, 0);
            leanh::lean_inc(v_it_438_);
            leanh::lean_dec_ref_known(v_x_431_, 1);
            v___x_439_ = leanh::lean_apply_1(v_h__2_433_, v_it_438_);
            return v___x_439_;
        }
        _ => {
            let mut v___x_440_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_441_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_433_);
            leanh::lean_dec(v_h__1_432_);
            v___x_440_ = leanh::lean_box(0);
            v___x_441_ = leanh::lean_apply_1(v_h__3_434_, v___x_440_);
            return v___x_441_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop_0__Std_IterM_toArray__eq__match__step_match__1_splitter(
    mut v_00_u03b1_442_: *mut leanh::LeanObject,
    mut v_00_u03b2_443_: *mut leanh::LeanObject,
    mut v_m_444_: *mut leanh::LeanObject,
    mut v_motive_445_: *mut leanh::LeanObject,
    mut v_x_446_: *mut leanh::LeanObject,
    mut v_h__1_447_: *mut leanh::LeanObject,
    mut v_h__2_448_: *mut leanh::LeanObject,
    mut v_h__3_449_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_446_) {
        0 => {
            let mut v_it_450_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_451_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_452_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_449_);
            leanh::lean_dec(v_h__2_448_);
            v_it_450_ = leanh::lean_ctor_get(v_x_446_, 0);
            leanh::lean_inc(v_it_450_);
            v_out_451_ = leanh::lean_ctor_get(v_x_446_, 1);
            leanh::lean_inc(v_out_451_);
            leanh::lean_dec_ref_known(v_x_446_, 2);
            v___x_452_ = leanh::lean_apply_2(v_h__1_447_, v_it_450_, v_out_451_);
            return v___x_452_;
        }
        1 => {
            let mut v_it_453_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_454_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_449_);
            leanh::lean_dec(v_h__1_447_);
            v_it_453_ = leanh::lean_ctor_get(v_x_446_, 0);
            leanh::lean_inc(v_it_453_);
            leanh::lean_dec_ref_known(v_x_446_, 1);
            v___x_454_ = leanh::lean_apply_1(v_h__2_448_, v_it_453_);
            return v___x_454_;
        }
        _ => {
            let mut v___x_455_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_456_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_448_);
            leanh::lean_dec(v_h__1_447_);
            v___x_455_ = leanh::lean_box(0);
            v___x_456_ = leanh::lean_apply_1(v_h__3_449_, v___x_455_);
            return v___x_456_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop_0__Std_IterM_length__eq__match__step_match__1_splitter___redArg(
    mut v_x_457_: *mut leanh::LeanObject,
    mut v_h__1_458_: *mut leanh::LeanObject,
    mut v_h__2_459_: *mut leanh::LeanObject,
    mut v_h__3_460_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_457_) {
        0 => {
            let mut v_it_461_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_462_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_463_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_460_);
            leanh::lean_dec(v_h__2_459_);
            v_it_461_ = leanh::lean_ctor_get(v_x_457_, 0);
            leanh::lean_inc(v_it_461_);
            v_out_462_ = leanh::lean_ctor_get(v_x_457_, 1);
            leanh::lean_inc(v_out_462_);
            leanh::lean_dec_ref_known(v_x_457_, 2);
            v___x_463_ = leanh::lean_apply_2(v_h__1_458_, v_it_461_, v_out_462_);
            return v___x_463_;
        }
        1 => {
            let mut v_it_464_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_465_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_460_);
            leanh::lean_dec(v_h__1_458_);
            v_it_464_ = leanh::lean_ctor_get(v_x_457_, 0);
            leanh::lean_inc(v_it_464_);
            leanh::lean_dec_ref_known(v_x_457_, 1);
            v___x_465_ = leanh::lean_apply_1(v_h__2_459_, v_it_464_);
            return v___x_465_;
        }
        _ => {
            let mut v___x_466_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_467_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_459_);
            leanh::lean_dec(v_h__1_458_);
            v___x_466_ = leanh::lean_box(0);
            v___x_467_ = leanh::lean_apply_1(v_h__3_460_, v___x_466_);
            return v___x_467_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop_0__Std_IterM_length__eq__match__step_match__1_splitter(
    mut v_00_u03b1_468_: *mut leanh::LeanObject,
    mut v_00_u03b2_469_: *mut leanh::LeanObject,
    mut v_m_470_: *mut leanh::LeanObject,
    mut v_motive_471_: *mut leanh::LeanObject,
    mut v_x_472_: *mut leanh::LeanObject,
    mut v_h__1_473_: *mut leanh::LeanObject,
    mut v_h__2_474_: *mut leanh::LeanObject,
    mut v_h__3_475_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_472_) {
        0 => {
            let mut v_it_476_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_477_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_478_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_475_);
            leanh::lean_dec(v_h__2_474_);
            v_it_476_ = leanh::lean_ctor_get(v_x_472_, 0);
            leanh::lean_inc(v_it_476_);
            v_out_477_ = leanh::lean_ctor_get(v_x_472_, 1);
            leanh::lean_inc(v_out_477_);
            leanh::lean_dec_ref_known(v_x_472_, 2);
            v___x_478_ = leanh::lean_apply_2(v_h__1_473_, v_it_476_, v_out_477_);
            return v___x_478_;
        }
        1 => {
            let mut v_it_479_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_480_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_475_);
            leanh::lean_dec(v_h__1_473_);
            v_it_479_ = leanh::lean_ctor_get(v_x_472_, 0);
            leanh::lean_inc(v_it_479_);
            leanh::lean_dec_ref_known(v_x_472_, 1);
            v___x_480_ = leanh::lean_apply_1(v_h__2_474_, v_it_479_);
            return v___x_480_;
        }
        _ => {
            let mut v___x_481_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_482_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_474_);
            leanh::lean_dec(v_h__1_473_);
            v___x_481_ = leanh::lean_box(0);
            v___x_482_ = leanh::lean_apply_1(v_h__3_475_, v___x_481_);
            return v___x_482_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop_0__Std_IterM_findSomeM_x3f_match__1_splitter___redArg(
    mut v_____do__lift_483_: *mut leanh::LeanObject,
    mut v_h__1_484_: *mut leanh::LeanObject,
    mut v_h__2_485_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_483_) == 0 {
        let mut v___x_486_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_487_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_485_);
        v___x_486_ = leanh::lean_box(0);
        v___x_487_ = leanh::lean_apply_1(v_h__1_484_, v___x_486_);
        return v___x_487_;
    } else {
        let mut v_val_488_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_489_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_484_);
        v_val_488_ = leanh::lean_ctor_get(v_____do__lift_483_, 0);
        leanh::lean_inc(v_val_488_);
        leanh::lean_dec_ref_known(v_____do__lift_483_, 1);
        v___x_489_ = leanh::lean_apply_1(v_h__2_485_, v_val_488_);
        return v___x_489_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop_0__Std_IterM_findSomeM_x3f_match__1_splitter(
    mut v_00_u03b3_490_: *mut leanh::LeanObject,
    mut v_motive_491_: *mut leanh::LeanObject,
    mut v_____do__lift_492_: *mut leanh::LeanObject,
    mut v_h__1_493_: *mut leanh::LeanObject,
    mut v_h__2_494_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_492_) == 0 {
        let mut v___x_495_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_496_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_494_);
        v___x_495_ = leanh::lean_box(0);
        v___x_496_ = leanh::lean_apply_1(v_h__1_493_, v___x_495_);
        return v___x_496_;
    } else {
        let mut v_val_497_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_498_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_493_);
        v_val_497_ = leanh::lean_ctor_get(v_____do__lift_492_, 0);
        leanh::lean_inc(v_val_497_);
        leanh::lean_dec_ref_known(v_____do__lift_492_, 1);
        v___x_498_ = leanh::lean_apply_1(v_h__2_494_, v_val_497_);
        return v___x_498_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop_0__Std_IterM_findSomeM_x3f__eq__match__step_match__1_splitter___redArg(
    mut v_____do__lift_499_: *mut leanh::LeanObject,
    mut v_h__1_500_: *mut leanh::LeanObject,
    mut v_h__2_501_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_499_) == 0 {
        let mut v___x_502_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_503_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_501_);
        v___x_502_ = leanh::lean_box(0);
        v___x_503_ = leanh::lean_apply_1(v_h__1_500_, v___x_502_);
        return v___x_503_;
    } else {
        let mut v_val_504_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_505_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_500_);
        v_val_504_ = leanh::lean_ctor_get(v_____do__lift_499_, 0);
        leanh::lean_inc(v_val_504_);
        leanh::lean_dec_ref_known(v_____do__lift_499_, 1);
        v___x_505_ = leanh::lean_apply_1(v_h__2_501_, v_val_504_);
        return v___x_505_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop_0__Std_IterM_findSomeM_x3f__eq__match__step_match__1_splitter(
    mut v_00_u03b3_506_: *mut leanh::LeanObject,
    mut v_motive_507_: *mut leanh::LeanObject,
    mut v_____do__lift_508_: *mut leanh::LeanObject,
    mut v_h__1_509_: *mut leanh::LeanObject,
    mut v_h__2_510_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_508_) == 0 {
        let mut v___x_511_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_512_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_510_);
        v___x_511_ = leanh::lean_box(0);
        v___x_512_ = leanh::lean_apply_1(v_h__1_509_, v___x_511_);
        return v___x_512_;
    } else {
        let mut v_val_513_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_514_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_509_);
        v_val_513_ = leanh::lean_ctor_get(v_____do__lift_508_, 0);
        leanh::lean_inc(v_val_513_);
        leanh::lean_dec_ref_known(v_____do__lift_508_, 1);
        v___x_514_ = leanh::lean_apply_1(v_h__2_510_, v_val_513_);
        return v___x_514_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop_0__Std_IteratorLoop_wellFounded__of__productive_match__1_splitter___redArg(
    mut v_s_515_: *mut leanh::LeanObject,
    mut v_h__1_516_: *mut leanh::LeanObject,
    mut v_h__2_517_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_s_515_) == 0 {
        let mut v_a_518_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_519_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_517_);
        v_a_518_ = leanh::lean_ctor_get(v_s_515_, 0);
        leanh::lean_inc(v_a_518_);
        leanh::lean_dec_ref_known(v_s_515_, 1);
        v___x_519_ = leanh::lean_apply_1(v_h__1_516_, v_a_518_);
        return v___x_519_;
    } else {
        let mut v___x_520_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_516_);
        v___x_520_ = leanh::lean_apply_2(v_h__2_517_, v_s_515_, leanh::lean_box(0));
        return v___x_520_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop_0__Std_IteratorLoop_wellFounded__of__productive_match__1_splitter(
    mut v_00_u03b3_521_: *mut leanh::LeanObject,
    mut v_motive_522_: *mut leanh::LeanObject,
    mut v_s_523_: *mut leanh::LeanObject,
    mut v_h__1_524_: *mut leanh::LeanObject,
    mut v_h__2_525_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_s_523_) == 0 {
        let mut v_a_526_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_527_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_525_);
        v_a_526_ = leanh::lean_ctor_get(v_s_523_, 0);
        leanh::lean_inc(v_a_526_);
        leanh::lean_dec_ref_known(v_s_523_, 1);
        v___x_527_ = leanh::lean_apply_1(v_h__1_524_, v_a_526_);
        return v___x_527_;
    } else {
        let mut v___x_528_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_524_);
        v___x_528_ = leanh::lean_apply_2(v_h__2_525_, v_s_523_, leanh::lean_box(0));
        return v___x_528_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop(
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
    res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Loop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Collect(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Control(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Bool(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Monadic_Basic(builtin);
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
pub unsafe fn meta_initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop(
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
pub unsafe fn initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop(
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
    res = initialize_Init_Data_Iterators_Consumers_Monadic_Loop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers_Monadic_Collect(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Control(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Bool(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Monadic_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop(builtin);
}