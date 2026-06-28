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
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_apply_1, lean_apply_2, lean_apply_3, lean_box,
    lean_ctor_get, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_obj_tag,
};
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop_0__Std_IterM_DefaultConsumers_forIn_x27_match__1_splitter___redArg(
    mut v_____do__lift_265_: *mut LeanObject,
    mut v_h__1_266_: *mut LeanObject,
    mut v_h__2_267_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_265_) == 0 {
        let mut v_a_268_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_269_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_266_);
        v_a_268_ = lean_ctor_get(v_____do__lift_265_, 0);
        lean_inc(v_a_268_);
        lean_dec_ref_known(v_____do__lift_265_, 1);
        v___x_269_ = lean_apply_2(v_h__2_267_, v_a_268_, lean_box(0));
        return v___x_269_;
    } else {
        let mut v_a_270_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_271_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_267_);
        v_a_270_ = lean_ctor_get(v_____do__lift_265_, 0);
        lean_inc(v_a_270_);
        lean_dec_ref_known(v_____do__lift_265_, 1);
        v___x_271_ = lean_apply_2(v_h__1_266_, v_a_270_, lean_box(0));
        return v___x_271_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop_0__Std_IterM_DefaultConsumers_forIn_x27_match__1_splitter(
    mut v_00_u03b2_272_: *mut LeanObject,
    mut v_00_u03b3_273_: *mut LeanObject,
    mut v_PlausibleForInStep_274_: *mut LeanObject,
    mut v_acc_275_: *mut LeanObject,
    mut v_out_276_: *mut LeanObject,
    mut v_motive_277_: *mut LeanObject,
    mut v_____do__lift_278_: *mut LeanObject,
    mut v_h__1_279_: *mut LeanObject,
    mut v_h__2_280_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_278_) == 0 {
        let mut v_a_281_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_282_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_279_);
        v_a_281_ = lean_ctor_get(v_____do__lift_278_, 0);
        lean_inc(v_a_281_);
        lean_dec_ref_known(v_____do__lift_278_, 1);
        v___x_282_ = lean_apply_2(v_h__2_280_, v_a_281_, lean_box(0));
        return v___x_282_;
    } else {
        let mut v_a_283_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_284_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_280_);
        v_a_283_ = lean_ctor_get(v_____do__lift_278_, 0);
        lean_inc(v_a_283_);
        lean_dec_ref_known(v_____do__lift_278_, 1);
        v___x_284_ = lean_apply_2(v_h__1_279_, v_a_283_, lean_box(0));
        return v___x_284_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop_0__Std_IterM_DefaultConsumers_forIn_x27_match__1_splitter___boxed(
    mut v_00_u03b2_285_: *mut LeanObject,
    mut v_00_u03b3_286_: *mut LeanObject,
    mut v_PlausibleForInStep_287_: *mut LeanObject,
    mut v_acc_288_: *mut LeanObject,
    mut v_out_289_: *mut LeanObject,
    mut v_motive_290_: *mut LeanObject,
    mut v_____do__lift_291_: *mut LeanObject,
    mut v_h__1_292_: *mut LeanObject,
    mut v_h__2_293_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_294_: *mut LeanObject = core::ptr::null_mut();
    v_res_294_ = l___private_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop_0__Std_IterM_DefaultConsumers_forIn_x27_match__1_splitter(v_00_u03b2_285_, v_00_u03b3_286_, v_PlausibleForInStep_287_, v_acc_288_, v_out_289_, v_motive_290_, v_____do__lift_291_, v_h__1_292_, v_h__2_293_);
    lean_dec(v_out_289_);
    lean_dec(v_acc_288_);
    return v_res_294_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop_0__Std_IterM_DefaultConsumers_forIn_x27_match__3_splitter___redArg(
    mut v_x_295_: *mut LeanObject,
    mut v_h__1_296_: *mut LeanObject,
    mut v_h__2_297_: *mut LeanObject,
    mut v_h__3_298_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_295_) {
        0 => {
            let mut v_it_299_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_300_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_301_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_298_);
            lean_dec(v_h__2_297_);
            v_it_299_ = lean_ctor_get(v_x_295_, 0);
            lean_inc(v_it_299_);
            v_out_300_ = lean_ctor_get(v_x_295_, 1);
            lean_inc(v_out_300_);
            lean_dec_ref_known(v_x_295_, 2);
            v___x_301_ = lean_apply_3(v_h__1_296_, v_it_299_, v_out_300_, lean_box(0));
            return v___x_301_;
        }
        1 => {
            let mut v_it_302_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_303_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_298_);
            lean_dec(v_h__1_296_);
            v_it_302_ = lean_ctor_get(v_x_295_, 0);
            lean_inc(v_it_302_);
            lean_dec_ref_known(v_x_295_, 1);
            v___x_303_ = lean_apply_2(v_h__2_297_, v_it_302_, lean_box(0));
            return v___x_303_;
        }
        _ => {
            let mut v___x_304_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_297_);
            lean_dec(v_h__1_296_);
            v___x_304_ = lean_apply_1(v_h__3_298_, lean_box(0));
            return v___x_304_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop_0__Std_IterM_DefaultConsumers_forIn_x27_match__3_splitter(
    mut v_m_305_: *mut LeanObject,
    mut v_00_u03b1_306_: *mut LeanObject,
    mut v_00_u03b2_307_: *mut LeanObject,
    mut v_inst_308_: *mut LeanObject,
    mut v_it_309_: *mut LeanObject,
    mut v_motive_310_: *mut LeanObject,
    mut v_x_311_: *mut LeanObject,
    mut v_h__1_312_: *mut LeanObject,
    mut v_h__2_313_: *mut LeanObject,
    mut v_h__3_314_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_311_) {
        0 => {
            let mut v_it_315_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_316_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_317_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_314_);
            lean_dec(v_h__2_313_);
            v_it_315_ = lean_ctor_get(v_x_311_, 0);
            lean_inc(v_it_315_);
            v_out_316_ = lean_ctor_get(v_x_311_, 1);
            lean_inc(v_out_316_);
            lean_dec_ref_known(v_x_311_, 2);
            v___x_317_ = lean_apply_3(v_h__1_312_, v_it_315_, v_out_316_, lean_box(0));
            return v___x_317_;
        }
        1 => {
            let mut v_it_318_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_319_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_314_);
            lean_dec(v_h__1_312_);
            v_it_318_ = lean_ctor_get(v_x_311_, 0);
            lean_inc(v_it_318_);
            lean_dec_ref_known(v_x_311_, 1);
            v___x_319_ = lean_apply_2(v_h__2_313_, v_it_318_, lean_box(0));
            return v___x_319_;
        }
        _ => {
            let mut v___x_320_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_313_);
            lean_dec(v_h__1_312_);
            v___x_320_ = lean_apply_1(v_h__3_314_, lean_box(0));
            return v___x_320_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop_0__Std_IterM_DefaultConsumers_forIn_x27_match__3_splitter___boxed(
    mut v_m_321_: *mut LeanObject,
    mut v_00_u03b1_322_: *mut LeanObject,
    mut v_00_u03b2_323_: *mut LeanObject,
    mut v_inst_324_: *mut LeanObject,
    mut v_it_325_: *mut LeanObject,
    mut v_motive_326_: *mut LeanObject,
    mut v_x_327_: *mut LeanObject,
    mut v_h__1_328_: *mut LeanObject,
    mut v_h__2_329_: *mut LeanObject,
    mut v_h__3_330_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_331_: *mut LeanObject = core::ptr::null_mut();
    v_res_331_ = l___private_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop_0__Std_IterM_DefaultConsumers_forIn_x27_match__3_splitter(v_m_321_, v_00_u03b1_322_, v_00_u03b2_323_, v_inst_324_, v_it_325_, v_motive_326_, v_x_327_, v_h__1_328_, v_h__2_329_, v_h__3_330_);
    lean_dec(v_it_325_);
    lean_dec(v_inst_324_);
    return v_res_331_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__1_splitter___redArg(
    mut v_____do__lift_332_: *mut LeanObject,
    mut v_h__1_333_: *mut LeanObject,
    mut v_h__2_334_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_332_) == 0 {
        let mut v_a_335_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_336_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_333_);
        v_a_335_ = lean_ctor_get(v_____do__lift_332_, 0);
        lean_inc(v_a_335_);
        lean_dec_ref_known(v_____do__lift_332_, 1);
        v___x_336_ = lean_apply_2(v_h__2_334_, v_a_335_, lean_box(0));
        return v___x_336_;
    } else {
        let mut v_a_337_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_338_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_334_);
        v_a_337_ = lean_ctor_get(v_____do__lift_332_, 0);
        lean_inc(v_a_337_);
        lean_dec_ref_known(v_____do__lift_332_, 1);
        v___x_338_ = lean_apply_2(v_h__1_333_, v_a_337_, lean_box(0));
        return v___x_338_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__1_splitter(
    mut v_00_u03b2_339_: *mut LeanObject,
    mut v_00_u03b3_340_: *mut LeanObject,
    mut v_init_341_: *mut LeanObject,
    mut v_PlausibleForInStep_342_: *mut LeanObject,
    mut v_out_343_: *mut LeanObject,
    mut v_motive_344_: *mut LeanObject,
    mut v_____do__lift_345_: *mut LeanObject,
    mut v_h__1_346_: *mut LeanObject,
    mut v_h__2_347_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_345_) == 0 {
        let mut v_a_348_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_349_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_346_);
        v_a_348_ = lean_ctor_get(v_____do__lift_345_, 0);
        lean_inc(v_a_348_);
        lean_dec_ref_known(v_____do__lift_345_, 1);
        v___x_349_ = lean_apply_2(v_h__2_347_, v_a_348_, lean_box(0));
        return v___x_349_;
    } else {
        let mut v_a_350_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_351_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_347_);
        v_a_350_ = lean_ctor_get(v_____do__lift_345_, 0);
        lean_inc(v_a_350_);
        lean_dec_ref_known(v_____do__lift_345_, 1);
        v___x_351_ = lean_apply_2(v_h__1_346_, v_a_350_, lean_box(0));
        return v___x_351_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__1_splitter___boxed(
    mut v_00_u03b2_352_: *mut LeanObject,
    mut v_00_u03b3_353_: *mut LeanObject,
    mut v_init_354_: *mut LeanObject,
    mut v_PlausibleForInStep_355_: *mut LeanObject,
    mut v_out_356_: *mut LeanObject,
    mut v_motive_357_: *mut LeanObject,
    mut v_____do__lift_358_: *mut LeanObject,
    mut v_h__1_359_: *mut LeanObject,
    mut v_h__2_360_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_361_: *mut LeanObject = core::ptr::null_mut();
    v_res_361_ = l___private_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__1_splitter(v_00_u03b2_352_, v_00_u03b3_353_, v_init_354_, v_PlausibleForInStep_355_, v_out_356_, v_motive_357_, v_____do__lift_358_, v_h__1_359_, v_h__2_360_);
    lean_dec(v_out_356_);
    lean_dec(v_init_354_);
    return v_res_361_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter___redArg(
    mut v_x_362_: *mut LeanObject,
    mut v_h__1_363_: *mut LeanObject,
    mut v_h__2_364_: *mut LeanObject,
    mut v_h__3_365_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_362_) {
        0 => {
            let mut v_it_366_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_367_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_368_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_365_);
            lean_dec(v_h__2_364_);
            v_it_366_ = lean_ctor_get(v_x_362_, 0);
            lean_inc(v_it_366_);
            v_out_367_ = lean_ctor_get(v_x_362_, 1);
            lean_inc(v_out_367_);
            lean_dec_ref_known(v_x_362_, 2);
            v___x_368_ = lean_apply_3(v_h__1_363_, v_it_366_, v_out_367_, lean_box(0));
            return v___x_368_;
        }
        1 => {
            let mut v_it_369_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_370_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_365_);
            lean_dec(v_h__1_363_);
            v_it_369_ = lean_ctor_get(v_x_362_, 0);
            lean_inc(v_it_369_);
            lean_dec_ref_known(v_x_362_, 1);
            v___x_370_ = lean_apply_2(v_h__2_364_, v_it_369_, lean_box(0));
            return v___x_370_;
        }
        _ => {
            let mut v___x_371_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_364_);
            lean_dec(v_h__1_363_);
            v___x_371_ = lean_apply_1(v_h__3_365_, lean_box(0));
            return v___x_371_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter(
    mut v_00_u03b1_372_: *mut LeanObject,
    mut v_00_u03b2_373_: *mut LeanObject,
    mut v_m_374_: *mut LeanObject,
    mut v_inst_375_: *mut LeanObject,
    mut v_it_376_: *mut LeanObject,
    mut v_motive_377_: *mut LeanObject,
    mut v_x_378_: *mut LeanObject,
    mut v_h__1_379_: *mut LeanObject,
    mut v_h__2_380_: *mut LeanObject,
    mut v_h__3_381_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_378_) {
        0 => {
            let mut v_it_382_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_383_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_384_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_381_);
            lean_dec(v_h__2_380_);
            v_it_382_ = lean_ctor_get(v_x_378_, 0);
            lean_inc(v_it_382_);
            v_out_383_ = lean_ctor_get(v_x_378_, 1);
            lean_inc(v_out_383_);
            lean_dec_ref_known(v_x_378_, 2);
            v___x_384_ = lean_apply_3(v_h__1_379_, v_it_382_, v_out_383_, lean_box(0));
            return v___x_384_;
        }
        1 => {
            let mut v_it_385_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_386_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_381_);
            lean_dec(v_h__1_379_);
            v_it_385_ = lean_ctor_get(v_x_378_, 0);
            lean_inc(v_it_385_);
            lean_dec_ref_known(v_x_378_, 1);
            v___x_386_ = lean_apply_2(v_h__2_380_, v_it_385_, lean_box(0));
            return v___x_386_;
        }
        _ => {
            let mut v___x_387_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_380_);
            lean_dec(v_h__1_379_);
            v___x_387_ = lean_apply_1(v_h__3_381_, lean_box(0));
            return v___x_387_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter___boxed(
    mut v_00_u03b1_388_: *mut LeanObject,
    mut v_00_u03b2_389_: *mut LeanObject,
    mut v_m_390_: *mut LeanObject,
    mut v_inst_391_: *mut LeanObject,
    mut v_it_392_: *mut LeanObject,
    mut v_motive_393_: *mut LeanObject,
    mut v_x_394_: *mut LeanObject,
    mut v_h__1_395_: *mut LeanObject,
    mut v_h__2_396_: *mut LeanObject,
    mut v_h__3_397_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_398_: *mut LeanObject = core::ptr::null_mut();
    v_res_398_ = l___private_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter(v_00_u03b1_388_, v_00_u03b2_389_, v_m_390_, v_inst_391_, v_it_392_, v_motive_393_, v_x_394_, v_h__1_395_, v_h__2_396_, v_h__3_397_);
    lean_dec(v_it_392_);
    lean_dec(v_inst_391_);
    return v_res_398_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop_0__Std_IterM_forIn_x27__eq__match__step_match__1_splitter___redArg(
    mut v_____do__lift_399_: *mut LeanObject,
    mut v_h__1_400_: *mut LeanObject,
    mut v_h__2_401_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_399_) == 0 {
        let mut v_a_402_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_403_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_400_);
        v_a_402_ = lean_ctor_get(v_____do__lift_399_, 0);
        lean_inc(v_a_402_);
        lean_dec_ref_known(v_____do__lift_399_, 1);
        v___x_403_ = lean_apply_1(v_h__2_401_, v_a_402_);
        return v___x_403_;
    } else {
        let mut v_a_404_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_405_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_401_);
        v_a_404_ = lean_ctor_get(v_____do__lift_399_, 0);
        lean_inc(v_a_404_);
        lean_dec_ref_known(v_____do__lift_399_, 1);
        v___x_405_ = lean_apply_1(v_h__1_400_, v_a_404_);
        return v___x_405_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop_0__Std_IterM_forIn_x27__eq__match__step_match__1_splitter(
    mut v_00_u03b3_406_: *mut LeanObject,
    mut v_motive_407_: *mut LeanObject,
    mut v_____do__lift_408_: *mut LeanObject,
    mut v_h__1_409_: *mut LeanObject,
    mut v_h__2_410_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_408_) == 0 {
        let mut v_a_411_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_412_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_409_);
        v_a_411_ = lean_ctor_get(v_____do__lift_408_, 0);
        lean_inc(v_a_411_);
        lean_dec_ref_known(v_____do__lift_408_, 1);
        v___x_412_ = lean_apply_1(v_h__2_410_, v_a_411_);
        return v___x_412_;
    } else {
        let mut v_a_413_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_414_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_410_);
        v_a_413_ = lean_ctor_get(v_____do__lift_408_, 0);
        lean_inc(v_a_413_);
        lean_dec_ref_known(v_____do__lift_408_, 1);
        v___x_414_ = lean_apply_1(v_h__1_409_, v_a_413_);
        return v___x_414_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop_0__List_forIn_x27__eq__foldlM_match__1_splitter___redArg(
    mut v_b_415_: *mut LeanObject,
    mut v_h__1_416_: *mut LeanObject,
    mut v_h__2_417_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_b_415_) == 0 {
        let mut v_a_418_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_419_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_416_);
        v_a_418_ = lean_ctor_get(v_b_415_, 0);
        lean_inc(v_a_418_);
        lean_dec_ref_known(v_b_415_, 1);
        v___x_419_ = lean_apply_1(v_h__2_417_, v_a_418_);
        return v___x_419_;
    } else {
        let mut v_a_420_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_421_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_417_);
        v_a_420_ = lean_ctor_get(v_b_415_, 0);
        lean_inc(v_a_420_);
        lean_dec_ref_known(v_b_415_, 1);
        v___x_421_ = lean_apply_1(v_h__1_416_, v_a_420_);
        return v___x_421_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop_0__List_forIn_x27__eq__foldlM_match__1_splitter(
    mut v_00_u03b2_422_: *mut LeanObject,
    mut v_motive_423_: *mut LeanObject,
    mut v_b_424_: *mut LeanObject,
    mut v_h__1_425_: *mut LeanObject,
    mut v_h__2_426_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_b_424_) == 0 {
        let mut v_a_427_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_428_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_425_);
        v_a_427_ = lean_ctor_get(v_b_424_, 0);
        lean_inc(v_a_427_);
        lean_dec_ref_known(v_b_424_, 1);
        v___x_428_ = lean_apply_1(v_h__2_426_, v_a_427_);
        return v___x_428_;
    } else {
        let mut v_a_429_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_430_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_426_);
        v_a_429_ = lean_ctor_get(v_b_424_, 0);
        lean_inc(v_a_429_);
        lean_dec_ref_known(v_b_424_, 1);
        v___x_430_ = lean_apply_1(v_h__1_425_, v_a_429_);
        return v___x_430_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop_0__Std_IterM_toArray__eq__match__step_match__1_splitter___redArg(
    mut v_x_431_: *mut LeanObject,
    mut v_h__1_432_: *mut LeanObject,
    mut v_h__2_433_: *mut LeanObject,
    mut v_h__3_434_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_431_) {
        0 => {
            let mut v_it_435_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_436_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_437_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_434_);
            lean_dec(v_h__2_433_);
            v_it_435_ = lean_ctor_get(v_x_431_, 0);
            lean_inc(v_it_435_);
            v_out_436_ = lean_ctor_get(v_x_431_, 1);
            lean_inc(v_out_436_);
            lean_dec_ref_known(v_x_431_, 2);
            v___x_437_ = lean_apply_2(v_h__1_432_, v_it_435_, v_out_436_);
            return v___x_437_;
        }
        1 => {
            let mut v_it_438_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_439_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_434_);
            lean_dec(v_h__1_432_);
            v_it_438_ = lean_ctor_get(v_x_431_, 0);
            lean_inc(v_it_438_);
            lean_dec_ref_known(v_x_431_, 1);
            v___x_439_ = lean_apply_1(v_h__2_433_, v_it_438_);
            return v___x_439_;
        }
        _ => {
            let mut v___x_440_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_441_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_433_);
            lean_dec(v_h__1_432_);
            v___x_440_ = lean_box(0);
            v___x_441_ = lean_apply_1(v_h__3_434_, v___x_440_);
            return v___x_441_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop_0__Std_IterM_toArray__eq__match__step_match__1_splitter(
    mut v_00_u03b1_442_: *mut LeanObject,
    mut v_00_u03b2_443_: *mut LeanObject,
    mut v_m_444_: *mut LeanObject,
    mut v_motive_445_: *mut LeanObject,
    mut v_x_446_: *mut LeanObject,
    mut v_h__1_447_: *mut LeanObject,
    mut v_h__2_448_: *mut LeanObject,
    mut v_h__3_449_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_446_) {
        0 => {
            let mut v_it_450_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_451_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_452_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_449_);
            lean_dec(v_h__2_448_);
            v_it_450_ = lean_ctor_get(v_x_446_, 0);
            lean_inc(v_it_450_);
            v_out_451_ = lean_ctor_get(v_x_446_, 1);
            lean_inc(v_out_451_);
            lean_dec_ref_known(v_x_446_, 2);
            v___x_452_ = lean_apply_2(v_h__1_447_, v_it_450_, v_out_451_);
            return v___x_452_;
        }
        1 => {
            let mut v_it_453_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_454_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_449_);
            lean_dec(v_h__1_447_);
            v_it_453_ = lean_ctor_get(v_x_446_, 0);
            lean_inc(v_it_453_);
            lean_dec_ref_known(v_x_446_, 1);
            v___x_454_ = lean_apply_1(v_h__2_448_, v_it_453_);
            return v___x_454_;
        }
        _ => {
            let mut v___x_455_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_456_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_448_);
            lean_dec(v_h__1_447_);
            v___x_455_ = lean_box(0);
            v___x_456_ = lean_apply_1(v_h__3_449_, v___x_455_);
            return v___x_456_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop_0__Std_IterM_length__eq__match__step_match__1_splitter___redArg(
    mut v_x_457_: *mut LeanObject,
    mut v_h__1_458_: *mut LeanObject,
    mut v_h__2_459_: *mut LeanObject,
    mut v_h__3_460_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_457_) {
        0 => {
            let mut v_it_461_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_462_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_463_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_460_);
            lean_dec(v_h__2_459_);
            v_it_461_ = lean_ctor_get(v_x_457_, 0);
            lean_inc(v_it_461_);
            v_out_462_ = lean_ctor_get(v_x_457_, 1);
            lean_inc(v_out_462_);
            lean_dec_ref_known(v_x_457_, 2);
            v___x_463_ = lean_apply_2(v_h__1_458_, v_it_461_, v_out_462_);
            return v___x_463_;
        }
        1 => {
            let mut v_it_464_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_465_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_460_);
            lean_dec(v_h__1_458_);
            v_it_464_ = lean_ctor_get(v_x_457_, 0);
            lean_inc(v_it_464_);
            lean_dec_ref_known(v_x_457_, 1);
            v___x_465_ = lean_apply_1(v_h__2_459_, v_it_464_);
            return v___x_465_;
        }
        _ => {
            let mut v___x_466_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_467_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_459_);
            lean_dec(v_h__1_458_);
            v___x_466_ = lean_box(0);
            v___x_467_ = lean_apply_1(v_h__3_460_, v___x_466_);
            return v___x_467_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop_0__Std_IterM_length__eq__match__step_match__1_splitter(
    mut v_00_u03b1_468_: *mut LeanObject,
    mut v_00_u03b2_469_: *mut LeanObject,
    mut v_m_470_: *mut LeanObject,
    mut v_motive_471_: *mut LeanObject,
    mut v_x_472_: *mut LeanObject,
    mut v_h__1_473_: *mut LeanObject,
    mut v_h__2_474_: *mut LeanObject,
    mut v_h__3_475_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_472_) {
        0 => {
            let mut v_it_476_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_477_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_478_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_475_);
            lean_dec(v_h__2_474_);
            v_it_476_ = lean_ctor_get(v_x_472_, 0);
            lean_inc(v_it_476_);
            v_out_477_ = lean_ctor_get(v_x_472_, 1);
            lean_inc(v_out_477_);
            lean_dec_ref_known(v_x_472_, 2);
            v___x_478_ = lean_apply_2(v_h__1_473_, v_it_476_, v_out_477_);
            return v___x_478_;
        }
        1 => {
            let mut v_it_479_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_480_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_475_);
            lean_dec(v_h__1_473_);
            v_it_479_ = lean_ctor_get(v_x_472_, 0);
            lean_inc(v_it_479_);
            lean_dec_ref_known(v_x_472_, 1);
            v___x_480_ = lean_apply_1(v_h__2_474_, v_it_479_);
            return v___x_480_;
        }
        _ => {
            let mut v___x_481_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_482_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_474_);
            lean_dec(v_h__1_473_);
            v___x_481_ = lean_box(0);
            v___x_482_ = lean_apply_1(v_h__3_475_, v___x_481_);
            return v___x_482_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop_0__Std_IterM_findSomeM_x3f_match__1_splitter___redArg(
    mut v_____do__lift_483_: *mut LeanObject,
    mut v_h__1_484_: *mut LeanObject,
    mut v_h__2_485_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_483_) == 0 {
        let mut v___x_486_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_487_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_485_);
        v___x_486_ = lean_box(0);
        v___x_487_ = lean_apply_1(v_h__1_484_, v___x_486_);
        return v___x_487_;
    } else {
        let mut v_val_488_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_489_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_484_);
        v_val_488_ = lean_ctor_get(v_____do__lift_483_, 0);
        lean_inc(v_val_488_);
        lean_dec_ref_known(v_____do__lift_483_, 1);
        v___x_489_ = lean_apply_1(v_h__2_485_, v_val_488_);
        return v___x_489_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop_0__Std_IterM_findSomeM_x3f_match__1_splitter(
    mut v_00_u03b3_490_: *mut LeanObject,
    mut v_motive_491_: *mut LeanObject,
    mut v_____do__lift_492_: *mut LeanObject,
    mut v_h__1_493_: *mut LeanObject,
    mut v_h__2_494_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_492_) == 0 {
        let mut v___x_495_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_496_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_494_);
        v___x_495_ = lean_box(0);
        v___x_496_ = lean_apply_1(v_h__1_493_, v___x_495_);
        return v___x_496_;
    } else {
        let mut v_val_497_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_498_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_493_);
        v_val_497_ = lean_ctor_get(v_____do__lift_492_, 0);
        lean_inc(v_val_497_);
        lean_dec_ref_known(v_____do__lift_492_, 1);
        v___x_498_ = lean_apply_1(v_h__2_494_, v_val_497_);
        return v___x_498_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop_0__Std_IterM_findSomeM_x3f__eq__match__step_match__1_splitter___redArg(
    mut v_____do__lift_499_: *mut LeanObject,
    mut v_h__1_500_: *mut LeanObject,
    mut v_h__2_501_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_499_) == 0 {
        let mut v___x_502_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_503_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_501_);
        v___x_502_ = lean_box(0);
        v___x_503_ = lean_apply_1(v_h__1_500_, v___x_502_);
        return v___x_503_;
    } else {
        let mut v_val_504_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_505_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_500_);
        v_val_504_ = lean_ctor_get(v_____do__lift_499_, 0);
        lean_inc(v_val_504_);
        lean_dec_ref_known(v_____do__lift_499_, 1);
        v___x_505_ = lean_apply_1(v_h__2_501_, v_val_504_);
        return v___x_505_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop_0__Std_IterM_findSomeM_x3f__eq__match__step_match__1_splitter(
    mut v_00_u03b3_506_: *mut LeanObject,
    mut v_motive_507_: *mut LeanObject,
    mut v_____do__lift_508_: *mut LeanObject,
    mut v_h__1_509_: *mut LeanObject,
    mut v_h__2_510_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_508_) == 0 {
        let mut v___x_511_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_512_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_510_);
        v___x_511_ = lean_box(0);
        v___x_512_ = lean_apply_1(v_h__1_509_, v___x_511_);
        return v___x_512_;
    } else {
        let mut v_val_513_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_514_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_509_);
        v_val_513_ = lean_ctor_get(v_____do__lift_508_, 0);
        lean_inc(v_val_513_);
        lean_dec_ref_known(v_____do__lift_508_, 1);
        v___x_514_ = lean_apply_1(v_h__2_510_, v_val_513_);
        return v___x_514_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop_0__Std_IteratorLoop_wellFounded__of__productive_match__1_splitter___redArg(
    mut v_s_515_: *mut LeanObject,
    mut v_h__1_516_: *mut LeanObject,
    mut v_h__2_517_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_s_515_) == 0 {
        let mut v_a_518_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_519_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_517_);
        v_a_518_ = lean_ctor_get(v_s_515_, 0);
        lean_inc(v_a_518_);
        lean_dec_ref_known(v_s_515_, 1);
        v___x_519_ = lean_apply_1(v_h__1_516_, v_a_518_);
        return v___x_519_;
    } else {
        let mut v___x_520_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_516_);
        v___x_520_ = lean_apply_2(v_h__2_517_, v_s_515_, lean_box(0));
        return v___x_520_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop_0__Std_IteratorLoop_wellFounded__of__productive_match__1_splitter(
    mut v_00_u03b3_521_: *mut LeanObject,
    mut v_motive_522_: *mut LeanObject,
    mut v_s_523_: *mut LeanObject,
    mut v_h__1_524_: *mut LeanObject,
    mut v_h__2_525_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_s_523_) == 0 {
        let mut v_a_526_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_527_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_525_);
        v_a_526_ = lean_ctor_get(v_s_523_, 0);
        lean_inc(v_a_526_);
        lean_dec_ref_known(v_s_523_, 1);
        v___x_527_ = lean_apply_1(v_h__1_524_, v_a_526_);
        return v___x_527_;
    } else {
        let mut v___x_528_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_524_);
        v___x_528_ = lean_apply_2(v_h__2_525_, v_s_523_, lean_box(0));
        return v___x_528_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop(
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
    res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Collect(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Control(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Bool(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Monadic_Basic(builtin);
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
pub unsafe fn meta_initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop(
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
pub unsafe fn initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop(
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
    res = initialize_Init_Data_Iterators_Consumers_Monadic_Collect(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_Control(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Array_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Bool(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Monadic_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop(builtin);
}
