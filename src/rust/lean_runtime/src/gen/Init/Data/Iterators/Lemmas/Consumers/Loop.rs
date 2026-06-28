// Lean compiler output
// Module: Init.Data.Iterators.Lemmas.Consumers.Loop
// Imports: Init.Data.Iterators.Lemmas.Consumers.Monadic.Loop Init.Data.Iterators.Consumers.Loop Init.Data.Iterators.Consumers.Monadic.Collect Init.Data.Array.Monadic Init.Data.Iterators.Consumers.Collect Init.Data.Iterators.Consumers.Loop Init.Data.List.Monadic Init.Data.Iterators.Lemmas.Basic Init.Data.Iterators.Lemmas.Consumers.Collect Init.Data.List.Find Init.Data.Option.Lemmas
use crate::r#gen::Init::Data::Array::Monadic::{
    initialize_Init_Data_Array_Monadic, runtime_initialize_Init_Data_Array_Monadic,
};
use crate::r#gen::Init::Data::Iterators::Consumers::Collect::{
    initialize_Init_Data_Iterators_Consumers_Collect,
    runtime_initialize_Init_Data_Iterators_Consumers_Collect,
};
use crate::r#gen::Init::Data::Iterators::Consumers::Loop::{
    initialize_Init_Data_Iterators_Consumers_Loop,
    runtime_initialize_Init_Data_Iterators_Consumers_Loop,
};
use crate::r#gen::Init::Data::Iterators::Consumers::Monadic::Collect::{
    initialize_Init_Data_Iterators_Consumers_Monadic_Collect,
    runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Collect,
};
use crate::r#gen::Init::Data::Iterators::Lemmas::Basic::{
    initialize_Init_Data_Iterators_Lemmas_Basic,
    runtime_initialize_Init_Data_Iterators_Lemmas_Basic,
};
use crate::r#gen::Init::Data::Iterators::Lemmas::Consumers::Collect::{
    initialize_Init_Data_Iterators_Lemmas_Consumers_Collect,
    runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Collect,
};
use crate::r#gen::Init::Data::Iterators::Lemmas::Consumers::Monadic::Loop::{
    initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop,
    runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop,
};
use crate::r#gen::Init::Data::List::Find::{
    initialize_Init_Data_List_Find, runtime_initialize_Init_Data_List_Find,
};
use crate::r#gen::Init::Data::List::Monadic::{
    initialize_Init_Data_List_Monadic, runtime_initialize_Init_Data_List_Monadic,
};
use crate::r#gen::Init::Data::Option::Lemmas::{
    initialize_Init_Data_Option_Lemmas, runtime_initialize_Init_Data_Option_Lemmas,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_apply_1, lean_apply_2, lean_apply_3, lean_box,
    lean_ctor_get, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_obj_tag,
};
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iter_forIn_x27__eq__match__step_match__3_splitter___redArg(
    mut v_x_259_: *mut LeanObject,
    mut v_h__1_260_: *mut LeanObject,
    mut v_h__2_261_: *mut LeanObject,
    mut v_h__3_262_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_259_) {
        0 => {
            let mut v_it_263_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_264_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_265_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_262_);
            lean_dec(v_h__2_261_);
            v_it_263_ = lean_ctor_get(v_x_259_, 0);
            lean_inc(v_it_263_);
            v_out_264_ = lean_ctor_get(v_x_259_, 1);
            lean_inc(v_out_264_);
            lean_dec_ref_known(v_x_259_, 2);
            v___x_265_ = lean_apply_3(v_h__1_260_, v_it_263_, v_out_264_, lean_box(0));
            return v___x_265_;
        }
        1 => {
            let mut v_it_266_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_267_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_262_);
            lean_dec(v_h__1_260_);
            v_it_266_ = lean_ctor_get(v_x_259_, 0);
            lean_inc(v_it_266_);
            lean_dec_ref_known(v_x_259_, 1);
            v___x_267_ = lean_apply_2(v_h__2_261_, v_it_266_, lean_box(0));
            return v___x_267_;
        }
        _ => {
            let mut v___x_268_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_261_);
            lean_dec(v_h__1_260_);
            v___x_268_ = lean_apply_1(v_h__3_262_, lean_box(0));
            return v___x_268_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iter_forIn_x27__eq__match__step_match__3_splitter(
    mut v_00_u03b1_269_: *mut LeanObject,
    mut v_00_u03b2_270_: *mut LeanObject,
    mut v_inst_271_: *mut LeanObject,
    mut v_it_272_: *mut LeanObject,
    mut v_motive_273_: *mut LeanObject,
    mut v_x_274_: *mut LeanObject,
    mut v_h__1_275_: *mut LeanObject,
    mut v_h__2_276_: *mut LeanObject,
    mut v_h__3_277_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_274_) {
        0 => {
            let mut v_it_278_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_279_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_280_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_277_);
            lean_dec(v_h__2_276_);
            v_it_278_ = lean_ctor_get(v_x_274_, 0);
            lean_inc(v_it_278_);
            v_out_279_ = lean_ctor_get(v_x_274_, 1);
            lean_inc(v_out_279_);
            lean_dec_ref_known(v_x_274_, 2);
            v___x_280_ = lean_apply_3(v_h__1_275_, v_it_278_, v_out_279_, lean_box(0));
            return v___x_280_;
        }
        1 => {
            let mut v_it_281_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_282_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_277_);
            lean_dec(v_h__1_275_);
            v_it_281_ = lean_ctor_get(v_x_274_, 0);
            lean_inc(v_it_281_);
            lean_dec_ref_known(v_x_274_, 1);
            v___x_282_ = lean_apply_2(v_h__2_276_, v_it_281_, lean_box(0));
            return v___x_282_;
        }
        _ => {
            let mut v___x_283_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_276_);
            lean_dec(v_h__1_275_);
            v___x_283_ = lean_apply_1(v_h__3_277_, lean_box(0));
            return v___x_283_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iter_forIn_x27__eq__match__step_match__3_splitter___boxed(
    mut v_00_u03b1_284_: *mut LeanObject,
    mut v_00_u03b2_285_: *mut LeanObject,
    mut v_inst_286_: *mut LeanObject,
    mut v_it_287_: *mut LeanObject,
    mut v_motive_288_: *mut LeanObject,
    mut v_x_289_: *mut LeanObject,
    mut v_h__1_290_: *mut LeanObject,
    mut v_h__2_291_: *mut LeanObject,
    mut v_h__3_292_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_293_: *mut LeanObject = core::ptr::null_mut();
    v_res_293_ = l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iter_forIn_x27__eq__match__step_match__3_splitter(v_00_u03b1_284_, v_00_u03b2_285_, v_inst_286_, v_it_287_, v_motive_288_, v_x_289_, v_h__1_290_, v_h__2_291_, v_h__3_292_);
    lean_dec(v_it_287_);
    lean_dec(v_inst_286_);
    return v_res_293_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iter_forIn_x27__eq__match__step_match__1_splitter___redArg(
    mut v_____do__lift_294_: *mut LeanObject,
    mut v_h__1_295_: *mut LeanObject,
    mut v_h__2_296_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_294_) == 0 {
        let mut v_a_297_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_298_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_295_);
        v_a_297_ = lean_ctor_get(v_____do__lift_294_, 0);
        lean_inc(v_a_297_);
        lean_dec_ref_known(v_____do__lift_294_, 1);
        v___x_298_ = lean_apply_1(v_h__2_296_, v_a_297_);
        return v___x_298_;
    } else {
        let mut v_a_299_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_300_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_296_);
        v_a_299_ = lean_ctor_get(v_____do__lift_294_, 0);
        lean_inc(v_a_299_);
        lean_dec_ref_known(v_____do__lift_294_, 1);
        v___x_300_ = lean_apply_1(v_h__1_295_, v_a_299_);
        return v___x_300_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iter_forIn_x27__eq__match__step_match__1_splitter(
    mut v_00_u03b3_301_: *mut LeanObject,
    mut v_motive_302_: *mut LeanObject,
    mut v_____do__lift_303_: *mut LeanObject,
    mut v_h__1_304_: *mut LeanObject,
    mut v_h__2_305_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_303_) == 0 {
        let mut v_a_306_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_307_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_304_);
        v_a_306_ = lean_ctor_get(v_____do__lift_303_, 0);
        lean_inc(v_a_306_);
        lean_dec_ref_known(v_____do__lift_303_, 1);
        v___x_307_ = lean_apply_1(v_h__2_305_, v_a_306_);
        return v___x_307_;
    } else {
        let mut v_a_308_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_309_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_305_);
        v_a_308_ = lean_ctor_get(v_____do__lift_303_, 0);
        lean_inc(v_a_308_);
        lean_dec_ref_known(v_____do__lift_303_, 1);
        v___x_309_ = lean_apply_1(v_h__1_304_, v_a_308_);
        return v___x_309_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter___redArg(
    mut v_x_310_: *mut LeanObject,
    mut v_h__1_311_: *mut LeanObject,
    mut v_h__2_312_: *mut LeanObject,
    mut v_h__3_313_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_310_) {
        0 => {
            let mut v_it_314_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_315_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_316_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_313_);
            lean_dec(v_h__2_312_);
            v_it_314_ = lean_ctor_get(v_x_310_, 0);
            lean_inc(v_it_314_);
            v_out_315_ = lean_ctor_get(v_x_310_, 1);
            lean_inc(v_out_315_);
            lean_dec_ref_known(v_x_310_, 2);
            v___x_316_ = lean_apply_3(v_h__1_311_, v_it_314_, v_out_315_, lean_box(0));
            return v___x_316_;
        }
        1 => {
            let mut v_it_317_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_318_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_313_);
            lean_dec(v_h__1_311_);
            v_it_317_ = lean_ctor_get(v_x_310_, 0);
            lean_inc(v_it_317_);
            lean_dec_ref_known(v_x_310_, 1);
            v___x_318_ = lean_apply_2(v_h__2_312_, v_it_317_, lean_box(0));
            return v___x_318_;
        }
        _ => {
            let mut v___x_319_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_312_);
            lean_dec(v_h__1_311_);
            v___x_319_ = lean_apply_1(v_h__3_313_, lean_box(0));
            return v___x_319_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter(
    mut v_00_u03b1_320_: *mut LeanObject,
    mut v_00_u03b2_321_: *mut LeanObject,
    mut v_m_322_: *mut LeanObject,
    mut v_inst_323_: *mut LeanObject,
    mut v_it_324_: *mut LeanObject,
    mut v_motive_325_: *mut LeanObject,
    mut v_x_326_: *mut LeanObject,
    mut v_h__1_327_: *mut LeanObject,
    mut v_h__2_328_: *mut LeanObject,
    mut v_h__3_329_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_326_) {
        0 => {
            let mut v_it_330_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_331_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_332_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_329_);
            lean_dec(v_h__2_328_);
            v_it_330_ = lean_ctor_get(v_x_326_, 0);
            lean_inc(v_it_330_);
            v_out_331_ = lean_ctor_get(v_x_326_, 1);
            lean_inc(v_out_331_);
            lean_dec_ref_known(v_x_326_, 2);
            v___x_332_ = lean_apply_3(v_h__1_327_, v_it_330_, v_out_331_, lean_box(0));
            return v___x_332_;
        }
        1 => {
            let mut v_it_333_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_334_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_329_);
            lean_dec(v_h__1_327_);
            v_it_333_ = lean_ctor_get(v_x_326_, 0);
            lean_inc(v_it_333_);
            lean_dec_ref_known(v_x_326_, 1);
            v___x_334_ = lean_apply_2(v_h__2_328_, v_it_333_, lean_box(0));
            return v___x_334_;
        }
        _ => {
            let mut v___x_335_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_328_);
            lean_dec(v_h__1_327_);
            v___x_335_ = lean_apply_1(v_h__3_329_, lean_box(0));
            return v___x_335_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter___boxed(
    mut v_00_u03b1_336_: *mut LeanObject,
    mut v_00_u03b2_337_: *mut LeanObject,
    mut v_m_338_: *mut LeanObject,
    mut v_inst_339_: *mut LeanObject,
    mut v_it_340_: *mut LeanObject,
    mut v_motive_341_: *mut LeanObject,
    mut v_x_342_: *mut LeanObject,
    mut v_h__1_343_: *mut LeanObject,
    mut v_h__2_344_: *mut LeanObject,
    mut v_h__3_345_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_346_: *mut LeanObject = core::ptr::null_mut();
    v_res_346_ = l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter(v_00_u03b1_336_, v_00_u03b2_337_, v_m_338_, v_inst_339_, v_it_340_, v_motive_341_, v_x_342_, v_h__1_343_, v_h__2_344_, v_h__3_345_);
    lean_dec(v_it_340_);
    lean_dec(v_inst_339_);
    return v_res_346_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__1_splitter___redArg(
    mut v_____do__lift_347_: *mut LeanObject,
    mut v_h__1_348_: *mut LeanObject,
    mut v_h__2_349_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_347_) == 0 {
        let mut v_a_350_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_351_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_348_);
        v_a_350_ = lean_ctor_get(v_____do__lift_347_, 0);
        lean_inc(v_a_350_);
        lean_dec_ref_known(v_____do__lift_347_, 1);
        v___x_351_ = lean_apply_2(v_h__2_349_, v_a_350_, lean_box(0));
        return v___x_351_;
    } else {
        let mut v_a_352_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_353_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_349_);
        v_a_352_ = lean_ctor_get(v_____do__lift_347_, 0);
        lean_inc(v_a_352_);
        lean_dec_ref_known(v_____do__lift_347_, 1);
        v___x_353_ = lean_apply_2(v_h__1_348_, v_a_352_, lean_box(0));
        return v___x_353_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__1_splitter(
    mut v_00_u03b2_354_: *mut LeanObject,
    mut v_00_u03b3_355_: *mut LeanObject,
    mut v_init_356_: *mut LeanObject,
    mut v_PlausibleForInStep_357_: *mut LeanObject,
    mut v_out_358_: *mut LeanObject,
    mut v_motive_359_: *mut LeanObject,
    mut v_____do__lift_360_: *mut LeanObject,
    mut v_h__1_361_: *mut LeanObject,
    mut v_h__2_362_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_360_) == 0 {
        let mut v_a_363_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_364_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_361_);
        v_a_363_ = lean_ctor_get(v_____do__lift_360_, 0);
        lean_inc(v_a_363_);
        lean_dec_ref_known(v_____do__lift_360_, 1);
        v___x_364_ = lean_apply_2(v_h__2_362_, v_a_363_, lean_box(0));
        return v___x_364_;
    } else {
        let mut v_a_365_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_366_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_362_);
        v_a_365_ = lean_ctor_get(v_____do__lift_360_, 0);
        lean_inc(v_a_365_);
        lean_dec_ref_known(v_____do__lift_360_, 1);
        v___x_366_ = lean_apply_2(v_h__1_361_, v_a_365_, lean_box(0));
        return v___x_366_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__1_splitter___boxed(
    mut v_00_u03b2_367_: *mut LeanObject,
    mut v_00_u03b3_368_: *mut LeanObject,
    mut v_init_369_: *mut LeanObject,
    mut v_PlausibleForInStep_370_: *mut LeanObject,
    mut v_out_371_: *mut LeanObject,
    mut v_motive_372_: *mut LeanObject,
    mut v_____do__lift_373_: *mut LeanObject,
    mut v_h__1_374_: *mut LeanObject,
    mut v_h__2_375_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_376_: *mut LeanObject = core::ptr::null_mut();
    v_res_376_ = l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__1_splitter(v_00_u03b2_367_, v_00_u03b3_368_, v_init_369_, v_PlausibleForInStep_370_, v_out_371_, v_motive_372_, v_____do__lift_373_, v_h__1_374_, v_h__2_375_);
    lean_dec(v_out_371_);
    lean_dec(v_init_369_);
    return v_res_376_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iter_toArray__eq__match__step_match__1_splitter___redArg(
    mut v_x_377_: *mut LeanObject,
    mut v_h__1_378_: *mut LeanObject,
    mut v_h__2_379_: *mut LeanObject,
    mut v_h__3_380_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_377_) {
        0 => {
            let mut v_it_381_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_382_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_383_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_380_);
            lean_dec(v_h__2_379_);
            v_it_381_ = lean_ctor_get(v_x_377_, 0);
            lean_inc(v_it_381_);
            v_out_382_ = lean_ctor_get(v_x_377_, 1);
            lean_inc(v_out_382_);
            lean_dec_ref_known(v_x_377_, 2);
            v___x_383_ = lean_apply_2(v_h__1_378_, v_it_381_, v_out_382_);
            return v___x_383_;
        }
        1 => {
            let mut v_it_384_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_385_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_380_);
            lean_dec(v_h__1_378_);
            v_it_384_ = lean_ctor_get(v_x_377_, 0);
            lean_inc(v_it_384_);
            lean_dec_ref_known(v_x_377_, 1);
            v___x_385_ = lean_apply_1(v_h__2_379_, v_it_384_);
            return v___x_385_;
        }
        _ => {
            let mut v___x_386_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_387_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_379_);
            lean_dec(v_h__1_378_);
            v___x_386_ = lean_box(0);
            v___x_387_ = lean_apply_1(v_h__3_380_, v___x_386_);
            return v___x_387_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iter_toArray__eq__match__step_match__1_splitter(
    mut v_00_u03b1_388_: *mut LeanObject,
    mut v_00_u03b2_389_: *mut LeanObject,
    mut v_motive_390_: *mut LeanObject,
    mut v_x_391_: *mut LeanObject,
    mut v_h__1_392_: *mut LeanObject,
    mut v_h__2_393_: *mut LeanObject,
    mut v_h__3_394_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_391_) {
        0 => {
            let mut v_it_395_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_396_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_397_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_394_);
            lean_dec(v_h__2_393_);
            v_it_395_ = lean_ctor_get(v_x_391_, 0);
            lean_inc(v_it_395_);
            v_out_396_ = lean_ctor_get(v_x_391_, 1);
            lean_inc(v_out_396_);
            lean_dec_ref_known(v_x_391_, 2);
            v___x_397_ = lean_apply_2(v_h__1_392_, v_it_395_, v_out_396_);
            return v___x_397_;
        }
        1 => {
            let mut v_it_398_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_399_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_394_);
            lean_dec(v_h__1_392_);
            v_it_398_ = lean_ctor_get(v_x_391_, 0);
            lean_inc(v_it_398_);
            lean_dec_ref_known(v_x_391_, 1);
            v___x_399_ = lean_apply_1(v_h__2_393_, v_it_398_);
            return v___x_399_;
        }
        _ => {
            let mut v___x_400_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_401_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_393_);
            lean_dec(v_h__1_392_);
            v___x_400_ = lean_box(0);
            v___x_401_ = lean_apply_1(v_h__3_394_, v___x_400_);
            return v___x_401_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__List_forIn_x27__eq__foldlM_match__1_splitter___redArg(
    mut v_b_402_: *mut LeanObject,
    mut v_h__1_403_: *mut LeanObject,
    mut v_h__2_404_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_b_402_) == 0 {
        let mut v_a_405_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_406_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_403_);
        v_a_405_ = lean_ctor_get(v_b_402_, 0);
        lean_inc(v_a_405_);
        lean_dec_ref_known(v_b_402_, 1);
        v___x_406_ = lean_apply_1(v_h__2_404_, v_a_405_);
        return v___x_406_;
    } else {
        let mut v_a_407_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_408_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_404_);
        v_a_407_ = lean_ctor_get(v_b_402_, 0);
        lean_inc(v_a_407_);
        lean_dec_ref_known(v_b_402_, 1);
        v___x_408_ = lean_apply_1(v_h__1_403_, v_a_407_);
        return v___x_408_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__List_forIn_x27__eq__foldlM_match__1_splitter(
    mut v_00_u03b2_409_: *mut LeanObject,
    mut v_motive_410_: *mut LeanObject,
    mut v_b_411_: *mut LeanObject,
    mut v_h__1_412_: *mut LeanObject,
    mut v_h__2_413_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_b_411_) == 0 {
        let mut v_a_414_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_415_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_412_);
        v_a_414_ = lean_ctor_get(v_b_411_, 0);
        lean_inc(v_a_414_);
        lean_dec_ref_known(v_b_411_, 1);
        v___x_415_ = lean_apply_1(v_h__2_413_, v_a_414_);
        return v___x_415_;
    } else {
        let mut v_a_416_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_417_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_413_);
        v_a_416_ = lean_ctor_get(v_b_411_, 0);
        lean_inc(v_a_416_);
        lean_dec_ref_known(v_b_411_, 1);
        v___x_417_ = lean_apply_1(v_h__1_412_, v_a_416_);
        return v___x_417_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iter_length__eq__match__step_match__1_splitter___redArg(
    mut v_x_418_: *mut LeanObject,
    mut v_h__1_419_: *mut LeanObject,
    mut v_h__2_420_: *mut LeanObject,
    mut v_h__3_421_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_418_) {
        0 => {
            let mut v_it_422_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_423_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_424_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_421_);
            lean_dec(v_h__2_420_);
            v_it_422_ = lean_ctor_get(v_x_418_, 0);
            lean_inc(v_it_422_);
            v_out_423_ = lean_ctor_get(v_x_418_, 1);
            lean_inc(v_out_423_);
            lean_dec_ref_known(v_x_418_, 2);
            v___x_424_ = lean_apply_2(v_h__1_419_, v_it_422_, v_out_423_);
            return v___x_424_;
        }
        1 => {
            let mut v_it_425_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_426_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_421_);
            lean_dec(v_h__1_419_);
            v_it_425_ = lean_ctor_get(v_x_418_, 0);
            lean_inc(v_it_425_);
            lean_dec_ref_known(v_x_418_, 1);
            v___x_426_ = lean_apply_1(v_h__2_420_, v_it_425_);
            return v___x_426_;
        }
        _ => {
            let mut v___x_427_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_428_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_420_);
            lean_dec(v_h__1_419_);
            v___x_427_ = lean_box(0);
            v___x_428_ = lean_apply_1(v_h__3_421_, v___x_427_);
            return v___x_428_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iter_length__eq__match__step_match__1_splitter(
    mut v_00_u03b1_429_: *mut LeanObject,
    mut v_00_u03b2_430_: *mut LeanObject,
    mut v_motive_431_: *mut LeanObject,
    mut v_x_432_: *mut LeanObject,
    mut v_h__1_433_: *mut LeanObject,
    mut v_h__2_434_: *mut LeanObject,
    mut v_h__3_435_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_432_) {
        0 => {
            let mut v_it_436_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_437_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_438_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_435_);
            lean_dec(v_h__2_434_);
            v_it_436_ = lean_ctor_get(v_x_432_, 0);
            lean_inc(v_it_436_);
            v_out_437_ = lean_ctor_get(v_x_432_, 1);
            lean_inc(v_out_437_);
            lean_dec_ref_known(v_x_432_, 2);
            v___x_438_ = lean_apply_2(v_h__1_433_, v_it_436_, v_out_437_);
            return v___x_438_;
        }
        1 => {
            let mut v_it_439_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_440_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_435_);
            lean_dec(v_h__1_433_);
            v_it_439_ = lean_ctor_get(v_x_432_, 0);
            lean_inc(v_it_439_);
            lean_dec_ref_known(v_x_432_, 1);
            v___x_440_ = lean_apply_1(v_h__2_434_, v_it_439_);
            return v___x_440_;
        }
        _ => {
            let mut v___x_441_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_442_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_434_);
            lean_dec(v_h__1_433_);
            v___x_441_ = lean_box(0);
            v___x_442_ = lean_apply_1(v_h__3_435_, v___x_441_);
            return v___x_442_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_IterM_length__eq__match__step_match__1_splitter___redArg(
    mut v_x_443_: *mut LeanObject,
    mut v_h__1_444_: *mut LeanObject,
    mut v_h__2_445_: *mut LeanObject,
    mut v_h__3_446_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_443_) {
        0 => {
            let mut v_it_447_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_448_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_449_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_446_);
            lean_dec(v_h__2_445_);
            v_it_447_ = lean_ctor_get(v_x_443_, 0);
            lean_inc(v_it_447_);
            v_out_448_ = lean_ctor_get(v_x_443_, 1);
            lean_inc(v_out_448_);
            lean_dec_ref_known(v_x_443_, 2);
            v___x_449_ = lean_apply_2(v_h__1_444_, v_it_447_, v_out_448_);
            return v___x_449_;
        }
        1 => {
            let mut v_it_450_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_451_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_446_);
            lean_dec(v_h__1_444_);
            v_it_450_ = lean_ctor_get(v_x_443_, 0);
            lean_inc(v_it_450_);
            lean_dec_ref_known(v_x_443_, 1);
            v___x_451_ = lean_apply_1(v_h__2_445_, v_it_450_);
            return v___x_451_;
        }
        _ => {
            let mut v___x_452_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_453_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_445_);
            lean_dec(v_h__1_444_);
            v___x_452_ = lean_box(0);
            v___x_453_ = lean_apply_1(v_h__3_446_, v___x_452_);
            return v___x_453_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_IterM_length__eq__match__step_match__1_splitter(
    mut v_00_u03b1_454_: *mut LeanObject,
    mut v_00_u03b2_455_: *mut LeanObject,
    mut v_m_456_: *mut LeanObject,
    mut v_motive_457_: *mut LeanObject,
    mut v_x_458_: *mut LeanObject,
    mut v_h__1_459_: *mut LeanObject,
    mut v_h__2_460_: *mut LeanObject,
    mut v_h__3_461_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_458_) {
        0 => {
            let mut v_it_462_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_463_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_464_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_461_);
            lean_dec(v_h__2_460_);
            v_it_462_ = lean_ctor_get(v_x_458_, 0);
            lean_inc(v_it_462_);
            v_out_463_ = lean_ctor_get(v_x_458_, 1);
            lean_inc(v_out_463_);
            lean_dec_ref_known(v_x_458_, 2);
            v___x_464_ = lean_apply_2(v_h__1_459_, v_it_462_, v_out_463_);
            return v___x_464_;
        }
        1 => {
            let mut v_it_465_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_466_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_461_);
            lean_dec(v_h__1_459_);
            v_it_465_ = lean_ctor_get(v_x_458_, 0);
            lean_inc(v_it_465_);
            lean_dec_ref_known(v_x_458_, 1);
            v___x_466_ = lean_apply_1(v_h__2_460_, v_it_465_);
            return v___x_466_;
        }
        _ => {
            let mut v___x_467_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_468_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_460_);
            lean_dec(v_h__1_459_);
            v___x_467_ = lean_box(0);
            v___x_468_ = lean_apply_1(v_h__3_461_, v___x_467_);
            return v___x_468_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iter_findSomeM_x3f_match__1_splitter___redArg(
    mut v_____do__lift_469_: *mut LeanObject,
    mut v_h__1_470_: *mut LeanObject,
    mut v_h__2_471_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_469_) == 0 {
        let mut v___x_472_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_473_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_471_);
        v___x_472_ = lean_box(0);
        v___x_473_ = lean_apply_1(v_h__1_470_, v___x_472_);
        return v___x_473_;
    } else {
        let mut v_val_474_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_475_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_470_);
        v_val_474_ = lean_ctor_get(v_____do__lift_469_, 0);
        lean_inc(v_val_474_);
        lean_dec_ref_known(v_____do__lift_469_, 1);
        v___x_475_ = lean_apply_1(v_h__2_471_, v_val_474_);
        return v___x_475_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iter_findSomeM_x3f_match__1_splitter(
    mut v_00_u03b3_476_: *mut LeanObject,
    mut v_motive_477_: *mut LeanObject,
    mut v_____do__lift_478_: *mut LeanObject,
    mut v_h__1_479_: *mut LeanObject,
    mut v_h__2_480_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_478_) == 0 {
        let mut v___x_481_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_482_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_480_);
        v___x_481_ = lean_box(0);
        v___x_482_ = lean_apply_1(v_h__1_479_, v___x_481_);
        return v___x_482_;
    } else {
        let mut v_val_483_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_484_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_479_);
        v_val_483_ = lean_ctor_get(v_____do__lift_478_, 0);
        lean_inc(v_val_483_);
        lean_dec_ref_known(v_____do__lift_478_, 1);
        v___x_484_ = lean_apply_1(v_h__2_480_, v_val_483_);
        return v___x_484_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iter_findSomeM_x3f__eq__match__step_match__1_splitter___redArg(
    mut v_____do__lift_485_: *mut LeanObject,
    mut v_h__1_486_: *mut LeanObject,
    mut v_h__2_487_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_485_) == 0 {
        let mut v___x_488_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_489_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_487_);
        v___x_488_ = lean_box(0);
        v___x_489_ = lean_apply_1(v_h__1_486_, v___x_488_);
        return v___x_489_;
    } else {
        let mut v_val_490_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_491_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_486_);
        v_val_490_ = lean_ctor_get(v_____do__lift_485_, 0);
        lean_inc(v_val_490_);
        lean_dec_ref_known(v_____do__lift_485_, 1);
        v___x_491_ = lean_apply_1(v_h__2_487_, v_val_490_);
        return v___x_491_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iter_findSomeM_x3f__eq__match__step_match__1_splitter(
    mut v_00_u03b3_492_: *mut LeanObject,
    mut v_motive_493_: *mut LeanObject,
    mut v_____do__lift_494_: *mut LeanObject,
    mut v_h__1_495_: *mut LeanObject,
    mut v_h__2_496_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_494_) == 0 {
        let mut v___x_497_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_498_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_496_);
        v___x_497_ = lean_box(0);
        v___x_498_ = lean_apply_1(v_h__1_495_, v___x_497_);
        return v___x_498_;
    } else {
        let mut v_val_499_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_500_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_495_);
        v_val_499_ = lean_ctor_get(v_____do__lift_494_, 0);
        lean_inc(v_val_499_);
        lean_dec_ref_known(v_____do__lift_494_, 1);
        v___x_500_ = lean_apply_1(v_h__2_496_, v_val_499_);
        return v___x_500_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__List_findSomeM_x3f__cons_match__1_splitter___redArg(
    mut v_____do__lift_501_: *mut LeanObject,
    mut v_h__1_502_: *mut LeanObject,
    mut v_h__2_503_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_501_) == 0 {
        let mut v___x_504_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_505_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_502_);
        v___x_504_ = lean_box(0);
        v___x_505_ = lean_apply_1(v_h__2_503_, v___x_504_);
        return v___x_505_;
    } else {
        let mut v_val_506_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_507_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_503_);
        v_val_506_ = lean_ctor_get(v_____do__lift_501_, 0);
        lean_inc(v_val_506_);
        lean_dec_ref_known(v_____do__lift_501_, 1);
        v___x_507_ = lean_apply_1(v_h__1_502_, v_val_506_);
        return v___x_507_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__List_findSomeM_x3f__cons_match__1_splitter(
    mut v_00_u03b2_508_: *mut LeanObject,
    mut v_motive_509_: *mut LeanObject,
    mut v_____do__lift_510_: *mut LeanObject,
    mut v_h__1_511_: *mut LeanObject,
    mut v_h__2_512_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_510_) == 0 {
        let mut v___x_513_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_514_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_511_);
        v___x_513_ = lean_box(0);
        v___x_514_ = lean_apply_1(v_h__2_512_, v___x_513_);
        return v___x_514_;
    } else {
        let mut v_val_515_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_516_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_512_);
        v_val_515_ = lean_ctor_get(v_____do__lift_510_, 0);
        lean_inc(v_val_515_);
        lean_dec_ref_known(v_____do__lift_510_, 1);
        v___x_516_ = lean_apply_1(v_h__1_511_, v_val_515_);
        return v___x_516_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Loop(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Loop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Collect(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Monadic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Collect(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Monadic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Find(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Iterators_Lemmas_Consumers_Loop(
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
pub unsafe fn initialize_Init_Data_Iterators_Lemmas_Consumers_Loop(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers_Loop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers_Monadic_Collect(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Array_Monadic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers_Collect(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_Monadic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_Find(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Option_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Loop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_Iterators_Lemmas_Consumers_Loop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_Iterators_Lemmas_Consumers_Loop(builtin);
}
