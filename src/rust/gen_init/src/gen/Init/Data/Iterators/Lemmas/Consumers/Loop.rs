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
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iter_forIn_x27__eq__match__step_match__3_splitter___redArg(
    mut v_x_259_: *mut leanh::LeanObject,
    mut v_h__1_260_: *mut leanh::LeanObject,
    mut v_h__2_261_: *mut leanh::LeanObject,
    mut v_h__3_262_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_259_) {
        0 => {
            let mut v_it_263_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_264_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_265_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_262_);
            leanh::lean_dec(v_h__2_261_);
            v_it_263_ = leanh::lean_ctor_get(v_x_259_, 0);
            leanh::lean_inc(v_it_263_);
            v_out_264_ = leanh::lean_ctor_get(v_x_259_, 1);
            leanh::lean_inc(v_out_264_);
            leanh::lean_dec_ref_known(v_x_259_, 2);
            v___x_265_ = leanh::lean_apply_3(
                v_h__1_260_,
                v_it_263_,
                v_out_264_,
                leanh::lean_box(0),
            );
            return v___x_265_;
        }
        1 => {
            let mut v_it_266_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_267_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_262_);
            leanh::lean_dec(v_h__1_260_);
            v_it_266_ = leanh::lean_ctor_get(v_x_259_, 0);
            leanh::lean_inc(v_it_266_);
            leanh::lean_dec_ref_known(v_x_259_, 1);
            v___x_267_ =
                leanh::lean_apply_2(v_h__2_261_, v_it_266_, leanh::lean_box(0));
            return v___x_267_;
        }
        _ => {
            let mut v___x_268_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_261_);
            leanh::lean_dec(v_h__1_260_);
            v___x_268_ = leanh::lean_apply_1(v_h__3_262_, leanh::lean_box(0));
            return v___x_268_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iter_forIn_x27__eq__match__step_match__3_splitter(
    mut v_00_u03b1_269_: *mut leanh::LeanObject,
    mut v_00_u03b2_270_: *mut leanh::LeanObject,
    mut v_inst_271_: *mut leanh::LeanObject,
    mut v_it_272_: *mut leanh::LeanObject,
    mut v_motive_273_: *mut leanh::LeanObject,
    mut v_x_274_: *mut leanh::LeanObject,
    mut v_h__1_275_: *mut leanh::LeanObject,
    mut v_h__2_276_: *mut leanh::LeanObject,
    mut v_h__3_277_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_274_) {
        0 => {
            let mut v_it_278_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_279_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_280_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_277_);
            leanh::lean_dec(v_h__2_276_);
            v_it_278_ = leanh::lean_ctor_get(v_x_274_, 0);
            leanh::lean_inc(v_it_278_);
            v_out_279_ = leanh::lean_ctor_get(v_x_274_, 1);
            leanh::lean_inc(v_out_279_);
            leanh::lean_dec_ref_known(v_x_274_, 2);
            v___x_280_ = leanh::lean_apply_3(
                v_h__1_275_,
                v_it_278_,
                v_out_279_,
                leanh::lean_box(0),
            );
            return v___x_280_;
        }
        1 => {
            let mut v_it_281_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_282_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_277_);
            leanh::lean_dec(v_h__1_275_);
            v_it_281_ = leanh::lean_ctor_get(v_x_274_, 0);
            leanh::lean_inc(v_it_281_);
            leanh::lean_dec_ref_known(v_x_274_, 1);
            v___x_282_ =
                leanh::lean_apply_2(v_h__2_276_, v_it_281_, leanh::lean_box(0));
            return v___x_282_;
        }
        _ => {
            let mut v___x_283_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_276_);
            leanh::lean_dec(v_h__1_275_);
            v___x_283_ = leanh::lean_apply_1(v_h__3_277_, leanh::lean_box(0));
            return v___x_283_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iter_forIn_x27__eq__match__step_match__3_splitter___boxed(
    mut v_00_u03b1_284_: *mut leanh::LeanObject,
    mut v_00_u03b2_285_: *mut leanh::LeanObject,
    mut v_inst_286_: *mut leanh::LeanObject,
    mut v_it_287_: *mut leanh::LeanObject,
    mut v_motive_288_: *mut leanh::LeanObject,
    mut v_x_289_: *mut leanh::LeanObject,
    mut v_h__1_290_: *mut leanh::LeanObject,
    mut v_h__2_291_: *mut leanh::LeanObject,
    mut v_h__3_292_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_293_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_293_ = l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iter_forIn_x27__eq__match__step_match__3_splitter(v_00_u03b1_284_, v_00_u03b2_285_, v_inst_286_, v_it_287_, v_motive_288_, v_x_289_, v_h__1_290_, v_h__2_291_, v_h__3_292_);
    leanh::lean_dec(v_it_287_);
    leanh::lean_dec(v_inst_286_);
    return v_res_293_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iter_forIn_x27__eq__match__step_match__1_splitter___redArg(
    mut v_____do__lift_294_: *mut leanh::LeanObject,
    mut v_h__1_295_: *mut leanh::LeanObject,
    mut v_h__2_296_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_294_) == 0 {
        let mut v_a_297_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_298_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_295_);
        v_a_297_ = leanh::lean_ctor_get(v_____do__lift_294_, 0);
        leanh::lean_inc(v_a_297_);
        leanh::lean_dec_ref_known(v_____do__lift_294_, 1);
        v___x_298_ = leanh::lean_apply_1(v_h__2_296_, v_a_297_);
        return v___x_298_;
    } else {
        let mut v_a_299_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_300_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_296_);
        v_a_299_ = leanh::lean_ctor_get(v_____do__lift_294_, 0);
        leanh::lean_inc(v_a_299_);
        leanh::lean_dec_ref_known(v_____do__lift_294_, 1);
        v___x_300_ = leanh::lean_apply_1(v_h__1_295_, v_a_299_);
        return v___x_300_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iter_forIn_x27__eq__match__step_match__1_splitter(
    mut v_00_u03b3_301_: *mut leanh::LeanObject,
    mut v_motive_302_: *mut leanh::LeanObject,
    mut v_____do__lift_303_: *mut leanh::LeanObject,
    mut v_h__1_304_: *mut leanh::LeanObject,
    mut v_h__2_305_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_303_) == 0 {
        let mut v_a_306_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_307_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_304_);
        v_a_306_ = leanh::lean_ctor_get(v_____do__lift_303_, 0);
        leanh::lean_inc(v_a_306_);
        leanh::lean_dec_ref_known(v_____do__lift_303_, 1);
        v___x_307_ = leanh::lean_apply_1(v_h__2_305_, v_a_306_);
        return v___x_307_;
    } else {
        let mut v_a_308_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_309_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_305_);
        v_a_308_ = leanh::lean_ctor_get(v_____do__lift_303_, 0);
        leanh::lean_inc(v_a_308_);
        leanh::lean_dec_ref_known(v_____do__lift_303_, 1);
        v___x_309_ = leanh::lean_apply_1(v_h__1_304_, v_a_308_);
        return v___x_309_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter___redArg(
    mut v_x_310_: *mut leanh::LeanObject,
    mut v_h__1_311_: *mut leanh::LeanObject,
    mut v_h__2_312_: *mut leanh::LeanObject,
    mut v_h__3_313_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_310_) {
        0 => {
            let mut v_it_314_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_315_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_316_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_313_);
            leanh::lean_dec(v_h__2_312_);
            v_it_314_ = leanh::lean_ctor_get(v_x_310_, 0);
            leanh::lean_inc(v_it_314_);
            v_out_315_ = leanh::lean_ctor_get(v_x_310_, 1);
            leanh::lean_inc(v_out_315_);
            leanh::lean_dec_ref_known(v_x_310_, 2);
            v___x_316_ = leanh::lean_apply_3(
                v_h__1_311_,
                v_it_314_,
                v_out_315_,
                leanh::lean_box(0),
            );
            return v___x_316_;
        }
        1 => {
            let mut v_it_317_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_318_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_313_);
            leanh::lean_dec(v_h__1_311_);
            v_it_317_ = leanh::lean_ctor_get(v_x_310_, 0);
            leanh::lean_inc(v_it_317_);
            leanh::lean_dec_ref_known(v_x_310_, 1);
            v___x_318_ =
                leanh::lean_apply_2(v_h__2_312_, v_it_317_, leanh::lean_box(0));
            return v___x_318_;
        }
        _ => {
            let mut v___x_319_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_312_);
            leanh::lean_dec(v_h__1_311_);
            v___x_319_ = leanh::lean_apply_1(v_h__3_313_, leanh::lean_box(0));
            return v___x_319_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter(
    mut v_00_u03b1_320_: *mut leanh::LeanObject,
    mut v_00_u03b2_321_: *mut leanh::LeanObject,
    mut v_m_322_: *mut leanh::LeanObject,
    mut v_inst_323_: *mut leanh::LeanObject,
    mut v_it_324_: *mut leanh::LeanObject,
    mut v_motive_325_: *mut leanh::LeanObject,
    mut v_x_326_: *mut leanh::LeanObject,
    mut v_h__1_327_: *mut leanh::LeanObject,
    mut v_h__2_328_: *mut leanh::LeanObject,
    mut v_h__3_329_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_326_) {
        0 => {
            let mut v_it_330_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_331_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_332_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_329_);
            leanh::lean_dec(v_h__2_328_);
            v_it_330_ = leanh::lean_ctor_get(v_x_326_, 0);
            leanh::lean_inc(v_it_330_);
            v_out_331_ = leanh::lean_ctor_get(v_x_326_, 1);
            leanh::lean_inc(v_out_331_);
            leanh::lean_dec_ref_known(v_x_326_, 2);
            v___x_332_ = leanh::lean_apply_3(
                v_h__1_327_,
                v_it_330_,
                v_out_331_,
                leanh::lean_box(0),
            );
            return v___x_332_;
        }
        1 => {
            let mut v_it_333_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_334_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_329_);
            leanh::lean_dec(v_h__1_327_);
            v_it_333_ = leanh::lean_ctor_get(v_x_326_, 0);
            leanh::lean_inc(v_it_333_);
            leanh::lean_dec_ref_known(v_x_326_, 1);
            v___x_334_ =
                leanh::lean_apply_2(v_h__2_328_, v_it_333_, leanh::lean_box(0));
            return v___x_334_;
        }
        _ => {
            let mut v___x_335_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_328_);
            leanh::lean_dec(v_h__1_327_);
            v___x_335_ = leanh::lean_apply_1(v_h__3_329_, leanh::lean_box(0));
            return v___x_335_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter___boxed(
    mut v_00_u03b1_336_: *mut leanh::LeanObject,
    mut v_00_u03b2_337_: *mut leanh::LeanObject,
    mut v_m_338_: *mut leanh::LeanObject,
    mut v_inst_339_: *mut leanh::LeanObject,
    mut v_it_340_: *mut leanh::LeanObject,
    mut v_motive_341_: *mut leanh::LeanObject,
    mut v_x_342_: *mut leanh::LeanObject,
    mut v_h__1_343_: *mut leanh::LeanObject,
    mut v_h__2_344_: *mut leanh::LeanObject,
    mut v_h__3_345_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_346_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_346_ = l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter(v_00_u03b1_336_, v_00_u03b2_337_, v_m_338_, v_inst_339_, v_it_340_, v_motive_341_, v_x_342_, v_h__1_343_, v_h__2_344_, v_h__3_345_);
    leanh::lean_dec(v_it_340_);
    leanh::lean_dec(v_inst_339_);
    return v_res_346_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__1_splitter___redArg(
    mut v_____do__lift_347_: *mut leanh::LeanObject,
    mut v_h__1_348_: *mut leanh::LeanObject,
    mut v_h__2_349_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_347_) == 0 {
        let mut v_a_350_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_351_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_348_);
        v_a_350_ = leanh::lean_ctor_get(v_____do__lift_347_, 0);
        leanh::lean_inc(v_a_350_);
        leanh::lean_dec_ref_known(v_____do__lift_347_, 1);
        v___x_351_ = leanh::lean_apply_2(v_h__2_349_, v_a_350_, leanh::lean_box(0));
        return v___x_351_;
    } else {
        let mut v_a_352_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_353_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_349_);
        v_a_352_ = leanh::lean_ctor_get(v_____do__lift_347_, 0);
        leanh::lean_inc(v_a_352_);
        leanh::lean_dec_ref_known(v_____do__lift_347_, 1);
        v___x_353_ = leanh::lean_apply_2(v_h__1_348_, v_a_352_, leanh::lean_box(0));
        return v___x_353_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__1_splitter(
    mut v_00_u03b2_354_: *mut leanh::LeanObject,
    mut v_00_u03b3_355_: *mut leanh::LeanObject,
    mut v_init_356_: *mut leanh::LeanObject,
    mut v_PlausibleForInStep_357_: *mut leanh::LeanObject,
    mut v_out_358_: *mut leanh::LeanObject,
    mut v_motive_359_: *mut leanh::LeanObject,
    mut v_____do__lift_360_: *mut leanh::LeanObject,
    mut v_h__1_361_: *mut leanh::LeanObject,
    mut v_h__2_362_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_360_) == 0 {
        let mut v_a_363_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_364_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_361_);
        v_a_363_ = leanh::lean_ctor_get(v_____do__lift_360_, 0);
        leanh::lean_inc(v_a_363_);
        leanh::lean_dec_ref_known(v_____do__lift_360_, 1);
        v___x_364_ = leanh::lean_apply_2(v_h__2_362_, v_a_363_, leanh::lean_box(0));
        return v___x_364_;
    } else {
        let mut v_a_365_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_366_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_362_);
        v_a_365_ = leanh::lean_ctor_get(v_____do__lift_360_, 0);
        leanh::lean_inc(v_a_365_);
        leanh::lean_dec_ref_known(v_____do__lift_360_, 1);
        v___x_366_ = leanh::lean_apply_2(v_h__1_361_, v_a_365_, leanh::lean_box(0));
        return v___x_366_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__1_splitter___boxed(
    mut v_00_u03b2_367_: *mut leanh::LeanObject,
    mut v_00_u03b3_368_: *mut leanh::LeanObject,
    mut v_init_369_: *mut leanh::LeanObject,
    mut v_PlausibleForInStep_370_: *mut leanh::LeanObject,
    mut v_out_371_: *mut leanh::LeanObject,
    mut v_motive_372_: *mut leanh::LeanObject,
    mut v_____do__lift_373_: *mut leanh::LeanObject,
    mut v_h__1_374_: *mut leanh::LeanObject,
    mut v_h__2_375_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_376_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_376_ = l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__1_splitter(v_00_u03b2_367_, v_00_u03b3_368_, v_init_369_, v_PlausibleForInStep_370_, v_out_371_, v_motive_372_, v_____do__lift_373_, v_h__1_374_, v_h__2_375_);
    leanh::lean_dec(v_out_371_);
    leanh::lean_dec(v_init_369_);
    return v_res_376_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iter_toArray__eq__match__step_match__1_splitter___redArg(
    mut v_x_377_: *mut leanh::LeanObject,
    mut v_h__1_378_: *mut leanh::LeanObject,
    mut v_h__2_379_: *mut leanh::LeanObject,
    mut v_h__3_380_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_377_) {
        0 => {
            let mut v_it_381_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_382_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_383_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_380_);
            leanh::lean_dec(v_h__2_379_);
            v_it_381_ = leanh::lean_ctor_get(v_x_377_, 0);
            leanh::lean_inc(v_it_381_);
            v_out_382_ = leanh::lean_ctor_get(v_x_377_, 1);
            leanh::lean_inc(v_out_382_);
            leanh::lean_dec_ref_known(v_x_377_, 2);
            v___x_383_ = leanh::lean_apply_2(v_h__1_378_, v_it_381_, v_out_382_);
            return v___x_383_;
        }
        1 => {
            let mut v_it_384_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_385_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_380_);
            leanh::lean_dec(v_h__1_378_);
            v_it_384_ = leanh::lean_ctor_get(v_x_377_, 0);
            leanh::lean_inc(v_it_384_);
            leanh::lean_dec_ref_known(v_x_377_, 1);
            v___x_385_ = leanh::lean_apply_1(v_h__2_379_, v_it_384_);
            return v___x_385_;
        }
        _ => {
            let mut v___x_386_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_387_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_379_);
            leanh::lean_dec(v_h__1_378_);
            v___x_386_ = leanh::lean_box(0);
            v___x_387_ = leanh::lean_apply_1(v_h__3_380_, v___x_386_);
            return v___x_387_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iter_toArray__eq__match__step_match__1_splitter(
    mut v_00_u03b1_388_: *mut leanh::LeanObject,
    mut v_00_u03b2_389_: *mut leanh::LeanObject,
    mut v_motive_390_: *mut leanh::LeanObject,
    mut v_x_391_: *mut leanh::LeanObject,
    mut v_h__1_392_: *mut leanh::LeanObject,
    mut v_h__2_393_: *mut leanh::LeanObject,
    mut v_h__3_394_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_391_) {
        0 => {
            let mut v_it_395_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_396_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_397_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_394_);
            leanh::lean_dec(v_h__2_393_);
            v_it_395_ = leanh::lean_ctor_get(v_x_391_, 0);
            leanh::lean_inc(v_it_395_);
            v_out_396_ = leanh::lean_ctor_get(v_x_391_, 1);
            leanh::lean_inc(v_out_396_);
            leanh::lean_dec_ref_known(v_x_391_, 2);
            v___x_397_ = leanh::lean_apply_2(v_h__1_392_, v_it_395_, v_out_396_);
            return v___x_397_;
        }
        1 => {
            let mut v_it_398_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_399_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_394_);
            leanh::lean_dec(v_h__1_392_);
            v_it_398_ = leanh::lean_ctor_get(v_x_391_, 0);
            leanh::lean_inc(v_it_398_);
            leanh::lean_dec_ref_known(v_x_391_, 1);
            v___x_399_ = leanh::lean_apply_1(v_h__2_393_, v_it_398_);
            return v___x_399_;
        }
        _ => {
            let mut v___x_400_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_401_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_393_);
            leanh::lean_dec(v_h__1_392_);
            v___x_400_ = leanh::lean_box(0);
            v___x_401_ = leanh::lean_apply_1(v_h__3_394_, v___x_400_);
            return v___x_401_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__List_forIn_x27__eq__foldlM_match__1_splitter___redArg(
    mut v_b_402_: *mut leanh::LeanObject,
    mut v_h__1_403_: *mut leanh::LeanObject,
    mut v_h__2_404_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_b_402_) == 0 {
        let mut v_a_405_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_406_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_403_);
        v_a_405_ = leanh::lean_ctor_get(v_b_402_, 0);
        leanh::lean_inc(v_a_405_);
        leanh::lean_dec_ref_known(v_b_402_, 1);
        v___x_406_ = leanh::lean_apply_1(v_h__2_404_, v_a_405_);
        return v___x_406_;
    } else {
        let mut v_a_407_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_408_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_404_);
        v_a_407_ = leanh::lean_ctor_get(v_b_402_, 0);
        leanh::lean_inc(v_a_407_);
        leanh::lean_dec_ref_known(v_b_402_, 1);
        v___x_408_ = leanh::lean_apply_1(v_h__1_403_, v_a_407_);
        return v___x_408_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__List_forIn_x27__eq__foldlM_match__1_splitter(
    mut v_00_u03b2_409_: *mut leanh::LeanObject,
    mut v_motive_410_: *mut leanh::LeanObject,
    mut v_b_411_: *mut leanh::LeanObject,
    mut v_h__1_412_: *mut leanh::LeanObject,
    mut v_h__2_413_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_b_411_) == 0 {
        let mut v_a_414_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_415_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_412_);
        v_a_414_ = leanh::lean_ctor_get(v_b_411_, 0);
        leanh::lean_inc(v_a_414_);
        leanh::lean_dec_ref_known(v_b_411_, 1);
        v___x_415_ = leanh::lean_apply_1(v_h__2_413_, v_a_414_);
        return v___x_415_;
    } else {
        let mut v_a_416_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_417_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_413_);
        v_a_416_ = leanh::lean_ctor_get(v_b_411_, 0);
        leanh::lean_inc(v_a_416_);
        leanh::lean_dec_ref_known(v_b_411_, 1);
        v___x_417_ = leanh::lean_apply_1(v_h__1_412_, v_a_416_);
        return v___x_417_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iter_length__eq__match__step_match__1_splitter___redArg(
    mut v_x_418_: *mut leanh::LeanObject,
    mut v_h__1_419_: *mut leanh::LeanObject,
    mut v_h__2_420_: *mut leanh::LeanObject,
    mut v_h__3_421_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_418_) {
        0 => {
            let mut v_it_422_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_423_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_424_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_421_);
            leanh::lean_dec(v_h__2_420_);
            v_it_422_ = leanh::lean_ctor_get(v_x_418_, 0);
            leanh::lean_inc(v_it_422_);
            v_out_423_ = leanh::lean_ctor_get(v_x_418_, 1);
            leanh::lean_inc(v_out_423_);
            leanh::lean_dec_ref_known(v_x_418_, 2);
            v___x_424_ = leanh::lean_apply_2(v_h__1_419_, v_it_422_, v_out_423_);
            return v___x_424_;
        }
        1 => {
            let mut v_it_425_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_426_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_421_);
            leanh::lean_dec(v_h__1_419_);
            v_it_425_ = leanh::lean_ctor_get(v_x_418_, 0);
            leanh::lean_inc(v_it_425_);
            leanh::lean_dec_ref_known(v_x_418_, 1);
            v___x_426_ = leanh::lean_apply_1(v_h__2_420_, v_it_425_);
            return v___x_426_;
        }
        _ => {
            let mut v___x_427_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_428_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_420_);
            leanh::lean_dec(v_h__1_419_);
            v___x_427_ = leanh::lean_box(0);
            v___x_428_ = leanh::lean_apply_1(v_h__3_421_, v___x_427_);
            return v___x_428_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iter_length__eq__match__step_match__1_splitter(
    mut v_00_u03b1_429_: *mut leanh::LeanObject,
    mut v_00_u03b2_430_: *mut leanh::LeanObject,
    mut v_motive_431_: *mut leanh::LeanObject,
    mut v_x_432_: *mut leanh::LeanObject,
    mut v_h__1_433_: *mut leanh::LeanObject,
    mut v_h__2_434_: *mut leanh::LeanObject,
    mut v_h__3_435_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_432_) {
        0 => {
            let mut v_it_436_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_437_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_438_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_435_);
            leanh::lean_dec(v_h__2_434_);
            v_it_436_ = leanh::lean_ctor_get(v_x_432_, 0);
            leanh::lean_inc(v_it_436_);
            v_out_437_ = leanh::lean_ctor_get(v_x_432_, 1);
            leanh::lean_inc(v_out_437_);
            leanh::lean_dec_ref_known(v_x_432_, 2);
            v___x_438_ = leanh::lean_apply_2(v_h__1_433_, v_it_436_, v_out_437_);
            return v___x_438_;
        }
        1 => {
            let mut v_it_439_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_440_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_435_);
            leanh::lean_dec(v_h__1_433_);
            v_it_439_ = leanh::lean_ctor_get(v_x_432_, 0);
            leanh::lean_inc(v_it_439_);
            leanh::lean_dec_ref_known(v_x_432_, 1);
            v___x_440_ = leanh::lean_apply_1(v_h__2_434_, v_it_439_);
            return v___x_440_;
        }
        _ => {
            let mut v___x_441_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_442_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_434_);
            leanh::lean_dec(v_h__1_433_);
            v___x_441_ = leanh::lean_box(0);
            v___x_442_ = leanh::lean_apply_1(v_h__3_435_, v___x_441_);
            return v___x_442_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_IterM_length__eq__match__step_match__1_splitter___redArg(
    mut v_x_443_: *mut leanh::LeanObject,
    mut v_h__1_444_: *mut leanh::LeanObject,
    mut v_h__2_445_: *mut leanh::LeanObject,
    mut v_h__3_446_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_443_) {
        0 => {
            let mut v_it_447_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_448_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_449_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_446_);
            leanh::lean_dec(v_h__2_445_);
            v_it_447_ = leanh::lean_ctor_get(v_x_443_, 0);
            leanh::lean_inc(v_it_447_);
            v_out_448_ = leanh::lean_ctor_get(v_x_443_, 1);
            leanh::lean_inc(v_out_448_);
            leanh::lean_dec_ref_known(v_x_443_, 2);
            v___x_449_ = leanh::lean_apply_2(v_h__1_444_, v_it_447_, v_out_448_);
            return v___x_449_;
        }
        1 => {
            let mut v_it_450_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_451_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_446_);
            leanh::lean_dec(v_h__1_444_);
            v_it_450_ = leanh::lean_ctor_get(v_x_443_, 0);
            leanh::lean_inc(v_it_450_);
            leanh::lean_dec_ref_known(v_x_443_, 1);
            v___x_451_ = leanh::lean_apply_1(v_h__2_445_, v_it_450_);
            return v___x_451_;
        }
        _ => {
            let mut v___x_452_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_453_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_445_);
            leanh::lean_dec(v_h__1_444_);
            v___x_452_ = leanh::lean_box(0);
            v___x_453_ = leanh::lean_apply_1(v_h__3_446_, v___x_452_);
            return v___x_453_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_IterM_length__eq__match__step_match__1_splitter(
    mut v_00_u03b1_454_: *mut leanh::LeanObject,
    mut v_00_u03b2_455_: *mut leanh::LeanObject,
    mut v_m_456_: *mut leanh::LeanObject,
    mut v_motive_457_: *mut leanh::LeanObject,
    mut v_x_458_: *mut leanh::LeanObject,
    mut v_h__1_459_: *mut leanh::LeanObject,
    mut v_h__2_460_: *mut leanh::LeanObject,
    mut v_h__3_461_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_458_) {
        0 => {
            let mut v_it_462_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_463_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_464_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_461_);
            leanh::lean_dec(v_h__2_460_);
            v_it_462_ = leanh::lean_ctor_get(v_x_458_, 0);
            leanh::lean_inc(v_it_462_);
            v_out_463_ = leanh::lean_ctor_get(v_x_458_, 1);
            leanh::lean_inc(v_out_463_);
            leanh::lean_dec_ref_known(v_x_458_, 2);
            v___x_464_ = leanh::lean_apply_2(v_h__1_459_, v_it_462_, v_out_463_);
            return v___x_464_;
        }
        1 => {
            let mut v_it_465_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_466_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_461_);
            leanh::lean_dec(v_h__1_459_);
            v_it_465_ = leanh::lean_ctor_get(v_x_458_, 0);
            leanh::lean_inc(v_it_465_);
            leanh::lean_dec_ref_known(v_x_458_, 1);
            v___x_466_ = leanh::lean_apply_1(v_h__2_460_, v_it_465_);
            return v___x_466_;
        }
        _ => {
            let mut v___x_467_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_468_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_460_);
            leanh::lean_dec(v_h__1_459_);
            v___x_467_ = leanh::lean_box(0);
            v___x_468_ = leanh::lean_apply_1(v_h__3_461_, v___x_467_);
            return v___x_468_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iter_findSomeM_x3f_match__1_splitter___redArg(
    mut v_____do__lift_469_: *mut leanh::LeanObject,
    mut v_h__1_470_: *mut leanh::LeanObject,
    mut v_h__2_471_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_469_) == 0 {
        let mut v___x_472_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_473_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_471_);
        v___x_472_ = leanh::lean_box(0);
        v___x_473_ = leanh::lean_apply_1(v_h__1_470_, v___x_472_);
        return v___x_473_;
    } else {
        let mut v_val_474_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_475_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_470_);
        v_val_474_ = leanh::lean_ctor_get(v_____do__lift_469_, 0);
        leanh::lean_inc(v_val_474_);
        leanh::lean_dec_ref_known(v_____do__lift_469_, 1);
        v___x_475_ = leanh::lean_apply_1(v_h__2_471_, v_val_474_);
        return v___x_475_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iter_findSomeM_x3f_match__1_splitter(
    mut v_00_u03b3_476_: *mut leanh::LeanObject,
    mut v_motive_477_: *mut leanh::LeanObject,
    mut v_____do__lift_478_: *mut leanh::LeanObject,
    mut v_h__1_479_: *mut leanh::LeanObject,
    mut v_h__2_480_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_478_) == 0 {
        let mut v___x_481_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_482_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_480_);
        v___x_481_ = leanh::lean_box(0);
        v___x_482_ = leanh::lean_apply_1(v_h__1_479_, v___x_481_);
        return v___x_482_;
    } else {
        let mut v_val_483_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_484_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_479_);
        v_val_483_ = leanh::lean_ctor_get(v_____do__lift_478_, 0);
        leanh::lean_inc(v_val_483_);
        leanh::lean_dec_ref_known(v_____do__lift_478_, 1);
        v___x_484_ = leanh::lean_apply_1(v_h__2_480_, v_val_483_);
        return v___x_484_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iter_findSomeM_x3f__eq__match__step_match__1_splitter___redArg(
    mut v_____do__lift_485_: *mut leanh::LeanObject,
    mut v_h__1_486_: *mut leanh::LeanObject,
    mut v_h__2_487_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_485_) == 0 {
        let mut v___x_488_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_489_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_487_);
        v___x_488_ = leanh::lean_box(0);
        v___x_489_ = leanh::lean_apply_1(v_h__1_486_, v___x_488_);
        return v___x_489_;
    } else {
        let mut v_val_490_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_491_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_486_);
        v_val_490_ = leanh::lean_ctor_get(v_____do__lift_485_, 0);
        leanh::lean_inc(v_val_490_);
        leanh::lean_dec_ref_known(v_____do__lift_485_, 1);
        v___x_491_ = leanh::lean_apply_1(v_h__2_487_, v_val_490_);
        return v___x_491_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iter_findSomeM_x3f__eq__match__step_match__1_splitter(
    mut v_00_u03b3_492_: *mut leanh::LeanObject,
    mut v_motive_493_: *mut leanh::LeanObject,
    mut v_____do__lift_494_: *mut leanh::LeanObject,
    mut v_h__1_495_: *mut leanh::LeanObject,
    mut v_h__2_496_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_494_) == 0 {
        let mut v___x_497_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_498_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_496_);
        v___x_497_ = leanh::lean_box(0);
        v___x_498_ = leanh::lean_apply_1(v_h__1_495_, v___x_497_);
        return v___x_498_;
    } else {
        let mut v_val_499_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_500_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_495_);
        v_val_499_ = leanh::lean_ctor_get(v_____do__lift_494_, 0);
        leanh::lean_inc(v_val_499_);
        leanh::lean_dec_ref_known(v_____do__lift_494_, 1);
        v___x_500_ = leanh::lean_apply_1(v_h__2_496_, v_val_499_);
        return v___x_500_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__List_findSomeM_x3f__cons_match__1_splitter___redArg(
    mut v_____do__lift_501_: *mut leanh::LeanObject,
    mut v_h__1_502_: *mut leanh::LeanObject,
    mut v_h__2_503_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_501_) == 0 {
        let mut v___x_504_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_505_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_502_);
        v___x_504_ = leanh::lean_box(0);
        v___x_505_ = leanh::lean_apply_1(v_h__2_503_, v___x_504_);
        return v___x_505_;
    } else {
        let mut v_val_506_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_507_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_503_);
        v_val_506_ = leanh::lean_ctor_get(v_____do__lift_501_, 0);
        leanh::lean_inc(v_val_506_);
        leanh::lean_dec_ref_known(v_____do__lift_501_, 1);
        v___x_507_ = leanh::lean_apply_1(v_h__1_502_, v_val_506_);
        return v___x_507_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__List_findSomeM_x3f__cons_match__1_splitter(
    mut v_00_u03b2_508_: *mut leanh::LeanObject,
    mut v_motive_509_: *mut leanh::LeanObject,
    mut v_____do__lift_510_: *mut leanh::LeanObject,
    mut v_h__1_511_: *mut leanh::LeanObject,
    mut v_h__2_512_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_510_) == 0 {
        let mut v___x_513_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_514_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_511_);
        v___x_513_ = leanh::lean_box(0);
        v___x_514_ = leanh::lean_apply_1(v_h__2_512_, v___x_513_);
        return v___x_514_;
    } else {
        let mut v_val_515_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_516_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_512_);
        v_val_515_ = leanh::lean_ctor_get(v_____do__lift_510_, 0);
        leanh::lean_inc(v_val_515_);
        leanh::lean_dec_ref_known(v_____do__lift_510_, 1);
        v___x_516_ = leanh::lean_apply_1(v_h__1_511_, v_val_515_);
        return v___x_516_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Loop(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Loop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Collect(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Monadic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Collect(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Loop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Monadic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Find(builtin);
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
pub unsafe fn meta_initialize_Init_Data_Iterators_Lemmas_Consumers_Loop(
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
pub unsafe fn initialize_Init_Data_Iterators_Lemmas_Consumers_Loop(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers_Loop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers_Monadic_Collect(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_Monadic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers_Collect(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers_Loop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Monadic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Find(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Option_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Loop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Iterators_Lemmas_Consumers_Loop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_Iterators_Lemmas_Consumers_Loop(builtin);
}