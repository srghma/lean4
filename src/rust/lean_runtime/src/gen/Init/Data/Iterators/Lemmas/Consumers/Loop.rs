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
    mut v_x_259_: *mut crate::leanh::LeanObject,
    mut v_h__1_260_: *mut crate::leanh::LeanObject,
    mut v_h__2_261_: *mut crate::leanh::LeanObject,
    mut v_h__3_262_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_259_) {
        0 => {
            let mut v_it_263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_262_);
            crate::leanh::lean_dec(v_h__2_261_);
            v_it_263_ = crate::leanh::lean_ctor_get(v_x_259_, 0);
            crate::leanh::lean_inc(v_it_263_);
            v_out_264_ = crate::leanh::lean_ctor_get(v_x_259_, 1);
            crate::leanh::lean_inc(v_out_264_);
            crate::leanh::lean_dec_ref_known(v_x_259_, 2);
            v___x_265_ = crate::leanh::lean_apply_3(
                v_h__1_260_,
                v_it_263_,
                v_out_264_,
                crate::leanh::lean_box(0),
            );
            return v___x_265_;
        }
        1 => {
            let mut v_it_266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_262_);
            crate::leanh::lean_dec(v_h__1_260_);
            v_it_266_ = crate::leanh::lean_ctor_get(v_x_259_, 0);
            crate::leanh::lean_inc(v_it_266_);
            crate::leanh::lean_dec_ref_known(v_x_259_, 1);
            v___x_267_ =
                crate::leanh::lean_apply_2(v_h__2_261_, v_it_266_, crate::leanh::lean_box(0));
            return v___x_267_;
        }
        _ => {
            let mut v___x_268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_261_);
            crate::leanh::lean_dec(v_h__1_260_);
            v___x_268_ = crate::leanh::lean_apply_1(v_h__3_262_, crate::leanh::lean_box(0));
            return v___x_268_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iter_forIn_x27__eq__match__step_match__3_splitter(
    mut v_00_u03b1_269_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_270_: *mut crate::leanh::LeanObject,
    mut v_inst_271_: *mut crate::leanh::LeanObject,
    mut v_it_272_: *mut crate::leanh::LeanObject,
    mut v_motive_273_: *mut crate::leanh::LeanObject,
    mut v_x_274_: *mut crate::leanh::LeanObject,
    mut v_h__1_275_: *mut crate::leanh::LeanObject,
    mut v_h__2_276_: *mut crate::leanh::LeanObject,
    mut v_h__3_277_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_274_) {
        0 => {
            let mut v_it_278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_277_);
            crate::leanh::lean_dec(v_h__2_276_);
            v_it_278_ = crate::leanh::lean_ctor_get(v_x_274_, 0);
            crate::leanh::lean_inc(v_it_278_);
            v_out_279_ = crate::leanh::lean_ctor_get(v_x_274_, 1);
            crate::leanh::lean_inc(v_out_279_);
            crate::leanh::lean_dec_ref_known(v_x_274_, 2);
            v___x_280_ = crate::leanh::lean_apply_3(
                v_h__1_275_,
                v_it_278_,
                v_out_279_,
                crate::leanh::lean_box(0),
            );
            return v___x_280_;
        }
        1 => {
            let mut v_it_281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_277_);
            crate::leanh::lean_dec(v_h__1_275_);
            v_it_281_ = crate::leanh::lean_ctor_get(v_x_274_, 0);
            crate::leanh::lean_inc(v_it_281_);
            crate::leanh::lean_dec_ref_known(v_x_274_, 1);
            v___x_282_ =
                crate::leanh::lean_apply_2(v_h__2_276_, v_it_281_, crate::leanh::lean_box(0));
            return v___x_282_;
        }
        _ => {
            let mut v___x_283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_276_);
            crate::leanh::lean_dec(v_h__1_275_);
            v___x_283_ = crate::leanh::lean_apply_1(v_h__3_277_, crate::leanh::lean_box(0));
            return v___x_283_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iter_forIn_x27__eq__match__step_match__3_splitter___boxed(
    mut v_00_u03b1_284_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_285_: *mut crate::leanh::LeanObject,
    mut v_inst_286_: *mut crate::leanh::LeanObject,
    mut v_it_287_: *mut crate::leanh::LeanObject,
    mut v_motive_288_: *mut crate::leanh::LeanObject,
    mut v_x_289_: *mut crate::leanh::LeanObject,
    mut v_h__1_290_: *mut crate::leanh::LeanObject,
    mut v_h__2_291_: *mut crate::leanh::LeanObject,
    mut v_h__3_292_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_293_ = l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iter_forIn_x27__eq__match__step_match__3_splitter(v_00_u03b1_284_, v_00_u03b2_285_, v_inst_286_, v_it_287_, v_motive_288_, v_x_289_, v_h__1_290_, v_h__2_291_, v_h__3_292_);
    crate::leanh::lean_dec(v_it_287_);
    crate::leanh::lean_dec(v_inst_286_);
    return v_res_293_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iter_forIn_x27__eq__match__step_match__1_splitter___redArg(
    mut v_____do__lift_294_: *mut crate::leanh::LeanObject,
    mut v_h__1_295_: *mut crate::leanh::LeanObject,
    mut v_h__2_296_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_294_) == 0 {
        let mut v_a_297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_295_);
        v_a_297_ = crate::leanh::lean_ctor_get(v_____do__lift_294_, 0);
        crate::leanh::lean_inc(v_a_297_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_294_, 1);
        v___x_298_ = crate::leanh::lean_apply_1(v_h__2_296_, v_a_297_);
        return v___x_298_;
    } else {
        let mut v_a_299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_296_);
        v_a_299_ = crate::leanh::lean_ctor_get(v_____do__lift_294_, 0);
        crate::leanh::lean_inc(v_a_299_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_294_, 1);
        v___x_300_ = crate::leanh::lean_apply_1(v_h__1_295_, v_a_299_);
        return v___x_300_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iter_forIn_x27__eq__match__step_match__1_splitter(
    mut v_00_u03b3_301_: *mut crate::leanh::LeanObject,
    mut v_motive_302_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_303_: *mut crate::leanh::LeanObject,
    mut v_h__1_304_: *mut crate::leanh::LeanObject,
    mut v_h__2_305_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_303_) == 0 {
        let mut v_a_306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_304_);
        v_a_306_ = crate::leanh::lean_ctor_get(v_____do__lift_303_, 0);
        crate::leanh::lean_inc(v_a_306_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_303_, 1);
        v___x_307_ = crate::leanh::lean_apply_1(v_h__2_305_, v_a_306_);
        return v___x_307_;
    } else {
        let mut v_a_308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_305_);
        v_a_308_ = crate::leanh::lean_ctor_get(v_____do__lift_303_, 0);
        crate::leanh::lean_inc(v_a_308_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_303_, 1);
        v___x_309_ = crate::leanh::lean_apply_1(v_h__1_304_, v_a_308_);
        return v___x_309_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter___redArg(
    mut v_x_310_: *mut crate::leanh::LeanObject,
    mut v_h__1_311_: *mut crate::leanh::LeanObject,
    mut v_h__2_312_: *mut crate::leanh::LeanObject,
    mut v_h__3_313_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_310_) {
        0 => {
            let mut v_it_314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_313_);
            crate::leanh::lean_dec(v_h__2_312_);
            v_it_314_ = crate::leanh::lean_ctor_get(v_x_310_, 0);
            crate::leanh::lean_inc(v_it_314_);
            v_out_315_ = crate::leanh::lean_ctor_get(v_x_310_, 1);
            crate::leanh::lean_inc(v_out_315_);
            crate::leanh::lean_dec_ref_known(v_x_310_, 2);
            v___x_316_ = crate::leanh::lean_apply_3(
                v_h__1_311_,
                v_it_314_,
                v_out_315_,
                crate::leanh::lean_box(0),
            );
            return v___x_316_;
        }
        1 => {
            let mut v_it_317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_313_);
            crate::leanh::lean_dec(v_h__1_311_);
            v_it_317_ = crate::leanh::lean_ctor_get(v_x_310_, 0);
            crate::leanh::lean_inc(v_it_317_);
            crate::leanh::lean_dec_ref_known(v_x_310_, 1);
            v___x_318_ =
                crate::leanh::lean_apply_2(v_h__2_312_, v_it_317_, crate::leanh::lean_box(0));
            return v___x_318_;
        }
        _ => {
            let mut v___x_319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_312_);
            crate::leanh::lean_dec(v_h__1_311_);
            v___x_319_ = crate::leanh::lean_apply_1(v_h__3_313_, crate::leanh::lean_box(0));
            return v___x_319_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter(
    mut v_00_u03b1_320_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_321_: *mut crate::leanh::LeanObject,
    mut v_m_322_: *mut crate::leanh::LeanObject,
    mut v_inst_323_: *mut crate::leanh::LeanObject,
    mut v_it_324_: *mut crate::leanh::LeanObject,
    mut v_motive_325_: *mut crate::leanh::LeanObject,
    mut v_x_326_: *mut crate::leanh::LeanObject,
    mut v_h__1_327_: *mut crate::leanh::LeanObject,
    mut v_h__2_328_: *mut crate::leanh::LeanObject,
    mut v_h__3_329_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_326_) {
        0 => {
            let mut v_it_330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_329_);
            crate::leanh::lean_dec(v_h__2_328_);
            v_it_330_ = crate::leanh::lean_ctor_get(v_x_326_, 0);
            crate::leanh::lean_inc(v_it_330_);
            v_out_331_ = crate::leanh::lean_ctor_get(v_x_326_, 1);
            crate::leanh::lean_inc(v_out_331_);
            crate::leanh::lean_dec_ref_known(v_x_326_, 2);
            v___x_332_ = crate::leanh::lean_apply_3(
                v_h__1_327_,
                v_it_330_,
                v_out_331_,
                crate::leanh::lean_box(0),
            );
            return v___x_332_;
        }
        1 => {
            let mut v_it_333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_329_);
            crate::leanh::lean_dec(v_h__1_327_);
            v_it_333_ = crate::leanh::lean_ctor_get(v_x_326_, 0);
            crate::leanh::lean_inc(v_it_333_);
            crate::leanh::lean_dec_ref_known(v_x_326_, 1);
            v___x_334_ =
                crate::leanh::lean_apply_2(v_h__2_328_, v_it_333_, crate::leanh::lean_box(0));
            return v___x_334_;
        }
        _ => {
            let mut v___x_335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_328_);
            crate::leanh::lean_dec(v_h__1_327_);
            v___x_335_ = crate::leanh::lean_apply_1(v_h__3_329_, crate::leanh::lean_box(0));
            return v___x_335_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter___boxed(
    mut v_00_u03b1_336_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_337_: *mut crate::leanh::LeanObject,
    mut v_m_338_: *mut crate::leanh::LeanObject,
    mut v_inst_339_: *mut crate::leanh::LeanObject,
    mut v_it_340_: *mut crate::leanh::LeanObject,
    mut v_motive_341_: *mut crate::leanh::LeanObject,
    mut v_x_342_: *mut crate::leanh::LeanObject,
    mut v_h__1_343_: *mut crate::leanh::LeanObject,
    mut v_h__2_344_: *mut crate::leanh::LeanObject,
    mut v_h__3_345_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_346_ = l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter(v_00_u03b1_336_, v_00_u03b2_337_, v_m_338_, v_inst_339_, v_it_340_, v_motive_341_, v_x_342_, v_h__1_343_, v_h__2_344_, v_h__3_345_);
    crate::leanh::lean_dec(v_it_340_);
    crate::leanh::lean_dec(v_inst_339_);
    return v_res_346_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__1_splitter___redArg(
    mut v_____do__lift_347_: *mut crate::leanh::LeanObject,
    mut v_h__1_348_: *mut crate::leanh::LeanObject,
    mut v_h__2_349_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_347_) == 0 {
        let mut v_a_350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_348_);
        v_a_350_ = crate::leanh::lean_ctor_get(v_____do__lift_347_, 0);
        crate::leanh::lean_inc(v_a_350_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_347_, 1);
        v___x_351_ = crate::leanh::lean_apply_2(v_h__2_349_, v_a_350_, crate::leanh::lean_box(0));
        return v___x_351_;
    } else {
        let mut v_a_352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_349_);
        v_a_352_ = crate::leanh::lean_ctor_get(v_____do__lift_347_, 0);
        crate::leanh::lean_inc(v_a_352_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_347_, 1);
        v___x_353_ = crate::leanh::lean_apply_2(v_h__1_348_, v_a_352_, crate::leanh::lean_box(0));
        return v___x_353_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__1_splitter(
    mut v_00_u03b2_354_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_355_: *mut crate::leanh::LeanObject,
    mut v_init_356_: *mut crate::leanh::LeanObject,
    mut v_PlausibleForInStep_357_: *mut crate::leanh::LeanObject,
    mut v_out_358_: *mut crate::leanh::LeanObject,
    mut v_motive_359_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_360_: *mut crate::leanh::LeanObject,
    mut v_h__1_361_: *mut crate::leanh::LeanObject,
    mut v_h__2_362_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_360_) == 0 {
        let mut v_a_363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_361_);
        v_a_363_ = crate::leanh::lean_ctor_get(v_____do__lift_360_, 0);
        crate::leanh::lean_inc(v_a_363_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_360_, 1);
        v___x_364_ = crate::leanh::lean_apply_2(v_h__2_362_, v_a_363_, crate::leanh::lean_box(0));
        return v___x_364_;
    } else {
        let mut v_a_365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_362_);
        v_a_365_ = crate::leanh::lean_ctor_get(v_____do__lift_360_, 0);
        crate::leanh::lean_inc(v_a_365_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_360_, 1);
        v___x_366_ = crate::leanh::lean_apply_2(v_h__1_361_, v_a_365_, crate::leanh::lean_box(0));
        return v___x_366_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__1_splitter___boxed(
    mut v_00_u03b2_367_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_368_: *mut crate::leanh::LeanObject,
    mut v_init_369_: *mut crate::leanh::LeanObject,
    mut v_PlausibleForInStep_370_: *mut crate::leanh::LeanObject,
    mut v_out_371_: *mut crate::leanh::LeanObject,
    mut v_motive_372_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_373_: *mut crate::leanh::LeanObject,
    mut v_h__1_374_: *mut crate::leanh::LeanObject,
    mut v_h__2_375_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_376_ = l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__1_splitter(v_00_u03b2_367_, v_00_u03b3_368_, v_init_369_, v_PlausibleForInStep_370_, v_out_371_, v_motive_372_, v_____do__lift_373_, v_h__1_374_, v_h__2_375_);
    crate::leanh::lean_dec(v_out_371_);
    crate::leanh::lean_dec(v_init_369_);
    return v_res_376_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iter_toArray__eq__match__step_match__1_splitter___redArg(
    mut v_x_377_: *mut crate::leanh::LeanObject,
    mut v_h__1_378_: *mut crate::leanh::LeanObject,
    mut v_h__2_379_: *mut crate::leanh::LeanObject,
    mut v_h__3_380_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_377_) {
        0 => {
            let mut v_it_381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_380_);
            crate::leanh::lean_dec(v_h__2_379_);
            v_it_381_ = crate::leanh::lean_ctor_get(v_x_377_, 0);
            crate::leanh::lean_inc(v_it_381_);
            v_out_382_ = crate::leanh::lean_ctor_get(v_x_377_, 1);
            crate::leanh::lean_inc(v_out_382_);
            crate::leanh::lean_dec_ref_known(v_x_377_, 2);
            v___x_383_ = crate::leanh::lean_apply_2(v_h__1_378_, v_it_381_, v_out_382_);
            return v___x_383_;
        }
        1 => {
            let mut v_it_384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_380_);
            crate::leanh::lean_dec(v_h__1_378_);
            v_it_384_ = crate::leanh::lean_ctor_get(v_x_377_, 0);
            crate::leanh::lean_inc(v_it_384_);
            crate::leanh::lean_dec_ref_known(v_x_377_, 1);
            v___x_385_ = crate::leanh::lean_apply_1(v_h__2_379_, v_it_384_);
            return v___x_385_;
        }
        _ => {
            let mut v___x_386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_379_);
            crate::leanh::lean_dec(v_h__1_378_);
            v___x_386_ = crate::leanh::lean_box(0);
            v___x_387_ = crate::leanh::lean_apply_1(v_h__3_380_, v___x_386_);
            return v___x_387_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iter_toArray__eq__match__step_match__1_splitter(
    mut v_00_u03b1_388_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_389_: *mut crate::leanh::LeanObject,
    mut v_motive_390_: *mut crate::leanh::LeanObject,
    mut v_x_391_: *mut crate::leanh::LeanObject,
    mut v_h__1_392_: *mut crate::leanh::LeanObject,
    mut v_h__2_393_: *mut crate::leanh::LeanObject,
    mut v_h__3_394_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_391_) {
        0 => {
            let mut v_it_395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_394_);
            crate::leanh::lean_dec(v_h__2_393_);
            v_it_395_ = crate::leanh::lean_ctor_get(v_x_391_, 0);
            crate::leanh::lean_inc(v_it_395_);
            v_out_396_ = crate::leanh::lean_ctor_get(v_x_391_, 1);
            crate::leanh::lean_inc(v_out_396_);
            crate::leanh::lean_dec_ref_known(v_x_391_, 2);
            v___x_397_ = crate::leanh::lean_apply_2(v_h__1_392_, v_it_395_, v_out_396_);
            return v___x_397_;
        }
        1 => {
            let mut v_it_398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_394_);
            crate::leanh::lean_dec(v_h__1_392_);
            v_it_398_ = crate::leanh::lean_ctor_get(v_x_391_, 0);
            crate::leanh::lean_inc(v_it_398_);
            crate::leanh::lean_dec_ref_known(v_x_391_, 1);
            v___x_399_ = crate::leanh::lean_apply_1(v_h__2_393_, v_it_398_);
            return v___x_399_;
        }
        _ => {
            let mut v___x_400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_393_);
            crate::leanh::lean_dec(v_h__1_392_);
            v___x_400_ = crate::leanh::lean_box(0);
            v___x_401_ = crate::leanh::lean_apply_1(v_h__3_394_, v___x_400_);
            return v___x_401_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__List_forIn_x27__eq__foldlM_match__1_splitter___redArg(
    mut v_b_402_: *mut crate::leanh::LeanObject,
    mut v_h__1_403_: *mut crate::leanh::LeanObject,
    mut v_h__2_404_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_b_402_) == 0 {
        let mut v_a_405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_403_);
        v_a_405_ = crate::leanh::lean_ctor_get(v_b_402_, 0);
        crate::leanh::lean_inc(v_a_405_);
        crate::leanh::lean_dec_ref_known(v_b_402_, 1);
        v___x_406_ = crate::leanh::lean_apply_1(v_h__2_404_, v_a_405_);
        return v___x_406_;
    } else {
        let mut v_a_407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_404_);
        v_a_407_ = crate::leanh::lean_ctor_get(v_b_402_, 0);
        crate::leanh::lean_inc(v_a_407_);
        crate::leanh::lean_dec_ref_known(v_b_402_, 1);
        v___x_408_ = crate::leanh::lean_apply_1(v_h__1_403_, v_a_407_);
        return v___x_408_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__List_forIn_x27__eq__foldlM_match__1_splitter(
    mut v_00_u03b2_409_: *mut crate::leanh::LeanObject,
    mut v_motive_410_: *mut crate::leanh::LeanObject,
    mut v_b_411_: *mut crate::leanh::LeanObject,
    mut v_h__1_412_: *mut crate::leanh::LeanObject,
    mut v_h__2_413_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_b_411_) == 0 {
        let mut v_a_414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_412_);
        v_a_414_ = crate::leanh::lean_ctor_get(v_b_411_, 0);
        crate::leanh::lean_inc(v_a_414_);
        crate::leanh::lean_dec_ref_known(v_b_411_, 1);
        v___x_415_ = crate::leanh::lean_apply_1(v_h__2_413_, v_a_414_);
        return v___x_415_;
    } else {
        let mut v_a_416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_413_);
        v_a_416_ = crate::leanh::lean_ctor_get(v_b_411_, 0);
        crate::leanh::lean_inc(v_a_416_);
        crate::leanh::lean_dec_ref_known(v_b_411_, 1);
        v___x_417_ = crate::leanh::lean_apply_1(v_h__1_412_, v_a_416_);
        return v___x_417_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iter_length__eq__match__step_match__1_splitter___redArg(
    mut v_x_418_: *mut crate::leanh::LeanObject,
    mut v_h__1_419_: *mut crate::leanh::LeanObject,
    mut v_h__2_420_: *mut crate::leanh::LeanObject,
    mut v_h__3_421_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_418_) {
        0 => {
            let mut v_it_422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_421_);
            crate::leanh::lean_dec(v_h__2_420_);
            v_it_422_ = crate::leanh::lean_ctor_get(v_x_418_, 0);
            crate::leanh::lean_inc(v_it_422_);
            v_out_423_ = crate::leanh::lean_ctor_get(v_x_418_, 1);
            crate::leanh::lean_inc(v_out_423_);
            crate::leanh::lean_dec_ref_known(v_x_418_, 2);
            v___x_424_ = crate::leanh::lean_apply_2(v_h__1_419_, v_it_422_, v_out_423_);
            return v___x_424_;
        }
        1 => {
            let mut v_it_425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_421_);
            crate::leanh::lean_dec(v_h__1_419_);
            v_it_425_ = crate::leanh::lean_ctor_get(v_x_418_, 0);
            crate::leanh::lean_inc(v_it_425_);
            crate::leanh::lean_dec_ref_known(v_x_418_, 1);
            v___x_426_ = crate::leanh::lean_apply_1(v_h__2_420_, v_it_425_);
            return v___x_426_;
        }
        _ => {
            let mut v___x_427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_420_);
            crate::leanh::lean_dec(v_h__1_419_);
            v___x_427_ = crate::leanh::lean_box(0);
            v___x_428_ = crate::leanh::lean_apply_1(v_h__3_421_, v___x_427_);
            return v___x_428_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iter_length__eq__match__step_match__1_splitter(
    mut v_00_u03b1_429_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_430_: *mut crate::leanh::LeanObject,
    mut v_motive_431_: *mut crate::leanh::LeanObject,
    mut v_x_432_: *mut crate::leanh::LeanObject,
    mut v_h__1_433_: *mut crate::leanh::LeanObject,
    mut v_h__2_434_: *mut crate::leanh::LeanObject,
    mut v_h__3_435_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_432_) {
        0 => {
            let mut v_it_436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_435_);
            crate::leanh::lean_dec(v_h__2_434_);
            v_it_436_ = crate::leanh::lean_ctor_get(v_x_432_, 0);
            crate::leanh::lean_inc(v_it_436_);
            v_out_437_ = crate::leanh::lean_ctor_get(v_x_432_, 1);
            crate::leanh::lean_inc(v_out_437_);
            crate::leanh::lean_dec_ref_known(v_x_432_, 2);
            v___x_438_ = crate::leanh::lean_apply_2(v_h__1_433_, v_it_436_, v_out_437_);
            return v___x_438_;
        }
        1 => {
            let mut v_it_439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_435_);
            crate::leanh::lean_dec(v_h__1_433_);
            v_it_439_ = crate::leanh::lean_ctor_get(v_x_432_, 0);
            crate::leanh::lean_inc(v_it_439_);
            crate::leanh::lean_dec_ref_known(v_x_432_, 1);
            v___x_440_ = crate::leanh::lean_apply_1(v_h__2_434_, v_it_439_);
            return v___x_440_;
        }
        _ => {
            let mut v___x_441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_434_);
            crate::leanh::lean_dec(v_h__1_433_);
            v___x_441_ = crate::leanh::lean_box(0);
            v___x_442_ = crate::leanh::lean_apply_1(v_h__3_435_, v___x_441_);
            return v___x_442_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_IterM_length__eq__match__step_match__1_splitter___redArg(
    mut v_x_443_: *mut crate::leanh::LeanObject,
    mut v_h__1_444_: *mut crate::leanh::LeanObject,
    mut v_h__2_445_: *mut crate::leanh::LeanObject,
    mut v_h__3_446_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_443_) {
        0 => {
            let mut v_it_447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_446_);
            crate::leanh::lean_dec(v_h__2_445_);
            v_it_447_ = crate::leanh::lean_ctor_get(v_x_443_, 0);
            crate::leanh::lean_inc(v_it_447_);
            v_out_448_ = crate::leanh::lean_ctor_get(v_x_443_, 1);
            crate::leanh::lean_inc(v_out_448_);
            crate::leanh::lean_dec_ref_known(v_x_443_, 2);
            v___x_449_ = crate::leanh::lean_apply_2(v_h__1_444_, v_it_447_, v_out_448_);
            return v___x_449_;
        }
        1 => {
            let mut v_it_450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_446_);
            crate::leanh::lean_dec(v_h__1_444_);
            v_it_450_ = crate::leanh::lean_ctor_get(v_x_443_, 0);
            crate::leanh::lean_inc(v_it_450_);
            crate::leanh::lean_dec_ref_known(v_x_443_, 1);
            v___x_451_ = crate::leanh::lean_apply_1(v_h__2_445_, v_it_450_);
            return v___x_451_;
        }
        _ => {
            let mut v___x_452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_445_);
            crate::leanh::lean_dec(v_h__1_444_);
            v___x_452_ = crate::leanh::lean_box(0);
            v___x_453_ = crate::leanh::lean_apply_1(v_h__3_446_, v___x_452_);
            return v___x_453_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_IterM_length__eq__match__step_match__1_splitter(
    mut v_00_u03b1_454_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_455_: *mut crate::leanh::LeanObject,
    mut v_m_456_: *mut crate::leanh::LeanObject,
    mut v_motive_457_: *mut crate::leanh::LeanObject,
    mut v_x_458_: *mut crate::leanh::LeanObject,
    mut v_h__1_459_: *mut crate::leanh::LeanObject,
    mut v_h__2_460_: *mut crate::leanh::LeanObject,
    mut v_h__3_461_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_458_) {
        0 => {
            let mut v_it_462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_461_);
            crate::leanh::lean_dec(v_h__2_460_);
            v_it_462_ = crate::leanh::lean_ctor_get(v_x_458_, 0);
            crate::leanh::lean_inc(v_it_462_);
            v_out_463_ = crate::leanh::lean_ctor_get(v_x_458_, 1);
            crate::leanh::lean_inc(v_out_463_);
            crate::leanh::lean_dec_ref_known(v_x_458_, 2);
            v___x_464_ = crate::leanh::lean_apply_2(v_h__1_459_, v_it_462_, v_out_463_);
            return v___x_464_;
        }
        1 => {
            let mut v_it_465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_461_);
            crate::leanh::lean_dec(v_h__1_459_);
            v_it_465_ = crate::leanh::lean_ctor_get(v_x_458_, 0);
            crate::leanh::lean_inc(v_it_465_);
            crate::leanh::lean_dec_ref_known(v_x_458_, 1);
            v___x_466_ = crate::leanh::lean_apply_1(v_h__2_460_, v_it_465_);
            return v___x_466_;
        }
        _ => {
            let mut v___x_467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_460_);
            crate::leanh::lean_dec(v_h__1_459_);
            v___x_467_ = crate::leanh::lean_box(0);
            v___x_468_ = crate::leanh::lean_apply_1(v_h__3_461_, v___x_467_);
            return v___x_468_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iter_findSomeM_x3f_match__1_splitter___redArg(
    mut v_____do__lift_469_: *mut crate::leanh::LeanObject,
    mut v_h__1_470_: *mut crate::leanh::LeanObject,
    mut v_h__2_471_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_469_) == 0 {
        let mut v___x_472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_471_);
        v___x_472_ = crate::leanh::lean_box(0);
        v___x_473_ = crate::leanh::lean_apply_1(v_h__1_470_, v___x_472_);
        return v___x_473_;
    } else {
        let mut v_val_474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_470_);
        v_val_474_ = crate::leanh::lean_ctor_get(v_____do__lift_469_, 0);
        crate::leanh::lean_inc(v_val_474_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_469_, 1);
        v___x_475_ = crate::leanh::lean_apply_1(v_h__2_471_, v_val_474_);
        return v___x_475_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iter_findSomeM_x3f_match__1_splitter(
    mut v_00_u03b3_476_: *mut crate::leanh::LeanObject,
    mut v_motive_477_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_478_: *mut crate::leanh::LeanObject,
    mut v_h__1_479_: *mut crate::leanh::LeanObject,
    mut v_h__2_480_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_478_) == 0 {
        let mut v___x_481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_480_);
        v___x_481_ = crate::leanh::lean_box(0);
        v___x_482_ = crate::leanh::lean_apply_1(v_h__1_479_, v___x_481_);
        return v___x_482_;
    } else {
        let mut v_val_483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_479_);
        v_val_483_ = crate::leanh::lean_ctor_get(v_____do__lift_478_, 0);
        crate::leanh::lean_inc(v_val_483_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_478_, 1);
        v___x_484_ = crate::leanh::lean_apply_1(v_h__2_480_, v_val_483_);
        return v___x_484_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iter_findSomeM_x3f__eq__match__step_match__1_splitter___redArg(
    mut v_____do__lift_485_: *mut crate::leanh::LeanObject,
    mut v_h__1_486_: *mut crate::leanh::LeanObject,
    mut v_h__2_487_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_485_) == 0 {
        let mut v___x_488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_487_);
        v___x_488_ = crate::leanh::lean_box(0);
        v___x_489_ = crate::leanh::lean_apply_1(v_h__1_486_, v___x_488_);
        return v___x_489_;
    } else {
        let mut v_val_490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_486_);
        v_val_490_ = crate::leanh::lean_ctor_get(v_____do__lift_485_, 0);
        crate::leanh::lean_inc(v_val_490_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_485_, 1);
        v___x_491_ = crate::leanh::lean_apply_1(v_h__2_487_, v_val_490_);
        return v___x_491_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__Std_Iter_findSomeM_x3f__eq__match__step_match__1_splitter(
    mut v_00_u03b3_492_: *mut crate::leanh::LeanObject,
    mut v_motive_493_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_494_: *mut crate::leanh::LeanObject,
    mut v_h__1_495_: *mut crate::leanh::LeanObject,
    mut v_h__2_496_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_494_) == 0 {
        let mut v___x_497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_496_);
        v___x_497_ = crate::leanh::lean_box(0);
        v___x_498_ = crate::leanh::lean_apply_1(v_h__1_495_, v___x_497_);
        return v___x_498_;
    } else {
        let mut v_val_499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_495_);
        v_val_499_ = crate::leanh::lean_ctor_get(v_____do__lift_494_, 0);
        crate::leanh::lean_inc(v_val_499_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_494_, 1);
        v___x_500_ = crate::leanh::lean_apply_1(v_h__2_496_, v_val_499_);
        return v___x_500_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__List_findSomeM_x3f__cons_match__1_splitter___redArg(
    mut v_____do__lift_501_: *mut crate::leanh::LeanObject,
    mut v_h__1_502_: *mut crate::leanh::LeanObject,
    mut v_h__2_503_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_501_) == 0 {
        let mut v___x_504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_502_);
        v___x_504_ = crate::leanh::lean_box(0);
        v___x_505_ = crate::leanh::lean_apply_1(v_h__2_503_, v___x_504_);
        return v___x_505_;
    } else {
        let mut v_val_506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_503_);
        v_val_506_ = crate::leanh::lean_ctor_get(v_____do__lift_501_, 0);
        crate::leanh::lean_inc(v_val_506_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_501_, 1);
        v___x_507_ = crate::leanh::lean_apply_1(v_h__1_502_, v_val_506_);
        return v___x_507_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Loop_0__List_findSomeM_x3f__cons_match__1_splitter(
    mut v_00_u03b2_508_: *mut crate::leanh::LeanObject,
    mut v_motive_509_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_510_: *mut crate::leanh::LeanObject,
    mut v_h__1_511_: *mut crate::leanh::LeanObject,
    mut v_h__2_512_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_510_) == 0 {
        let mut v___x_513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_511_);
        v___x_513_ = crate::leanh::lean_box(0);
        v___x_514_ = crate::leanh::lean_apply_1(v_h__2_512_, v___x_513_);
        return v___x_514_;
    } else {
        let mut v_val_515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_512_);
        v_val_515_ = crate::leanh::lean_ctor_get(v_____do__lift_510_, 0);
        crate::leanh::lean_inc(v_val_515_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_510_, 1);
        v___x_516_ = crate::leanh::lean_apply_1(v_h__1_511_, v_val_515_);
        return v___x_516_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Loop(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Loop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Collect(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Monadic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Collect(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Loop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Monadic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Find(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Iterators_Lemmas_Consumers_Loop(
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
pub unsafe fn initialize_Init_Data_Iterators_Lemmas_Consumers_Loop(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers_Loop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers_Monadic_Collect(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_Monadic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers_Collect(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers_Loop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Monadic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Find(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Option_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Loop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Iterators_Lemmas_Consumers_Loop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_Iterators_Lemmas_Consumers_Loop(builtin);
}
