// Lean compiler output
// Module: Std.Data.Iterators.Lemmas.Combinators.Zip
// Imports: Std.Data.Iterators.Combinators.Zip Std.Data.Iterators.Lemmas.Combinators.Monadic.Zip Init.Data.Iterators.Lemmas.Combinators.Take Init.Data.Iterators.Lemmas.Basic Init.Data.Iterators.Lemmas.Consumers.Access Init.Data.Iterators.Lemmas.Consumers.Collect Init.Data.List.ToArray Init.Data.List.Zip
use crate::r#gen::Init::Data::Iterators::Lemmas::Basic::{
    initialize_Init_Data_Iterators_Lemmas_Basic,
    runtime_initialize_Init_Data_Iterators_Lemmas_Basic,
};
use crate::r#gen::Init::Data::Iterators::Lemmas::Combinators::Take::{
    initialize_Init_Data_Iterators_Lemmas_Combinators_Take,
    runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_Take,
};
use crate::r#gen::Init::Data::Iterators::Lemmas::Consumers::Access::{
    initialize_Init_Data_Iterators_Lemmas_Consumers_Access,
    runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Access,
};
use crate::r#gen::Init::Data::Iterators::Lemmas::Consumers::Collect::{
    initialize_Init_Data_Iterators_Lemmas_Consumers_Collect,
    runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Collect,
};
use crate::r#gen::Init::Data::List::ToArray::{
    initialize_Init_Data_List_ToArray, runtime_initialize_Init_Data_List_ToArray,
};
use crate::r#gen::Init::Data::List::Zip::{
    initialize_Init_Data_List_Zip, runtime_initialize_Init_Data_List_Zip,
};
use crate::r#gen::Std::Data::Iterators::Combinators::Zip::{
    initialize_Std_Data_Iterators_Combinators_Zip,
    runtime_initialize_Std_Data_Iterators_Combinators_Zip,
};
use crate::r#gen::Std::Data::Iterators::Lemmas::Combinators::Monadic::Zip::{
    initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_Zip,
    runtime_initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_Zip,
};
use crate::ffi::{lean_nat_dec_eq, lean_nat_sub};
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_IterM_step__intermediateZip_match__3_splitter___redArg(
    mut v_memo_262_: *mut crate::leanh::LeanObject,
    mut v_h__1_263_: *mut crate::leanh::LeanObject,
    mut v_h__2_264_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_memo_262_) == 0 {
        let mut v___x_265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_264_);
        v___x_265_ = crate::leanh::lean_box(0);
        v___x_266_ = crate::leanh::lean_apply_1(v_h__1_263_, v___x_265_);
        return v___x_266_;
    } else {
        let mut v_val_267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_263_);
        v_val_267_ = crate::leanh::lean_ctor_get(v_memo_262_, 0);
        crate::leanh::lean_inc(v_val_267_);
        crate::leanh::lean_dec_ref_known(v_memo_262_, 1);
        v___x_268_ = crate::leanh::lean_apply_1(v_h__2_264_, v_val_267_);
        return v___x_268_;
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_IterM_step__intermediateZip_match__3_splitter(
    mut v_00_u03b1_u2081_269_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_u2081_270_: *mut crate::leanh::LeanObject,
    mut v_m_271_: *mut crate::leanh::LeanObject,
    mut v_inst_272_: *mut crate::leanh::LeanObject,
    mut v_motive_273_: *mut crate::leanh::LeanObject,
    mut v_memo_274_: *mut crate::leanh::LeanObject,
    mut v_h__1_275_: *mut crate::leanh::LeanObject,
    mut v_h__2_276_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_memo_274_) == 0 {
        let mut v___x_277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_276_);
        v___x_277_ = crate::leanh::lean_box(0);
        v___x_278_ = crate::leanh::lean_apply_1(v_h__1_275_, v___x_277_);
        return v___x_278_;
    } else {
        let mut v_val_279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_275_);
        v_val_279_ = crate::leanh::lean_ctor_get(v_memo_274_, 0);
        crate::leanh::lean_inc(v_val_279_);
        crate::leanh::lean_dec_ref_known(v_memo_274_, 1);
        v___x_280_ = crate::leanh::lean_apply_1(v_h__2_276_, v_val_279_);
        return v___x_280_;
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_IterM_step__intermediateZip_match__3_splitter___boxed(
    mut v_00_u03b1_u2081_281_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_u2081_282_: *mut crate::leanh::LeanObject,
    mut v_m_283_: *mut crate::leanh::LeanObject,
    mut v_inst_284_: *mut crate::leanh::LeanObject,
    mut v_motive_285_: *mut crate::leanh::LeanObject,
    mut v_memo_286_: *mut crate::leanh::LeanObject,
    mut v_h__1_287_: *mut crate::leanh::LeanObject,
    mut v_h__2_288_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_289_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_IterM_step__intermediateZip_match__3_splitter(v_00_u03b1_u2081_281_, v_00_u03b2_u2081_282_, v_m_283_, v_inst_284_, v_motive_285_, v_memo_286_, v_h__1_287_, v_h__2_288_);
    crate::leanh::lean_dec(v_inst_284_);
    return v_res_289_;
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_IterM_step__intermediateZip_match__1_splitter___redArg(
    mut v_x_290_: *mut crate::leanh::LeanObject,
    mut v_h__1_291_: *mut crate::leanh::LeanObject,
    mut v_h__2_292_: *mut crate::leanh::LeanObject,
    mut v_h__3_293_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_290_) {
        0 => {
            let mut v_it_294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_293_);
            crate::leanh::lean_dec(v_h__2_292_);
            v_it_294_ = crate::leanh::lean_ctor_get(v_x_290_, 0);
            crate::leanh::lean_inc(v_it_294_);
            v_out_295_ = crate::leanh::lean_ctor_get(v_x_290_, 1);
            crate::leanh::lean_inc(v_out_295_);
            crate::leanh::lean_dec_ref_known(v_x_290_, 2);
            v___x_296_ = crate::leanh::lean_apply_3(
                v_h__1_291_,
                v_it_294_,
                v_out_295_,
                crate::leanh::lean_box(0),
            );
            return v___x_296_;
        }
        1 => {
            let mut v_it_297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_293_);
            crate::leanh::lean_dec(v_h__1_291_);
            v_it_297_ = crate::leanh::lean_ctor_get(v_x_290_, 0);
            crate::leanh::lean_inc(v_it_297_);
            crate::leanh::lean_dec_ref_known(v_x_290_, 1);
            v___x_298_ =
                crate::leanh::lean_apply_2(v_h__2_292_, v_it_297_, crate::leanh::lean_box(0));
            return v___x_298_;
        }
        _ => {
            let mut v___x_299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_292_);
            crate::leanh::lean_dec(v_h__1_291_);
            v___x_299_ = crate::leanh::lean_apply_1(v_h__3_293_, crate::leanh::lean_box(0));
            return v___x_299_;
        }
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_IterM_step__intermediateZip_match__1_splitter(
    mut v_00_u03b1_u2081_300_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_u2081_301_: *mut crate::leanh::LeanObject,
    mut v_m_302_: *mut crate::leanh::LeanObject,
    mut v_inst_303_: *mut crate::leanh::LeanObject,
    mut v_it_u2081_304_: *mut crate::leanh::LeanObject,
    mut v_motive_305_: *mut crate::leanh::LeanObject,
    mut v_x_306_: *mut crate::leanh::LeanObject,
    mut v_h__1_307_: *mut crate::leanh::LeanObject,
    mut v_h__2_308_: *mut crate::leanh::LeanObject,
    mut v_h__3_309_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_306_) {
        0 => {
            let mut v_it_310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_309_);
            crate::leanh::lean_dec(v_h__2_308_);
            v_it_310_ = crate::leanh::lean_ctor_get(v_x_306_, 0);
            crate::leanh::lean_inc(v_it_310_);
            v_out_311_ = crate::leanh::lean_ctor_get(v_x_306_, 1);
            crate::leanh::lean_inc(v_out_311_);
            crate::leanh::lean_dec_ref_known(v_x_306_, 2);
            v___x_312_ = crate::leanh::lean_apply_3(
                v_h__1_307_,
                v_it_310_,
                v_out_311_,
                crate::leanh::lean_box(0),
            );
            return v___x_312_;
        }
        1 => {
            let mut v_it_313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_309_);
            crate::leanh::lean_dec(v_h__1_307_);
            v_it_313_ = crate::leanh::lean_ctor_get(v_x_306_, 0);
            crate::leanh::lean_inc(v_it_313_);
            crate::leanh::lean_dec_ref_known(v_x_306_, 1);
            v___x_314_ =
                crate::leanh::lean_apply_2(v_h__2_308_, v_it_313_, crate::leanh::lean_box(0));
            return v___x_314_;
        }
        _ => {
            let mut v___x_315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_308_);
            crate::leanh::lean_dec(v_h__1_307_);
            v___x_315_ = crate::leanh::lean_apply_1(v_h__3_309_, crate::leanh::lean_box(0));
            return v___x_315_;
        }
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_IterM_step__intermediateZip_match__1_splitter___boxed(
    mut v_00_u03b1_u2081_316_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_u2081_317_: *mut crate::leanh::LeanObject,
    mut v_m_318_: *mut crate::leanh::LeanObject,
    mut v_inst_319_: *mut crate::leanh::LeanObject,
    mut v_it_u2081_320_: *mut crate::leanh::LeanObject,
    mut v_motive_321_: *mut crate::leanh::LeanObject,
    mut v_x_322_: *mut crate::leanh::LeanObject,
    mut v_h__1_323_: *mut crate::leanh::LeanObject,
    mut v_h__2_324_: *mut crate::leanh::LeanObject,
    mut v_h__3_325_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_326_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_IterM_step__intermediateZip_match__1_splitter(v_00_u03b1_u2081_316_, v_00_u03b2_u2081_317_, v_m_318_, v_inst_319_, v_it_u2081_320_, v_motive_321_, v_x_322_, v_h__1_323_, v_h__2_324_, v_h__3_325_);
    crate::leanh::lean_dec(v_it_u2081_320_);
    crate::leanh::lean_dec(v_inst_319_);
    return v_res_326_;
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_step__intermediateZip_match__3_splitter___redArg(
    mut v_memo_327_: *mut crate::leanh::LeanObject,
    mut v_h__1_328_: *mut crate::leanh::LeanObject,
    mut v_h__2_329_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_memo_327_) == 0 {
        let mut v___x_330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_329_);
        v___x_330_ = crate::leanh::lean_box(0);
        v___x_331_ = crate::leanh::lean_apply_1(v_h__1_328_, v___x_330_);
        return v___x_331_;
    } else {
        let mut v_val_332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_328_);
        v_val_332_ = crate::leanh::lean_ctor_get(v_memo_327_, 0);
        crate::leanh::lean_inc(v_val_332_);
        crate::leanh::lean_dec_ref_known(v_memo_327_, 1);
        v___x_333_ = crate::leanh::lean_apply_1(v_h__2_329_, v_val_332_);
        return v___x_333_;
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_step__intermediateZip_match__3_splitter(
    mut v_00_u03b1_u2081_334_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_u2081_335_: *mut crate::leanh::LeanObject,
    mut v_inst_336_: *mut crate::leanh::LeanObject,
    mut v_motive_337_: *mut crate::leanh::LeanObject,
    mut v_memo_338_: *mut crate::leanh::LeanObject,
    mut v_h__1_339_: *mut crate::leanh::LeanObject,
    mut v_h__2_340_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_memo_338_) == 0 {
        let mut v___x_341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_340_);
        v___x_341_ = crate::leanh::lean_box(0);
        v___x_342_ = crate::leanh::lean_apply_1(v_h__1_339_, v___x_341_);
        return v___x_342_;
    } else {
        let mut v_val_343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_339_);
        v_val_343_ = crate::leanh::lean_ctor_get(v_memo_338_, 0);
        crate::leanh::lean_inc(v_val_343_);
        crate::leanh::lean_dec_ref_known(v_memo_338_, 1);
        v___x_344_ = crate::leanh::lean_apply_1(v_h__2_340_, v_val_343_);
        return v___x_344_;
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_step__intermediateZip_match__3_splitter___boxed(
    mut v_00_u03b1_u2081_345_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_u2081_346_: *mut crate::leanh::LeanObject,
    mut v_inst_347_: *mut crate::leanh::LeanObject,
    mut v_motive_348_: *mut crate::leanh::LeanObject,
    mut v_memo_349_: *mut crate::leanh::LeanObject,
    mut v_h__1_350_: *mut crate::leanh::LeanObject,
    mut v_h__2_351_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_352_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_step__intermediateZip_match__3_splitter(v_00_u03b1_u2081_345_, v_00_u03b2_u2081_346_, v_inst_347_, v_motive_348_, v_memo_349_, v_h__1_350_, v_h__2_351_);
    crate::leanh::lean_dec(v_inst_347_);
    return v_res_352_;
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_step__intermediateZip_match__1_splitter___redArg(
    mut v_x_353_: *mut crate::leanh::LeanObject,
    mut v_h__1_354_: *mut crate::leanh::LeanObject,
    mut v_h__2_355_: *mut crate::leanh::LeanObject,
    mut v_h__3_356_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_353_) {
        0 => {
            let mut v_it_357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_356_);
            crate::leanh::lean_dec(v_h__2_355_);
            v_it_357_ = crate::leanh::lean_ctor_get(v_x_353_, 0);
            crate::leanh::lean_inc(v_it_357_);
            v_out_358_ = crate::leanh::lean_ctor_get(v_x_353_, 1);
            crate::leanh::lean_inc(v_out_358_);
            crate::leanh::lean_dec_ref_known(v_x_353_, 2);
            v___x_359_ = crate::leanh::lean_apply_3(
                v_h__1_354_,
                v_it_357_,
                v_out_358_,
                crate::leanh::lean_box(0),
            );
            return v___x_359_;
        }
        1 => {
            let mut v_it_360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_356_);
            crate::leanh::lean_dec(v_h__1_354_);
            v_it_360_ = crate::leanh::lean_ctor_get(v_x_353_, 0);
            crate::leanh::lean_inc(v_it_360_);
            crate::leanh::lean_dec_ref_known(v_x_353_, 1);
            v___x_361_ =
                crate::leanh::lean_apply_2(v_h__2_355_, v_it_360_, crate::leanh::lean_box(0));
            return v___x_361_;
        }
        _ => {
            let mut v___x_362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_355_);
            crate::leanh::lean_dec(v_h__1_354_);
            v___x_362_ = crate::leanh::lean_apply_1(v_h__3_356_, crate::leanh::lean_box(0));
            return v___x_362_;
        }
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_step__intermediateZip_match__1_splitter(
    mut v_00_u03b1_u2081_363_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_u2081_364_: *mut crate::leanh::LeanObject,
    mut v_inst_365_: *mut crate::leanh::LeanObject,
    mut v_it_u2081_366_: *mut crate::leanh::LeanObject,
    mut v_motive_367_: *mut crate::leanh::LeanObject,
    mut v_x_368_: *mut crate::leanh::LeanObject,
    mut v_h__1_369_: *mut crate::leanh::LeanObject,
    mut v_h__2_370_: *mut crate::leanh::LeanObject,
    mut v_h__3_371_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_368_) {
        0 => {
            let mut v_it_372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_371_);
            crate::leanh::lean_dec(v_h__2_370_);
            v_it_372_ = crate::leanh::lean_ctor_get(v_x_368_, 0);
            crate::leanh::lean_inc(v_it_372_);
            v_out_373_ = crate::leanh::lean_ctor_get(v_x_368_, 1);
            crate::leanh::lean_inc(v_out_373_);
            crate::leanh::lean_dec_ref_known(v_x_368_, 2);
            v___x_374_ = crate::leanh::lean_apply_3(
                v_h__1_369_,
                v_it_372_,
                v_out_373_,
                crate::leanh::lean_box(0),
            );
            return v___x_374_;
        }
        1 => {
            let mut v_it_375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_371_);
            crate::leanh::lean_dec(v_h__1_369_);
            v_it_375_ = crate::leanh::lean_ctor_get(v_x_368_, 0);
            crate::leanh::lean_inc(v_it_375_);
            crate::leanh::lean_dec_ref_known(v_x_368_, 1);
            v___x_376_ =
                crate::leanh::lean_apply_2(v_h__2_370_, v_it_375_, crate::leanh::lean_box(0));
            return v___x_376_;
        }
        _ => {
            let mut v___x_377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_370_);
            crate::leanh::lean_dec(v_h__1_369_);
            v___x_377_ = crate::leanh::lean_apply_1(v_h__3_371_, crate::leanh::lean_box(0));
            return v___x_377_;
        }
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_step__intermediateZip_match__1_splitter___boxed(
    mut v_00_u03b1_u2081_378_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_u2081_379_: *mut crate::leanh::LeanObject,
    mut v_inst_380_: *mut crate::leanh::LeanObject,
    mut v_it_u2081_381_: *mut crate::leanh::LeanObject,
    mut v_motive_382_: *mut crate::leanh::LeanObject,
    mut v_x_383_: *mut crate::leanh::LeanObject,
    mut v_h__1_384_: *mut crate::leanh::LeanObject,
    mut v_h__2_385_: *mut crate::leanh::LeanObject,
    mut v_h__3_386_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_387_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_step__intermediateZip_match__1_splitter(v_00_u03b1_u2081_378_, v_00_u03b2_u2081_379_, v_inst_380_, v_it_u2081_381_, v_motive_382_, v_x_383_, v_h__1_384_, v_h__2_385_, v_h__3_386_);
    crate::leanh::lean_dec(v_it_u2081_381_);
    crate::leanh::lean_dec(v_inst_380_);
    return v_res_387_;
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f_match__3_splitter___redArg(
    mut v_x_388_: *mut crate::leanh::LeanObject,
    mut v_h__1_389_: *mut crate::leanh::LeanObject,
    mut v_h__2_390_: *mut crate::leanh::LeanObject,
    mut v_h__3_391_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_388_) {
        0 => {
            let mut v_it_392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_391_);
            crate::leanh::lean_dec(v_h__2_390_);
            v_it_392_ = crate::leanh::lean_ctor_get(v_x_388_, 0);
            crate::leanh::lean_inc(v_it_392_);
            v_out_393_ = crate::leanh::lean_ctor_get(v_x_388_, 1);
            crate::leanh::lean_inc(v_out_393_);
            crate::leanh::lean_dec_ref_known(v_x_388_, 2);
            v___x_394_ = crate::leanh::lean_apply_3(
                v_h__1_389_,
                v_it_392_,
                v_out_393_,
                crate::leanh::lean_box(0),
            );
            return v___x_394_;
        }
        1 => {
            let mut v_it_395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_391_);
            crate::leanh::lean_dec(v_h__1_389_);
            v_it_395_ = crate::leanh::lean_ctor_get(v_x_388_, 0);
            crate::leanh::lean_inc(v_it_395_);
            crate::leanh::lean_dec_ref_known(v_x_388_, 1);
            v___x_396_ =
                crate::leanh::lean_apply_2(v_h__2_390_, v_it_395_, crate::leanh::lean_box(0));
            return v___x_396_;
        }
        _ => {
            let mut v___x_397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_390_);
            crate::leanh::lean_dec(v_h__1_389_);
            v___x_397_ = crate::leanh::lean_apply_1(v_h__3_391_, crate::leanh::lean_box(0));
            return v___x_397_;
        }
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f_match__3_splitter(
    mut v_00_u03b1_398_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_399_: *mut crate::leanh::LeanObject,
    mut v_inst_400_: *mut crate::leanh::LeanObject,
    mut v_it_401_: *mut crate::leanh::LeanObject,
    mut v_motive_402_: *mut crate::leanh::LeanObject,
    mut v_x_403_: *mut crate::leanh::LeanObject,
    mut v_h__1_404_: *mut crate::leanh::LeanObject,
    mut v_h__2_405_: *mut crate::leanh::LeanObject,
    mut v_h__3_406_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_403_) {
        0 => {
            let mut v_it_407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_406_);
            crate::leanh::lean_dec(v_h__2_405_);
            v_it_407_ = crate::leanh::lean_ctor_get(v_x_403_, 0);
            crate::leanh::lean_inc(v_it_407_);
            v_out_408_ = crate::leanh::lean_ctor_get(v_x_403_, 1);
            crate::leanh::lean_inc(v_out_408_);
            crate::leanh::lean_dec_ref_known(v_x_403_, 2);
            v___x_409_ = crate::leanh::lean_apply_3(
                v_h__1_404_,
                v_it_407_,
                v_out_408_,
                crate::leanh::lean_box(0),
            );
            return v___x_409_;
        }
        1 => {
            let mut v_it_410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_406_);
            crate::leanh::lean_dec(v_h__1_404_);
            v_it_410_ = crate::leanh::lean_ctor_get(v_x_403_, 0);
            crate::leanh::lean_inc(v_it_410_);
            crate::leanh::lean_dec_ref_known(v_x_403_, 1);
            v___x_411_ =
                crate::leanh::lean_apply_2(v_h__2_405_, v_it_410_, crate::leanh::lean_box(0));
            return v___x_411_;
        }
        _ => {
            let mut v___x_412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_405_);
            crate::leanh::lean_dec(v_h__1_404_);
            v___x_412_ = crate::leanh::lean_apply_1(v_h__3_406_, crate::leanh::lean_box(0));
            return v___x_412_;
        }
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f_match__3_splitter___boxed(
    mut v_00_u03b1_413_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_414_: *mut crate::leanh::LeanObject,
    mut v_inst_415_: *mut crate::leanh::LeanObject,
    mut v_it_416_: *mut crate::leanh::LeanObject,
    mut v_motive_417_: *mut crate::leanh::LeanObject,
    mut v_x_418_: *mut crate::leanh::LeanObject,
    mut v_h__1_419_: *mut crate::leanh::LeanObject,
    mut v_h__2_420_: *mut crate::leanh::LeanObject,
    mut v_h__3_421_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_422_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f_match__3_splitter(v_00_u03b1_413_, v_00_u03b2_414_, v_inst_415_, v_it_416_, v_motive_417_, v_x_418_, v_h__1_419_, v_h__2_420_, v_h__3_421_);
    crate::leanh::lean_dec(v_it_416_);
    crate::leanh::lean_dec(v_inst_415_);
    return v_res_422_;
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f_match__1_splitter___redArg(
    mut v_n_423_: *mut crate::leanh::LeanObject,
    mut v_recur_424_: *mut crate::leanh::LeanObject,
    mut v_h__1_425_: *mut crate::leanh::LeanObject,
    mut v_h__2_426_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_428_: u8 = 0;
    v_zero_427_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_428_ = lean_nat_dec_eq(v_n_423_, v_zero_427_);
    if v_isZero_428_ == 1 {
        let mut v___x_429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_426_);
        v___x_429_ = crate::leanh::lean_apply_1(v_h__1_425_, v_recur_424_);
        return v___x_429_;
    } else {
        let mut v_one_430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_425_);
        v_one_430_ = crate::leanh::lean_unsigned_to_nat(1);
        v_n_431_ = lean_nat_sub(v_n_423_, v_one_430_);
        v___x_432_ = crate::leanh::lean_apply_2(v_h__2_426_, v_n_431_, v_recur_424_);
        return v___x_432_;
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f_match__1_splitter___redArg___boxed(
    mut v_n_433_: *mut crate::leanh::LeanObject,
    mut v_recur_434_: *mut crate::leanh::LeanObject,
    mut v_h__1_435_: *mut crate::leanh::LeanObject,
    mut v_h__2_436_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_437_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f_match__1_splitter___redArg(v_n_433_, v_recur_434_, v_h__1_435_, v_h__2_436_);
    crate::leanh::lean_dec(v_n_433_);
    return v_res_437_;
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f_match__1_splitter(
    mut v_00_u03b1_438_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_439_: *mut crate::leanh::LeanObject,
    mut v_inst_440_: *mut crate::leanh::LeanObject,
    mut v_it_441_: *mut crate::leanh::LeanObject,
    mut v_motive_442_: *mut crate::leanh::LeanObject,
    mut v_n_443_: *mut crate::leanh::LeanObject,
    mut v_recur_444_: *mut crate::leanh::LeanObject,
    mut v_h__1_445_: *mut crate::leanh::LeanObject,
    mut v_h__2_446_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_448_: u8 = 0;
    v_zero_447_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_448_ = lean_nat_dec_eq(v_n_443_, v_zero_447_);
    if v_isZero_448_ == 1 {
        let mut v___x_449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_446_);
        v___x_449_ = crate::leanh::lean_apply_1(v_h__1_445_, v_recur_444_);
        return v___x_449_;
    } else {
        let mut v_one_450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_445_);
        v_one_450_ = crate::leanh::lean_unsigned_to_nat(1);
        v_n_451_ = lean_nat_sub(v_n_443_, v_one_450_);
        v___x_452_ = crate::leanh::lean_apply_2(v_h__2_446_, v_n_451_, v_recur_444_);
        return v___x_452_;
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f_match__1_splitter___boxed(
    mut v_00_u03b1_453_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_454_: *mut crate::leanh::LeanObject,
    mut v_inst_455_: *mut crate::leanh::LeanObject,
    mut v_it_456_: *mut crate::leanh::LeanObject,
    mut v_motive_457_: *mut crate::leanh::LeanObject,
    mut v_n_458_: *mut crate::leanh::LeanObject,
    mut v_recur_459_: *mut crate::leanh::LeanObject,
    mut v_h__1_460_: *mut crate::leanh::LeanObject,
    mut v_h__2_461_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_462_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f_match__1_splitter(v_00_u03b1_453_, v_00_u03b2_454_, v_inst_455_, v_it_456_, v_motive_457_, v_n_458_, v_recur_459_, v_h__1_460_, v_h__2_461_);
    crate::leanh::lean_dec(v_n_458_);
    crate::leanh::lean_dec(v_it_456_);
    crate::leanh::lean_dec(v_inst_455_);
    return v_res_462_;
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f__intermediateZip_match__1_splitter___redArg(
    mut v_n_463_: *mut crate::leanh::LeanObject,
    mut v_h__1_464_: *mut crate::leanh::LeanObject,
    mut v_h__2_465_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_467_: u8 = 0;
    v_zero_466_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_467_ = lean_nat_dec_eq(v_n_463_, v_zero_466_);
    if v_isZero_467_ == 1 {
        let mut v___x_468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_465_);
        v___x_468_ = crate::leanh::lean_box(0);
        v___x_469_ = crate::leanh::lean_apply_1(v_h__1_464_, v___x_468_);
        return v___x_469_;
    } else {
        let mut v_one_470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_464_);
        v_one_470_ = crate::leanh::lean_unsigned_to_nat(1);
        v_n_471_ = lean_nat_sub(v_n_463_, v_one_470_);
        v___x_472_ = crate::leanh::lean_apply_1(v_h__2_465_, v_n_471_);
        return v___x_472_;
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f__intermediateZip_match__1_splitter___redArg___boxed(
    mut v_n_473_: *mut crate::leanh::LeanObject,
    mut v_h__1_474_: *mut crate::leanh::LeanObject,
    mut v_h__2_475_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_476_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f__intermediateZip_match__1_splitter___redArg(v_n_473_, v_h__1_474_, v_h__2_475_);
    crate::leanh::lean_dec(v_n_473_);
    return v_res_476_;
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f__intermediateZip_match__1_splitter(
    mut v_motive_477_: *mut crate::leanh::LeanObject,
    mut v_n_478_: *mut crate::leanh::LeanObject,
    mut v_h__1_479_: *mut crate::leanh::LeanObject,
    mut v_h__2_480_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_482_: u8 = 0;
    v_zero_481_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_482_ = lean_nat_dec_eq(v_n_478_, v_zero_481_);
    if v_isZero_482_ == 1 {
        let mut v___x_483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_480_);
        v___x_483_ = crate::leanh::lean_box(0);
        v___x_484_ = crate::leanh::lean_apply_1(v_h__1_479_, v___x_483_);
        return v___x_484_;
    } else {
        let mut v_one_485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_479_);
        v_one_485_ = crate::leanh::lean_unsigned_to_nat(1);
        v_n_486_ = lean_nat_sub(v_n_478_, v_one_485_);
        v___x_487_ = crate::leanh::lean_apply_1(v_h__2_480_, v_n_486_);
        return v___x_487_;
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f__intermediateZip_match__1_splitter___boxed(
    mut v_motive_488_: *mut crate::leanh::LeanObject,
    mut v_n_489_: *mut crate::leanh::LeanObject,
    mut v_h__1_490_: *mut crate::leanh::LeanObject,
    mut v_h__2_491_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_492_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f__intermediateZip_match__1_splitter(v_motive_488_, v_n_489_, v_h__1_490_, v_h__2_491_);
    crate::leanh::lean_dec(v_n_489_);
    return v_res_492_;
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f__eq__match_match__1_splitter___redArg(
    mut v_n_493_: *mut crate::leanh::LeanObject,
    mut v_h__1_494_: *mut crate::leanh::LeanObject,
    mut v_h__2_495_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_497_: u8 = 0;
    v_zero_496_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_497_ = lean_nat_dec_eq(v_n_493_, v_zero_496_);
    if v_isZero_497_ == 1 {
        let mut v___x_498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_495_);
        v___x_498_ = crate::leanh::lean_box(0);
        v___x_499_ = crate::leanh::lean_apply_1(v_h__1_494_, v___x_498_);
        return v___x_499_;
    } else {
        let mut v_one_500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_494_);
        v_one_500_ = crate::leanh::lean_unsigned_to_nat(1);
        v_n_501_ = lean_nat_sub(v_n_493_, v_one_500_);
        v___x_502_ = crate::leanh::lean_apply_1(v_h__2_495_, v_n_501_);
        return v___x_502_;
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f__eq__match_match__1_splitter___redArg___boxed(
    mut v_n_503_: *mut crate::leanh::LeanObject,
    mut v_h__1_504_: *mut crate::leanh::LeanObject,
    mut v_h__2_505_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_506_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f__eq__match_match__1_splitter___redArg(v_n_503_, v_h__1_504_, v_h__2_505_);
    crate::leanh::lean_dec(v_n_503_);
    return v_res_506_;
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f__eq__match_match__1_splitter(
    mut v_motive_507_: *mut crate::leanh::LeanObject,
    mut v_n_508_: *mut crate::leanh::LeanObject,
    mut v_h__1_509_: *mut crate::leanh::LeanObject,
    mut v_h__2_510_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_512_: u8 = 0;
    v_zero_511_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_512_ = lean_nat_dec_eq(v_n_508_, v_zero_511_);
    if v_isZero_512_ == 1 {
        let mut v___x_513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_510_);
        v___x_513_ = crate::leanh::lean_box(0);
        v___x_514_ = crate::leanh::lean_apply_1(v_h__1_509_, v___x_513_);
        return v___x_514_;
    } else {
        let mut v_one_515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_509_);
        v_one_515_ = crate::leanh::lean_unsigned_to_nat(1);
        v_n_516_ = lean_nat_sub(v_n_508_, v_one_515_);
        v___x_517_ = crate::leanh::lean_apply_1(v_h__2_510_, v_n_516_);
        return v___x_517_;
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f__eq__match_match__1_splitter___boxed(
    mut v_motive_518_: *mut crate::leanh::LeanObject,
    mut v_n_519_: *mut crate::leanh::LeanObject,
    mut v_h__1_520_: *mut crate::leanh::LeanObject,
    mut v_h__2_521_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_522_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f__eq__match_match__1_splitter(v_motive_518_, v_n_519_, v_h__1_520_, v_h__2_521_);
    crate::leanh::lean_dec(v_n_519_);
    return v_res_522_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_Iterators_Lemmas_Combinators_Zip(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_Iterators_Combinators_Zip(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_Zip(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_Take(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Access(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_ToArray(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Zip(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_Iterators_Lemmas_Combinators_Zip(
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
pub unsafe fn initialize_Std_Data_Iterators_Lemmas_Combinators_Zip(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_Iterators_Combinators_Zip(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_Zip(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Combinators_Take(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Consumers_Access(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_ToArray(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Zip(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Lemmas_Combinators_Zip(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Data_Iterators_Lemmas_Combinators_Zip(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Data_Iterators_Lemmas_Combinators_Zip(builtin);
}
