// Lean compiler output
// Module: Std.Data.Iterators.Lemmas.Combinators.Zip
// Imports: Std.Data.Iterators.Combinators.Zip Std.Data.Iterators.Lemmas.Combinators.Monadic.Zip Init.Data.Iterators.Lemmas.Combinators.Take Init.Data.Iterators.Lemmas.Basic Init.Data.Iterators.Lemmas.Consumers.Access Init.Data.Iterators.Lemmas.Consumers.Collect Init.Data.List.ToArray Init.Data.List.Zip
use crate::ffi::{lean_nat_dec_eq, lean_nat_sub};
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
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_IterM_step__intermediateZip_match__3_splitter___redArg(
    mut v_memo_262_: *mut leanh::LeanObject,
    mut v_h__1_263_: *mut leanh::LeanObject,
    mut v_h__2_264_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_memo_262_) == 0 {
        let mut v___x_265_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_266_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_264_);
        v___x_265_ = leanh::lean_box(0);
        v___x_266_ = leanh::lean_apply_1(v_h__1_263_, v___x_265_);
        return v___x_266_;
    } else {
        let mut v_val_267_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_268_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_263_);
        v_val_267_ = leanh::lean_ctor_get(v_memo_262_, 0);
        leanh::lean_inc(v_val_267_);
        leanh::lean_dec_ref_known(v_memo_262_, 1);
        v___x_268_ = leanh::lean_apply_1(v_h__2_264_, v_val_267_);
        return v___x_268_;
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_IterM_step__intermediateZip_match__3_splitter(
    mut v_00_u03b1_u2081_269_: *mut leanh::LeanObject,
    mut v_00_u03b2_u2081_270_: *mut leanh::LeanObject,
    mut v_m_271_: *mut leanh::LeanObject,
    mut v_inst_272_: *mut leanh::LeanObject,
    mut v_motive_273_: *mut leanh::LeanObject,
    mut v_memo_274_: *mut leanh::LeanObject,
    mut v_h__1_275_: *mut leanh::LeanObject,
    mut v_h__2_276_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_memo_274_) == 0 {
        let mut v___x_277_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_278_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_276_);
        v___x_277_ = leanh::lean_box(0);
        v___x_278_ = leanh::lean_apply_1(v_h__1_275_, v___x_277_);
        return v___x_278_;
    } else {
        let mut v_val_279_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_280_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_275_);
        v_val_279_ = leanh::lean_ctor_get(v_memo_274_, 0);
        leanh::lean_inc(v_val_279_);
        leanh::lean_dec_ref_known(v_memo_274_, 1);
        v___x_280_ = leanh::lean_apply_1(v_h__2_276_, v_val_279_);
        return v___x_280_;
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_IterM_step__intermediateZip_match__3_splitter___boxed(
    mut v_00_u03b1_u2081_281_: *mut leanh::LeanObject,
    mut v_00_u03b2_u2081_282_: *mut leanh::LeanObject,
    mut v_m_283_: *mut leanh::LeanObject,
    mut v_inst_284_: *mut leanh::LeanObject,
    mut v_motive_285_: *mut leanh::LeanObject,
    mut v_memo_286_: *mut leanh::LeanObject,
    mut v_h__1_287_: *mut leanh::LeanObject,
    mut v_h__2_288_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_289_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_289_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_IterM_step__intermediateZip_match__3_splitter(v_00_u03b1_u2081_281_, v_00_u03b2_u2081_282_, v_m_283_, v_inst_284_, v_motive_285_, v_memo_286_, v_h__1_287_, v_h__2_288_);
    leanh::lean_dec(v_inst_284_);
    return v_res_289_;
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_IterM_step__intermediateZip_match__1_splitter___redArg(
    mut v_x_290_: *mut leanh::LeanObject,
    mut v_h__1_291_: *mut leanh::LeanObject,
    mut v_h__2_292_: *mut leanh::LeanObject,
    mut v_h__3_293_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_290_) {
        0 => {
            let mut v_it_294_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_295_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_296_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_293_);
            leanh::lean_dec(v_h__2_292_);
            v_it_294_ = leanh::lean_ctor_get(v_x_290_, 0);
            leanh::lean_inc(v_it_294_);
            v_out_295_ = leanh::lean_ctor_get(v_x_290_, 1);
            leanh::lean_inc(v_out_295_);
            leanh::lean_dec_ref_known(v_x_290_, 2);
            v___x_296_ = leanh::lean_apply_3(
                v_h__1_291_,
                v_it_294_,
                v_out_295_,
                leanh::lean_box(0),
            );
            return v___x_296_;
        }
        1 => {
            let mut v_it_297_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_298_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_293_);
            leanh::lean_dec(v_h__1_291_);
            v_it_297_ = leanh::lean_ctor_get(v_x_290_, 0);
            leanh::lean_inc(v_it_297_);
            leanh::lean_dec_ref_known(v_x_290_, 1);
            v___x_298_ =
                leanh::lean_apply_2(v_h__2_292_, v_it_297_, leanh::lean_box(0));
            return v___x_298_;
        }
        _ => {
            let mut v___x_299_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_292_);
            leanh::lean_dec(v_h__1_291_);
            v___x_299_ = leanh::lean_apply_1(v_h__3_293_, leanh::lean_box(0));
            return v___x_299_;
        }
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_IterM_step__intermediateZip_match__1_splitter(
    mut v_00_u03b1_u2081_300_: *mut leanh::LeanObject,
    mut v_00_u03b2_u2081_301_: *mut leanh::LeanObject,
    mut v_m_302_: *mut leanh::LeanObject,
    mut v_inst_303_: *mut leanh::LeanObject,
    mut v_it_u2081_304_: *mut leanh::LeanObject,
    mut v_motive_305_: *mut leanh::LeanObject,
    mut v_x_306_: *mut leanh::LeanObject,
    mut v_h__1_307_: *mut leanh::LeanObject,
    mut v_h__2_308_: *mut leanh::LeanObject,
    mut v_h__3_309_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_306_) {
        0 => {
            let mut v_it_310_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_311_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_312_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_309_);
            leanh::lean_dec(v_h__2_308_);
            v_it_310_ = leanh::lean_ctor_get(v_x_306_, 0);
            leanh::lean_inc(v_it_310_);
            v_out_311_ = leanh::lean_ctor_get(v_x_306_, 1);
            leanh::lean_inc(v_out_311_);
            leanh::lean_dec_ref_known(v_x_306_, 2);
            v___x_312_ = leanh::lean_apply_3(
                v_h__1_307_,
                v_it_310_,
                v_out_311_,
                leanh::lean_box(0),
            );
            return v___x_312_;
        }
        1 => {
            let mut v_it_313_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_314_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_309_);
            leanh::lean_dec(v_h__1_307_);
            v_it_313_ = leanh::lean_ctor_get(v_x_306_, 0);
            leanh::lean_inc(v_it_313_);
            leanh::lean_dec_ref_known(v_x_306_, 1);
            v___x_314_ =
                leanh::lean_apply_2(v_h__2_308_, v_it_313_, leanh::lean_box(0));
            return v___x_314_;
        }
        _ => {
            let mut v___x_315_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_308_);
            leanh::lean_dec(v_h__1_307_);
            v___x_315_ = leanh::lean_apply_1(v_h__3_309_, leanh::lean_box(0));
            return v___x_315_;
        }
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_IterM_step__intermediateZip_match__1_splitter___boxed(
    mut v_00_u03b1_u2081_316_: *mut leanh::LeanObject,
    mut v_00_u03b2_u2081_317_: *mut leanh::LeanObject,
    mut v_m_318_: *mut leanh::LeanObject,
    mut v_inst_319_: *mut leanh::LeanObject,
    mut v_it_u2081_320_: *mut leanh::LeanObject,
    mut v_motive_321_: *mut leanh::LeanObject,
    mut v_x_322_: *mut leanh::LeanObject,
    mut v_h__1_323_: *mut leanh::LeanObject,
    mut v_h__2_324_: *mut leanh::LeanObject,
    mut v_h__3_325_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_326_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_326_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_IterM_step__intermediateZip_match__1_splitter(v_00_u03b1_u2081_316_, v_00_u03b2_u2081_317_, v_m_318_, v_inst_319_, v_it_u2081_320_, v_motive_321_, v_x_322_, v_h__1_323_, v_h__2_324_, v_h__3_325_);
    leanh::lean_dec(v_it_u2081_320_);
    leanh::lean_dec(v_inst_319_);
    return v_res_326_;
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_step__intermediateZip_match__3_splitter___redArg(
    mut v_memo_327_: *mut leanh::LeanObject,
    mut v_h__1_328_: *mut leanh::LeanObject,
    mut v_h__2_329_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_memo_327_) == 0 {
        let mut v___x_330_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_331_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_329_);
        v___x_330_ = leanh::lean_box(0);
        v___x_331_ = leanh::lean_apply_1(v_h__1_328_, v___x_330_);
        return v___x_331_;
    } else {
        let mut v_val_332_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_333_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_328_);
        v_val_332_ = leanh::lean_ctor_get(v_memo_327_, 0);
        leanh::lean_inc(v_val_332_);
        leanh::lean_dec_ref_known(v_memo_327_, 1);
        v___x_333_ = leanh::lean_apply_1(v_h__2_329_, v_val_332_);
        return v___x_333_;
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_step__intermediateZip_match__3_splitter(
    mut v_00_u03b1_u2081_334_: *mut leanh::LeanObject,
    mut v_00_u03b2_u2081_335_: *mut leanh::LeanObject,
    mut v_inst_336_: *mut leanh::LeanObject,
    mut v_motive_337_: *mut leanh::LeanObject,
    mut v_memo_338_: *mut leanh::LeanObject,
    mut v_h__1_339_: *mut leanh::LeanObject,
    mut v_h__2_340_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_memo_338_) == 0 {
        let mut v___x_341_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_342_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_340_);
        v___x_341_ = leanh::lean_box(0);
        v___x_342_ = leanh::lean_apply_1(v_h__1_339_, v___x_341_);
        return v___x_342_;
    } else {
        let mut v_val_343_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_344_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_339_);
        v_val_343_ = leanh::lean_ctor_get(v_memo_338_, 0);
        leanh::lean_inc(v_val_343_);
        leanh::lean_dec_ref_known(v_memo_338_, 1);
        v___x_344_ = leanh::lean_apply_1(v_h__2_340_, v_val_343_);
        return v___x_344_;
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_step__intermediateZip_match__3_splitter___boxed(
    mut v_00_u03b1_u2081_345_: *mut leanh::LeanObject,
    mut v_00_u03b2_u2081_346_: *mut leanh::LeanObject,
    mut v_inst_347_: *mut leanh::LeanObject,
    mut v_motive_348_: *mut leanh::LeanObject,
    mut v_memo_349_: *mut leanh::LeanObject,
    mut v_h__1_350_: *mut leanh::LeanObject,
    mut v_h__2_351_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_352_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_352_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_step__intermediateZip_match__3_splitter(v_00_u03b1_u2081_345_, v_00_u03b2_u2081_346_, v_inst_347_, v_motive_348_, v_memo_349_, v_h__1_350_, v_h__2_351_);
    leanh::lean_dec(v_inst_347_);
    return v_res_352_;
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_step__intermediateZip_match__1_splitter___redArg(
    mut v_x_353_: *mut leanh::LeanObject,
    mut v_h__1_354_: *mut leanh::LeanObject,
    mut v_h__2_355_: *mut leanh::LeanObject,
    mut v_h__3_356_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_353_) {
        0 => {
            let mut v_it_357_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_358_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_359_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_356_);
            leanh::lean_dec(v_h__2_355_);
            v_it_357_ = leanh::lean_ctor_get(v_x_353_, 0);
            leanh::lean_inc(v_it_357_);
            v_out_358_ = leanh::lean_ctor_get(v_x_353_, 1);
            leanh::lean_inc(v_out_358_);
            leanh::lean_dec_ref_known(v_x_353_, 2);
            v___x_359_ = leanh::lean_apply_3(
                v_h__1_354_,
                v_it_357_,
                v_out_358_,
                leanh::lean_box(0),
            );
            return v___x_359_;
        }
        1 => {
            let mut v_it_360_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_361_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_356_);
            leanh::lean_dec(v_h__1_354_);
            v_it_360_ = leanh::lean_ctor_get(v_x_353_, 0);
            leanh::lean_inc(v_it_360_);
            leanh::lean_dec_ref_known(v_x_353_, 1);
            v___x_361_ =
                leanh::lean_apply_2(v_h__2_355_, v_it_360_, leanh::lean_box(0));
            return v___x_361_;
        }
        _ => {
            let mut v___x_362_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_355_);
            leanh::lean_dec(v_h__1_354_);
            v___x_362_ = leanh::lean_apply_1(v_h__3_356_, leanh::lean_box(0));
            return v___x_362_;
        }
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_step__intermediateZip_match__1_splitter(
    mut v_00_u03b1_u2081_363_: *mut leanh::LeanObject,
    mut v_00_u03b2_u2081_364_: *mut leanh::LeanObject,
    mut v_inst_365_: *mut leanh::LeanObject,
    mut v_it_u2081_366_: *mut leanh::LeanObject,
    mut v_motive_367_: *mut leanh::LeanObject,
    mut v_x_368_: *mut leanh::LeanObject,
    mut v_h__1_369_: *mut leanh::LeanObject,
    mut v_h__2_370_: *mut leanh::LeanObject,
    mut v_h__3_371_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_368_) {
        0 => {
            let mut v_it_372_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_373_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_374_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_371_);
            leanh::lean_dec(v_h__2_370_);
            v_it_372_ = leanh::lean_ctor_get(v_x_368_, 0);
            leanh::lean_inc(v_it_372_);
            v_out_373_ = leanh::lean_ctor_get(v_x_368_, 1);
            leanh::lean_inc(v_out_373_);
            leanh::lean_dec_ref_known(v_x_368_, 2);
            v___x_374_ = leanh::lean_apply_3(
                v_h__1_369_,
                v_it_372_,
                v_out_373_,
                leanh::lean_box(0),
            );
            return v___x_374_;
        }
        1 => {
            let mut v_it_375_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_376_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_371_);
            leanh::lean_dec(v_h__1_369_);
            v_it_375_ = leanh::lean_ctor_get(v_x_368_, 0);
            leanh::lean_inc(v_it_375_);
            leanh::lean_dec_ref_known(v_x_368_, 1);
            v___x_376_ =
                leanh::lean_apply_2(v_h__2_370_, v_it_375_, leanh::lean_box(0));
            return v___x_376_;
        }
        _ => {
            let mut v___x_377_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_370_);
            leanh::lean_dec(v_h__1_369_);
            v___x_377_ = leanh::lean_apply_1(v_h__3_371_, leanh::lean_box(0));
            return v___x_377_;
        }
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_step__intermediateZip_match__1_splitter___boxed(
    mut v_00_u03b1_u2081_378_: *mut leanh::LeanObject,
    mut v_00_u03b2_u2081_379_: *mut leanh::LeanObject,
    mut v_inst_380_: *mut leanh::LeanObject,
    mut v_it_u2081_381_: *mut leanh::LeanObject,
    mut v_motive_382_: *mut leanh::LeanObject,
    mut v_x_383_: *mut leanh::LeanObject,
    mut v_h__1_384_: *mut leanh::LeanObject,
    mut v_h__2_385_: *mut leanh::LeanObject,
    mut v_h__3_386_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_387_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_387_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_step__intermediateZip_match__1_splitter(v_00_u03b1_u2081_378_, v_00_u03b2_u2081_379_, v_inst_380_, v_it_u2081_381_, v_motive_382_, v_x_383_, v_h__1_384_, v_h__2_385_, v_h__3_386_);
    leanh::lean_dec(v_it_u2081_381_);
    leanh::lean_dec(v_inst_380_);
    return v_res_387_;
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f_match__3_splitter___redArg(
    mut v_x_388_: *mut leanh::LeanObject,
    mut v_h__1_389_: *mut leanh::LeanObject,
    mut v_h__2_390_: *mut leanh::LeanObject,
    mut v_h__3_391_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_388_) {
        0 => {
            let mut v_it_392_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_393_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_394_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_391_);
            leanh::lean_dec(v_h__2_390_);
            v_it_392_ = leanh::lean_ctor_get(v_x_388_, 0);
            leanh::lean_inc(v_it_392_);
            v_out_393_ = leanh::lean_ctor_get(v_x_388_, 1);
            leanh::lean_inc(v_out_393_);
            leanh::lean_dec_ref_known(v_x_388_, 2);
            v___x_394_ = leanh::lean_apply_3(
                v_h__1_389_,
                v_it_392_,
                v_out_393_,
                leanh::lean_box(0),
            );
            return v___x_394_;
        }
        1 => {
            let mut v_it_395_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_396_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_391_);
            leanh::lean_dec(v_h__1_389_);
            v_it_395_ = leanh::lean_ctor_get(v_x_388_, 0);
            leanh::lean_inc(v_it_395_);
            leanh::lean_dec_ref_known(v_x_388_, 1);
            v___x_396_ =
                leanh::lean_apply_2(v_h__2_390_, v_it_395_, leanh::lean_box(0));
            return v___x_396_;
        }
        _ => {
            let mut v___x_397_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_390_);
            leanh::lean_dec(v_h__1_389_);
            v___x_397_ = leanh::lean_apply_1(v_h__3_391_, leanh::lean_box(0));
            return v___x_397_;
        }
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f_match__3_splitter(
    mut v_00_u03b1_398_: *mut leanh::LeanObject,
    mut v_00_u03b2_399_: *mut leanh::LeanObject,
    mut v_inst_400_: *mut leanh::LeanObject,
    mut v_it_401_: *mut leanh::LeanObject,
    mut v_motive_402_: *mut leanh::LeanObject,
    mut v_x_403_: *mut leanh::LeanObject,
    mut v_h__1_404_: *mut leanh::LeanObject,
    mut v_h__2_405_: *mut leanh::LeanObject,
    mut v_h__3_406_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_403_) {
        0 => {
            let mut v_it_407_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_408_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_409_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_406_);
            leanh::lean_dec(v_h__2_405_);
            v_it_407_ = leanh::lean_ctor_get(v_x_403_, 0);
            leanh::lean_inc(v_it_407_);
            v_out_408_ = leanh::lean_ctor_get(v_x_403_, 1);
            leanh::lean_inc(v_out_408_);
            leanh::lean_dec_ref_known(v_x_403_, 2);
            v___x_409_ = leanh::lean_apply_3(
                v_h__1_404_,
                v_it_407_,
                v_out_408_,
                leanh::lean_box(0),
            );
            return v___x_409_;
        }
        1 => {
            let mut v_it_410_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_411_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_406_);
            leanh::lean_dec(v_h__1_404_);
            v_it_410_ = leanh::lean_ctor_get(v_x_403_, 0);
            leanh::lean_inc(v_it_410_);
            leanh::lean_dec_ref_known(v_x_403_, 1);
            v___x_411_ =
                leanh::lean_apply_2(v_h__2_405_, v_it_410_, leanh::lean_box(0));
            return v___x_411_;
        }
        _ => {
            let mut v___x_412_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_405_);
            leanh::lean_dec(v_h__1_404_);
            v___x_412_ = leanh::lean_apply_1(v_h__3_406_, leanh::lean_box(0));
            return v___x_412_;
        }
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f_match__3_splitter___boxed(
    mut v_00_u03b1_413_: *mut leanh::LeanObject,
    mut v_00_u03b2_414_: *mut leanh::LeanObject,
    mut v_inst_415_: *mut leanh::LeanObject,
    mut v_it_416_: *mut leanh::LeanObject,
    mut v_motive_417_: *mut leanh::LeanObject,
    mut v_x_418_: *mut leanh::LeanObject,
    mut v_h__1_419_: *mut leanh::LeanObject,
    mut v_h__2_420_: *mut leanh::LeanObject,
    mut v_h__3_421_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_422_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_422_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f_match__3_splitter(v_00_u03b1_413_, v_00_u03b2_414_, v_inst_415_, v_it_416_, v_motive_417_, v_x_418_, v_h__1_419_, v_h__2_420_, v_h__3_421_);
    leanh::lean_dec(v_it_416_);
    leanh::lean_dec(v_inst_415_);
    return v_res_422_;
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f_match__1_splitter___redArg(
    mut v_n_423_: *mut leanh::LeanObject,
    mut v_recur_424_: *mut leanh::LeanObject,
    mut v_h__1_425_: *mut leanh::LeanObject,
    mut v_h__2_426_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_428_: u8 = 0;
    v_zero_427_ = leanh::lean_unsigned_to_nat(0);
    v_isZero_428_ = lean_nat_dec_eq(v_n_423_, v_zero_427_);
    if v_isZero_428_ == 1 {
        let mut v___x_429_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_426_);
        v___x_429_ = leanh::lean_apply_1(v_h__1_425_, v_recur_424_);
        return v___x_429_;
    } else {
        let mut v_one_430_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_431_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_432_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_425_);
        v_one_430_ = leanh::lean_unsigned_to_nat(1);
        v_n_431_ = lean_nat_sub(v_n_423_, v_one_430_);
        v___x_432_ = leanh::lean_apply_2(v_h__2_426_, v_n_431_, v_recur_424_);
        return v___x_432_;
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f_match__1_splitter___redArg___boxed(
    mut v_n_433_: *mut leanh::LeanObject,
    mut v_recur_434_: *mut leanh::LeanObject,
    mut v_h__1_435_: *mut leanh::LeanObject,
    mut v_h__2_436_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_437_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_437_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f_match__1_splitter___redArg(v_n_433_, v_recur_434_, v_h__1_435_, v_h__2_436_);
    leanh::lean_dec(v_n_433_);
    return v_res_437_;
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f_match__1_splitter(
    mut v_00_u03b1_438_: *mut leanh::LeanObject,
    mut v_00_u03b2_439_: *mut leanh::LeanObject,
    mut v_inst_440_: *mut leanh::LeanObject,
    mut v_it_441_: *mut leanh::LeanObject,
    mut v_motive_442_: *mut leanh::LeanObject,
    mut v_n_443_: *mut leanh::LeanObject,
    mut v_recur_444_: *mut leanh::LeanObject,
    mut v_h__1_445_: *mut leanh::LeanObject,
    mut v_h__2_446_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_448_: u8 = 0;
    v_zero_447_ = leanh::lean_unsigned_to_nat(0);
    v_isZero_448_ = lean_nat_dec_eq(v_n_443_, v_zero_447_);
    if v_isZero_448_ == 1 {
        let mut v___x_449_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_446_);
        v___x_449_ = leanh::lean_apply_1(v_h__1_445_, v_recur_444_);
        return v___x_449_;
    } else {
        let mut v_one_450_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_451_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_452_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_445_);
        v_one_450_ = leanh::lean_unsigned_to_nat(1);
        v_n_451_ = lean_nat_sub(v_n_443_, v_one_450_);
        v___x_452_ = leanh::lean_apply_2(v_h__2_446_, v_n_451_, v_recur_444_);
        return v___x_452_;
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f_match__1_splitter___boxed(
    mut v_00_u03b1_453_: *mut leanh::LeanObject,
    mut v_00_u03b2_454_: *mut leanh::LeanObject,
    mut v_inst_455_: *mut leanh::LeanObject,
    mut v_it_456_: *mut leanh::LeanObject,
    mut v_motive_457_: *mut leanh::LeanObject,
    mut v_n_458_: *mut leanh::LeanObject,
    mut v_recur_459_: *mut leanh::LeanObject,
    mut v_h__1_460_: *mut leanh::LeanObject,
    mut v_h__2_461_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_462_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_462_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f_match__1_splitter(v_00_u03b1_453_, v_00_u03b2_454_, v_inst_455_, v_it_456_, v_motive_457_, v_n_458_, v_recur_459_, v_h__1_460_, v_h__2_461_);
    leanh::lean_dec(v_n_458_);
    leanh::lean_dec(v_it_456_);
    leanh::lean_dec(v_inst_455_);
    return v_res_462_;
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f__intermediateZip_match__1_splitter___redArg(
    mut v_n_463_: *mut leanh::LeanObject,
    mut v_h__1_464_: *mut leanh::LeanObject,
    mut v_h__2_465_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_467_: u8 = 0;
    v_zero_466_ = leanh::lean_unsigned_to_nat(0);
    v_isZero_467_ = lean_nat_dec_eq(v_n_463_, v_zero_466_);
    if v_isZero_467_ == 1 {
        let mut v___x_468_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_469_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_465_);
        v___x_468_ = leanh::lean_box(0);
        v___x_469_ = leanh::lean_apply_1(v_h__1_464_, v___x_468_);
        return v___x_469_;
    } else {
        let mut v_one_470_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_471_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_472_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_464_);
        v_one_470_ = leanh::lean_unsigned_to_nat(1);
        v_n_471_ = lean_nat_sub(v_n_463_, v_one_470_);
        v___x_472_ = leanh::lean_apply_1(v_h__2_465_, v_n_471_);
        return v___x_472_;
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f__intermediateZip_match__1_splitter___redArg___boxed(
    mut v_n_473_: *mut leanh::LeanObject,
    mut v_h__1_474_: *mut leanh::LeanObject,
    mut v_h__2_475_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_476_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_476_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f__intermediateZip_match__1_splitter___redArg(v_n_473_, v_h__1_474_, v_h__2_475_);
    leanh::lean_dec(v_n_473_);
    return v_res_476_;
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f__intermediateZip_match__1_splitter(
    mut v_motive_477_: *mut leanh::LeanObject,
    mut v_n_478_: *mut leanh::LeanObject,
    mut v_h__1_479_: *mut leanh::LeanObject,
    mut v_h__2_480_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_482_: u8 = 0;
    v_zero_481_ = leanh::lean_unsigned_to_nat(0);
    v_isZero_482_ = lean_nat_dec_eq(v_n_478_, v_zero_481_);
    if v_isZero_482_ == 1 {
        let mut v___x_483_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_484_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_480_);
        v___x_483_ = leanh::lean_box(0);
        v___x_484_ = leanh::lean_apply_1(v_h__1_479_, v___x_483_);
        return v___x_484_;
    } else {
        let mut v_one_485_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_486_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_487_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_479_);
        v_one_485_ = leanh::lean_unsigned_to_nat(1);
        v_n_486_ = lean_nat_sub(v_n_478_, v_one_485_);
        v___x_487_ = leanh::lean_apply_1(v_h__2_480_, v_n_486_);
        return v___x_487_;
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f__intermediateZip_match__1_splitter___boxed(
    mut v_motive_488_: *mut leanh::LeanObject,
    mut v_n_489_: *mut leanh::LeanObject,
    mut v_h__1_490_: *mut leanh::LeanObject,
    mut v_h__2_491_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_492_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_492_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f__intermediateZip_match__1_splitter(v_motive_488_, v_n_489_, v_h__1_490_, v_h__2_491_);
    leanh::lean_dec(v_n_489_);
    return v_res_492_;
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f__eq__match_match__1_splitter___redArg(
    mut v_n_493_: *mut leanh::LeanObject,
    mut v_h__1_494_: *mut leanh::LeanObject,
    mut v_h__2_495_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_497_: u8 = 0;
    v_zero_496_ = leanh::lean_unsigned_to_nat(0);
    v_isZero_497_ = lean_nat_dec_eq(v_n_493_, v_zero_496_);
    if v_isZero_497_ == 1 {
        let mut v___x_498_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_499_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_495_);
        v___x_498_ = leanh::lean_box(0);
        v___x_499_ = leanh::lean_apply_1(v_h__1_494_, v___x_498_);
        return v___x_499_;
    } else {
        let mut v_one_500_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_501_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_502_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_494_);
        v_one_500_ = leanh::lean_unsigned_to_nat(1);
        v_n_501_ = lean_nat_sub(v_n_493_, v_one_500_);
        v___x_502_ = leanh::lean_apply_1(v_h__2_495_, v_n_501_);
        return v___x_502_;
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f__eq__match_match__1_splitter___redArg___boxed(
    mut v_n_503_: *mut leanh::LeanObject,
    mut v_h__1_504_: *mut leanh::LeanObject,
    mut v_h__2_505_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_506_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_506_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f__eq__match_match__1_splitter___redArg(v_n_503_, v_h__1_504_, v_h__2_505_);
    leanh::lean_dec(v_n_503_);
    return v_res_506_;
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f__eq__match_match__1_splitter(
    mut v_motive_507_: *mut leanh::LeanObject,
    mut v_n_508_: *mut leanh::LeanObject,
    mut v_h__1_509_: *mut leanh::LeanObject,
    mut v_h__2_510_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_512_: u8 = 0;
    v_zero_511_ = leanh::lean_unsigned_to_nat(0);
    v_isZero_512_ = lean_nat_dec_eq(v_n_508_, v_zero_511_);
    if v_isZero_512_ == 1 {
        let mut v___x_513_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_514_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_510_);
        v___x_513_ = leanh::lean_box(0);
        v___x_514_ = leanh::lean_apply_1(v_h__1_509_, v___x_513_);
        return v___x_514_;
    } else {
        let mut v_one_515_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_516_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_517_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_509_);
        v_one_515_ = leanh::lean_unsigned_to_nat(1);
        v_n_516_ = lean_nat_sub(v_n_508_, v_one_515_);
        v___x_517_ = leanh::lean_apply_1(v_h__2_510_, v_n_516_);
        return v___x_517_;
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f__eq__match_match__1_splitter___boxed(
    mut v_motive_518_: *mut leanh::LeanObject,
    mut v_n_519_: *mut leanh::LeanObject,
    mut v_h__1_520_: *mut leanh::LeanObject,
    mut v_h__2_521_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_522_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_522_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f__eq__match_match__1_splitter(v_motive_518_, v_n_519_, v_h__1_520_, v_h__2_521_);
    leanh::lean_dec(v_n_519_);
    return v_res_522_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_Iterators_Lemmas_Combinators_Zip(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_Iterators_Combinators_Zip(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_Zip(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_Take(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Access(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_ToArray(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Zip(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_Iterators_Lemmas_Combinators_Zip(
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
pub unsafe fn initialize_Std_Data_Iterators_Lemmas_Combinators_Zip(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_Iterators_Combinators_Zip(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_Zip(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Combinators_Take(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Consumers_Access(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_ToArray(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Zip(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Lemmas_Combinators_Zip(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Data_Iterators_Lemmas_Combinators_Zip(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Data_Iterators_Lemmas_Combinators_Zip(builtin);
}