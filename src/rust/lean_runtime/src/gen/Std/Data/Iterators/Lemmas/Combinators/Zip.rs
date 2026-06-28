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
use crate::lean_imports_rs::Init::Prelude::{lean_nat_dec_eq, lean_nat_sub};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_apply_1, lean_apply_2, lean_apply_3, lean_box,
    lean_ctor_get, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_obj_tag, lean_unsigned_to_nat,
};
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_IterM_step__intermediateZip_match__3_splitter___redArg(
    mut v_memo_262_: *mut LeanObject,
    mut v_h__1_263_: *mut LeanObject,
    mut v_h__2_264_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_memo_262_) == 0 {
        let mut v___x_265_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_266_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_264_);
        v___x_265_ = lean_box(0);
        v___x_266_ = lean_apply_1(v_h__1_263_, v___x_265_);
        return v___x_266_;
    } else {
        let mut v_val_267_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_268_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_263_);
        v_val_267_ = lean_ctor_get(v_memo_262_, 0);
        lean_inc(v_val_267_);
        lean_dec_ref_known(v_memo_262_, 1);
        v___x_268_ = lean_apply_1(v_h__2_264_, v_val_267_);
        return v___x_268_;
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_IterM_step__intermediateZip_match__3_splitter(
    mut v_00_u03b1_u2081_269_: *mut LeanObject,
    mut v_00_u03b2_u2081_270_: *mut LeanObject,
    mut v_m_271_: *mut LeanObject,
    mut v_inst_272_: *mut LeanObject,
    mut v_motive_273_: *mut LeanObject,
    mut v_memo_274_: *mut LeanObject,
    mut v_h__1_275_: *mut LeanObject,
    mut v_h__2_276_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_memo_274_) == 0 {
        let mut v___x_277_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_278_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_276_);
        v___x_277_ = lean_box(0);
        v___x_278_ = lean_apply_1(v_h__1_275_, v___x_277_);
        return v___x_278_;
    } else {
        let mut v_val_279_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_280_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_275_);
        v_val_279_ = lean_ctor_get(v_memo_274_, 0);
        lean_inc(v_val_279_);
        lean_dec_ref_known(v_memo_274_, 1);
        v___x_280_ = lean_apply_1(v_h__2_276_, v_val_279_);
        return v___x_280_;
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_IterM_step__intermediateZip_match__3_splitter___boxed(
    mut v_00_u03b1_u2081_281_: *mut LeanObject,
    mut v_00_u03b2_u2081_282_: *mut LeanObject,
    mut v_m_283_: *mut LeanObject,
    mut v_inst_284_: *mut LeanObject,
    mut v_motive_285_: *mut LeanObject,
    mut v_memo_286_: *mut LeanObject,
    mut v_h__1_287_: *mut LeanObject,
    mut v_h__2_288_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_289_: *mut LeanObject = core::ptr::null_mut();
    v_res_289_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_IterM_step__intermediateZip_match__3_splitter(v_00_u03b1_u2081_281_, v_00_u03b2_u2081_282_, v_m_283_, v_inst_284_, v_motive_285_, v_memo_286_, v_h__1_287_, v_h__2_288_);
    lean_dec(v_inst_284_);
    return v_res_289_;
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_IterM_step__intermediateZip_match__1_splitter___redArg(
    mut v_x_290_: *mut LeanObject,
    mut v_h__1_291_: *mut LeanObject,
    mut v_h__2_292_: *mut LeanObject,
    mut v_h__3_293_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_290_) {
        0 => {
            let mut v_it_294_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_295_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_296_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_293_);
            lean_dec(v_h__2_292_);
            v_it_294_ = lean_ctor_get(v_x_290_, 0);
            lean_inc(v_it_294_);
            v_out_295_ = lean_ctor_get(v_x_290_, 1);
            lean_inc(v_out_295_);
            lean_dec_ref_known(v_x_290_, 2);
            v___x_296_ = lean_apply_3(v_h__1_291_, v_it_294_, v_out_295_, lean_box(0));
            return v___x_296_;
        }
        1 => {
            let mut v_it_297_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_298_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_293_);
            lean_dec(v_h__1_291_);
            v_it_297_ = lean_ctor_get(v_x_290_, 0);
            lean_inc(v_it_297_);
            lean_dec_ref_known(v_x_290_, 1);
            v___x_298_ = lean_apply_2(v_h__2_292_, v_it_297_, lean_box(0));
            return v___x_298_;
        }
        _ => {
            let mut v___x_299_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_292_);
            lean_dec(v_h__1_291_);
            v___x_299_ = lean_apply_1(v_h__3_293_, lean_box(0));
            return v___x_299_;
        }
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_IterM_step__intermediateZip_match__1_splitter(
    mut v_00_u03b1_u2081_300_: *mut LeanObject,
    mut v_00_u03b2_u2081_301_: *mut LeanObject,
    mut v_m_302_: *mut LeanObject,
    mut v_inst_303_: *mut LeanObject,
    mut v_it_u2081_304_: *mut LeanObject,
    mut v_motive_305_: *mut LeanObject,
    mut v_x_306_: *mut LeanObject,
    mut v_h__1_307_: *mut LeanObject,
    mut v_h__2_308_: *mut LeanObject,
    mut v_h__3_309_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_306_) {
        0 => {
            let mut v_it_310_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_311_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_312_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_309_);
            lean_dec(v_h__2_308_);
            v_it_310_ = lean_ctor_get(v_x_306_, 0);
            lean_inc(v_it_310_);
            v_out_311_ = lean_ctor_get(v_x_306_, 1);
            lean_inc(v_out_311_);
            lean_dec_ref_known(v_x_306_, 2);
            v___x_312_ = lean_apply_3(v_h__1_307_, v_it_310_, v_out_311_, lean_box(0));
            return v___x_312_;
        }
        1 => {
            let mut v_it_313_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_314_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_309_);
            lean_dec(v_h__1_307_);
            v_it_313_ = lean_ctor_get(v_x_306_, 0);
            lean_inc(v_it_313_);
            lean_dec_ref_known(v_x_306_, 1);
            v___x_314_ = lean_apply_2(v_h__2_308_, v_it_313_, lean_box(0));
            return v___x_314_;
        }
        _ => {
            let mut v___x_315_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_308_);
            lean_dec(v_h__1_307_);
            v___x_315_ = lean_apply_1(v_h__3_309_, lean_box(0));
            return v___x_315_;
        }
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_IterM_step__intermediateZip_match__1_splitter___boxed(
    mut v_00_u03b1_u2081_316_: *mut LeanObject,
    mut v_00_u03b2_u2081_317_: *mut LeanObject,
    mut v_m_318_: *mut LeanObject,
    mut v_inst_319_: *mut LeanObject,
    mut v_it_u2081_320_: *mut LeanObject,
    mut v_motive_321_: *mut LeanObject,
    mut v_x_322_: *mut LeanObject,
    mut v_h__1_323_: *mut LeanObject,
    mut v_h__2_324_: *mut LeanObject,
    mut v_h__3_325_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_326_: *mut LeanObject = core::ptr::null_mut();
    v_res_326_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_IterM_step__intermediateZip_match__1_splitter(v_00_u03b1_u2081_316_, v_00_u03b2_u2081_317_, v_m_318_, v_inst_319_, v_it_u2081_320_, v_motive_321_, v_x_322_, v_h__1_323_, v_h__2_324_, v_h__3_325_);
    lean_dec(v_it_u2081_320_);
    lean_dec(v_inst_319_);
    return v_res_326_;
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_step__intermediateZip_match__3_splitter___redArg(
    mut v_memo_327_: *mut LeanObject,
    mut v_h__1_328_: *mut LeanObject,
    mut v_h__2_329_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_memo_327_) == 0 {
        let mut v___x_330_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_331_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_329_);
        v___x_330_ = lean_box(0);
        v___x_331_ = lean_apply_1(v_h__1_328_, v___x_330_);
        return v___x_331_;
    } else {
        let mut v_val_332_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_333_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_328_);
        v_val_332_ = lean_ctor_get(v_memo_327_, 0);
        lean_inc(v_val_332_);
        lean_dec_ref_known(v_memo_327_, 1);
        v___x_333_ = lean_apply_1(v_h__2_329_, v_val_332_);
        return v___x_333_;
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_step__intermediateZip_match__3_splitter(
    mut v_00_u03b1_u2081_334_: *mut LeanObject,
    mut v_00_u03b2_u2081_335_: *mut LeanObject,
    mut v_inst_336_: *mut LeanObject,
    mut v_motive_337_: *mut LeanObject,
    mut v_memo_338_: *mut LeanObject,
    mut v_h__1_339_: *mut LeanObject,
    mut v_h__2_340_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_memo_338_) == 0 {
        let mut v___x_341_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_342_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_340_);
        v___x_341_ = lean_box(0);
        v___x_342_ = lean_apply_1(v_h__1_339_, v___x_341_);
        return v___x_342_;
    } else {
        let mut v_val_343_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_344_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_339_);
        v_val_343_ = lean_ctor_get(v_memo_338_, 0);
        lean_inc(v_val_343_);
        lean_dec_ref_known(v_memo_338_, 1);
        v___x_344_ = lean_apply_1(v_h__2_340_, v_val_343_);
        return v___x_344_;
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_step__intermediateZip_match__3_splitter___boxed(
    mut v_00_u03b1_u2081_345_: *mut LeanObject,
    mut v_00_u03b2_u2081_346_: *mut LeanObject,
    mut v_inst_347_: *mut LeanObject,
    mut v_motive_348_: *mut LeanObject,
    mut v_memo_349_: *mut LeanObject,
    mut v_h__1_350_: *mut LeanObject,
    mut v_h__2_351_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_352_: *mut LeanObject = core::ptr::null_mut();
    v_res_352_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_step__intermediateZip_match__3_splitter(v_00_u03b1_u2081_345_, v_00_u03b2_u2081_346_, v_inst_347_, v_motive_348_, v_memo_349_, v_h__1_350_, v_h__2_351_);
    lean_dec(v_inst_347_);
    return v_res_352_;
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_step__intermediateZip_match__1_splitter___redArg(
    mut v_x_353_: *mut LeanObject,
    mut v_h__1_354_: *mut LeanObject,
    mut v_h__2_355_: *mut LeanObject,
    mut v_h__3_356_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_353_) {
        0 => {
            let mut v_it_357_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_358_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_359_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_356_);
            lean_dec(v_h__2_355_);
            v_it_357_ = lean_ctor_get(v_x_353_, 0);
            lean_inc(v_it_357_);
            v_out_358_ = lean_ctor_get(v_x_353_, 1);
            lean_inc(v_out_358_);
            lean_dec_ref_known(v_x_353_, 2);
            v___x_359_ = lean_apply_3(v_h__1_354_, v_it_357_, v_out_358_, lean_box(0));
            return v___x_359_;
        }
        1 => {
            let mut v_it_360_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_361_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_356_);
            lean_dec(v_h__1_354_);
            v_it_360_ = lean_ctor_get(v_x_353_, 0);
            lean_inc(v_it_360_);
            lean_dec_ref_known(v_x_353_, 1);
            v___x_361_ = lean_apply_2(v_h__2_355_, v_it_360_, lean_box(0));
            return v___x_361_;
        }
        _ => {
            let mut v___x_362_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_355_);
            lean_dec(v_h__1_354_);
            v___x_362_ = lean_apply_1(v_h__3_356_, lean_box(0));
            return v___x_362_;
        }
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_step__intermediateZip_match__1_splitter(
    mut v_00_u03b1_u2081_363_: *mut LeanObject,
    mut v_00_u03b2_u2081_364_: *mut LeanObject,
    mut v_inst_365_: *mut LeanObject,
    mut v_it_u2081_366_: *mut LeanObject,
    mut v_motive_367_: *mut LeanObject,
    mut v_x_368_: *mut LeanObject,
    mut v_h__1_369_: *mut LeanObject,
    mut v_h__2_370_: *mut LeanObject,
    mut v_h__3_371_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_368_) {
        0 => {
            let mut v_it_372_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_373_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_374_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_371_);
            lean_dec(v_h__2_370_);
            v_it_372_ = lean_ctor_get(v_x_368_, 0);
            lean_inc(v_it_372_);
            v_out_373_ = lean_ctor_get(v_x_368_, 1);
            lean_inc(v_out_373_);
            lean_dec_ref_known(v_x_368_, 2);
            v___x_374_ = lean_apply_3(v_h__1_369_, v_it_372_, v_out_373_, lean_box(0));
            return v___x_374_;
        }
        1 => {
            let mut v_it_375_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_376_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_371_);
            lean_dec(v_h__1_369_);
            v_it_375_ = lean_ctor_get(v_x_368_, 0);
            lean_inc(v_it_375_);
            lean_dec_ref_known(v_x_368_, 1);
            v___x_376_ = lean_apply_2(v_h__2_370_, v_it_375_, lean_box(0));
            return v___x_376_;
        }
        _ => {
            let mut v___x_377_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_370_);
            lean_dec(v_h__1_369_);
            v___x_377_ = lean_apply_1(v_h__3_371_, lean_box(0));
            return v___x_377_;
        }
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_step__intermediateZip_match__1_splitter___boxed(
    mut v_00_u03b1_u2081_378_: *mut LeanObject,
    mut v_00_u03b2_u2081_379_: *mut LeanObject,
    mut v_inst_380_: *mut LeanObject,
    mut v_it_u2081_381_: *mut LeanObject,
    mut v_motive_382_: *mut LeanObject,
    mut v_x_383_: *mut LeanObject,
    mut v_h__1_384_: *mut LeanObject,
    mut v_h__2_385_: *mut LeanObject,
    mut v_h__3_386_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_387_: *mut LeanObject = core::ptr::null_mut();
    v_res_387_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_step__intermediateZip_match__1_splitter(v_00_u03b1_u2081_378_, v_00_u03b2_u2081_379_, v_inst_380_, v_it_u2081_381_, v_motive_382_, v_x_383_, v_h__1_384_, v_h__2_385_, v_h__3_386_);
    lean_dec(v_it_u2081_381_);
    lean_dec(v_inst_380_);
    return v_res_387_;
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f_match__3_splitter___redArg(
    mut v_x_388_: *mut LeanObject,
    mut v_h__1_389_: *mut LeanObject,
    mut v_h__2_390_: *mut LeanObject,
    mut v_h__3_391_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_388_) {
        0 => {
            let mut v_it_392_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_393_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_394_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_391_);
            lean_dec(v_h__2_390_);
            v_it_392_ = lean_ctor_get(v_x_388_, 0);
            lean_inc(v_it_392_);
            v_out_393_ = lean_ctor_get(v_x_388_, 1);
            lean_inc(v_out_393_);
            lean_dec_ref_known(v_x_388_, 2);
            v___x_394_ = lean_apply_3(v_h__1_389_, v_it_392_, v_out_393_, lean_box(0));
            return v___x_394_;
        }
        1 => {
            let mut v_it_395_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_396_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_391_);
            lean_dec(v_h__1_389_);
            v_it_395_ = lean_ctor_get(v_x_388_, 0);
            lean_inc(v_it_395_);
            lean_dec_ref_known(v_x_388_, 1);
            v___x_396_ = lean_apply_2(v_h__2_390_, v_it_395_, lean_box(0));
            return v___x_396_;
        }
        _ => {
            let mut v___x_397_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_390_);
            lean_dec(v_h__1_389_);
            v___x_397_ = lean_apply_1(v_h__3_391_, lean_box(0));
            return v___x_397_;
        }
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f_match__3_splitter(
    mut v_00_u03b1_398_: *mut LeanObject,
    mut v_00_u03b2_399_: *mut LeanObject,
    mut v_inst_400_: *mut LeanObject,
    mut v_it_401_: *mut LeanObject,
    mut v_motive_402_: *mut LeanObject,
    mut v_x_403_: *mut LeanObject,
    mut v_h__1_404_: *mut LeanObject,
    mut v_h__2_405_: *mut LeanObject,
    mut v_h__3_406_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_403_) {
        0 => {
            let mut v_it_407_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_408_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_409_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_406_);
            lean_dec(v_h__2_405_);
            v_it_407_ = lean_ctor_get(v_x_403_, 0);
            lean_inc(v_it_407_);
            v_out_408_ = lean_ctor_get(v_x_403_, 1);
            lean_inc(v_out_408_);
            lean_dec_ref_known(v_x_403_, 2);
            v___x_409_ = lean_apply_3(v_h__1_404_, v_it_407_, v_out_408_, lean_box(0));
            return v___x_409_;
        }
        1 => {
            let mut v_it_410_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_411_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_406_);
            lean_dec(v_h__1_404_);
            v_it_410_ = lean_ctor_get(v_x_403_, 0);
            lean_inc(v_it_410_);
            lean_dec_ref_known(v_x_403_, 1);
            v___x_411_ = lean_apply_2(v_h__2_405_, v_it_410_, lean_box(0));
            return v___x_411_;
        }
        _ => {
            let mut v___x_412_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_405_);
            lean_dec(v_h__1_404_);
            v___x_412_ = lean_apply_1(v_h__3_406_, lean_box(0));
            return v___x_412_;
        }
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f_match__3_splitter___boxed(
    mut v_00_u03b1_413_: *mut LeanObject,
    mut v_00_u03b2_414_: *mut LeanObject,
    mut v_inst_415_: *mut LeanObject,
    mut v_it_416_: *mut LeanObject,
    mut v_motive_417_: *mut LeanObject,
    mut v_x_418_: *mut LeanObject,
    mut v_h__1_419_: *mut LeanObject,
    mut v_h__2_420_: *mut LeanObject,
    mut v_h__3_421_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_422_: *mut LeanObject = core::ptr::null_mut();
    v_res_422_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f_match__3_splitter(v_00_u03b1_413_, v_00_u03b2_414_, v_inst_415_, v_it_416_, v_motive_417_, v_x_418_, v_h__1_419_, v_h__2_420_, v_h__3_421_);
    lean_dec(v_it_416_);
    lean_dec(v_inst_415_);
    return v_res_422_;
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f_match__1_splitter___redArg(
    mut v_n_423_: *mut LeanObject,
    mut v_recur_424_: *mut LeanObject,
    mut v_h__1_425_: *mut LeanObject,
    mut v_h__2_426_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_427_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_428_: u8 = 0;
    v_zero_427_ = lean_unsigned_to_nat(0);
    v_isZero_428_ = lean_nat_dec_eq(v_n_423_, v_zero_427_);
    if v_isZero_428_ == 1 {
        let mut v___x_429_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_426_);
        v___x_429_ = lean_apply_1(v_h__1_425_, v_recur_424_);
        return v___x_429_;
    } else {
        let mut v_one_430_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_431_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_432_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_425_);
        v_one_430_ = lean_unsigned_to_nat(1);
        v_n_431_ = lean_nat_sub(v_n_423_, v_one_430_);
        v___x_432_ = lean_apply_2(v_h__2_426_, v_n_431_, v_recur_424_);
        return v___x_432_;
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f_match__1_splitter___redArg___boxed(
    mut v_n_433_: *mut LeanObject,
    mut v_recur_434_: *mut LeanObject,
    mut v_h__1_435_: *mut LeanObject,
    mut v_h__2_436_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_437_: *mut LeanObject = core::ptr::null_mut();
    v_res_437_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f_match__1_splitter___redArg(v_n_433_, v_recur_434_, v_h__1_435_, v_h__2_436_);
    lean_dec(v_n_433_);
    return v_res_437_;
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f_match__1_splitter(
    mut v_00_u03b1_438_: *mut LeanObject,
    mut v_00_u03b2_439_: *mut LeanObject,
    mut v_inst_440_: *mut LeanObject,
    mut v_it_441_: *mut LeanObject,
    mut v_motive_442_: *mut LeanObject,
    mut v_n_443_: *mut LeanObject,
    mut v_recur_444_: *mut LeanObject,
    mut v_h__1_445_: *mut LeanObject,
    mut v_h__2_446_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_447_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_448_: u8 = 0;
    v_zero_447_ = lean_unsigned_to_nat(0);
    v_isZero_448_ = lean_nat_dec_eq(v_n_443_, v_zero_447_);
    if v_isZero_448_ == 1 {
        let mut v___x_449_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_446_);
        v___x_449_ = lean_apply_1(v_h__1_445_, v_recur_444_);
        return v___x_449_;
    } else {
        let mut v_one_450_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_451_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_452_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_445_);
        v_one_450_ = lean_unsigned_to_nat(1);
        v_n_451_ = lean_nat_sub(v_n_443_, v_one_450_);
        v___x_452_ = lean_apply_2(v_h__2_446_, v_n_451_, v_recur_444_);
        return v___x_452_;
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f_match__1_splitter___boxed(
    mut v_00_u03b1_453_: *mut LeanObject,
    mut v_00_u03b2_454_: *mut LeanObject,
    mut v_inst_455_: *mut LeanObject,
    mut v_it_456_: *mut LeanObject,
    mut v_motive_457_: *mut LeanObject,
    mut v_n_458_: *mut LeanObject,
    mut v_recur_459_: *mut LeanObject,
    mut v_h__1_460_: *mut LeanObject,
    mut v_h__2_461_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_462_: *mut LeanObject = core::ptr::null_mut();
    v_res_462_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f_match__1_splitter(v_00_u03b1_453_, v_00_u03b2_454_, v_inst_455_, v_it_456_, v_motive_457_, v_n_458_, v_recur_459_, v_h__1_460_, v_h__2_461_);
    lean_dec(v_n_458_);
    lean_dec(v_it_456_);
    lean_dec(v_inst_455_);
    return v_res_462_;
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f__intermediateZip_match__1_splitter___redArg(
    mut v_n_463_: *mut LeanObject,
    mut v_h__1_464_: *mut LeanObject,
    mut v_h__2_465_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_467_: u8 = 0;
    v_zero_466_ = lean_unsigned_to_nat(0);
    v_isZero_467_ = lean_nat_dec_eq(v_n_463_, v_zero_466_);
    if v_isZero_467_ == 1 {
        let mut v___x_468_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_469_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_465_);
        v___x_468_ = lean_box(0);
        v___x_469_ = lean_apply_1(v_h__1_464_, v___x_468_);
        return v___x_469_;
    } else {
        let mut v_one_470_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_471_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_472_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_464_);
        v_one_470_ = lean_unsigned_to_nat(1);
        v_n_471_ = lean_nat_sub(v_n_463_, v_one_470_);
        v___x_472_ = lean_apply_1(v_h__2_465_, v_n_471_);
        return v___x_472_;
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f__intermediateZip_match__1_splitter___redArg___boxed(
    mut v_n_473_: *mut LeanObject,
    mut v_h__1_474_: *mut LeanObject,
    mut v_h__2_475_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_476_: *mut LeanObject = core::ptr::null_mut();
    v_res_476_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f__intermediateZip_match__1_splitter___redArg(v_n_473_, v_h__1_474_, v_h__2_475_);
    lean_dec(v_n_473_);
    return v_res_476_;
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f__intermediateZip_match__1_splitter(
    mut v_motive_477_: *mut LeanObject,
    mut v_n_478_: *mut LeanObject,
    mut v_h__1_479_: *mut LeanObject,
    mut v_h__2_480_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_481_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_482_: u8 = 0;
    v_zero_481_ = lean_unsigned_to_nat(0);
    v_isZero_482_ = lean_nat_dec_eq(v_n_478_, v_zero_481_);
    if v_isZero_482_ == 1 {
        let mut v___x_483_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_484_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_480_);
        v___x_483_ = lean_box(0);
        v___x_484_ = lean_apply_1(v_h__1_479_, v___x_483_);
        return v___x_484_;
    } else {
        let mut v_one_485_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_486_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_487_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_479_);
        v_one_485_ = lean_unsigned_to_nat(1);
        v_n_486_ = lean_nat_sub(v_n_478_, v_one_485_);
        v___x_487_ = lean_apply_1(v_h__2_480_, v_n_486_);
        return v___x_487_;
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f__intermediateZip_match__1_splitter___boxed(
    mut v_motive_488_: *mut LeanObject,
    mut v_n_489_: *mut LeanObject,
    mut v_h__1_490_: *mut LeanObject,
    mut v_h__2_491_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_492_: *mut LeanObject = core::ptr::null_mut();
    v_res_492_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f__intermediateZip_match__1_splitter(v_motive_488_, v_n_489_, v_h__1_490_, v_h__2_491_);
    lean_dec(v_n_489_);
    return v_res_492_;
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f__eq__match_match__1_splitter___redArg(
    mut v_n_493_: *mut LeanObject,
    mut v_h__1_494_: *mut LeanObject,
    mut v_h__2_495_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_496_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_497_: u8 = 0;
    v_zero_496_ = lean_unsigned_to_nat(0);
    v_isZero_497_ = lean_nat_dec_eq(v_n_493_, v_zero_496_);
    if v_isZero_497_ == 1 {
        let mut v___x_498_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_499_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_495_);
        v___x_498_ = lean_box(0);
        v___x_499_ = lean_apply_1(v_h__1_494_, v___x_498_);
        return v___x_499_;
    } else {
        let mut v_one_500_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_501_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_502_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_494_);
        v_one_500_ = lean_unsigned_to_nat(1);
        v_n_501_ = lean_nat_sub(v_n_493_, v_one_500_);
        v___x_502_ = lean_apply_1(v_h__2_495_, v_n_501_);
        return v___x_502_;
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f__eq__match_match__1_splitter___redArg___boxed(
    mut v_n_503_: *mut LeanObject,
    mut v_h__1_504_: *mut LeanObject,
    mut v_h__2_505_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_506_: *mut LeanObject = core::ptr::null_mut();
    v_res_506_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f__eq__match_match__1_splitter___redArg(v_n_503_, v_h__1_504_, v_h__2_505_);
    lean_dec(v_n_503_);
    return v_res_506_;
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f__eq__match_match__1_splitter(
    mut v_motive_507_: *mut LeanObject,
    mut v_n_508_: *mut LeanObject,
    mut v_h__1_509_: *mut LeanObject,
    mut v_h__2_510_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_512_: u8 = 0;
    v_zero_511_ = lean_unsigned_to_nat(0);
    v_isZero_512_ = lean_nat_dec_eq(v_n_508_, v_zero_511_);
    if v_isZero_512_ == 1 {
        let mut v___x_513_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_514_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_510_);
        v___x_513_ = lean_box(0);
        v___x_514_ = lean_apply_1(v_h__1_509_, v___x_513_);
        return v___x_514_;
    } else {
        let mut v_one_515_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_516_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_517_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_509_);
        v_one_515_ = lean_unsigned_to_nat(1);
        v_n_516_ = lean_nat_sub(v_n_508_, v_one_515_);
        v___x_517_ = lean_apply_1(v_h__2_510_, v_n_516_);
        return v___x_517_;
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f__eq__match_match__1_splitter___boxed(
    mut v_motive_518_: *mut LeanObject,
    mut v_n_519_: *mut LeanObject,
    mut v_h__1_520_: *mut LeanObject,
    mut v_h__2_521_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_522_: *mut LeanObject = core::ptr::null_mut();
    v_res_522_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Zip_0__Std_Iter_atIdxSlow_x3f__eq__match_match__1_splitter(v_motive_518_, v_n_519_, v_h__1_520_, v_h__2_521_);
    lean_dec(v_n_519_);
    return v_res_522_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_Iterators_Lemmas_Combinators_Zip(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_Iterators_Combinators_Zip(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_Zip(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_Take(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Access(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_ToArray(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Zip(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_Iterators_Lemmas_Combinators_Zip(
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
pub unsafe fn initialize_Std_Data_Iterators_Lemmas_Combinators_Zip(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_Iterators_Combinators_Zip(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_Zip(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Combinators_Take(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Consumers_Access(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_ToArray(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_Zip(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Lemmas_Combinators_Zip(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Data_Iterators_Lemmas_Combinators_Zip(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Data_Iterators_Lemmas_Combinators_Zip(builtin);
}
