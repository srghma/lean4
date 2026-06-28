// Lean compiler output
// Module: Init.Data.Iterators.Lemmas.Combinators.Monadic.FlatMap
// Imports: Init.Data.Iterators.Lemmas.Combinators.Monadic.FilterMap Init.Data.Iterators.Combinators.Monadic.FlatMap Init.Data.Iterators.Combinators.Monadic.FlatMap Init.Data.Iterators.Consumers.Monadic.Collect Init.Data.Array.Lemmas Init.Data.Iterators.Lemmas.Consumers.Monadic Init.Data.Iterators.Lemmas.Monadic.Basic
use crate::r#gen::Init::Data::Array::Lemmas::{
    initialize_Init_Data_Array_Lemmas, runtime_initialize_Init_Data_Array_Lemmas,
};
use crate::r#gen::Init::Data::Iterators::Combinators::Monadic::FlatMap::{
    initialize_Init_Data_Iterators_Combinators_Monadic_FlatMap,
    runtime_initialize_Init_Data_Iterators_Combinators_Monadic_FlatMap,
};
use crate::r#gen::Init::Data::Iterators::Consumers::Monadic::Collect::{
    initialize_Init_Data_Iterators_Consumers_Monadic_Collect,
    runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Collect,
};
use crate::r#gen::Init::Data::Iterators::Lemmas::Combinators::Monadic::FilterMap::{
    initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap,
    runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap,
};
use crate::r#gen::Init::Data::Iterators::Lemmas::Consumers::Monadic::{
    initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic,
    runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic,
};
use crate::r#gen::Init::Data::Iterators::Lemmas::Monadic::Basic::{
    initialize_Init_Data_Iterators_Lemmas_Monadic_Basic,
    runtime_initialize_Init_Data_Iterators_Lemmas_Monadic_Basic,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_apply_1, lean_apply_2, lean_apply_3, lean_box,
    lean_ctor_get, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_obj_tag,
};
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FlatMap_0__Std_IterM_step__flattenAfter_match__5_splitter___redArg(
    mut v_it_u2082_213_: *mut LeanObject,
    mut v_h__1_214_: *mut LeanObject,
    mut v_h__2_215_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_it_u2082_213_) == 0 {
        let mut v___x_216_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_217_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_215_);
        v___x_216_ = lean_box(0);
        v___x_217_ = lean_apply_1(v_h__1_214_, v___x_216_);
        return v___x_217_;
    } else {
        let mut v_val_218_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_219_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_214_);
        v_val_218_ = lean_ctor_get(v_it_u2082_213_, 0);
        lean_inc(v_val_218_);
        lean_dec_ref_known(v_it_u2082_213_, 1);
        v___x_219_ = lean_apply_1(v_h__2_215_, v_val_218_);
        return v___x_219_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FlatMap_0__Std_IterM_step__flattenAfter_match__5_splitter(
    mut v_00_u03b1_u2082_220_: *mut LeanObject,
    mut v_00_u03b2_221_: *mut LeanObject,
    mut v_m_222_: *mut LeanObject,
    mut v_motive_223_: *mut LeanObject,
    mut v_it_u2082_224_: *mut LeanObject,
    mut v_h__1_225_: *mut LeanObject,
    mut v_h__2_226_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_it_u2082_224_) == 0 {
        let mut v___x_227_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_228_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_226_);
        v___x_227_ = lean_box(0);
        v___x_228_ = lean_apply_1(v_h__1_225_, v___x_227_);
        return v___x_228_;
    } else {
        let mut v_val_229_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_230_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_225_);
        v_val_229_ = lean_ctor_get(v_it_u2082_224_, 0);
        lean_inc(v_val_229_);
        lean_dec_ref_known(v_it_u2082_224_, 1);
        v___x_230_ = lean_apply_1(v_h__2_226_, v_val_229_);
        return v___x_230_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FlatMap_0__Std_IterM_step__filterMapWithPostcondition_match__3_splitter___redArg(
    mut v_x_231_: *mut LeanObject,
    mut v_h__1_232_: *mut LeanObject,
    mut v_h__2_233_: *mut LeanObject,
    mut v_h__3_234_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_231_) {
        0 => {
            let mut v_it_235_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_236_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_237_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_234_);
            lean_dec(v_h__2_233_);
            v_it_235_ = lean_ctor_get(v_x_231_, 0);
            lean_inc(v_it_235_);
            v_out_236_ = lean_ctor_get(v_x_231_, 1);
            lean_inc(v_out_236_);
            lean_dec_ref_known(v_x_231_, 2);
            v___x_237_ = lean_apply_3(v_h__1_232_, v_it_235_, v_out_236_, lean_box(0));
            return v___x_237_;
        }
        1 => {
            let mut v_it_238_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_239_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_234_);
            lean_dec(v_h__1_232_);
            v_it_238_ = lean_ctor_get(v_x_231_, 0);
            lean_inc(v_it_238_);
            lean_dec_ref_known(v_x_231_, 1);
            v___x_239_ = lean_apply_2(v_h__2_233_, v_it_238_, lean_box(0));
            return v___x_239_;
        }
        _ => {
            let mut v___x_240_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_233_);
            lean_dec(v_h__1_232_);
            v___x_240_ = lean_apply_1(v_h__3_234_, lean_box(0));
            return v___x_240_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FlatMap_0__Std_IterM_step__filterMapWithPostcondition_match__3_splitter(
    mut v_00_u03b1_241_: *mut LeanObject,
    mut v_00_u03b2_242_: *mut LeanObject,
    mut v_m_243_: *mut LeanObject,
    mut v_inst_244_: *mut LeanObject,
    mut v_it_245_: *mut LeanObject,
    mut v_motive_246_: *mut LeanObject,
    mut v_x_247_: *mut LeanObject,
    mut v_h__1_248_: *mut LeanObject,
    mut v_h__2_249_: *mut LeanObject,
    mut v_h__3_250_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_247_) {
        0 => {
            let mut v_it_251_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_252_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_253_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_250_);
            lean_dec(v_h__2_249_);
            v_it_251_ = lean_ctor_get(v_x_247_, 0);
            lean_inc(v_it_251_);
            v_out_252_ = lean_ctor_get(v_x_247_, 1);
            lean_inc(v_out_252_);
            lean_dec_ref_known(v_x_247_, 2);
            v___x_253_ = lean_apply_3(v_h__1_248_, v_it_251_, v_out_252_, lean_box(0));
            return v___x_253_;
        }
        1 => {
            let mut v_it_254_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_255_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_250_);
            lean_dec(v_h__1_248_);
            v_it_254_ = lean_ctor_get(v_x_247_, 0);
            lean_inc(v_it_254_);
            lean_dec_ref_known(v_x_247_, 1);
            v___x_255_ = lean_apply_2(v_h__2_249_, v_it_254_, lean_box(0));
            return v___x_255_;
        }
        _ => {
            let mut v___x_256_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_249_);
            lean_dec(v_h__1_248_);
            v___x_256_ = lean_apply_1(v_h__3_250_, lean_box(0));
            return v___x_256_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FlatMap_0__Std_IterM_step__filterMapWithPostcondition_match__3_splitter___boxed(
    mut v_00_u03b1_257_: *mut LeanObject,
    mut v_00_u03b2_258_: *mut LeanObject,
    mut v_m_259_: *mut LeanObject,
    mut v_inst_260_: *mut LeanObject,
    mut v_it_261_: *mut LeanObject,
    mut v_motive_262_: *mut LeanObject,
    mut v_x_263_: *mut LeanObject,
    mut v_h__1_264_: *mut LeanObject,
    mut v_h__2_265_: *mut LeanObject,
    mut v_h__3_266_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_267_: *mut LeanObject = core::ptr::null_mut();
    v_res_267_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FlatMap_0__Std_IterM_step__filterMapWithPostcondition_match__3_splitter(v_00_u03b1_257_, v_00_u03b2_258_, v_m_259_, v_inst_260_, v_it_261_, v_motive_262_, v_x_263_, v_h__1_264_, v_h__2_265_, v_h__3_266_);
    lean_dec(v_it_261_);
    lean_dec(v_inst_260_);
    return v_res_267_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FlatMap_0__Std_IterM_step__flattenAfter_match__1_splitter___redArg(
    mut v_x_268_: *mut LeanObject,
    mut v_h__1_269_: *mut LeanObject,
    mut v_h__2_270_: *mut LeanObject,
    mut v_h__3_271_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_268_) {
        0 => {
            let mut v_it_272_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_273_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_274_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_271_);
            lean_dec(v_h__2_270_);
            v_it_272_ = lean_ctor_get(v_x_268_, 0);
            lean_inc(v_it_272_);
            v_out_273_ = lean_ctor_get(v_x_268_, 1);
            lean_inc(v_out_273_);
            lean_dec_ref_known(v_x_268_, 2);
            v___x_274_ = lean_apply_3(v_h__1_269_, v_it_272_, v_out_273_, lean_box(0));
            return v___x_274_;
        }
        1 => {
            let mut v_it_275_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_276_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_271_);
            lean_dec(v_h__1_269_);
            v_it_275_ = lean_ctor_get(v_x_268_, 0);
            lean_inc(v_it_275_);
            lean_dec_ref_known(v_x_268_, 1);
            v___x_276_ = lean_apply_2(v_h__2_270_, v_it_275_, lean_box(0));
            return v___x_276_;
        }
        _ => {
            let mut v___x_277_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_270_);
            lean_dec(v_h__1_269_);
            v___x_277_ = lean_apply_1(v_h__3_271_, lean_box(0));
            return v___x_277_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FlatMap_0__Std_IterM_step__flattenAfter_match__1_splitter(
    mut v_00_u03b1_278_: *mut LeanObject,
    mut v_00_u03b1_u2082_279_: *mut LeanObject,
    mut v_00_u03b2_280_: *mut LeanObject,
    mut v_m_281_: *mut LeanObject,
    mut v_inst_282_: *mut LeanObject,
    mut v_it_u2081_283_: *mut LeanObject,
    mut v_motive_284_: *mut LeanObject,
    mut v_x_285_: *mut LeanObject,
    mut v_h__1_286_: *mut LeanObject,
    mut v_h__2_287_: *mut LeanObject,
    mut v_h__3_288_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_285_) {
        0 => {
            let mut v_it_289_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_290_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_291_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_288_);
            lean_dec(v_h__2_287_);
            v_it_289_ = lean_ctor_get(v_x_285_, 0);
            lean_inc(v_it_289_);
            v_out_290_ = lean_ctor_get(v_x_285_, 1);
            lean_inc(v_out_290_);
            lean_dec_ref_known(v_x_285_, 2);
            v___x_291_ = lean_apply_3(v_h__1_286_, v_it_289_, v_out_290_, lean_box(0));
            return v___x_291_;
        }
        1 => {
            let mut v_it_292_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_293_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_288_);
            lean_dec(v_h__1_286_);
            v_it_292_ = lean_ctor_get(v_x_285_, 0);
            lean_inc(v_it_292_);
            lean_dec_ref_known(v_x_285_, 1);
            v___x_293_ = lean_apply_2(v_h__2_287_, v_it_292_, lean_box(0));
            return v___x_293_;
        }
        _ => {
            let mut v___x_294_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_287_);
            lean_dec(v_h__1_286_);
            v___x_294_ = lean_apply_1(v_h__3_288_, lean_box(0));
            return v___x_294_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FlatMap_0__Std_IterM_step__flattenAfter_match__1_splitter___boxed(
    mut v_00_u03b1_295_: *mut LeanObject,
    mut v_00_u03b1_u2082_296_: *mut LeanObject,
    mut v_00_u03b2_297_: *mut LeanObject,
    mut v_m_298_: *mut LeanObject,
    mut v_inst_299_: *mut LeanObject,
    mut v_it_u2081_300_: *mut LeanObject,
    mut v_motive_301_: *mut LeanObject,
    mut v_x_302_: *mut LeanObject,
    mut v_h__1_303_: *mut LeanObject,
    mut v_h__2_304_: *mut LeanObject,
    mut v_h__3_305_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_306_: *mut LeanObject = core::ptr::null_mut();
    v_res_306_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FlatMap_0__Std_IterM_step__flattenAfter_match__1_splitter(v_00_u03b1_295_, v_00_u03b1_u2082_296_, v_00_u03b2_297_, v_m_298_, v_inst_299_, v_it_u2081_300_, v_motive_301_, v_x_302_, v_h__1_303_, v_h__2_304_, v_h__3_305_);
    lean_dec(v_it_u2081_300_);
    lean_dec(v_inst_299_);
    return v_res_306_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FlatMap_0__Std_IterM_step__flattenAfter_match__3_splitter___redArg(
    mut v_x_307_: *mut LeanObject,
    mut v_h__1_308_: *mut LeanObject,
    mut v_h__2_309_: *mut LeanObject,
    mut v_h__3_310_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_307_) {
        0 => {
            let mut v_it_311_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_312_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_313_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_310_);
            lean_dec(v_h__2_309_);
            v_it_311_ = lean_ctor_get(v_x_307_, 0);
            lean_inc(v_it_311_);
            v_out_312_ = lean_ctor_get(v_x_307_, 1);
            lean_inc(v_out_312_);
            lean_dec_ref_known(v_x_307_, 2);
            v___x_313_ = lean_apply_3(v_h__1_308_, v_it_311_, v_out_312_, lean_box(0));
            return v___x_313_;
        }
        1 => {
            let mut v_it_314_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_315_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_310_);
            lean_dec(v_h__1_308_);
            v_it_314_ = lean_ctor_get(v_x_307_, 0);
            lean_inc(v_it_314_);
            lean_dec_ref_known(v_x_307_, 1);
            v___x_315_ = lean_apply_2(v_h__2_309_, v_it_314_, lean_box(0));
            return v___x_315_;
        }
        _ => {
            let mut v___x_316_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_309_);
            lean_dec(v_h__1_308_);
            v___x_316_ = lean_apply_1(v_h__3_310_, lean_box(0));
            return v___x_316_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FlatMap_0__Std_IterM_step__flattenAfter_match__3_splitter(
    mut v_00_u03b1_u2082_317_: *mut LeanObject,
    mut v_00_u03b2_318_: *mut LeanObject,
    mut v_m_319_: *mut LeanObject,
    mut v_inst_320_: *mut LeanObject,
    mut v_it_u2082_321_: *mut LeanObject,
    mut v_motive_322_: *mut LeanObject,
    mut v_x_323_: *mut LeanObject,
    mut v_h__1_324_: *mut LeanObject,
    mut v_h__2_325_: *mut LeanObject,
    mut v_h__3_326_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_323_) {
        0 => {
            let mut v_it_327_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_328_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_329_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_326_);
            lean_dec(v_h__2_325_);
            v_it_327_ = lean_ctor_get(v_x_323_, 0);
            lean_inc(v_it_327_);
            v_out_328_ = lean_ctor_get(v_x_323_, 1);
            lean_inc(v_out_328_);
            lean_dec_ref_known(v_x_323_, 2);
            v___x_329_ = lean_apply_3(v_h__1_324_, v_it_327_, v_out_328_, lean_box(0));
            return v___x_329_;
        }
        1 => {
            let mut v_it_330_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_331_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_326_);
            lean_dec(v_h__1_324_);
            v_it_330_ = lean_ctor_get(v_x_323_, 0);
            lean_inc(v_it_330_);
            lean_dec_ref_known(v_x_323_, 1);
            v___x_331_ = lean_apply_2(v_h__2_325_, v_it_330_, lean_box(0));
            return v___x_331_;
        }
        _ => {
            let mut v___x_332_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_325_);
            lean_dec(v_h__1_324_);
            v___x_332_ = lean_apply_1(v_h__3_326_, lean_box(0));
            return v___x_332_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FlatMap_0__Std_IterM_step__flattenAfter_match__3_splitter___boxed(
    mut v_00_u03b1_u2082_333_: *mut LeanObject,
    mut v_00_u03b2_334_: *mut LeanObject,
    mut v_m_335_: *mut LeanObject,
    mut v_inst_336_: *mut LeanObject,
    mut v_it_u2082_337_: *mut LeanObject,
    mut v_motive_338_: *mut LeanObject,
    mut v_x_339_: *mut LeanObject,
    mut v_h__1_340_: *mut LeanObject,
    mut v_h__2_341_: *mut LeanObject,
    mut v_h__3_342_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_343_: *mut LeanObject = core::ptr::null_mut();
    v_res_343_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FlatMap_0__Std_IterM_step__flattenAfter_match__3_splitter(v_00_u03b1_u2082_333_, v_00_u03b2_334_, v_m_335_, v_inst_336_, v_it_u2082_337_, v_motive_338_, v_x_339_, v_h__1_340_, v_h__2_341_, v_h__3_342_);
    lean_dec(v_it_u2082_337_);
    lean_dec(v_inst_336_);
    return v_res_343_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FlatMap_0__Std_IterM_step__flatMapAfterM_match__3_splitter___redArg(
    mut v_it_u2082_344_: *mut LeanObject,
    mut v_h__1_345_: *mut LeanObject,
    mut v_h__2_346_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_it_u2082_344_) == 0 {
        let mut v___x_347_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_348_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_346_);
        v___x_347_ = lean_box(0);
        v___x_348_ = lean_apply_1(v_h__1_345_, v___x_347_);
        return v___x_348_;
    } else {
        let mut v_val_349_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_350_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_345_);
        v_val_349_ = lean_ctor_get(v_it_u2082_344_, 0);
        lean_inc(v_val_349_);
        lean_dec_ref_known(v_it_u2082_344_, 1);
        v___x_350_ = lean_apply_1(v_h__2_346_, v_val_349_);
        return v___x_350_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FlatMap_0__Std_IterM_step__flatMapAfterM_match__3_splitter(
    mut v_00_u03b1_u2082_351_: *mut LeanObject,
    mut v_00_u03b3_352_: *mut LeanObject,
    mut v_m_353_: *mut LeanObject,
    mut v_motive_354_: *mut LeanObject,
    mut v_it_u2082_355_: *mut LeanObject,
    mut v_h__1_356_: *mut LeanObject,
    mut v_h__2_357_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_it_u2082_355_) == 0 {
        let mut v___x_358_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_359_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_357_);
        v___x_358_ = lean_box(0);
        v___x_359_ = lean_apply_1(v_h__1_356_, v___x_358_);
        return v___x_359_;
    } else {
        let mut v_val_360_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_361_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_356_);
        v_val_360_ = lean_ctor_get(v_it_u2082_355_, 0);
        lean_inc(v_val_360_);
        lean_dec_ref_known(v_it_u2082_355_, 1);
        v___x_361_ = lean_apply_1(v_h__2_357_, v_val_360_);
        return v___x_361_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FlatMap_0__Std_IterM_step__flatMapAfterM_match__1_splitter___redArg(
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
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FlatMap_0__Std_IterM_step__flatMapAfterM_match__1_splitter(
    mut v_00_u03b1_372_: *mut LeanObject,
    mut v_00_u03b2_373_: *mut LeanObject,
    mut v_m_374_: *mut LeanObject,
    mut v_inst_375_: *mut LeanObject,
    mut v_it_u2081_376_: *mut LeanObject,
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
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FlatMap_0__Std_IterM_step__flatMapAfterM_match__1_splitter___boxed(
    mut v_00_u03b1_388_: *mut LeanObject,
    mut v_00_u03b2_389_: *mut LeanObject,
    mut v_m_390_: *mut LeanObject,
    mut v_inst_391_: *mut LeanObject,
    mut v_it_u2081_392_: *mut LeanObject,
    mut v_motive_393_: *mut LeanObject,
    mut v_x_394_: *mut LeanObject,
    mut v_h__1_395_: *mut LeanObject,
    mut v_h__2_396_: *mut LeanObject,
    mut v_h__3_397_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_398_: *mut LeanObject = core::ptr::null_mut();
    v_res_398_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FlatMap_0__Std_IterM_step__flatMapAfterM_match__1_splitter(v_00_u03b1_388_, v_00_u03b2_389_, v_m_390_, v_inst_391_, v_it_u2081_392_, v_motive_393_, v_x_394_, v_h__1_395_, v_h__2_396_, v_h__3_397_);
    lean_dec(v_it_u2081_392_);
    lean_dec(v_inst_391_);
    return v_res_398_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FlatMap_0__Std_IterM_toArray__eq__match__step_match__1_splitter___redArg(
    mut v_x_399_: *mut LeanObject,
    mut v_h__1_400_: *mut LeanObject,
    mut v_h__2_401_: *mut LeanObject,
    mut v_h__3_402_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_399_) {
        0 => {
            let mut v_it_403_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_404_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_405_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_402_);
            lean_dec(v_h__2_401_);
            v_it_403_ = lean_ctor_get(v_x_399_, 0);
            lean_inc(v_it_403_);
            v_out_404_ = lean_ctor_get(v_x_399_, 1);
            lean_inc(v_out_404_);
            lean_dec_ref_known(v_x_399_, 2);
            v___x_405_ = lean_apply_2(v_h__1_400_, v_it_403_, v_out_404_);
            return v___x_405_;
        }
        1 => {
            let mut v_it_406_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_407_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_402_);
            lean_dec(v_h__1_400_);
            v_it_406_ = lean_ctor_get(v_x_399_, 0);
            lean_inc(v_it_406_);
            lean_dec_ref_known(v_x_399_, 1);
            v___x_407_ = lean_apply_1(v_h__2_401_, v_it_406_);
            return v___x_407_;
        }
        _ => {
            let mut v___x_408_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_409_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_401_);
            lean_dec(v_h__1_400_);
            v___x_408_ = lean_box(0);
            v___x_409_ = lean_apply_1(v_h__3_402_, v___x_408_);
            return v___x_409_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FlatMap_0__Std_IterM_toArray__eq__match__step_match__1_splitter(
    mut v_00_u03b1_410_: *mut LeanObject,
    mut v_00_u03b2_411_: *mut LeanObject,
    mut v_m_412_: *mut LeanObject,
    mut v_motive_413_: *mut LeanObject,
    mut v_x_414_: *mut LeanObject,
    mut v_h__1_415_: *mut LeanObject,
    mut v_h__2_416_: *mut LeanObject,
    mut v_h__3_417_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_414_) {
        0 => {
            let mut v_it_418_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_419_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_420_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_417_);
            lean_dec(v_h__2_416_);
            v_it_418_ = lean_ctor_get(v_x_414_, 0);
            lean_inc(v_it_418_);
            v_out_419_ = lean_ctor_get(v_x_414_, 1);
            lean_inc(v_out_419_);
            lean_dec_ref_known(v_x_414_, 2);
            v___x_420_ = lean_apply_2(v_h__1_415_, v_it_418_, v_out_419_);
            return v___x_420_;
        }
        1 => {
            let mut v_it_421_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_422_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_417_);
            lean_dec(v_h__1_415_);
            v_it_421_ = lean_ctor_get(v_x_414_, 0);
            lean_inc(v_it_421_);
            lean_dec_ref_known(v_x_414_, 1);
            v___x_422_ = lean_apply_1(v_h__2_416_, v_it_421_);
            return v___x_422_;
        }
        _ => {
            let mut v___x_423_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_424_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_416_);
            lean_dec(v_h__1_415_);
            v___x_423_ = lean_box(0);
            v___x_424_ = lean_apply_1(v_h__3_417_, v___x_423_);
            return v___x_424_;
        }
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_FlatMap(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Combinators_Monadic_FlatMap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Collect(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Monadic_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_FlatMap(
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
pub unsafe fn initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_FlatMap(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Combinators_Monadic_FlatMap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers_Monadic_Collect(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Array_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Monadic_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_FlatMap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_FlatMap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_FlatMap(builtin);
}
