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
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FlatMap_0__Std_IterM_step__flattenAfter_match__5_splitter___redArg(
    mut v_it_u2082_213_: *mut leanh::LeanObject,
    mut v_h__1_214_: *mut leanh::LeanObject,
    mut v_h__2_215_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_it_u2082_213_) == 0 {
        let mut v___x_216_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_217_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_215_);
        v___x_216_ = leanh::lean_box(0);
        v___x_217_ = leanh::lean_apply_1(v_h__1_214_, v___x_216_);
        return v___x_217_;
    } else {
        let mut v_val_218_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_219_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_214_);
        v_val_218_ = leanh::lean_ctor_get(v_it_u2082_213_, 0);
        leanh::lean_inc(v_val_218_);
        leanh::lean_dec_ref_known(v_it_u2082_213_, 1);
        v___x_219_ = leanh::lean_apply_1(v_h__2_215_, v_val_218_);
        return v___x_219_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FlatMap_0__Std_IterM_step__flattenAfter_match__5_splitter(
    mut v_00_u03b1_u2082_220_: *mut leanh::LeanObject,
    mut v_00_u03b2_221_: *mut leanh::LeanObject,
    mut v_m_222_: *mut leanh::LeanObject,
    mut v_motive_223_: *mut leanh::LeanObject,
    mut v_it_u2082_224_: *mut leanh::LeanObject,
    mut v_h__1_225_: *mut leanh::LeanObject,
    mut v_h__2_226_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_it_u2082_224_) == 0 {
        let mut v___x_227_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_228_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_226_);
        v___x_227_ = leanh::lean_box(0);
        v___x_228_ = leanh::lean_apply_1(v_h__1_225_, v___x_227_);
        return v___x_228_;
    } else {
        let mut v_val_229_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_230_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_225_);
        v_val_229_ = leanh::lean_ctor_get(v_it_u2082_224_, 0);
        leanh::lean_inc(v_val_229_);
        leanh::lean_dec_ref_known(v_it_u2082_224_, 1);
        v___x_230_ = leanh::lean_apply_1(v_h__2_226_, v_val_229_);
        return v___x_230_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FlatMap_0__Std_IterM_step__filterMapWithPostcondition_match__3_splitter___redArg(
    mut v_x_231_: *mut leanh::LeanObject,
    mut v_h__1_232_: *mut leanh::LeanObject,
    mut v_h__2_233_: *mut leanh::LeanObject,
    mut v_h__3_234_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_231_) {
        0 => {
            let mut v_it_235_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_236_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_237_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_234_);
            leanh::lean_dec(v_h__2_233_);
            v_it_235_ = leanh::lean_ctor_get(v_x_231_, 0);
            leanh::lean_inc(v_it_235_);
            v_out_236_ = leanh::lean_ctor_get(v_x_231_, 1);
            leanh::lean_inc(v_out_236_);
            leanh::lean_dec_ref_known(v_x_231_, 2);
            v___x_237_ = leanh::lean_apply_3(
                v_h__1_232_,
                v_it_235_,
                v_out_236_,
                leanh::lean_box(0),
            );
            return v___x_237_;
        }
        1 => {
            let mut v_it_238_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_239_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_234_);
            leanh::lean_dec(v_h__1_232_);
            v_it_238_ = leanh::lean_ctor_get(v_x_231_, 0);
            leanh::lean_inc(v_it_238_);
            leanh::lean_dec_ref_known(v_x_231_, 1);
            v___x_239_ =
                leanh::lean_apply_2(v_h__2_233_, v_it_238_, leanh::lean_box(0));
            return v___x_239_;
        }
        _ => {
            let mut v___x_240_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_233_);
            leanh::lean_dec(v_h__1_232_);
            v___x_240_ = leanh::lean_apply_1(v_h__3_234_, leanh::lean_box(0));
            return v___x_240_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FlatMap_0__Std_IterM_step__filterMapWithPostcondition_match__3_splitter(
    mut v_00_u03b1_241_: *mut leanh::LeanObject,
    mut v_00_u03b2_242_: *mut leanh::LeanObject,
    mut v_m_243_: *mut leanh::LeanObject,
    mut v_inst_244_: *mut leanh::LeanObject,
    mut v_it_245_: *mut leanh::LeanObject,
    mut v_motive_246_: *mut leanh::LeanObject,
    mut v_x_247_: *mut leanh::LeanObject,
    mut v_h__1_248_: *mut leanh::LeanObject,
    mut v_h__2_249_: *mut leanh::LeanObject,
    mut v_h__3_250_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_247_) {
        0 => {
            let mut v_it_251_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_252_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_253_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_250_);
            leanh::lean_dec(v_h__2_249_);
            v_it_251_ = leanh::lean_ctor_get(v_x_247_, 0);
            leanh::lean_inc(v_it_251_);
            v_out_252_ = leanh::lean_ctor_get(v_x_247_, 1);
            leanh::lean_inc(v_out_252_);
            leanh::lean_dec_ref_known(v_x_247_, 2);
            v___x_253_ = leanh::lean_apply_3(
                v_h__1_248_,
                v_it_251_,
                v_out_252_,
                leanh::lean_box(0),
            );
            return v___x_253_;
        }
        1 => {
            let mut v_it_254_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_255_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_250_);
            leanh::lean_dec(v_h__1_248_);
            v_it_254_ = leanh::lean_ctor_get(v_x_247_, 0);
            leanh::lean_inc(v_it_254_);
            leanh::lean_dec_ref_known(v_x_247_, 1);
            v___x_255_ =
                leanh::lean_apply_2(v_h__2_249_, v_it_254_, leanh::lean_box(0));
            return v___x_255_;
        }
        _ => {
            let mut v___x_256_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_249_);
            leanh::lean_dec(v_h__1_248_);
            v___x_256_ = leanh::lean_apply_1(v_h__3_250_, leanh::lean_box(0));
            return v___x_256_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FlatMap_0__Std_IterM_step__filterMapWithPostcondition_match__3_splitter___boxed(
    mut v_00_u03b1_257_: *mut leanh::LeanObject,
    mut v_00_u03b2_258_: *mut leanh::LeanObject,
    mut v_m_259_: *mut leanh::LeanObject,
    mut v_inst_260_: *mut leanh::LeanObject,
    mut v_it_261_: *mut leanh::LeanObject,
    mut v_motive_262_: *mut leanh::LeanObject,
    mut v_x_263_: *mut leanh::LeanObject,
    mut v_h__1_264_: *mut leanh::LeanObject,
    mut v_h__2_265_: *mut leanh::LeanObject,
    mut v_h__3_266_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_267_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_267_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FlatMap_0__Std_IterM_step__filterMapWithPostcondition_match__3_splitter(v_00_u03b1_257_, v_00_u03b2_258_, v_m_259_, v_inst_260_, v_it_261_, v_motive_262_, v_x_263_, v_h__1_264_, v_h__2_265_, v_h__3_266_);
    leanh::lean_dec(v_it_261_);
    leanh::lean_dec(v_inst_260_);
    return v_res_267_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FlatMap_0__Std_IterM_step__flattenAfter_match__1_splitter___redArg(
    mut v_x_268_: *mut leanh::LeanObject,
    mut v_h__1_269_: *mut leanh::LeanObject,
    mut v_h__2_270_: *mut leanh::LeanObject,
    mut v_h__3_271_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_268_) {
        0 => {
            let mut v_it_272_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_273_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_274_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_271_);
            leanh::lean_dec(v_h__2_270_);
            v_it_272_ = leanh::lean_ctor_get(v_x_268_, 0);
            leanh::lean_inc(v_it_272_);
            v_out_273_ = leanh::lean_ctor_get(v_x_268_, 1);
            leanh::lean_inc(v_out_273_);
            leanh::lean_dec_ref_known(v_x_268_, 2);
            v___x_274_ = leanh::lean_apply_3(
                v_h__1_269_,
                v_it_272_,
                v_out_273_,
                leanh::lean_box(0),
            );
            return v___x_274_;
        }
        1 => {
            let mut v_it_275_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_276_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_271_);
            leanh::lean_dec(v_h__1_269_);
            v_it_275_ = leanh::lean_ctor_get(v_x_268_, 0);
            leanh::lean_inc(v_it_275_);
            leanh::lean_dec_ref_known(v_x_268_, 1);
            v___x_276_ =
                leanh::lean_apply_2(v_h__2_270_, v_it_275_, leanh::lean_box(0));
            return v___x_276_;
        }
        _ => {
            let mut v___x_277_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_270_);
            leanh::lean_dec(v_h__1_269_);
            v___x_277_ = leanh::lean_apply_1(v_h__3_271_, leanh::lean_box(0));
            return v___x_277_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FlatMap_0__Std_IterM_step__flattenAfter_match__1_splitter(
    mut v_00_u03b1_278_: *mut leanh::LeanObject,
    mut v_00_u03b1_u2082_279_: *mut leanh::LeanObject,
    mut v_00_u03b2_280_: *mut leanh::LeanObject,
    mut v_m_281_: *mut leanh::LeanObject,
    mut v_inst_282_: *mut leanh::LeanObject,
    mut v_it_u2081_283_: *mut leanh::LeanObject,
    mut v_motive_284_: *mut leanh::LeanObject,
    mut v_x_285_: *mut leanh::LeanObject,
    mut v_h__1_286_: *mut leanh::LeanObject,
    mut v_h__2_287_: *mut leanh::LeanObject,
    mut v_h__3_288_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_285_) {
        0 => {
            let mut v_it_289_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_290_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_291_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_288_);
            leanh::lean_dec(v_h__2_287_);
            v_it_289_ = leanh::lean_ctor_get(v_x_285_, 0);
            leanh::lean_inc(v_it_289_);
            v_out_290_ = leanh::lean_ctor_get(v_x_285_, 1);
            leanh::lean_inc(v_out_290_);
            leanh::lean_dec_ref_known(v_x_285_, 2);
            v___x_291_ = leanh::lean_apply_3(
                v_h__1_286_,
                v_it_289_,
                v_out_290_,
                leanh::lean_box(0),
            );
            return v___x_291_;
        }
        1 => {
            let mut v_it_292_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_293_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_288_);
            leanh::lean_dec(v_h__1_286_);
            v_it_292_ = leanh::lean_ctor_get(v_x_285_, 0);
            leanh::lean_inc(v_it_292_);
            leanh::lean_dec_ref_known(v_x_285_, 1);
            v___x_293_ =
                leanh::lean_apply_2(v_h__2_287_, v_it_292_, leanh::lean_box(0));
            return v___x_293_;
        }
        _ => {
            let mut v___x_294_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_287_);
            leanh::lean_dec(v_h__1_286_);
            v___x_294_ = leanh::lean_apply_1(v_h__3_288_, leanh::lean_box(0));
            return v___x_294_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FlatMap_0__Std_IterM_step__flattenAfter_match__1_splitter___boxed(
    mut v_00_u03b1_295_: *mut leanh::LeanObject,
    mut v_00_u03b1_u2082_296_: *mut leanh::LeanObject,
    mut v_00_u03b2_297_: *mut leanh::LeanObject,
    mut v_m_298_: *mut leanh::LeanObject,
    mut v_inst_299_: *mut leanh::LeanObject,
    mut v_it_u2081_300_: *mut leanh::LeanObject,
    mut v_motive_301_: *mut leanh::LeanObject,
    mut v_x_302_: *mut leanh::LeanObject,
    mut v_h__1_303_: *mut leanh::LeanObject,
    mut v_h__2_304_: *mut leanh::LeanObject,
    mut v_h__3_305_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_306_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_306_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FlatMap_0__Std_IterM_step__flattenAfter_match__1_splitter(v_00_u03b1_295_, v_00_u03b1_u2082_296_, v_00_u03b2_297_, v_m_298_, v_inst_299_, v_it_u2081_300_, v_motive_301_, v_x_302_, v_h__1_303_, v_h__2_304_, v_h__3_305_);
    leanh::lean_dec(v_it_u2081_300_);
    leanh::lean_dec(v_inst_299_);
    return v_res_306_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FlatMap_0__Std_IterM_step__flattenAfter_match__3_splitter___redArg(
    mut v_x_307_: *mut leanh::LeanObject,
    mut v_h__1_308_: *mut leanh::LeanObject,
    mut v_h__2_309_: *mut leanh::LeanObject,
    mut v_h__3_310_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_307_) {
        0 => {
            let mut v_it_311_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_312_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_313_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_310_);
            leanh::lean_dec(v_h__2_309_);
            v_it_311_ = leanh::lean_ctor_get(v_x_307_, 0);
            leanh::lean_inc(v_it_311_);
            v_out_312_ = leanh::lean_ctor_get(v_x_307_, 1);
            leanh::lean_inc(v_out_312_);
            leanh::lean_dec_ref_known(v_x_307_, 2);
            v___x_313_ = leanh::lean_apply_3(
                v_h__1_308_,
                v_it_311_,
                v_out_312_,
                leanh::lean_box(0),
            );
            return v___x_313_;
        }
        1 => {
            let mut v_it_314_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_315_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_310_);
            leanh::lean_dec(v_h__1_308_);
            v_it_314_ = leanh::lean_ctor_get(v_x_307_, 0);
            leanh::lean_inc(v_it_314_);
            leanh::lean_dec_ref_known(v_x_307_, 1);
            v___x_315_ =
                leanh::lean_apply_2(v_h__2_309_, v_it_314_, leanh::lean_box(0));
            return v___x_315_;
        }
        _ => {
            let mut v___x_316_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_309_);
            leanh::lean_dec(v_h__1_308_);
            v___x_316_ = leanh::lean_apply_1(v_h__3_310_, leanh::lean_box(0));
            return v___x_316_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FlatMap_0__Std_IterM_step__flattenAfter_match__3_splitter(
    mut v_00_u03b1_u2082_317_: *mut leanh::LeanObject,
    mut v_00_u03b2_318_: *mut leanh::LeanObject,
    mut v_m_319_: *mut leanh::LeanObject,
    mut v_inst_320_: *mut leanh::LeanObject,
    mut v_it_u2082_321_: *mut leanh::LeanObject,
    mut v_motive_322_: *mut leanh::LeanObject,
    mut v_x_323_: *mut leanh::LeanObject,
    mut v_h__1_324_: *mut leanh::LeanObject,
    mut v_h__2_325_: *mut leanh::LeanObject,
    mut v_h__3_326_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_323_) {
        0 => {
            let mut v_it_327_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_328_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_329_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_326_);
            leanh::lean_dec(v_h__2_325_);
            v_it_327_ = leanh::lean_ctor_get(v_x_323_, 0);
            leanh::lean_inc(v_it_327_);
            v_out_328_ = leanh::lean_ctor_get(v_x_323_, 1);
            leanh::lean_inc(v_out_328_);
            leanh::lean_dec_ref_known(v_x_323_, 2);
            v___x_329_ = leanh::lean_apply_3(
                v_h__1_324_,
                v_it_327_,
                v_out_328_,
                leanh::lean_box(0),
            );
            return v___x_329_;
        }
        1 => {
            let mut v_it_330_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_331_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_326_);
            leanh::lean_dec(v_h__1_324_);
            v_it_330_ = leanh::lean_ctor_get(v_x_323_, 0);
            leanh::lean_inc(v_it_330_);
            leanh::lean_dec_ref_known(v_x_323_, 1);
            v___x_331_ =
                leanh::lean_apply_2(v_h__2_325_, v_it_330_, leanh::lean_box(0));
            return v___x_331_;
        }
        _ => {
            let mut v___x_332_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_325_);
            leanh::lean_dec(v_h__1_324_);
            v___x_332_ = leanh::lean_apply_1(v_h__3_326_, leanh::lean_box(0));
            return v___x_332_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FlatMap_0__Std_IterM_step__flattenAfter_match__3_splitter___boxed(
    mut v_00_u03b1_u2082_333_: *mut leanh::LeanObject,
    mut v_00_u03b2_334_: *mut leanh::LeanObject,
    mut v_m_335_: *mut leanh::LeanObject,
    mut v_inst_336_: *mut leanh::LeanObject,
    mut v_it_u2082_337_: *mut leanh::LeanObject,
    mut v_motive_338_: *mut leanh::LeanObject,
    mut v_x_339_: *mut leanh::LeanObject,
    mut v_h__1_340_: *mut leanh::LeanObject,
    mut v_h__2_341_: *mut leanh::LeanObject,
    mut v_h__3_342_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_343_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_343_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FlatMap_0__Std_IterM_step__flattenAfter_match__3_splitter(v_00_u03b1_u2082_333_, v_00_u03b2_334_, v_m_335_, v_inst_336_, v_it_u2082_337_, v_motive_338_, v_x_339_, v_h__1_340_, v_h__2_341_, v_h__3_342_);
    leanh::lean_dec(v_it_u2082_337_);
    leanh::lean_dec(v_inst_336_);
    return v_res_343_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FlatMap_0__Std_IterM_step__flatMapAfterM_match__3_splitter___redArg(
    mut v_it_u2082_344_: *mut leanh::LeanObject,
    mut v_h__1_345_: *mut leanh::LeanObject,
    mut v_h__2_346_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_it_u2082_344_) == 0 {
        let mut v___x_347_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_348_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_346_);
        v___x_347_ = leanh::lean_box(0);
        v___x_348_ = leanh::lean_apply_1(v_h__1_345_, v___x_347_);
        return v___x_348_;
    } else {
        let mut v_val_349_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_350_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_345_);
        v_val_349_ = leanh::lean_ctor_get(v_it_u2082_344_, 0);
        leanh::lean_inc(v_val_349_);
        leanh::lean_dec_ref_known(v_it_u2082_344_, 1);
        v___x_350_ = leanh::lean_apply_1(v_h__2_346_, v_val_349_);
        return v___x_350_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FlatMap_0__Std_IterM_step__flatMapAfterM_match__3_splitter(
    mut v_00_u03b1_u2082_351_: *mut leanh::LeanObject,
    mut v_00_u03b3_352_: *mut leanh::LeanObject,
    mut v_m_353_: *mut leanh::LeanObject,
    mut v_motive_354_: *mut leanh::LeanObject,
    mut v_it_u2082_355_: *mut leanh::LeanObject,
    mut v_h__1_356_: *mut leanh::LeanObject,
    mut v_h__2_357_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_it_u2082_355_) == 0 {
        let mut v___x_358_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_359_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_357_);
        v___x_358_ = leanh::lean_box(0);
        v___x_359_ = leanh::lean_apply_1(v_h__1_356_, v___x_358_);
        return v___x_359_;
    } else {
        let mut v_val_360_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_361_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_356_);
        v_val_360_ = leanh::lean_ctor_get(v_it_u2082_355_, 0);
        leanh::lean_inc(v_val_360_);
        leanh::lean_dec_ref_known(v_it_u2082_355_, 1);
        v___x_361_ = leanh::lean_apply_1(v_h__2_357_, v_val_360_);
        return v___x_361_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FlatMap_0__Std_IterM_step__flatMapAfterM_match__1_splitter___redArg(
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
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FlatMap_0__Std_IterM_step__flatMapAfterM_match__1_splitter(
    mut v_00_u03b1_372_: *mut leanh::LeanObject,
    mut v_00_u03b2_373_: *mut leanh::LeanObject,
    mut v_m_374_: *mut leanh::LeanObject,
    mut v_inst_375_: *mut leanh::LeanObject,
    mut v_it_u2081_376_: *mut leanh::LeanObject,
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
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FlatMap_0__Std_IterM_step__flatMapAfterM_match__1_splitter___boxed(
    mut v_00_u03b1_388_: *mut leanh::LeanObject,
    mut v_00_u03b2_389_: *mut leanh::LeanObject,
    mut v_m_390_: *mut leanh::LeanObject,
    mut v_inst_391_: *mut leanh::LeanObject,
    mut v_it_u2081_392_: *mut leanh::LeanObject,
    mut v_motive_393_: *mut leanh::LeanObject,
    mut v_x_394_: *mut leanh::LeanObject,
    mut v_h__1_395_: *mut leanh::LeanObject,
    mut v_h__2_396_: *mut leanh::LeanObject,
    mut v_h__3_397_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_398_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_398_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FlatMap_0__Std_IterM_step__flatMapAfterM_match__1_splitter(v_00_u03b1_388_, v_00_u03b2_389_, v_m_390_, v_inst_391_, v_it_u2081_392_, v_motive_393_, v_x_394_, v_h__1_395_, v_h__2_396_, v_h__3_397_);
    leanh::lean_dec(v_it_u2081_392_);
    leanh::lean_dec(v_inst_391_);
    return v_res_398_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FlatMap_0__Std_IterM_toArray__eq__match__step_match__1_splitter___redArg(
    mut v_x_399_: *mut leanh::LeanObject,
    mut v_h__1_400_: *mut leanh::LeanObject,
    mut v_h__2_401_: *mut leanh::LeanObject,
    mut v_h__3_402_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_399_) {
        0 => {
            let mut v_it_403_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_404_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_405_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_402_);
            leanh::lean_dec(v_h__2_401_);
            v_it_403_ = leanh::lean_ctor_get(v_x_399_, 0);
            leanh::lean_inc(v_it_403_);
            v_out_404_ = leanh::lean_ctor_get(v_x_399_, 1);
            leanh::lean_inc(v_out_404_);
            leanh::lean_dec_ref_known(v_x_399_, 2);
            v___x_405_ = leanh::lean_apply_2(v_h__1_400_, v_it_403_, v_out_404_);
            return v___x_405_;
        }
        1 => {
            let mut v_it_406_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_407_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_402_);
            leanh::lean_dec(v_h__1_400_);
            v_it_406_ = leanh::lean_ctor_get(v_x_399_, 0);
            leanh::lean_inc(v_it_406_);
            leanh::lean_dec_ref_known(v_x_399_, 1);
            v___x_407_ = leanh::lean_apply_1(v_h__2_401_, v_it_406_);
            return v___x_407_;
        }
        _ => {
            let mut v___x_408_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_409_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_401_);
            leanh::lean_dec(v_h__1_400_);
            v___x_408_ = leanh::lean_box(0);
            v___x_409_ = leanh::lean_apply_1(v_h__3_402_, v___x_408_);
            return v___x_409_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FlatMap_0__Std_IterM_toArray__eq__match__step_match__1_splitter(
    mut v_00_u03b1_410_: *mut leanh::LeanObject,
    mut v_00_u03b2_411_: *mut leanh::LeanObject,
    mut v_m_412_: *mut leanh::LeanObject,
    mut v_motive_413_: *mut leanh::LeanObject,
    mut v_x_414_: *mut leanh::LeanObject,
    mut v_h__1_415_: *mut leanh::LeanObject,
    mut v_h__2_416_: *mut leanh::LeanObject,
    mut v_h__3_417_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_414_) {
        0 => {
            let mut v_it_418_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_419_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_420_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_417_);
            leanh::lean_dec(v_h__2_416_);
            v_it_418_ = leanh::lean_ctor_get(v_x_414_, 0);
            leanh::lean_inc(v_it_418_);
            v_out_419_ = leanh::lean_ctor_get(v_x_414_, 1);
            leanh::lean_inc(v_out_419_);
            leanh::lean_dec_ref_known(v_x_414_, 2);
            v___x_420_ = leanh::lean_apply_2(v_h__1_415_, v_it_418_, v_out_419_);
            return v___x_420_;
        }
        1 => {
            let mut v_it_421_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_422_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_417_);
            leanh::lean_dec(v_h__1_415_);
            v_it_421_ = leanh::lean_ctor_get(v_x_414_, 0);
            leanh::lean_inc(v_it_421_);
            leanh::lean_dec_ref_known(v_x_414_, 1);
            v___x_422_ = leanh::lean_apply_1(v_h__2_416_, v_it_421_);
            return v___x_422_;
        }
        _ => {
            let mut v___x_423_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_424_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_416_);
            leanh::lean_dec(v_h__1_415_);
            v___x_423_ = leanh::lean_box(0);
            v___x_424_ = leanh::lean_apply_1(v_h__3_417_, v___x_423_);
            return v___x_424_;
        }
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_FlatMap(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Combinators_Monadic_FlatMap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Combinators_Monadic_FlatMap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Collect(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Monadic_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_FlatMap(
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
pub unsafe fn initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_FlatMap(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Combinators_Monadic_FlatMap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Combinators_Monadic_FlatMap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers_Monadic_Collect(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Monadic_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_FlatMap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_FlatMap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_FlatMap(builtin);
}