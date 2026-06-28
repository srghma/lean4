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
    mut v_it_u2082_213_: *mut crate::leanh::LeanObject,
    mut v_h__1_214_: *mut crate::leanh::LeanObject,
    mut v_h__2_215_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_it_u2082_213_) == 0 {
        let mut v___x_216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_215_);
        v___x_216_ = crate::leanh::lean_box(0);
        v___x_217_ = crate::leanh::lean_apply_1(v_h__1_214_, v___x_216_);
        return v___x_217_;
    } else {
        let mut v_val_218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_214_);
        v_val_218_ = crate::leanh::lean_ctor_get(v_it_u2082_213_, 0);
        crate::leanh::lean_inc(v_val_218_);
        crate::leanh::lean_dec_ref_known(v_it_u2082_213_, 1);
        v___x_219_ = crate::leanh::lean_apply_1(v_h__2_215_, v_val_218_);
        return v___x_219_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FlatMap_0__Std_IterM_step__flattenAfter_match__5_splitter(
    mut v_00_u03b1_u2082_220_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_221_: *mut crate::leanh::LeanObject,
    mut v_m_222_: *mut crate::leanh::LeanObject,
    mut v_motive_223_: *mut crate::leanh::LeanObject,
    mut v_it_u2082_224_: *mut crate::leanh::LeanObject,
    mut v_h__1_225_: *mut crate::leanh::LeanObject,
    mut v_h__2_226_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_it_u2082_224_) == 0 {
        let mut v___x_227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_226_);
        v___x_227_ = crate::leanh::lean_box(0);
        v___x_228_ = crate::leanh::lean_apply_1(v_h__1_225_, v___x_227_);
        return v___x_228_;
    } else {
        let mut v_val_229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_225_);
        v_val_229_ = crate::leanh::lean_ctor_get(v_it_u2082_224_, 0);
        crate::leanh::lean_inc(v_val_229_);
        crate::leanh::lean_dec_ref_known(v_it_u2082_224_, 1);
        v___x_230_ = crate::leanh::lean_apply_1(v_h__2_226_, v_val_229_);
        return v___x_230_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FlatMap_0__Std_IterM_step__filterMapWithPostcondition_match__3_splitter___redArg(
    mut v_x_231_: *mut crate::leanh::LeanObject,
    mut v_h__1_232_: *mut crate::leanh::LeanObject,
    mut v_h__2_233_: *mut crate::leanh::LeanObject,
    mut v_h__3_234_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_231_) {
        0 => {
            let mut v_it_235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_234_);
            crate::leanh::lean_dec(v_h__2_233_);
            v_it_235_ = crate::leanh::lean_ctor_get(v_x_231_, 0);
            crate::leanh::lean_inc(v_it_235_);
            v_out_236_ = crate::leanh::lean_ctor_get(v_x_231_, 1);
            crate::leanh::lean_inc(v_out_236_);
            crate::leanh::lean_dec_ref_known(v_x_231_, 2);
            v___x_237_ = crate::leanh::lean_apply_3(
                v_h__1_232_,
                v_it_235_,
                v_out_236_,
                crate::leanh::lean_box(0),
            );
            return v___x_237_;
        }
        1 => {
            let mut v_it_238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_234_);
            crate::leanh::lean_dec(v_h__1_232_);
            v_it_238_ = crate::leanh::lean_ctor_get(v_x_231_, 0);
            crate::leanh::lean_inc(v_it_238_);
            crate::leanh::lean_dec_ref_known(v_x_231_, 1);
            v___x_239_ =
                crate::leanh::lean_apply_2(v_h__2_233_, v_it_238_, crate::leanh::lean_box(0));
            return v___x_239_;
        }
        _ => {
            let mut v___x_240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_233_);
            crate::leanh::lean_dec(v_h__1_232_);
            v___x_240_ = crate::leanh::lean_apply_1(v_h__3_234_, crate::leanh::lean_box(0));
            return v___x_240_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FlatMap_0__Std_IterM_step__filterMapWithPostcondition_match__3_splitter(
    mut v_00_u03b1_241_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_242_: *mut crate::leanh::LeanObject,
    mut v_m_243_: *mut crate::leanh::LeanObject,
    mut v_inst_244_: *mut crate::leanh::LeanObject,
    mut v_it_245_: *mut crate::leanh::LeanObject,
    mut v_motive_246_: *mut crate::leanh::LeanObject,
    mut v_x_247_: *mut crate::leanh::LeanObject,
    mut v_h__1_248_: *mut crate::leanh::LeanObject,
    mut v_h__2_249_: *mut crate::leanh::LeanObject,
    mut v_h__3_250_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_247_) {
        0 => {
            let mut v_it_251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_250_);
            crate::leanh::lean_dec(v_h__2_249_);
            v_it_251_ = crate::leanh::lean_ctor_get(v_x_247_, 0);
            crate::leanh::lean_inc(v_it_251_);
            v_out_252_ = crate::leanh::lean_ctor_get(v_x_247_, 1);
            crate::leanh::lean_inc(v_out_252_);
            crate::leanh::lean_dec_ref_known(v_x_247_, 2);
            v___x_253_ = crate::leanh::lean_apply_3(
                v_h__1_248_,
                v_it_251_,
                v_out_252_,
                crate::leanh::lean_box(0),
            );
            return v___x_253_;
        }
        1 => {
            let mut v_it_254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_250_);
            crate::leanh::lean_dec(v_h__1_248_);
            v_it_254_ = crate::leanh::lean_ctor_get(v_x_247_, 0);
            crate::leanh::lean_inc(v_it_254_);
            crate::leanh::lean_dec_ref_known(v_x_247_, 1);
            v___x_255_ =
                crate::leanh::lean_apply_2(v_h__2_249_, v_it_254_, crate::leanh::lean_box(0));
            return v___x_255_;
        }
        _ => {
            let mut v___x_256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_249_);
            crate::leanh::lean_dec(v_h__1_248_);
            v___x_256_ = crate::leanh::lean_apply_1(v_h__3_250_, crate::leanh::lean_box(0));
            return v___x_256_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FlatMap_0__Std_IterM_step__filterMapWithPostcondition_match__3_splitter___boxed(
    mut v_00_u03b1_257_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_258_: *mut crate::leanh::LeanObject,
    mut v_m_259_: *mut crate::leanh::LeanObject,
    mut v_inst_260_: *mut crate::leanh::LeanObject,
    mut v_it_261_: *mut crate::leanh::LeanObject,
    mut v_motive_262_: *mut crate::leanh::LeanObject,
    mut v_x_263_: *mut crate::leanh::LeanObject,
    mut v_h__1_264_: *mut crate::leanh::LeanObject,
    mut v_h__2_265_: *mut crate::leanh::LeanObject,
    mut v_h__3_266_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_267_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FlatMap_0__Std_IterM_step__filterMapWithPostcondition_match__3_splitter(v_00_u03b1_257_, v_00_u03b2_258_, v_m_259_, v_inst_260_, v_it_261_, v_motive_262_, v_x_263_, v_h__1_264_, v_h__2_265_, v_h__3_266_);
    crate::leanh::lean_dec(v_it_261_);
    crate::leanh::lean_dec(v_inst_260_);
    return v_res_267_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FlatMap_0__Std_IterM_step__flattenAfter_match__1_splitter___redArg(
    mut v_x_268_: *mut crate::leanh::LeanObject,
    mut v_h__1_269_: *mut crate::leanh::LeanObject,
    mut v_h__2_270_: *mut crate::leanh::LeanObject,
    mut v_h__3_271_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_268_) {
        0 => {
            let mut v_it_272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_271_);
            crate::leanh::lean_dec(v_h__2_270_);
            v_it_272_ = crate::leanh::lean_ctor_get(v_x_268_, 0);
            crate::leanh::lean_inc(v_it_272_);
            v_out_273_ = crate::leanh::lean_ctor_get(v_x_268_, 1);
            crate::leanh::lean_inc(v_out_273_);
            crate::leanh::lean_dec_ref_known(v_x_268_, 2);
            v___x_274_ = crate::leanh::lean_apply_3(
                v_h__1_269_,
                v_it_272_,
                v_out_273_,
                crate::leanh::lean_box(0),
            );
            return v___x_274_;
        }
        1 => {
            let mut v_it_275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_271_);
            crate::leanh::lean_dec(v_h__1_269_);
            v_it_275_ = crate::leanh::lean_ctor_get(v_x_268_, 0);
            crate::leanh::lean_inc(v_it_275_);
            crate::leanh::lean_dec_ref_known(v_x_268_, 1);
            v___x_276_ =
                crate::leanh::lean_apply_2(v_h__2_270_, v_it_275_, crate::leanh::lean_box(0));
            return v___x_276_;
        }
        _ => {
            let mut v___x_277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_270_);
            crate::leanh::lean_dec(v_h__1_269_);
            v___x_277_ = crate::leanh::lean_apply_1(v_h__3_271_, crate::leanh::lean_box(0));
            return v___x_277_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FlatMap_0__Std_IterM_step__flattenAfter_match__1_splitter(
    mut v_00_u03b1_278_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_u2082_279_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_280_: *mut crate::leanh::LeanObject,
    mut v_m_281_: *mut crate::leanh::LeanObject,
    mut v_inst_282_: *mut crate::leanh::LeanObject,
    mut v_it_u2081_283_: *mut crate::leanh::LeanObject,
    mut v_motive_284_: *mut crate::leanh::LeanObject,
    mut v_x_285_: *mut crate::leanh::LeanObject,
    mut v_h__1_286_: *mut crate::leanh::LeanObject,
    mut v_h__2_287_: *mut crate::leanh::LeanObject,
    mut v_h__3_288_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_285_) {
        0 => {
            let mut v_it_289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_288_);
            crate::leanh::lean_dec(v_h__2_287_);
            v_it_289_ = crate::leanh::lean_ctor_get(v_x_285_, 0);
            crate::leanh::lean_inc(v_it_289_);
            v_out_290_ = crate::leanh::lean_ctor_get(v_x_285_, 1);
            crate::leanh::lean_inc(v_out_290_);
            crate::leanh::lean_dec_ref_known(v_x_285_, 2);
            v___x_291_ = crate::leanh::lean_apply_3(
                v_h__1_286_,
                v_it_289_,
                v_out_290_,
                crate::leanh::lean_box(0),
            );
            return v___x_291_;
        }
        1 => {
            let mut v_it_292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_288_);
            crate::leanh::lean_dec(v_h__1_286_);
            v_it_292_ = crate::leanh::lean_ctor_get(v_x_285_, 0);
            crate::leanh::lean_inc(v_it_292_);
            crate::leanh::lean_dec_ref_known(v_x_285_, 1);
            v___x_293_ =
                crate::leanh::lean_apply_2(v_h__2_287_, v_it_292_, crate::leanh::lean_box(0));
            return v___x_293_;
        }
        _ => {
            let mut v___x_294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_287_);
            crate::leanh::lean_dec(v_h__1_286_);
            v___x_294_ = crate::leanh::lean_apply_1(v_h__3_288_, crate::leanh::lean_box(0));
            return v___x_294_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FlatMap_0__Std_IterM_step__flattenAfter_match__1_splitter___boxed(
    mut v_00_u03b1_295_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_u2082_296_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_297_: *mut crate::leanh::LeanObject,
    mut v_m_298_: *mut crate::leanh::LeanObject,
    mut v_inst_299_: *mut crate::leanh::LeanObject,
    mut v_it_u2081_300_: *mut crate::leanh::LeanObject,
    mut v_motive_301_: *mut crate::leanh::LeanObject,
    mut v_x_302_: *mut crate::leanh::LeanObject,
    mut v_h__1_303_: *mut crate::leanh::LeanObject,
    mut v_h__2_304_: *mut crate::leanh::LeanObject,
    mut v_h__3_305_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_306_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FlatMap_0__Std_IterM_step__flattenAfter_match__1_splitter(v_00_u03b1_295_, v_00_u03b1_u2082_296_, v_00_u03b2_297_, v_m_298_, v_inst_299_, v_it_u2081_300_, v_motive_301_, v_x_302_, v_h__1_303_, v_h__2_304_, v_h__3_305_);
    crate::leanh::lean_dec(v_it_u2081_300_);
    crate::leanh::lean_dec(v_inst_299_);
    return v_res_306_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FlatMap_0__Std_IterM_step__flattenAfter_match__3_splitter___redArg(
    mut v_x_307_: *mut crate::leanh::LeanObject,
    mut v_h__1_308_: *mut crate::leanh::LeanObject,
    mut v_h__2_309_: *mut crate::leanh::LeanObject,
    mut v_h__3_310_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_307_) {
        0 => {
            let mut v_it_311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_310_);
            crate::leanh::lean_dec(v_h__2_309_);
            v_it_311_ = crate::leanh::lean_ctor_get(v_x_307_, 0);
            crate::leanh::lean_inc(v_it_311_);
            v_out_312_ = crate::leanh::lean_ctor_get(v_x_307_, 1);
            crate::leanh::lean_inc(v_out_312_);
            crate::leanh::lean_dec_ref_known(v_x_307_, 2);
            v___x_313_ = crate::leanh::lean_apply_3(
                v_h__1_308_,
                v_it_311_,
                v_out_312_,
                crate::leanh::lean_box(0),
            );
            return v___x_313_;
        }
        1 => {
            let mut v_it_314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_310_);
            crate::leanh::lean_dec(v_h__1_308_);
            v_it_314_ = crate::leanh::lean_ctor_get(v_x_307_, 0);
            crate::leanh::lean_inc(v_it_314_);
            crate::leanh::lean_dec_ref_known(v_x_307_, 1);
            v___x_315_ =
                crate::leanh::lean_apply_2(v_h__2_309_, v_it_314_, crate::leanh::lean_box(0));
            return v___x_315_;
        }
        _ => {
            let mut v___x_316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_309_);
            crate::leanh::lean_dec(v_h__1_308_);
            v___x_316_ = crate::leanh::lean_apply_1(v_h__3_310_, crate::leanh::lean_box(0));
            return v___x_316_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FlatMap_0__Std_IterM_step__flattenAfter_match__3_splitter(
    mut v_00_u03b1_u2082_317_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_318_: *mut crate::leanh::LeanObject,
    mut v_m_319_: *mut crate::leanh::LeanObject,
    mut v_inst_320_: *mut crate::leanh::LeanObject,
    mut v_it_u2082_321_: *mut crate::leanh::LeanObject,
    mut v_motive_322_: *mut crate::leanh::LeanObject,
    mut v_x_323_: *mut crate::leanh::LeanObject,
    mut v_h__1_324_: *mut crate::leanh::LeanObject,
    mut v_h__2_325_: *mut crate::leanh::LeanObject,
    mut v_h__3_326_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_323_) {
        0 => {
            let mut v_it_327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_326_);
            crate::leanh::lean_dec(v_h__2_325_);
            v_it_327_ = crate::leanh::lean_ctor_get(v_x_323_, 0);
            crate::leanh::lean_inc(v_it_327_);
            v_out_328_ = crate::leanh::lean_ctor_get(v_x_323_, 1);
            crate::leanh::lean_inc(v_out_328_);
            crate::leanh::lean_dec_ref_known(v_x_323_, 2);
            v___x_329_ = crate::leanh::lean_apply_3(
                v_h__1_324_,
                v_it_327_,
                v_out_328_,
                crate::leanh::lean_box(0),
            );
            return v___x_329_;
        }
        1 => {
            let mut v_it_330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_326_);
            crate::leanh::lean_dec(v_h__1_324_);
            v_it_330_ = crate::leanh::lean_ctor_get(v_x_323_, 0);
            crate::leanh::lean_inc(v_it_330_);
            crate::leanh::lean_dec_ref_known(v_x_323_, 1);
            v___x_331_ =
                crate::leanh::lean_apply_2(v_h__2_325_, v_it_330_, crate::leanh::lean_box(0));
            return v___x_331_;
        }
        _ => {
            let mut v___x_332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_325_);
            crate::leanh::lean_dec(v_h__1_324_);
            v___x_332_ = crate::leanh::lean_apply_1(v_h__3_326_, crate::leanh::lean_box(0));
            return v___x_332_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FlatMap_0__Std_IterM_step__flattenAfter_match__3_splitter___boxed(
    mut v_00_u03b1_u2082_333_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_334_: *mut crate::leanh::LeanObject,
    mut v_m_335_: *mut crate::leanh::LeanObject,
    mut v_inst_336_: *mut crate::leanh::LeanObject,
    mut v_it_u2082_337_: *mut crate::leanh::LeanObject,
    mut v_motive_338_: *mut crate::leanh::LeanObject,
    mut v_x_339_: *mut crate::leanh::LeanObject,
    mut v_h__1_340_: *mut crate::leanh::LeanObject,
    mut v_h__2_341_: *mut crate::leanh::LeanObject,
    mut v_h__3_342_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_343_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FlatMap_0__Std_IterM_step__flattenAfter_match__3_splitter(v_00_u03b1_u2082_333_, v_00_u03b2_334_, v_m_335_, v_inst_336_, v_it_u2082_337_, v_motive_338_, v_x_339_, v_h__1_340_, v_h__2_341_, v_h__3_342_);
    crate::leanh::lean_dec(v_it_u2082_337_);
    crate::leanh::lean_dec(v_inst_336_);
    return v_res_343_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FlatMap_0__Std_IterM_step__flatMapAfterM_match__3_splitter___redArg(
    mut v_it_u2082_344_: *mut crate::leanh::LeanObject,
    mut v_h__1_345_: *mut crate::leanh::LeanObject,
    mut v_h__2_346_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_it_u2082_344_) == 0 {
        let mut v___x_347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_346_);
        v___x_347_ = crate::leanh::lean_box(0);
        v___x_348_ = crate::leanh::lean_apply_1(v_h__1_345_, v___x_347_);
        return v___x_348_;
    } else {
        let mut v_val_349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_345_);
        v_val_349_ = crate::leanh::lean_ctor_get(v_it_u2082_344_, 0);
        crate::leanh::lean_inc(v_val_349_);
        crate::leanh::lean_dec_ref_known(v_it_u2082_344_, 1);
        v___x_350_ = crate::leanh::lean_apply_1(v_h__2_346_, v_val_349_);
        return v___x_350_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FlatMap_0__Std_IterM_step__flatMapAfterM_match__3_splitter(
    mut v_00_u03b1_u2082_351_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_352_: *mut crate::leanh::LeanObject,
    mut v_m_353_: *mut crate::leanh::LeanObject,
    mut v_motive_354_: *mut crate::leanh::LeanObject,
    mut v_it_u2082_355_: *mut crate::leanh::LeanObject,
    mut v_h__1_356_: *mut crate::leanh::LeanObject,
    mut v_h__2_357_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_it_u2082_355_) == 0 {
        let mut v___x_358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_357_);
        v___x_358_ = crate::leanh::lean_box(0);
        v___x_359_ = crate::leanh::lean_apply_1(v_h__1_356_, v___x_358_);
        return v___x_359_;
    } else {
        let mut v_val_360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_356_);
        v_val_360_ = crate::leanh::lean_ctor_get(v_it_u2082_355_, 0);
        crate::leanh::lean_inc(v_val_360_);
        crate::leanh::lean_dec_ref_known(v_it_u2082_355_, 1);
        v___x_361_ = crate::leanh::lean_apply_1(v_h__2_357_, v_val_360_);
        return v___x_361_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FlatMap_0__Std_IterM_step__flatMapAfterM_match__1_splitter___redArg(
    mut v_x_362_: *mut crate::leanh::LeanObject,
    mut v_h__1_363_: *mut crate::leanh::LeanObject,
    mut v_h__2_364_: *mut crate::leanh::LeanObject,
    mut v_h__3_365_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_362_) {
        0 => {
            let mut v_it_366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_365_);
            crate::leanh::lean_dec(v_h__2_364_);
            v_it_366_ = crate::leanh::lean_ctor_get(v_x_362_, 0);
            crate::leanh::lean_inc(v_it_366_);
            v_out_367_ = crate::leanh::lean_ctor_get(v_x_362_, 1);
            crate::leanh::lean_inc(v_out_367_);
            crate::leanh::lean_dec_ref_known(v_x_362_, 2);
            v___x_368_ = crate::leanh::lean_apply_3(
                v_h__1_363_,
                v_it_366_,
                v_out_367_,
                crate::leanh::lean_box(0),
            );
            return v___x_368_;
        }
        1 => {
            let mut v_it_369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_365_);
            crate::leanh::lean_dec(v_h__1_363_);
            v_it_369_ = crate::leanh::lean_ctor_get(v_x_362_, 0);
            crate::leanh::lean_inc(v_it_369_);
            crate::leanh::lean_dec_ref_known(v_x_362_, 1);
            v___x_370_ =
                crate::leanh::lean_apply_2(v_h__2_364_, v_it_369_, crate::leanh::lean_box(0));
            return v___x_370_;
        }
        _ => {
            let mut v___x_371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_364_);
            crate::leanh::lean_dec(v_h__1_363_);
            v___x_371_ = crate::leanh::lean_apply_1(v_h__3_365_, crate::leanh::lean_box(0));
            return v___x_371_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FlatMap_0__Std_IterM_step__flatMapAfterM_match__1_splitter(
    mut v_00_u03b1_372_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_373_: *mut crate::leanh::LeanObject,
    mut v_m_374_: *mut crate::leanh::LeanObject,
    mut v_inst_375_: *mut crate::leanh::LeanObject,
    mut v_it_u2081_376_: *mut crate::leanh::LeanObject,
    mut v_motive_377_: *mut crate::leanh::LeanObject,
    mut v_x_378_: *mut crate::leanh::LeanObject,
    mut v_h__1_379_: *mut crate::leanh::LeanObject,
    mut v_h__2_380_: *mut crate::leanh::LeanObject,
    mut v_h__3_381_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_378_) {
        0 => {
            let mut v_it_382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_381_);
            crate::leanh::lean_dec(v_h__2_380_);
            v_it_382_ = crate::leanh::lean_ctor_get(v_x_378_, 0);
            crate::leanh::lean_inc(v_it_382_);
            v_out_383_ = crate::leanh::lean_ctor_get(v_x_378_, 1);
            crate::leanh::lean_inc(v_out_383_);
            crate::leanh::lean_dec_ref_known(v_x_378_, 2);
            v___x_384_ = crate::leanh::lean_apply_3(
                v_h__1_379_,
                v_it_382_,
                v_out_383_,
                crate::leanh::lean_box(0),
            );
            return v___x_384_;
        }
        1 => {
            let mut v_it_385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_381_);
            crate::leanh::lean_dec(v_h__1_379_);
            v_it_385_ = crate::leanh::lean_ctor_get(v_x_378_, 0);
            crate::leanh::lean_inc(v_it_385_);
            crate::leanh::lean_dec_ref_known(v_x_378_, 1);
            v___x_386_ =
                crate::leanh::lean_apply_2(v_h__2_380_, v_it_385_, crate::leanh::lean_box(0));
            return v___x_386_;
        }
        _ => {
            let mut v___x_387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_380_);
            crate::leanh::lean_dec(v_h__1_379_);
            v___x_387_ = crate::leanh::lean_apply_1(v_h__3_381_, crate::leanh::lean_box(0));
            return v___x_387_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FlatMap_0__Std_IterM_step__flatMapAfterM_match__1_splitter___boxed(
    mut v_00_u03b1_388_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_389_: *mut crate::leanh::LeanObject,
    mut v_m_390_: *mut crate::leanh::LeanObject,
    mut v_inst_391_: *mut crate::leanh::LeanObject,
    mut v_it_u2081_392_: *mut crate::leanh::LeanObject,
    mut v_motive_393_: *mut crate::leanh::LeanObject,
    mut v_x_394_: *mut crate::leanh::LeanObject,
    mut v_h__1_395_: *mut crate::leanh::LeanObject,
    mut v_h__2_396_: *mut crate::leanh::LeanObject,
    mut v_h__3_397_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_398_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FlatMap_0__Std_IterM_step__flatMapAfterM_match__1_splitter(v_00_u03b1_388_, v_00_u03b2_389_, v_m_390_, v_inst_391_, v_it_u2081_392_, v_motive_393_, v_x_394_, v_h__1_395_, v_h__2_396_, v_h__3_397_);
    crate::leanh::lean_dec(v_it_u2081_392_);
    crate::leanh::lean_dec(v_inst_391_);
    return v_res_398_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FlatMap_0__Std_IterM_toArray__eq__match__step_match__1_splitter___redArg(
    mut v_x_399_: *mut crate::leanh::LeanObject,
    mut v_h__1_400_: *mut crate::leanh::LeanObject,
    mut v_h__2_401_: *mut crate::leanh::LeanObject,
    mut v_h__3_402_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_399_) {
        0 => {
            let mut v_it_403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_402_);
            crate::leanh::lean_dec(v_h__2_401_);
            v_it_403_ = crate::leanh::lean_ctor_get(v_x_399_, 0);
            crate::leanh::lean_inc(v_it_403_);
            v_out_404_ = crate::leanh::lean_ctor_get(v_x_399_, 1);
            crate::leanh::lean_inc(v_out_404_);
            crate::leanh::lean_dec_ref_known(v_x_399_, 2);
            v___x_405_ = crate::leanh::lean_apply_2(v_h__1_400_, v_it_403_, v_out_404_);
            return v___x_405_;
        }
        1 => {
            let mut v_it_406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_402_);
            crate::leanh::lean_dec(v_h__1_400_);
            v_it_406_ = crate::leanh::lean_ctor_get(v_x_399_, 0);
            crate::leanh::lean_inc(v_it_406_);
            crate::leanh::lean_dec_ref_known(v_x_399_, 1);
            v___x_407_ = crate::leanh::lean_apply_1(v_h__2_401_, v_it_406_);
            return v___x_407_;
        }
        _ => {
            let mut v___x_408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_401_);
            crate::leanh::lean_dec(v_h__1_400_);
            v___x_408_ = crate::leanh::lean_box(0);
            v___x_409_ = crate::leanh::lean_apply_1(v_h__3_402_, v___x_408_);
            return v___x_409_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_FlatMap_0__Std_IterM_toArray__eq__match__step_match__1_splitter(
    mut v_00_u03b1_410_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_411_: *mut crate::leanh::LeanObject,
    mut v_m_412_: *mut crate::leanh::LeanObject,
    mut v_motive_413_: *mut crate::leanh::LeanObject,
    mut v_x_414_: *mut crate::leanh::LeanObject,
    mut v_h__1_415_: *mut crate::leanh::LeanObject,
    mut v_h__2_416_: *mut crate::leanh::LeanObject,
    mut v_h__3_417_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_414_) {
        0 => {
            let mut v_it_418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_417_);
            crate::leanh::lean_dec(v_h__2_416_);
            v_it_418_ = crate::leanh::lean_ctor_get(v_x_414_, 0);
            crate::leanh::lean_inc(v_it_418_);
            v_out_419_ = crate::leanh::lean_ctor_get(v_x_414_, 1);
            crate::leanh::lean_inc(v_out_419_);
            crate::leanh::lean_dec_ref_known(v_x_414_, 2);
            v___x_420_ = crate::leanh::lean_apply_2(v_h__1_415_, v_it_418_, v_out_419_);
            return v___x_420_;
        }
        1 => {
            let mut v_it_421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_417_);
            crate::leanh::lean_dec(v_h__1_415_);
            v_it_421_ = crate::leanh::lean_ctor_get(v_x_414_, 0);
            crate::leanh::lean_inc(v_it_421_);
            crate::leanh::lean_dec_ref_known(v_x_414_, 1);
            v___x_422_ = crate::leanh::lean_apply_1(v_h__2_416_, v_it_421_);
            return v___x_422_;
        }
        _ => {
            let mut v___x_423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_416_);
            crate::leanh::lean_dec(v_h__1_415_);
            v___x_423_ = crate::leanh::lean_box(0);
            v___x_424_ = crate::leanh::lean_apply_1(v_h__3_417_, v___x_423_);
            return v___x_424_;
        }
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_FlatMap(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Combinators_Monadic_FlatMap(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Combinators_Monadic_FlatMap(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Collect(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Monadic_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_FlatMap(
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
pub unsafe fn initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_FlatMap(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Combinators_Monadic_FlatMap(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Combinators_Monadic_FlatMap(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers_Monadic_Collect(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Monadic_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_FlatMap(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_FlatMap(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_FlatMap(builtin);
}
