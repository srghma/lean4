// Lean compiler output
// Module: Init.Data.Iterators.Lemmas.Combinators.FlatMap
// Imports: Init.Data.Iterators.Lemmas.Combinators.FilterMap Init.Data.Iterators.Combinators.FlatMap Init.Data.Iterators.Combinators.FlatMap Init.Data.Iterators.Combinators.FilterMap Init.Data.Iterators.Consumers.Collect Init.Data.Iterators.Lemmas.Combinators.Monadic.FilterMap Init.Data.Iterators.Lemmas.Combinators.Monadic.FlatMap Init.Data.List.Monadic Init.Data.Option.Lemmas
use crate::r#gen::Init::Data::Iterators::Combinators::FilterMap::{
    initialize_Init_Data_Iterators_Combinators_FilterMap,
    runtime_initialize_Init_Data_Iterators_Combinators_FilterMap,
};
use crate::r#gen::Init::Data::Iterators::Combinators::FlatMap::{
    initialize_Init_Data_Iterators_Combinators_FlatMap,
    runtime_initialize_Init_Data_Iterators_Combinators_FlatMap,
};
use crate::r#gen::Init::Data::Iterators::Consumers::Collect::{
    initialize_Init_Data_Iterators_Consumers_Collect,
    runtime_initialize_Init_Data_Iterators_Consumers_Collect,
};
use crate::r#gen::Init::Data::Iterators::Lemmas::Combinators::FilterMap::{
    initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap,
    runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap,
};
use crate::r#gen::Init::Data::Iterators::Lemmas::Combinators::Monadic::FilterMap::{
    initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap,
    runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap,
};
use crate::r#gen::Init::Data::Iterators::Lemmas::Combinators::Monadic::FlatMap::{
    initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_FlatMap,
    runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_FlatMap,
};
use crate::r#gen::Init::Data::List::Monadic::{
    initialize_Init_Data_List_Monadic, runtime_initialize_Init_Data_List_Monadic,
};
use crate::r#gen::Init::Data::Option::Lemmas::{
    initialize_Init_Data_Option_Lemmas, runtime_initialize_Init_Data_Option_Lemmas,
};
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FlatMap_0__Std_IterM_step__flatMapAfterM_match__3_splitter___redArg(
    mut v_it_u2082_214_: *mut leanh::LeanObject,
    mut v_h__1_215_: *mut leanh::LeanObject,
    mut v_h__2_216_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_it_u2082_214_) == 0 {
        let mut v___x_217_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_218_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_216_);
        v___x_217_ = leanh::lean_box(0);
        v___x_218_ = leanh::lean_apply_1(v_h__1_215_, v___x_217_);
        return v___x_218_;
    } else {
        let mut v_val_219_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_220_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_215_);
        v_val_219_ = leanh::lean_ctor_get(v_it_u2082_214_, 0);
        leanh::lean_inc(v_val_219_);
        leanh::lean_dec_ref_known(v_it_u2082_214_, 1);
        v___x_220_ = leanh::lean_apply_1(v_h__2_216_, v_val_219_);
        return v___x_220_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FlatMap_0__Std_IterM_step__flatMapAfterM_match__3_splitter(
    mut v_00_u03b1_u2082_221_: *mut leanh::LeanObject,
    mut v_00_u03b3_222_: *mut leanh::LeanObject,
    mut v_m_223_: *mut leanh::LeanObject,
    mut v_motive_224_: *mut leanh::LeanObject,
    mut v_it_u2082_225_: *mut leanh::LeanObject,
    mut v_h__1_226_: *mut leanh::LeanObject,
    mut v_h__2_227_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_it_u2082_225_) == 0 {
        let mut v___x_228_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_229_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_227_);
        v___x_228_ = leanh::lean_box(0);
        v___x_229_ = leanh::lean_apply_1(v_h__1_226_, v___x_228_);
        return v___x_229_;
    } else {
        let mut v_val_230_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_231_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_226_);
        v_val_230_ = leanh::lean_ctor_get(v_it_u2082_225_, 0);
        leanh::lean_inc(v_val_230_);
        leanh::lean_dec_ref_known(v_it_u2082_225_, 1);
        v___x_231_ = leanh::lean_apply_1(v_h__2_227_, v_val_230_);
        return v___x_231_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FlatMap_0__Std_Iter_step__filterMapWithPostcondition_match__3_splitter___redArg(
    mut v_x_232_: *mut leanh::LeanObject,
    mut v_h__1_233_: *mut leanh::LeanObject,
    mut v_h__2_234_: *mut leanh::LeanObject,
    mut v_h__3_235_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_232_) {
        0 => {
            let mut v_it_236_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_237_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_238_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_235_);
            leanh::lean_dec(v_h__2_234_);
            v_it_236_ = leanh::lean_ctor_get(v_x_232_, 0);
            leanh::lean_inc(v_it_236_);
            v_out_237_ = leanh::lean_ctor_get(v_x_232_, 1);
            leanh::lean_inc(v_out_237_);
            leanh::lean_dec_ref_known(v_x_232_, 2);
            v___x_238_ = leanh::lean_apply_3(
                v_h__1_233_,
                v_it_236_,
                v_out_237_,
                leanh::lean_box(0),
            );
            return v___x_238_;
        }
        1 => {
            let mut v_it_239_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_240_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_235_);
            leanh::lean_dec(v_h__1_233_);
            v_it_239_ = leanh::lean_ctor_get(v_x_232_, 0);
            leanh::lean_inc(v_it_239_);
            leanh::lean_dec_ref_known(v_x_232_, 1);
            v___x_240_ =
                leanh::lean_apply_2(v_h__2_234_, v_it_239_, leanh::lean_box(0));
            return v___x_240_;
        }
        _ => {
            let mut v___x_241_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_234_);
            leanh::lean_dec(v_h__1_233_);
            v___x_241_ = leanh::lean_apply_1(v_h__3_235_, leanh::lean_box(0));
            return v___x_241_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FlatMap_0__Std_Iter_step__filterMapWithPostcondition_match__3_splitter(
    mut v_00_u03b1_242_: *mut leanh::LeanObject,
    mut v_00_u03b2_243_: *mut leanh::LeanObject,
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
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FlatMap_0__Std_Iter_step__filterMapWithPostcondition_match__3_splitter___boxed(
    mut v_00_u03b1_257_: *mut leanh::LeanObject,
    mut v_00_u03b2_258_: *mut leanh::LeanObject,
    mut v_inst_259_: *mut leanh::LeanObject,
    mut v_it_260_: *mut leanh::LeanObject,
    mut v_motive_261_: *mut leanh::LeanObject,
    mut v_x_262_: *mut leanh::LeanObject,
    mut v_h__1_263_: *mut leanh::LeanObject,
    mut v_h__2_264_: *mut leanh::LeanObject,
    mut v_h__3_265_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_266_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_266_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FlatMap_0__Std_Iter_step__filterMapWithPostcondition_match__3_splitter(v_00_u03b1_257_, v_00_u03b2_258_, v_inst_259_, v_it_260_, v_motive_261_, v_x_262_, v_h__1_263_, v_h__2_264_, v_h__3_265_);
    leanh::lean_dec(v_it_260_);
    leanh::lean_dec(v_inst_259_);
    return v_res_266_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FlatMap_0__Std_IterM_step__flatMapAfterM_match__1_splitter___redArg(
    mut v_x_267_: *mut leanh::LeanObject,
    mut v_h__1_268_: *mut leanh::LeanObject,
    mut v_h__2_269_: *mut leanh::LeanObject,
    mut v_h__3_270_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_267_) {
        0 => {
            let mut v_it_271_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_272_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_273_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_270_);
            leanh::lean_dec(v_h__2_269_);
            v_it_271_ = leanh::lean_ctor_get(v_x_267_, 0);
            leanh::lean_inc(v_it_271_);
            v_out_272_ = leanh::lean_ctor_get(v_x_267_, 1);
            leanh::lean_inc(v_out_272_);
            leanh::lean_dec_ref_known(v_x_267_, 2);
            v___x_273_ = leanh::lean_apply_3(
                v_h__1_268_,
                v_it_271_,
                v_out_272_,
                leanh::lean_box(0),
            );
            return v___x_273_;
        }
        1 => {
            let mut v_it_274_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_275_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_270_);
            leanh::lean_dec(v_h__1_268_);
            v_it_274_ = leanh::lean_ctor_get(v_x_267_, 0);
            leanh::lean_inc(v_it_274_);
            leanh::lean_dec_ref_known(v_x_267_, 1);
            v___x_275_ =
                leanh::lean_apply_2(v_h__2_269_, v_it_274_, leanh::lean_box(0));
            return v___x_275_;
        }
        _ => {
            let mut v___x_276_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_269_);
            leanh::lean_dec(v_h__1_268_);
            v___x_276_ = leanh::lean_apply_1(v_h__3_270_, leanh::lean_box(0));
            return v___x_276_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FlatMap_0__Std_IterM_step__flatMapAfterM_match__1_splitter(
    mut v_00_u03b1_277_: *mut leanh::LeanObject,
    mut v_00_u03b2_278_: *mut leanh::LeanObject,
    mut v_m_279_: *mut leanh::LeanObject,
    mut v_inst_280_: *mut leanh::LeanObject,
    mut v_it_u2081_281_: *mut leanh::LeanObject,
    mut v_motive_282_: *mut leanh::LeanObject,
    mut v_x_283_: *mut leanh::LeanObject,
    mut v_h__1_284_: *mut leanh::LeanObject,
    mut v_h__2_285_: *mut leanh::LeanObject,
    mut v_h__3_286_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_283_) {
        0 => {
            let mut v_it_287_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_288_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_289_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_286_);
            leanh::lean_dec(v_h__2_285_);
            v_it_287_ = leanh::lean_ctor_get(v_x_283_, 0);
            leanh::lean_inc(v_it_287_);
            v_out_288_ = leanh::lean_ctor_get(v_x_283_, 1);
            leanh::lean_inc(v_out_288_);
            leanh::lean_dec_ref_known(v_x_283_, 2);
            v___x_289_ = leanh::lean_apply_3(
                v_h__1_284_,
                v_it_287_,
                v_out_288_,
                leanh::lean_box(0),
            );
            return v___x_289_;
        }
        1 => {
            let mut v_it_290_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_291_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_286_);
            leanh::lean_dec(v_h__1_284_);
            v_it_290_ = leanh::lean_ctor_get(v_x_283_, 0);
            leanh::lean_inc(v_it_290_);
            leanh::lean_dec_ref_known(v_x_283_, 1);
            v___x_291_ =
                leanh::lean_apply_2(v_h__2_285_, v_it_290_, leanh::lean_box(0));
            return v___x_291_;
        }
        _ => {
            let mut v___x_292_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_285_);
            leanh::lean_dec(v_h__1_284_);
            v___x_292_ = leanh::lean_apply_1(v_h__3_286_, leanh::lean_box(0));
            return v___x_292_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FlatMap_0__Std_IterM_step__flatMapAfterM_match__1_splitter___boxed(
    mut v_00_u03b1_293_: *mut leanh::LeanObject,
    mut v_00_u03b2_294_: *mut leanh::LeanObject,
    mut v_m_295_: *mut leanh::LeanObject,
    mut v_inst_296_: *mut leanh::LeanObject,
    mut v_it_u2081_297_: *mut leanh::LeanObject,
    mut v_motive_298_: *mut leanh::LeanObject,
    mut v_x_299_: *mut leanh::LeanObject,
    mut v_h__1_300_: *mut leanh::LeanObject,
    mut v_h__2_301_: *mut leanh::LeanObject,
    mut v_h__3_302_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_303_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_303_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FlatMap_0__Std_IterM_step__flatMapAfterM_match__1_splitter(v_00_u03b1_293_, v_00_u03b2_294_, v_m_295_, v_inst_296_, v_it_u2081_297_, v_motive_298_, v_x_299_, v_h__1_300_, v_h__2_301_, v_h__3_302_);
    leanh::lean_dec(v_it_u2081_297_);
    leanh::lean_dec(v_inst_296_);
    return v_res_303_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FlatMap_0__Std_Iter_step__flatMapAfterM_match__5_splitter___redArg(
    mut v_it_u2082_304_: *mut leanh::LeanObject,
    mut v_h__1_305_: *mut leanh::LeanObject,
    mut v_h__2_306_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_it_u2082_304_) == 0 {
        let mut v___x_307_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_306_);
        v___x_307_ = leanh::lean_apply_1(v_h__1_305_, leanh::lean_box(0));
        return v___x_307_;
    } else {
        let mut v_val_308_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_309_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_305_);
        v_val_308_ = leanh::lean_ctor_get(v_it_u2082_304_, 0);
        leanh::lean_inc(v_val_308_);
        leanh::lean_dec_ref_known(v_it_u2082_304_, 1);
        v___x_309_ = leanh::lean_apply_2(v_h__2_306_, v_val_308_, leanh::lean_box(0));
        return v___x_309_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FlatMap_0__Std_Iter_step__flatMapAfterM_match__5_splitter(
    mut v_00_u03b1_u2082_310_: *mut leanh::LeanObject,
    mut v_00_u03b3_311_: *mut leanh::LeanObject,
    mut v_m_312_: *mut leanh::LeanObject,
    mut v_motive_313_: *mut leanh::LeanObject,
    mut v_it_u2082_314_: *mut leanh::LeanObject,
    mut v_h__1_315_: *mut leanh::LeanObject,
    mut v_h__2_316_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_it_u2082_314_) == 0 {
        let mut v___x_317_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_316_);
        v___x_317_ = leanh::lean_apply_1(v_h__1_315_, leanh::lean_box(0));
        return v___x_317_;
    } else {
        let mut v_val_318_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_319_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_315_);
        v_val_318_ = leanh::lean_ctor_get(v_it_u2082_314_, 0);
        leanh::lean_inc(v_val_318_);
        leanh::lean_dec_ref_known(v_it_u2082_314_, 1);
        v___x_319_ = leanh::lean_apply_2(v_h__2_316_, v_val_318_, leanh::lean_box(0));
        return v___x_319_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FlatMap_0__Std_Iter_step__flatMapAfterM_match__1_splitter___redArg(
    mut v_x_320_: *mut leanh::LeanObject,
    mut v_h__1_321_: *mut leanh::LeanObject,
    mut v_h__2_322_: *mut leanh::LeanObject,
    mut v_h__3_323_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_320_) {
        0 => {
            let mut v_it_324_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_325_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_326_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_323_);
            leanh::lean_dec(v_h__2_322_);
            v_it_324_ = leanh::lean_ctor_get(v_x_320_, 0);
            leanh::lean_inc(v_it_324_);
            v_out_325_ = leanh::lean_ctor_get(v_x_320_, 1);
            leanh::lean_inc(v_out_325_);
            leanh::lean_dec_ref_known(v_x_320_, 2);
            v___x_326_ = leanh::lean_apply_3(
                v_h__1_321_,
                v_it_324_,
                v_out_325_,
                leanh::lean_box(0),
            );
            return v___x_326_;
        }
        1 => {
            let mut v_it_327_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_328_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_323_);
            leanh::lean_dec(v_h__1_321_);
            v_it_327_ = leanh::lean_ctor_get(v_x_320_, 0);
            leanh::lean_inc(v_it_327_);
            leanh::lean_dec_ref_known(v_x_320_, 1);
            v___x_328_ =
                leanh::lean_apply_2(v_h__2_322_, v_it_327_, leanh::lean_box(0));
            return v___x_328_;
        }
        _ => {
            let mut v___x_329_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_322_);
            leanh::lean_dec(v_h__1_321_);
            v___x_329_ = leanh::lean_apply_1(v_h__3_323_, leanh::lean_box(0));
            return v___x_329_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FlatMap_0__Std_Iter_step__flatMapAfterM_match__1_splitter(
    mut v_00_u03b1_330_: *mut leanh::LeanObject,
    mut v_00_u03b2_331_: *mut leanh::LeanObject,
    mut v_inst_332_: *mut leanh::LeanObject,
    mut v_it_u2081_333_: *mut leanh::LeanObject,
    mut v_motive_334_: *mut leanh::LeanObject,
    mut v_x_335_: *mut leanh::LeanObject,
    mut v_h__1_336_: *mut leanh::LeanObject,
    mut v_h__2_337_: *mut leanh::LeanObject,
    mut v_h__3_338_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_335_) {
        0 => {
            let mut v_it_339_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_340_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_341_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_338_);
            leanh::lean_dec(v_h__2_337_);
            v_it_339_ = leanh::lean_ctor_get(v_x_335_, 0);
            leanh::lean_inc(v_it_339_);
            v_out_340_ = leanh::lean_ctor_get(v_x_335_, 1);
            leanh::lean_inc(v_out_340_);
            leanh::lean_dec_ref_known(v_x_335_, 2);
            v___x_341_ = leanh::lean_apply_3(
                v_h__1_336_,
                v_it_339_,
                v_out_340_,
                leanh::lean_box(0),
            );
            return v___x_341_;
        }
        1 => {
            let mut v_it_342_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_343_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_338_);
            leanh::lean_dec(v_h__1_336_);
            v_it_342_ = leanh::lean_ctor_get(v_x_335_, 0);
            leanh::lean_inc(v_it_342_);
            leanh::lean_dec_ref_known(v_x_335_, 1);
            v___x_343_ =
                leanh::lean_apply_2(v_h__2_337_, v_it_342_, leanh::lean_box(0));
            return v___x_343_;
        }
        _ => {
            let mut v___x_344_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_337_);
            leanh::lean_dec(v_h__1_336_);
            v___x_344_ = leanh::lean_apply_1(v_h__3_338_, leanh::lean_box(0));
            return v___x_344_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FlatMap_0__Std_Iter_step__flatMapAfterM_match__1_splitter___boxed(
    mut v_00_u03b1_345_: *mut leanh::LeanObject,
    mut v_00_u03b2_346_: *mut leanh::LeanObject,
    mut v_inst_347_: *mut leanh::LeanObject,
    mut v_it_u2081_348_: *mut leanh::LeanObject,
    mut v_motive_349_: *mut leanh::LeanObject,
    mut v_x_350_: *mut leanh::LeanObject,
    mut v_h__1_351_: *mut leanh::LeanObject,
    mut v_h__2_352_: *mut leanh::LeanObject,
    mut v_h__3_353_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_354_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_354_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FlatMap_0__Std_Iter_step__flatMapAfterM_match__1_splitter(v_00_u03b1_345_, v_00_u03b2_346_, v_inst_347_, v_it_u2081_348_, v_motive_349_, v_x_350_, v_h__1_351_, v_h__2_352_, v_h__3_353_);
    leanh::lean_dec(v_it_u2081_348_);
    leanh::lean_dec(v_inst_347_);
    return v_res_354_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FlatMap_0__Std_Iter_step__flatMapAfterM_match__3_splitter___redArg(
    mut v_x_355_: *mut leanh::LeanObject,
    mut v_h__1_356_: *mut leanh::LeanObject,
    mut v_h__2_357_: *mut leanh::LeanObject,
    mut v_h__3_358_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_355_) {
        0 => {
            let mut v_it_359_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_360_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_361_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_358_);
            leanh::lean_dec(v_h__2_357_);
            v_it_359_ = leanh::lean_ctor_get(v_x_355_, 0);
            leanh::lean_inc(v_it_359_);
            v_out_360_ = leanh::lean_ctor_get(v_x_355_, 1);
            leanh::lean_inc(v_out_360_);
            leanh::lean_dec_ref_known(v_x_355_, 2);
            v___x_361_ = leanh::lean_apply_3(
                v_h__1_356_,
                v_it_359_,
                v_out_360_,
                leanh::lean_box(0),
            );
            return v___x_361_;
        }
        1 => {
            let mut v_it_362_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_363_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_358_);
            leanh::lean_dec(v_h__1_356_);
            v_it_362_ = leanh::lean_ctor_get(v_x_355_, 0);
            leanh::lean_inc(v_it_362_);
            leanh::lean_dec_ref_known(v_x_355_, 1);
            v___x_363_ =
                leanh::lean_apply_2(v_h__2_357_, v_it_362_, leanh::lean_box(0));
            return v___x_363_;
        }
        _ => {
            let mut v___x_364_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_357_);
            leanh::lean_dec(v_h__1_356_);
            v___x_364_ = leanh::lean_apply_1(v_h__3_358_, leanh::lean_box(0));
            return v___x_364_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FlatMap_0__Std_Iter_step__flatMapAfterM_match__3_splitter(
    mut v_00_u03b1_u2082_365_: *mut leanh::LeanObject,
    mut v_00_u03b3_366_: *mut leanh::LeanObject,
    mut v_m_367_: *mut leanh::LeanObject,
    mut v_inst_368_: *mut leanh::LeanObject,
    mut v_it_u2082_369_: *mut leanh::LeanObject,
    mut v_motive_370_: *mut leanh::LeanObject,
    mut v_x_371_: *mut leanh::LeanObject,
    mut v_h__1_372_: *mut leanh::LeanObject,
    mut v_h__2_373_: *mut leanh::LeanObject,
    mut v_h__3_374_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_371_) {
        0 => {
            let mut v_it_375_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_376_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_377_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_374_);
            leanh::lean_dec(v_h__2_373_);
            v_it_375_ = leanh::lean_ctor_get(v_x_371_, 0);
            leanh::lean_inc(v_it_375_);
            v_out_376_ = leanh::lean_ctor_get(v_x_371_, 1);
            leanh::lean_inc(v_out_376_);
            leanh::lean_dec_ref_known(v_x_371_, 2);
            v___x_377_ = leanh::lean_apply_3(
                v_h__1_372_,
                v_it_375_,
                v_out_376_,
                leanh::lean_box(0),
            );
            return v___x_377_;
        }
        1 => {
            let mut v_it_378_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_379_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_374_);
            leanh::lean_dec(v_h__1_372_);
            v_it_378_ = leanh::lean_ctor_get(v_x_371_, 0);
            leanh::lean_inc(v_it_378_);
            leanh::lean_dec_ref_known(v_x_371_, 1);
            v___x_379_ =
                leanh::lean_apply_2(v_h__2_373_, v_it_378_, leanh::lean_box(0));
            return v___x_379_;
        }
        _ => {
            let mut v___x_380_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_373_);
            leanh::lean_dec(v_h__1_372_);
            v___x_380_ = leanh::lean_apply_1(v_h__3_374_, leanh::lean_box(0));
            return v___x_380_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FlatMap_0__Std_Iter_step__flatMapAfterM_match__3_splitter___boxed(
    mut v_00_u03b1_u2082_381_: *mut leanh::LeanObject,
    mut v_00_u03b3_382_: *mut leanh::LeanObject,
    mut v_m_383_: *mut leanh::LeanObject,
    mut v_inst_384_: *mut leanh::LeanObject,
    mut v_it_u2082_385_: *mut leanh::LeanObject,
    mut v_motive_386_: *mut leanh::LeanObject,
    mut v_x_387_: *mut leanh::LeanObject,
    mut v_h__1_388_: *mut leanh::LeanObject,
    mut v_h__2_389_: *mut leanh::LeanObject,
    mut v_h__3_390_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_391_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_391_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FlatMap_0__Std_Iter_step__flatMapAfterM_match__3_splitter(v_00_u03b1_u2082_381_, v_00_u03b3_382_, v_m_383_, v_inst_384_, v_it_u2082_385_, v_motive_386_, v_x_387_, v_h__1_388_, v_h__2_389_, v_h__3_390_);
    leanh::lean_dec(v_it_u2082_385_);
    leanh::lean_dec(v_inst_384_);
    return v_res_391_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FlatMap_0__Std_Iter_step__flatMapAfter_match__1_splitter___redArg(
    mut v_it_u2082_392_: *mut leanh::LeanObject,
    mut v_h__1_393_: *mut leanh::LeanObject,
    mut v_h__2_394_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_it_u2082_392_) == 0 {
        let mut v___x_395_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_396_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_394_);
        v___x_395_ = leanh::lean_box(0);
        v___x_396_ = leanh::lean_apply_1(v_h__1_393_, v___x_395_);
        return v___x_396_;
    } else {
        let mut v_val_397_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_398_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_393_);
        v_val_397_ = leanh::lean_ctor_get(v_it_u2082_392_, 0);
        leanh::lean_inc(v_val_397_);
        leanh::lean_dec_ref_known(v_it_u2082_392_, 1);
        v___x_398_ = leanh::lean_apply_1(v_h__2_394_, v_val_397_);
        return v___x_398_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FlatMap_0__Std_Iter_step__flatMapAfter_match__1_splitter(
    mut v_00_u03b1_u2082_399_: *mut leanh::LeanObject,
    mut v_00_u03b3_400_: *mut leanh::LeanObject,
    mut v_motive_401_: *mut leanh::LeanObject,
    mut v_it_u2082_402_: *mut leanh::LeanObject,
    mut v_h__1_403_: *mut leanh::LeanObject,
    mut v_h__2_404_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_it_u2082_402_) == 0 {
        let mut v___x_405_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_406_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_404_);
        v___x_405_ = leanh::lean_box(0);
        v___x_406_ = leanh::lean_apply_1(v_h__1_403_, v___x_405_);
        return v___x_406_;
    } else {
        let mut v_val_407_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_408_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_403_);
        v_val_407_ = leanh::lean_ctor_get(v_it_u2082_402_, 0);
        leanh::lean_inc(v_val_407_);
        leanh::lean_dec_ref_known(v_it_u2082_402_, 1);
        v___x_408_ = leanh::lean_apply_1(v_h__2_404_, v_val_407_);
        return v___x_408_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FlatMap_0__Std_Iter_toList__flatMapAfterM_match__1_splitter___redArg(
    mut v_it_u2082_409_: *mut leanh::LeanObject,
    mut v_h__1_410_: *mut leanh::LeanObject,
    mut v_h__2_411_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_it_u2082_409_) == 0 {
        let mut v___x_412_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_413_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_411_);
        v___x_412_ = leanh::lean_box(0);
        v___x_413_ = leanh::lean_apply_1(v_h__1_410_, v___x_412_);
        return v___x_413_;
    } else {
        let mut v_val_414_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_415_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_410_);
        v_val_414_ = leanh::lean_ctor_get(v_it_u2082_409_, 0);
        leanh::lean_inc(v_val_414_);
        leanh::lean_dec_ref_known(v_it_u2082_409_, 1);
        v___x_415_ = leanh::lean_apply_1(v_h__2_411_, v_val_414_);
        return v___x_415_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FlatMap_0__Std_Iter_toList__flatMapAfterM_match__1_splitter(
    mut v_00_u03b1_u2082_416_: *mut leanh::LeanObject,
    mut v_00_u03b3_417_: *mut leanh::LeanObject,
    mut v_m_418_: *mut leanh::LeanObject,
    mut v_motive_419_: *mut leanh::LeanObject,
    mut v_it_u2082_420_: *mut leanh::LeanObject,
    mut v_h__1_421_: *mut leanh::LeanObject,
    mut v_h__2_422_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_it_u2082_420_) == 0 {
        let mut v___x_423_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_424_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_422_);
        v___x_423_ = leanh::lean_box(0);
        v___x_424_ = leanh::lean_apply_1(v_h__1_421_, v___x_423_);
        return v___x_424_;
    } else {
        let mut v_val_425_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_426_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_421_);
        v_val_425_ = leanh::lean_ctor_get(v_it_u2082_420_, 0);
        leanh::lean_inc(v_val_425_);
        leanh::lean_dec_ref_known(v_it_u2082_420_, 1);
        v___x_426_ = leanh::lean_apply_1(v_h__2_422_, v_val_425_);
        return v___x_426_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_FlatMap(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Combinators_FlatMap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Combinators_FlatMap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Combinators_FilterMap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Collect(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_FlatMap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Monadic(builtin);
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
pub unsafe fn meta_initialize_Init_Data_Iterators_Lemmas_Combinators_FlatMap(
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
pub unsafe fn initialize_Init_Data_Iterators_Lemmas_Combinators_FlatMap(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Combinators_FlatMap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Combinators_FlatMap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Combinators_FilterMap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers_Collect(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_FlatMap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Monadic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Option_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_FlatMap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Iterators_Lemmas_Combinators_FlatMap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_Iterators_Lemmas_Combinators_FlatMap(builtin);
}