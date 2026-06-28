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
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_apply_1, lean_apply_2, lean_apply_3, lean_box,
    lean_ctor_get, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_obj_tag,
};
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FlatMap_0__Std_IterM_step__flatMapAfterM_match__3_splitter___redArg(
    mut v_it_u2082_214_: *mut LeanObject,
    mut v_h__1_215_: *mut LeanObject,
    mut v_h__2_216_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_it_u2082_214_) == 0 {
        let mut v___x_217_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_218_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_216_);
        v___x_217_ = lean_box(0);
        v___x_218_ = lean_apply_1(v_h__1_215_, v___x_217_);
        return v___x_218_;
    } else {
        let mut v_val_219_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_220_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_215_);
        v_val_219_ = lean_ctor_get(v_it_u2082_214_, 0);
        lean_inc(v_val_219_);
        lean_dec_ref_known(v_it_u2082_214_, 1);
        v___x_220_ = lean_apply_1(v_h__2_216_, v_val_219_);
        return v___x_220_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FlatMap_0__Std_IterM_step__flatMapAfterM_match__3_splitter(
    mut v_00_u03b1_u2082_221_: *mut LeanObject,
    mut v_00_u03b3_222_: *mut LeanObject,
    mut v_m_223_: *mut LeanObject,
    mut v_motive_224_: *mut LeanObject,
    mut v_it_u2082_225_: *mut LeanObject,
    mut v_h__1_226_: *mut LeanObject,
    mut v_h__2_227_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_it_u2082_225_) == 0 {
        let mut v___x_228_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_229_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_227_);
        v___x_228_ = lean_box(0);
        v___x_229_ = lean_apply_1(v_h__1_226_, v___x_228_);
        return v___x_229_;
    } else {
        let mut v_val_230_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_231_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_226_);
        v_val_230_ = lean_ctor_get(v_it_u2082_225_, 0);
        lean_inc(v_val_230_);
        lean_dec_ref_known(v_it_u2082_225_, 1);
        v___x_231_ = lean_apply_1(v_h__2_227_, v_val_230_);
        return v___x_231_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FlatMap_0__Std_Iter_step__filterMapWithPostcondition_match__3_splitter___redArg(
    mut v_x_232_: *mut LeanObject,
    mut v_h__1_233_: *mut LeanObject,
    mut v_h__2_234_: *mut LeanObject,
    mut v_h__3_235_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_232_) {
        0 => {
            let mut v_it_236_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_237_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_238_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_235_);
            lean_dec(v_h__2_234_);
            v_it_236_ = lean_ctor_get(v_x_232_, 0);
            lean_inc(v_it_236_);
            v_out_237_ = lean_ctor_get(v_x_232_, 1);
            lean_inc(v_out_237_);
            lean_dec_ref_known(v_x_232_, 2);
            v___x_238_ = lean_apply_3(v_h__1_233_, v_it_236_, v_out_237_, lean_box(0));
            return v___x_238_;
        }
        1 => {
            let mut v_it_239_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_240_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_235_);
            lean_dec(v_h__1_233_);
            v_it_239_ = lean_ctor_get(v_x_232_, 0);
            lean_inc(v_it_239_);
            lean_dec_ref_known(v_x_232_, 1);
            v___x_240_ = lean_apply_2(v_h__2_234_, v_it_239_, lean_box(0));
            return v___x_240_;
        }
        _ => {
            let mut v___x_241_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_234_);
            lean_dec(v_h__1_233_);
            v___x_241_ = lean_apply_1(v_h__3_235_, lean_box(0));
            return v___x_241_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FlatMap_0__Std_Iter_step__filterMapWithPostcondition_match__3_splitter(
    mut v_00_u03b1_242_: *mut LeanObject,
    mut v_00_u03b2_243_: *mut LeanObject,
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
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FlatMap_0__Std_Iter_step__filterMapWithPostcondition_match__3_splitter___boxed(
    mut v_00_u03b1_257_: *mut LeanObject,
    mut v_00_u03b2_258_: *mut LeanObject,
    mut v_inst_259_: *mut LeanObject,
    mut v_it_260_: *mut LeanObject,
    mut v_motive_261_: *mut LeanObject,
    mut v_x_262_: *mut LeanObject,
    mut v_h__1_263_: *mut LeanObject,
    mut v_h__2_264_: *mut LeanObject,
    mut v_h__3_265_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_266_: *mut LeanObject = core::ptr::null_mut();
    v_res_266_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FlatMap_0__Std_Iter_step__filterMapWithPostcondition_match__3_splitter(v_00_u03b1_257_, v_00_u03b2_258_, v_inst_259_, v_it_260_, v_motive_261_, v_x_262_, v_h__1_263_, v_h__2_264_, v_h__3_265_);
    lean_dec(v_it_260_);
    lean_dec(v_inst_259_);
    return v_res_266_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FlatMap_0__Std_IterM_step__flatMapAfterM_match__1_splitter___redArg(
    mut v_x_267_: *mut LeanObject,
    mut v_h__1_268_: *mut LeanObject,
    mut v_h__2_269_: *mut LeanObject,
    mut v_h__3_270_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_267_) {
        0 => {
            let mut v_it_271_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_272_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_273_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_270_);
            lean_dec(v_h__2_269_);
            v_it_271_ = lean_ctor_get(v_x_267_, 0);
            lean_inc(v_it_271_);
            v_out_272_ = lean_ctor_get(v_x_267_, 1);
            lean_inc(v_out_272_);
            lean_dec_ref_known(v_x_267_, 2);
            v___x_273_ = lean_apply_3(v_h__1_268_, v_it_271_, v_out_272_, lean_box(0));
            return v___x_273_;
        }
        1 => {
            let mut v_it_274_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_275_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_270_);
            lean_dec(v_h__1_268_);
            v_it_274_ = lean_ctor_get(v_x_267_, 0);
            lean_inc(v_it_274_);
            lean_dec_ref_known(v_x_267_, 1);
            v___x_275_ = lean_apply_2(v_h__2_269_, v_it_274_, lean_box(0));
            return v___x_275_;
        }
        _ => {
            let mut v___x_276_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_269_);
            lean_dec(v_h__1_268_);
            v___x_276_ = lean_apply_1(v_h__3_270_, lean_box(0));
            return v___x_276_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FlatMap_0__Std_IterM_step__flatMapAfterM_match__1_splitter(
    mut v_00_u03b1_277_: *mut LeanObject,
    mut v_00_u03b2_278_: *mut LeanObject,
    mut v_m_279_: *mut LeanObject,
    mut v_inst_280_: *mut LeanObject,
    mut v_it_u2081_281_: *mut LeanObject,
    mut v_motive_282_: *mut LeanObject,
    mut v_x_283_: *mut LeanObject,
    mut v_h__1_284_: *mut LeanObject,
    mut v_h__2_285_: *mut LeanObject,
    mut v_h__3_286_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_283_) {
        0 => {
            let mut v_it_287_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_288_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_289_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_286_);
            lean_dec(v_h__2_285_);
            v_it_287_ = lean_ctor_get(v_x_283_, 0);
            lean_inc(v_it_287_);
            v_out_288_ = lean_ctor_get(v_x_283_, 1);
            lean_inc(v_out_288_);
            lean_dec_ref_known(v_x_283_, 2);
            v___x_289_ = lean_apply_3(v_h__1_284_, v_it_287_, v_out_288_, lean_box(0));
            return v___x_289_;
        }
        1 => {
            let mut v_it_290_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_291_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_286_);
            lean_dec(v_h__1_284_);
            v_it_290_ = lean_ctor_get(v_x_283_, 0);
            lean_inc(v_it_290_);
            lean_dec_ref_known(v_x_283_, 1);
            v___x_291_ = lean_apply_2(v_h__2_285_, v_it_290_, lean_box(0));
            return v___x_291_;
        }
        _ => {
            let mut v___x_292_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_285_);
            lean_dec(v_h__1_284_);
            v___x_292_ = lean_apply_1(v_h__3_286_, lean_box(0));
            return v___x_292_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FlatMap_0__Std_IterM_step__flatMapAfterM_match__1_splitter___boxed(
    mut v_00_u03b1_293_: *mut LeanObject,
    mut v_00_u03b2_294_: *mut LeanObject,
    mut v_m_295_: *mut LeanObject,
    mut v_inst_296_: *mut LeanObject,
    mut v_it_u2081_297_: *mut LeanObject,
    mut v_motive_298_: *mut LeanObject,
    mut v_x_299_: *mut LeanObject,
    mut v_h__1_300_: *mut LeanObject,
    mut v_h__2_301_: *mut LeanObject,
    mut v_h__3_302_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_303_: *mut LeanObject = core::ptr::null_mut();
    v_res_303_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FlatMap_0__Std_IterM_step__flatMapAfterM_match__1_splitter(v_00_u03b1_293_, v_00_u03b2_294_, v_m_295_, v_inst_296_, v_it_u2081_297_, v_motive_298_, v_x_299_, v_h__1_300_, v_h__2_301_, v_h__3_302_);
    lean_dec(v_it_u2081_297_);
    lean_dec(v_inst_296_);
    return v_res_303_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FlatMap_0__Std_Iter_step__flatMapAfterM_match__5_splitter___redArg(
    mut v_it_u2082_304_: *mut LeanObject,
    mut v_h__1_305_: *mut LeanObject,
    mut v_h__2_306_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_it_u2082_304_) == 0 {
        let mut v___x_307_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_306_);
        v___x_307_ = lean_apply_1(v_h__1_305_, lean_box(0));
        return v___x_307_;
    } else {
        let mut v_val_308_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_309_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_305_);
        v_val_308_ = lean_ctor_get(v_it_u2082_304_, 0);
        lean_inc(v_val_308_);
        lean_dec_ref_known(v_it_u2082_304_, 1);
        v___x_309_ = lean_apply_2(v_h__2_306_, v_val_308_, lean_box(0));
        return v___x_309_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FlatMap_0__Std_Iter_step__flatMapAfterM_match__5_splitter(
    mut v_00_u03b1_u2082_310_: *mut LeanObject,
    mut v_00_u03b3_311_: *mut LeanObject,
    mut v_m_312_: *mut LeanObject,
    mut v_motive_313_: *mut LeanObject,
    mut v_it_u2082_314_: *mut LeanObject,
    mut v_h__1_315_: *mut LeanObject,
    mut v_h__2_316_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_it_u2082_314_) == 0 {
        let mut v___x_317_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_316_);
        v___x_317_ = lean_apply_1(v_h__1_315_, lean_box(0));
        return v___x_317_;
    } else {
        let mut v_val_318_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_319_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_315_);
        v_val_318_ = lean_ctor_get(v_it_u2082_314_, 0);
        lean_inc(v_val_318_);
        lean_dec_ref_known(v_it_u2082_314_, 1);
        v___x_319_ = lean_apply_2(v_h__2_316_, v_val_318_, lean_box(0));
        return v___x_319_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FlatMap_0__Std_Iter_step__flatMapAfterM_match__1_splitter___redArg(
    mut v_x_320_: *mut LeanObject,
    mut v_h__1_321_: *mut LeanObject,
    mut v_h__2_322_: *mut LeanObject,
    mut v_h__3_323_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_320_) {
        0 => {
            let mut v_it_324_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_325_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_326_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_323_);
            lean_dec(v_h__2_322_);
            v_it_324_ = lean_ctor_get(v_x_320_, 0);
            lean_inc(v_it_324_);
            v_out_325_ = lean_ctor_get(v_x_320_, 1);
            lean_inc(v_out_325_);
            lean_dec_ref_known(v_x_320_, 2);
            v___x_326_ = lean_apply_3(v_h__1_321_, v_it_324_, v_out_325_, lean_box(0));
            return v___x_326_;
        }
        1 => {
            let mut v_it_327_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_328_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_323_);
            lean_dec(v_h__1_321_);
            v_it_327_ = lean_ctor_get(v_x_320_, 0);
            lean_inc(v_it_327_);
            lean_dec_ref_known(v_x_320_, 1);
            v___x_328_ = lean_apply_2(v_h__2_322_, v_it_327_, lean_box(0));
            return v___x_328_;
        }
        _ => {
            let mut v___x_329_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_322_);
            lean_dec(v_h__1_321_);
            v___x_329_ = lean_apply_1(v_h__3_323_, lean_box(0));
            return v___x_329_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FlatMap_0__Std_Iter_step__flatMapAfterM_match__1_splitter(
    mut v_00_u03b1_330_: *mut LeanObject,
    mut v_00_u03b2_331_: *mut LeanObject,
    mut v_inst_332_: *mut LeanObject,
    mut v_it_u2081_333_: *mut LeanObject,
    mut v_motive_334_: *mut LeanObject,
    mut v_x_335_: *mut LeanObject,
    mut v_h__1_336_: *mut LeanObject,
    mut v_h__2_337_: *mut LeanObject,
    mut v_h__3_338_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_335_) {
        0 => {
            let mut v_it_339_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_340_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_341_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_338_);
            lean_dec(v_h__2_337_);
            v_it_339_ = lean_ctor_get(v_x_335_, 0);
            lean_inc(v_it_339_);
            v_out_340_ = lean_ctor_get(v_x_335_, 1);
            lean_inc(v_out_340_);
            lean_dec_ref_known(v_x_335_, 2);
            v___x_341_ = lean_apply_3(v_h__1_336_, v_it_339_, v_out_340_, lean_box(0));
            return v___x_341_;
        }
        1 => {
            let mut v_it_342_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_343_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_338_);
            lean_dec(v_h__1_336_);
            v_it_342_ = lean_ctor_get(v_x_335_, 0);
            lean_inc(v_it_342_);
            lean_dec_ref_known(v_x_335_, 1);
            v___x_343_ = lean_apply_2(v_h__2_337_, v_it_342_, lean_box(0));
            return v___x_343_;
        }
        _ => {
            let mut v___x_344_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_337_);
            lean_dec(v_h__1_336_);
            v___x_344_ = lean_apply_1(v_h__3_338_, lean_box(0));
            return v___x_344_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FlatMap_0__Std_Iter_step__flatMapAfterM_match__1_splitter___boxed(
    mut v_00_u03b1_345_: *mut LeanObject,
    mut v_00_u03b2_346_: *mut LeanObject,
    mut v_inst_347_: *mut LeanObject,
    mut v_it_u2081_348_: *mut LeanObject,
    mut v_motive_349_: *mut LeanObject,
    mut v_x_350_: *mut LeanObject,
    mut v_h__1_351_: *mut LeanObject,
    mut v_h__2_352_: *mut LeanObject,
    mut v_h__3_353_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_354_: *mut LeanObject = core::ptr::null_mut();
    v_res_354_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FlatMap_0__Std_Iter_step__flatMapAfterM_match__1_splitter(v_00_u03b1_345_, v_00_u03b2_346_, v_inst_347_, v_it_u2081_348_, v_motive_349_, v_x_350_, v_h__1_351_, v_h__2_352_, v_h__3_353_);
    lean_dec(v_it_u2081_348_);
    lean_dec(v_inst_347_);
    return v_res_354_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FlatMap_0__Std_Iter_step__flatMapAfterM_match__3_splitter___redArg(
    mut v_x_355_: *mut LeanObject,
    mut v_h__1_356_: *mut LeanObject,
    mut v_h__2_357_: *mut LeanObject,
    mut v_h__3_358_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_355_) {
        0 => {
            let mut v_it_359_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_360_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_361_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_358_);
            lean_dec(v_h__2_357_);
            v_it_359_ = lean_ctor_get(v_x_355_, 0);
            lean_inc(v_it_359_);
            v_out_360_ = lean_ctor_get(v_x_355_, 1);
            lean_inc(v_out_360_);
            lean_dec_ref_known(v_x_355_, 2);
            v___x_361_ = lean_apply_3(v_h__1_356_, v_it_359_, v_out_360_, lean_box(0));
            return v___x_361_;
        }
        1 => {
            let mut v_it_362_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_363_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_358_);
            lean_dec(v_h__1_356_);
            v_it_362_ = lean_ctor_get(v_x_355_, 0);
            lean_inc(v_it_362_);
            lean_dec_ref_known(v_x_355_, 1);
            v___x_363_ = lean_apply_2(v_h__2_357_, v_it_362_, lean_box(0));
            return v___x_363_;
        }
        _ => {
            let mut v___x_364_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_357_);
            lean_dec(v_h__1_356_);
            v___x_364_ = lean_apply_1(v_h__3_358_, lean_box(0));
            return v___x_364_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FlatMap_0__Std_Iter_step__flatMapAfterM_match__3_splitter(
    mut v_00_u03b1_u2082_365_: *mut LeanObject,
    mut v_00_u03b3_366_: *mut LeanObject,
    mut v_m_367_: *mut LeanObject,
    mut v_inst_368_: *mut LeanObject,
    mut v_it_u2082_369_: *mut LeanObject,
    mut v_motive_370_: *mut LeanObject,
    mut v_x_371_: *mut LeanObject,
    mut v_h__1_372_: *mut LeanObject,
    mut v_h__2_373_: *mut LeanObject,
    mut v_h__3_374_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_371_) {
        0 => {
            let mut v_it_375_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_376_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_377_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_374_);
            lean_dec(v_h__2_373_);
            v_it_375_ = lean_ctor_get(v_x_371_, 0);
            lean_inc(v_it_375_);
            v_out_376_ = lean_ctor_get(v_x_371_, 1);
            lean_inc(v_out_376_);
            lean_dec_ref_known(v_x_371_, 2);
            v___x_377_ = lean_apply_3(v_h__1_372_, v_it_375_, v_out_376_, lean_box(0));
            return v___x_377_;
        }
        1 => {
            let mut v_it_378_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_379_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_374_);
            lean_dec(v_h__1_372_);
            v_it_378_ = lean_ctor_get(v_x_371_, 0);
            lean_inc(v_it_378_);
            lean_dec_ref_known(v_x_371_, 1);
            v___x_379_ = lean_apply_2(v_h__2_373_, v_it_378_, lean_box(0));
            return v___x_379_;
        }
        _ => {
            let mut v___x_380_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_373_);
            lean_dec(v_h__1_372_);
            v___x_380_ = lean_apply_1(v_h__3_374_, lean_box(0));
            return v___x_380_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FlatMap_0__Std_Iter_step__flatMapAfterM_match__3_splitter___boxed(
    mut v_00_u03b1_u2082_381_: *mut LeanObject,
    mut v_00_u03b3_382_: *mut LeanObject,
    mut v_m_383_: *mut LeanObject,
    mut v_inst_384_: *mut LeanObject,
    mut v_it_u2082_385_: *mut LeanObject,
    mut v_motive_386_: *mut LeanObject,
    mut v_x_387_: *mut LeanObject,
    mut v_h__1_388_: *mut LeanObject,
    mut v_h__2_389_: *mut LeanObject,
    mut v_h__3_390_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_391_: *mut LeanObject = core::ptr::null_mut();
    v_res_391_ = l___private_Init_Data_Iterators_Lemmas_Combinators_FlatMap_0__Std_Iter_step__flatMapAfterM_match__3_splitter(v_00_u03b1_u2082_381_, v_00_u03b3_382_, v_m_383_, v_inst_384_, v_it_u2082_385_, v_motive_386_, v_x_387_, v_h__1_388_, v_h__2_389_, v_h__3_390_);
    lean_dec(v_it_u2082_385_);
    lean_dec(v_inst_384_);
    return v_res_391_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FlatMap_0__Std_Iter_step__flatMapAfter_match__1_splitter___redArg(
    mut v_it_u2082_392_: *mut LeanObject,
    mut v_h__1_393_: *mut LeanObject,
    mut v_h__2_394_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_it_u2082_392_) == 0 {
        let mut v___x_395_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_396_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_394_);
        v___x_395_ = lean_box(0);
        v___x_396_ = lean_apply_1(v_h__1_393_, v___x_395_);
        return v___x_396_;
    } else {
        let mut v_val_397_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_398_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_393_);
        v_val_397_ = lean_ctor_get(v_it_u2082_392_, 0);
        lean_inc(v_val_397_);
        lean_dec_ref_known(v_it_u2082_392_, 1);
        v___x_398_ = lean_apply_1(v_h__2_394_, v_val_397_);
        return v___x_398_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FlatMap_0__Std_Iter_step__flatMapAfter_match__1_splitter(
    mut v_00_u03b1_u2082_399_: *mut LeanObject,
    mut v_00_u03b3_400_: *mut LeanObject,
    mut v_motive_401_: *mut LeanObject,
    mut v_it_u2082_402_: *mut LeanObject,
    mut v_h__1_403_: *mut LeanObject,
    mut v_h__2_404_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_it_u2082_402_) == 0 {
        let mut v___x_405_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_406_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_404_);
        v___x_405_ = lean_box(0);
        v___x_406_ = lean_apply_1(v_h__1_403_, v___x_405_);
        return v___x_406_;
    } else {
        let mut v_val_407_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_408_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_403_);
        v_val_407_ = lean_ctor_get(v_it_u2082_402_, 0);
        lean_inc(v_val_407_);
        lean_dec_ref_known(v_it_u2082_402_, 1);
        v___x_408_ = lean_apply_1(v_h__2_404_, v_val_407_);
        return v___x_408_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FlatMap_0__Std_Iter_toList__flatMapAfterM_match__1_splitter___redArg(
    mut v_it_u2082_409_: *mut LeanObject,
    mut v_h__1_410_: *mut LeanObject,
    mut v_h__2_411_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_it_u2082_409_) == 0 {
        let mut v___x_412_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_413_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_411_);
        v___x_412_ = lean_box(0);
        v___x_413_ = lean_apply_1(v_h__1_410_, v___x_412_);
        return v___x_413_;
    } else {
        let mut v_val_414_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_415_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_410_);
        v_val_414_ = lean_ctor_get(v_it_u2082_409_, 0);
        lean_inc(v_val_414_);
        lean_dec_ref_known(v_it_u2082_409_, 1);
        v___x_415_ = lean_apply_1(v_h__2_411_, v_val_414_);
        return v___x_415_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_FlatMap_0__Std_Iter_toList__flatMapAfterM_match__1_splitter(
    mut v_00_u03b1_u2082_416_: *mut LeanObject,
    mut v_00_u03b3_417_: *mut LeanObject,
    mut v_m_418_: *mut LeanObject,
    mut v_motive_419_: *mut LeanObject,
    mut v_it_u2082_420_: *mut LeanObject,
    mut v_h__1_421_: *mut LeanObject,
    mut v_h__2_422_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_it_u2082_420_) == 0 {
        let mut v___x_423_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_424_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_422_);
        v___x_423_ = lean_box(0);
        v___x_424_ = lean_apply_1(v_h__1_421_, v___x_423_);
        return v___x_424_;
    } else {
        let mut v_val_425_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_426_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_421_);
        v_val_425_ = lean_ctor_get(v_it_u2082_420_, 0);
        lean_inc(v_val_425_);
        lean_dec_ref_known(v_it_u2082_420_, 1);
        v___x_426_ = lean_apply_1(v_h__2_422_, v_val_425_);
        return v___x_426_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_FlatMap(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Combinators_FlatMap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Combinators_FilterMap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Collect(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_FlatMap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Monadic(builtin);
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
pub unsafe fn meta_initialize_Init_Data_Iterators_Lemmas_Combinators_FlatMap(
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
pub unsafe fn initialize_Init_Data_Iterators_Lemmas_Combinators_FlatMap(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Combinators_FlatMap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Combinators_FilterMap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers_Collect(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_FlatMap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_Monadic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Option_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_FlatMap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_Iterators_Lemmas_Combinators_FlatMap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_Iterators_Lemmas_Combinators_FlatMap(builtin);
}
