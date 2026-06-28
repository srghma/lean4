// Lean compiler output
// Module: Std.Data.Iterators.Lemmas.Combinators.DropWhile
// Imports: Std.Data.Iterators.Combinators.DropWhile Std.Data.Iterators.Lemmas.Combinators.Monadic.DropWhile Init.Data.Iterators.Lemmas.Consumers Init.Data.Bool Init.Data.Iterators.Lemmas.Basic Init.Data.List.TakeDrop
use crate::r#gen::Init::Data::Bool::{
    initialize_Init_Data_Bool, runtime_initialize_Init_Data_Bool,
};
use crate::r#gen::Init::Data::Iterators::Lemmas::Basic::{
    initialize_Init_Data_Iterators_Lemmas_Basic,
    runtime_initialize_Init_Data_Iterators_Lemmas_Basic,
};
use crate::r#gen::Init::Data::Iterators::Lemmas::Consumers::{
    initialize_Init_Data_Iterators_Lemmas_Consumers,
    runtime_initialize_Init_Data_Iterators_Lemmas_Consumers,
};
use crate::r#gen::Init::Data::List::TakeDrop::{
    initialize_Init_Data_List_TakeDrop, runtime_initialize_Init_Data_List_TakeDrop,
};
use crate::r#gen::Std::Data::Iterators::Combinators::DropWhile::{
    initialize_Std_Data_Iterators_Combinators_DropWhile,
    runtime_initialize_Std_Data_Iterators_Combinators_DropWhile,
};
use crate::r#gen::Std::Data::Iterators::Lemmas::Combinators::Monadic::DropWhile::{
    initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_DropWhile,
    runtime_initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_DropWhile,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_apply_1, lean_apply_2, lean_apply_3, lean_box,
    lean_ctor_get, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_obj_tag, lean_unbox,
};
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_IterM_step__intermediateDropWhileWithPostcondition_match__3_splitter___redArg(
    mut v_x_193_: *mut LeanObject,
    mut v_h__1_194_: *mut LeanObject,
    mut v_h__2_195_: *mut LeanObject,
    mut v_h__3_196_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_193_) {
        0 => {
            let mut v_it_197_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_198_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_199_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_196_);
            lean_dec(v_h__2_195_);
            v_it_197_ = lean_ctor_get(v_x_193_, 0);
            lean_inc(v_it_197_);
            v_out_198_ = lean_ctor_get(v_x_193_, 1);
            lean_inc(v_out_198_);
            lean_dec_ref_known(v_x_193_, 2);
            v___x_199_ = lean_apply_3(v_h__1_194_, v_it_197_, v_out_198_, lean_box(0));
            return v___x_199_;
        }
        1 => {
            let mut v_it_200_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_201_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_196_);
            lean_dec(v_h__1_194_);
            v_it_200_ = lean_ctor_get(v_x_193_, 0);
            lean_inc(v_it_200_);
            lean_dec_ref_known(v_x_193_, 1);
            v___x_201_ = lean_apply_2(v_h__2_195_, v_it_200_, lean_box(0));
            return v___x_201_;
        }
        _ => {
            let mut v___x_202_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_195_);
            lean_dec(v_h__1_194_);
            v___x_202_ = lean_apply_1(v_h__3_196_, lean_box(0));
            return v___x_202_;
        }
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_IterM_step__intermediateDropWhileWithPostcondition_match__3_splitter(
    mut v_00_u03b1_203_: *mut LeanObject,
    mut v_m_204_: *mut LeanObject,
    mut v_00_u03b2_205_: *mut LeanObject,
    mut v_inst_206_: *mut LeanObject,
    mut v_it_207_: *mut LeanObject,
    mut v_motive_208_: *mut LeanObject,
    mut v_x_209_: *mut LeanObject,
    mut v_h__1_210_: *mut LeanObject,
    mut v_h__2_211_: *mut LeanObject,
    mut v_h__3_212_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_209_) {
        0 => {
            let mut v_it_213_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_214_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_215_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_212_);
            lean_dec(v_h__2_211_);
            v_it_213_ = lean_ctor_get(v_x_209_, 0);
            lean_inc(v_it_213_);
            v_out_214_ = lean_ctor_get(v_x_209_, 1);
            lean_inc(v_out_214_);
            lean_dec_ref_known(v_x_209_, 2);
            v___x_215_ = lean_apply_3(v_h__1_210_, v_it_213_, v_out_214_, lean_box(0));
            return v___x_215_;
        }
        1 => {
            let mut v_it_216_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_217_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_212_);
            lean_dec(v_h__1_210_);
            v_it_216_ = lean_ctor_get(v_x_209_, 0);
            lean_inc(v_it_216_);
            lean_dec_ref_known(v_x_209_, 1);
            v___x_217_ = lean_apply_2(v_h__2_211_, v_it_216_, lean_box(0));
            return v___x_217_;
        }
        _ => {
            let mut v___x_218_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_211_);
            lean_dec(v_h__1_210_);
            v___x_218_ = lean_apply_1(v_h__3_212_, lean_box(0));
            return v___x_218_;
        }
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_IterM_step__intermediateDropWhileWithPostcondition_match__3_splitter___boxed(
    mut v_00_u03b1_219_: *mut LeanObject,
    mut v_m_220_: *mut LeanObject,
    mut v_00_u03b2_221_: *mut LeanObject,
    mut v_inst_222_: *mut LeanObject,
    mut v_it_223_: *mut LeanObject,
    mut v_motive_224_: *mut LeanObject,
    mut v_x_225_: *mut LeanObject,
    mut v_h__1_226_: *mut LeanObject,
    mut v_h__2_227_: *mut LeanObject,
    mut v_h__3_228_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_229_: *mut LeanObject = core::ptr::null_mut();
    v_res_229_ = l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_IterM_step__intermediateDropWhileWithPostcondition_match__3_splitter(v_00_u03b1_219_, v_m_220_, v_00_u03b2_221_, v_inst_222_, v_it_223_, v_motive_224_, v_x_225_, v_h__1_226_, v_h__2_227_, v_h__3_228_);
    lean_dec(v_it_223_);
    lean_dec(v_inst_222_);
    return v_res_229_;
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_IterM_step__intermediateDropWhile_match__1_splitter___redArg(
    mut v_x_230_: u8,
    mut v_h__1_231_: *mut LeanObject,
    mut v_h__2_232_: *mut LeanObject,
) -> *mut LeanObject {
    if v_x_230_ == 0 {
        let mut v___x_233_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_231_);
        v___x_233_ = lean_apply_1(v_h__2_232_, lean_box(0));
        return v___x_233_;
    } else {
        let mut v___x_234_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_232_);
        v___x_234_ = lean_apply_1(v_h__1_231_, lean_box(0));
        return v___x_234_;
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_IterM_step__intermediateDropWhile_match__1_splitter___redArg___boxed(
    mut v_x_235_: *mut LeanObject,
    mut v_h__1_236_: *mut LeanObject,
    mut v_h__2_237_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_26__boxed_238_: u8 = 0;
    let mut v_res_239_: *mut LeanObject = core::ptr::null_mut();
    v_x_26__boxed_238_ = (lean_unbox(v_x_235_) as u8);
    v_res_239_ = l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_IterM_step__intermediateDropWhile_match__1_splitter___redArg(v_x_26__boxed_238_, v_h__1_236_, v_h__2_237_);
    return v_res_239_;
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_IterM_step__intermediateDropWhile_match__1_splitter(
    mut v_motive_240_: *mut LeanObject,
    mut v_x_241_: u8,
    mut v_h__1_242_: *mut LeanObject,
    mut v_h__2_243_: *mut LeanObject,
) -> *mut LeanObject {
    if v_x_241_ == 0 {
        let mut v___x_244_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_242_);
        v___x_244_ = lean_apply_1(v_h__2_243_, lean_box(0));
        return v___x_244_;
    } else {
        let mut v___x_245_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_243_);
        v___x_245_ = lean_apply_1(v_h__1_242_, lean_box(0));
        return v___x_245_;
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_IterM_step__intermediateDropWhile_match__1_splitter___boxed(
    mut v_motive_246_: *mut LeanObject,
    mut v_x_247_: *mut LeanObject,
    mut v_h__1_248_: *mut LeanObject,
    mut v_h__2_249_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_33__boxed_250_: u8 = 0;
    let mut v_res_251_: *mut LeanObject = core::ptr::null_mut();
    v_x_33__boxed_250_ = (lean_unbox(v_x_247_) as u8);
    v_res_251_ = l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_IterM_step__intermediateDropWhile_match__1_splitter(v_motive_246_, v_x_33__boxed_250_, v_h__1_248_, v_h__2_249_);
    return v_res_251_;
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_step__intermediateDropWhile_match__3_splitter___redArg(
    mut v_x_252_: *mut LeanObject,
    mut v_h__1_253_: *mut LeanObject,
    mut v_h__2_254_: *mut LeanObject,
    mut v_h__3_255_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_252_) {
        0 => {
            let mut v_it_256_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_257_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_258_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_255_);
            lean_dec(v_h__2_254_);
            v_it_256_ = lean_ctor_get(v_x_252_, 0);
            lean_inc(v_it_256_);
            v_out_257_ = lean_ctor_get(v_x_252_, 1);
            lean_inc(v_out_257_);
            lean_dec_ref_known(v_x_252_, 2);
            v___x_258_ = lean_apply_3(v_h__1_253_, v_it_256_, v_out_257_, lean_box(0));
            return v___x_258_;
        }
        1 => {
            let mut v_it_259_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_260_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_255_);
            lean_dec(v_h__1_253_);
            v_it_259_ = lean_ctor_get(v_x_252_, 0);
            lean_inc(v_it_259_);
            lean_dec_ref_known(v_x_252_, 1);
            v___x_260_ = lean_apply_2(v_h__2_254_, v_it_259_, lean_box(0));
            return v___x_260_;
        }
        _ => {
            let mut v___x_261_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_254_);
            lean_dec(v_h__1_253_);
            v___x_261_ = lean_apply_1(v_h__3_255_, lean_box(0));
            return v___x_261_;
        }
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_step__intermediateDropWhile_match__3_splitter(
    mut v_00_u03b1_262_: *mut LeanObject,
    mut v_00_u03b2_263_: *mut LeanObject,
    mut v_inst_264_: *mut LeanObject,
    mut v_it_265_: *mut LeanObject,
    mut v_motive_266_: *mut LeanObject,
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
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_step__intermediateDropWhile_match__3_splitter___boxed(
    mut v_00_u03b1_277_: *mut LeanObject,
    mut v_00_u03b2_278_: *mut LeanObject,
    mut v_inst_279_: *mut LeanObject,
    mut v_it_280_: *mut LeanObject,
    mut v_motive_281_: *mut LeanObject,
    mut v_x_282_: *mut LeanObject,
    mut v_h__1_283_: *mut LeanObject,
    mut v_h__2_284_: *mut LeanObject,
    mut v_h__3_285_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_286_: *mut LeanObject = core::ptr::null_mut();
    v_res_286_ = l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_step__intermediateDropWhile_match__3_splitter(v_00_u03b1_277_, v_00_u03b2_278_, v_inst_279_, v_it_280_, v_motive_281_, v_x_282_, v_h__1_283_, v_h__2_284_, v_h__3_285_);
    lean_dec(v_it_280_);
    lean_dec(v_inst_279_);
    return v_res_286_;
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_step__intermediateDropWhile_match__1_splitter___redArg(
    mut v_x_287_: u8,
    mut v_h__1_288_: *mut LeanObject,
    mut v_h__2_289_: *mut LeanObject,
) -> *mut LeanObject {
    if v_x_287_ == 0 {
        let mut v___x_290_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_288_);
        v___x_290_ = lean_apply_1(v_h__2_289_, lean_box(0));
        return v___x_290_;
    } else {
        let mut v___x_291_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_289_);
        v___x_291_ = lean_apply_1(v_h__1_288_, lean_box(0));
        return v___x_291_;
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_step__intermediateDropWhile_match__1_splitter___redArg___boxed(
    mut v_x_292_: *mut LeanObject,
    mut v_h__1_293_: *mut LeanObject,
    mut v_h__2_294_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_26__boxed_295_: u8 = 0;
    let mut v_res_296_: *mut LeanObject = core::ptr::null_mut();
    v_x_26__boxed_295_ = (lean_unbox(v_x_292_) as u8);
    v_res_296_ = l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_step__intermediateDropWhile_match__1_splitter___redArg(v_x_26__boxed_295_, v_h__1_293_, v_h__2_294_);
    return v_res_296_;
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_step__intermediateDropWhile_match__1_splitter(
    mut v_motive_297_: *mut LeanObject,
    mut v_x_298_: u8,
    mut v_h__1_299_: *mut LeanObject,
    mut v_h__2_300_: *mut LeanObject,
) -> *mut LeanObject {
    if v_x_298_ == 0 {
        let mut v___x_301_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_299_);
        v___x_301_ = lean_apply_1(v_h__2_300_, lean_box(0));
        return v___x_301_;
    } else {
        let mut v___x_302_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_300_);
        v___x_302_ = lean_apply_1(v_h__1_299_, lean_box(0));
        return v___x_302_;
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_step__intermediateDropWhile_match__1_splitter___boxed(
    mut v_motive_303_: *mut LeanObject,
    mut v_x_304_: *mut LeanObject,
    mut v_h__1_305_: *mut LeanObject,
    mut v_h__2_306_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_33__boxed_307_: u8 = 0;
    let mut v_res_308_: *mut LeanObject = core::ptr::null_mut();
    v_x_33__boxed_307_ = (lean_unbox(v_x_304_) as u8);
    v_res_308_ = l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_step__intermediateDropWhile_match__1_splitter(v_motive_303_, v_x_33__boxed_307_, v_h__1_305_, v_h__2_306_);
    return v_res_308_;
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_val__step__intermediateDropWhile_match__1_splitter___redArg(
    mut v_x_309_: u8,
    mut v_h__1_310_: *mut LeanObject,
    mut v_h__2_311_: *mut LeanObject,
) -> *mut LeanObject {
    if v_x_309_ == 0 {
        let mut v___x_312_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_313_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_310_);
        v___x_312_ = lean_box(0);
        v___x_313_ = lean_apply_1(v_h__2_311_, v___x_312_);
        return v___x_313_;
    } else {
        let mut v___x_314_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_315_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_311_);
        v___x_314_ = lean_box(0);
        v___x_315_ = lean_apply_1(v_h__1_310_, v___x_314_);
        return v___x_315_;
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_val__step__intermediateDropWhile_match__1_splitter___redArg___boxed(
    mut v_x_316_: *mut LeanObject,
    mut v_h__1_317_: *mut LeanObject,
    mut v_h__2_318_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_26__boxed_319_: u8 = 0;
    let mut v_res_320_: *mut LeanObject = core::ptr::null_mut();
    v_x_26__boxed_319_ = (lean_unbox(v_x_316_) as u8);
    v_res_320_ = l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_val__step__intermediateDropWhile_match__1_splitter___redArg(v_x_26__boxed_319_, v_h__1_317_, v_h__2_318_);
    return v_res_320_;
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_val__step__intermediateDropWhile_match__1_splitter(
    mut v_motive_321_: *mut LeanObject,
    mut v_x_322_: u8,
    mut v_h__1_323_: *mut LeanObject,
    mut v_h__2_324_: *mut LeanObject,
) -> *mut LeanObject {
    if v_x_322_ == 0 {
        let mut v___x_325_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_326_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_323_);
        v___x_325_ = lean_box(0);
        v___x_326_ = lean_apply_1(v_h__2_324_, v___x_325_);
        return v___x_326_;
    } else {
        let mut v___x_327_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_328_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_324_);
        v___x_327_ = lean_box(0);
        v___x_328_ = lean_apply_1(v_h__1_323_, v___x_327_);
        return v___x_328_;
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_val__step__intermediateDropWhile_match__1_splitter___boxed(
    mut v_motive_329_: *mut LeanObject,
    mut v_x_330_: *mut LeanObject,
    mut v_h__1_331_: *mut LeanObject,
    mut v_h__2_332_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_37__boxed_333_: u8 = 0;
    let mut v_res_334_: *mut LeanObject = core::ptr::null_mut();
    v_x_37__boxed_333_ = (lean_unbox(v_x_330_) as u8);
    v_res_334_ = l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_val__step__intermediateDropWhile_match__1_splitter(v_motive_329_, v_x_37__boxed_333_, v_h__1_331_, v_h__2_332_);
    return v_res_334_;
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_val__step__intermediateDropWhile_match__3_splitter___redArg(
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
            v___x_341_ = lean_apply_2(v_h__1_336_, v_it_339_, v_out_340_);
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
            v___x_343_ = lean_apply_1(v_h__2_337_, v_it_342_);
            return v___x_343_;
        }
        _ => {
            let mut v___x_344_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_345_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_337_);
            lean_dec(v_h__1_336_);
            v___x_344_ = lean_box(0);
            v___x_345_ = lean_apply_1(v_h__3_338_, v___x_344_);
            return v___x_345_;
        }
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_val__step__intermediateDropWhile_match__3_splitter(
    mut v_00_u03b1_346_: *mut LeanObject,
    mut v_00_u03b2_347_: *mut LeanObject,
    mut v_motive_348_: *mut LeanObject,
    mut v_x_349_: *mut LeanObject,
    mut v_h__1_350_: *mut LeanObject,
    mut v_h__2_351_: *mut LeanObject,
    mut v_h__3_352_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_349_) {
        0 => {
            let mut v_it_353_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_354_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_355_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_352_);
            lean_dec(v_h__2_351_);
            v_it_353_ = lean_ctor_get(v_x_349_, 0);
            lean_inc(v_it_353_);
            v_out_354_ = lean_ctor_get(v_x_349_, 1);
            lean_inc(v_out_354_);
            lean_dec_ref_known(v_x_349_, 2);
            v___x_355_ = lean_apply_2(v_h__1_350_, v_it_353_, v_out_354_);
            return v___x_355_;
        }
        1 => {
            let mut v_it_356_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_357_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_352_);
            lean_dec(v_h__1_350_);
            v_it_356_ = lean_ctor_get(v_x_349_, 0);
            lean_inc(v_it_356_);
            lean_dec_ref_known(v_x_349_, 1);
            v___x_357_ = lean_apply_1(v_h__2_351_, v_it_356_);
            return v___x_357_;
        }
        _ => {
            let mut v___x_358_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_359_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_351_);
            lean_dec(v_h__1_350_);
            v___x_358_ = lean_box(0);
            v___x_359_ = lean_apply_1(v_h__3_352_, v___x_358_);
            return v___x_359_;
        }
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_toArray__eq__match__step_match__1_splitter___redArg(
    mut v_x_360_: *mut LeanObject,
    mut v_h__1_361_: *mut LeanObject,
    mut v_h__2_362_: *mut LeanObject,
    mut v_h__3_363_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_360_) {
        0 => {
            let mut v_it_364_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_365_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_366_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_363_);
            lean_dec(v_h__2_362_);
            v_it_364_ = lean_ctor_get(v_x_360_, 0);
            lean_inc(v_it_364_);
            v_out_365_ = lean_ctor_get(v_x_360_, 1);
            lean_inc(v_out_365_);
            lean_dec_ref_known(v_x_360_, 2);
            v___x_366_ = lean_apply_2(v_h__1_361_, v_it_364_, v_out_365_);
            return v___x_366_;
        }
        1 => {
            let mut v_it_367_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_368_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_363_);
            lean_dec(v_h__1_361_);
            v_it_367_ = lean_ctor_get(v_x_360_, 0);
            lean_inc(v_it_367_);
            lean_dec_ref_known(v_x_360_, 1);
            v___x_368_ = lean_apply_1(v_h__2_362_, v_it_367_);
            return v___x_368_;
        }
        _ => {
            let mut v___x_369_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_370_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_362_);
            lean_dec(v_h__1_361_);
            v___x_369_ = lean_box(0);
            v___x_370_ = lean_apply_1(v_h__3_363_, v___x_369_);
            return v___x_370_;
        }
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_toArray__eq__match__step_match__1_splitter(
    mut v_00_u03b1_371_: *mut LeanObject,
    mut v_00_u03b2_372_: *mut LeanObject,
    mut v_motive_373_: *mut LeanObject,
    mut v_x_374_: *mut LeanObject,
    mut v_h__1_375_: *mut LeanObject,
    mut v_h__2_376_: *mut LeanObject,
    mut v_h__3_377_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_374_) {
        0 => {
            let mut v_it_378_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_379_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_380_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_377_);
            lean_dec(v_h__2_376_);
            v_it_378_ = lean_ctor_get(v_x_374_, 0);
            lean_inc(v_it_378_);
            v_out_379_ = lean_ctor_get(v_x_374_, 1);
            lean_inc(v_out_379_);
            lean_dec_ref_known(v_x_374_, 2);
            v___x_380_ = lean_apply_2(v_h__1_375_, v_it_378_, v_out_379_);
            return v___x_380_;
        }
        1 => {
            let mut v_it_381_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_382_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_377_);
            lean_dec(v_h__1_375_);
            v_it_381_ = lean_ctor_get(v_x_374_, 0);
            lean_inc(v_it_381_);
            lean_dec_ref_known(v_x_374_, 1);
            v___x_382_ = lean_apply_1(v_h__2_376_, v_it_381_);
            return v___x_382_;
        }
        _ => {
            let mut v___x_383_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_384_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_376_);
            lean_dec(v_h__1_375_);
            v___x_383_ = lean_box(0);
            v___x_384_ = lean_apply_1(v_h__3_377_, v___x_383_);
            return v___x_384_;
        }
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_Iterators_Lemmas_Combinators_DropWhile(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_Iterators_Combinators_DropWhile(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_DropWhile(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Bool(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_TakeDrop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_Iterators_Lemmas_Combinators_DropWhile(
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
pub unsafe fn initialize_Std_Data_Iterators_Lemmas_Combinators_DropWhile(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_Iterators_Combinators_DropWhile(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_DropWhile(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Consumers(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Bool(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_TakeDrop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Lemmas_Combinators_DropWhile(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Data_Iterators_Lemmas_Combinators_DropWhile(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Data_Iterators_Lemmas_Combinators_DropWhile(builtin);
}
