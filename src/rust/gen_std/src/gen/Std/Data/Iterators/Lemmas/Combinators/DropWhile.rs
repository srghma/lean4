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
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_IterM_step__intermediateDropWhileWithPostcondition_match__3_splitter___redArg(
    mut v_x_193_: *mut leanh::LeanObject,
    mut v_h__1_194_: *mut leanh::LeanObject,
    mut v_h__2_195_: *mut leanh::LeanObject,
    mut v_h__3_196_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_193_) {
        0 => {
            let mut v_it_197_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_198_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_199_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_196_);
            leanh::lean_dec(v_h__2_195_);
            v_it_197_ = leanh::lean_ctor_get(v_x_193_, 0);
            leanh::lean_inc(v_it_197_);
            v_out_198_ = leanh::lean_ctor_get(v_x_193_, 1);
            leanh::lean_inc(v_out_198_);
            leanh::lean_dec_ref_known(v_x_193_, 2);
            v___x_199_ = leanh::lean_apply_3(
                v_h__1_194_,
                v_it_197_,
                v_out_198_,
                leanh::lean_box(0),
            );
            return v___x_199_;
        }
        1 => {
            let mut v_it_200_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_201_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_196_);
            leanh::lean_dec(v_h__1_194_);
            v_it_200_ = leanh::lean_ctor_get(v_x_193_, 0);
            leanh::lean_inc(v_it_200_);
            leanh::lean_dec_ref_known(v_x_193_, 1);
            v___x_201_ =
                leanh::lean_apply_2(v_h__2_195_, v_it_200_, leanh::lean_box(0));
            return v___x_201_;
        }
        _ => {
            let mut v___x_202_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_195_);
            leanh::lean_dec(v_h__1_194_);
            v___x_202_ = leanh::lean_apply_1(v_h__3_196_, leanh::lean_box(0));
            return v___x_202_;
        }
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_IterM_step__intermediateDropWhileWithPostcondition_match__3_splitter(
    mut v_00_u03b1_203_: *mut leanh::LeanObject,
    mut v_m_204_: *mut leanh::LeanObject,
    mut v_00_u03b2_205_: *mut leanh::LeanObject,
    mut v_inst_206_: *mut leanh::LeanObject,
    mut v_it_207_: *mut leanh::LeanObject,
    mut v_motive_208_: *mut leanh::LeanObject,
    mut v_x_209_: *mut leanh::LeanObject,
    mut v_h__1_210_: *mut leanh::LeanObject,
    mut v_h__2_211_: *mut leanh::LeanObject,
    mut v_h__3_212_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_209_) {
        0 => {
            let mut v_it_213_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_214_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_215_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_212_);
            leanh::lean_dec(v_h__2_211_);
            v_it_213_ = leanh::lean_ctor_get(v_x_209_, 0);
            leanh::lean_inc(v_it_213_);
            v_out_214_ = leanh::lean_ctor_get(v_x_209_, 1);
            leanh::lean_inc(v_out_214_);
            leanh::lean_dec_ref_known(v_x_209_, 2);
            v___x_215_ = leanh::lean_apply_3(
                v_h__1_210_,
                v_it_213_,
                v_out_214_,
                leanh::lean_box(0),
            );
            return v___x_215_;
        }
        1 => {
            let mut v_it_216_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_217_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_212_);
            leanh::lean_dec(v_h__1_210_);
            v_it_216_ = leanh::lean_ctor_get(v_x_209_, 0);
            leanh::lean_inc(v_it_216_);
            leanh::lean_dec_ref_known(v_x_209_, 1);
            v___x_217_ =
                leanh::lean_apply_2(v_h__2_211_, v_it_216_, leanh::lean_box(0));
            return v___x_217_;
        }
        _ => {
            let mut v___x_218_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_211_);
            leanh::lean_dec(v_h__1_210_);
            v___x_218_ = leanh::lean_apply_1(v_h__3_212_, leanh::lean_box(0));
            return v___x_218_;
        }
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_IterM_step__intermediateDropWhileWithPostcondition_match__3_splitter___boxed(
    mut v_00_u03b1_219_: *mut leanh::LeanObject,
    mut v_m_220_: *mut leanh::LeanObject,
    mut v_00_u03b2_221_: *mut leanh::LeanObject,
    mut v_inst_222_: *mut leanh::LeanObject,
    mut v_it_223_: *mut leanh::LeanObject,
    mut v_motive_224_: *mut leanh::LeanObject,
    mut v_x_225_: *mut leanh::LeanObject,
    mut v_h__1_226_: *mut leanh::LeanObject,
    mut v_h__2_227_: *mut leanh::LeanObject,
    mut v_h__3_228_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_229_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_229_ = l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_IterM_step__intermediateDropWhileWithPostcondition_match__3_splitter(v_00_u03b1_219_, v_m_220_, v_00_u03b2_221_, v_inst_222_, v_it_223_, v_motive_224_, v_x_225_, v_h__1_226_, v_h__2_227_, v_h__3_228_);
    leanh::lean_dec(v_it_223_);
    leanh::lean_dec(v_inst_222_);
    return v_res_229_;
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_IterM_step__intermediateDropWhile_match__1_splitter___redArg(
    mut v_x_230_: u8,
    mut v_h__1_231_: *mut leanh::LeanObject,
    mut v_h__2_232_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if v_x_230_ == 0 {
        let mut v___x_233_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_231_);
        v___x_233_ = leanh::lean_apply_1(v_h__2_232_, leanh::lean_box(0));
        return v___x_233_;
    } else {
        let mut v___x_234_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_232_);
        v___x_234_ = leanh::lean_apply_1(v_h__1_231_, leanh::lean_box(0));
        return v___x_234_;
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_IterM_step__intermediateDropWhile_match__1_splitter___redArg___boxed(
    mut v_x_235_: *mut leanh::LeanObject,
    mut v_h__1_236_: *mut leanh::LeanObject,
    mut v_h__2_237_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_26__boxed_238_: u8 = 0;
    let mut v_res_239_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_26__boxed_238_ = (leanh::lean_unbox(v_x_235_) as u8);
    v_res_239_ = l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_IterM_step__intermediateDropWhile_match__1_splitter___redArg(v_x_26__boxed_238_, v_h__1_236_, v_h__2_237_);
    return v_res_239_;
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_IterM_step__intermediateDropWhile_match__1_splitter(
    mut v_motive_240_: *mut leanh::LeanObject,
    mut v_x_241_: u8,
    mut v_h__1_242_: *mut leanh::LeanObject,
    mut v_h__2_243_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if v_x_241_ == 0 {
        let mut v___x_244_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_242_);
        v___x_244_ = leanh::lean_apply_1(v_h__2_243_, leanh::lean_box(0));
        return v___x_244_;
    } else {
        let mut v___x_245_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_243_);
        v___x_245_ = leanh::lean_apply_1(v_h__1_242_, leanh::lean_box(0));
        return v___x_245_;
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_IterM_step__intermediateDropWhile_match__1_splitter___boxed(
    mut v_motive_246_: *mut leanh::LeanObject,
    mut v_x_247_: *mut leanh::LeanObject,
    mut v_h__1_248_: *mut leanh::LeanObject,
    mut v_h__2_249_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_33__boxed_250_: u8 = 0;
    let mut v_res_251_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_33__boxed_250_ = (leanh::lean_unbox(v_x_247_) as u8);
    v_res_251_ = l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_IterM_step__intermediateDropWhile_match__1_splitter(v_motive_246_, v_x_33__boxed_250_, v_h__1_248_, v_h__2_249_);
    return v_res_251_;
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_step__intermediateDropWhile_match__3_splitter___redArg(
    mut v_x_252_: *mut leanh::LeanObject,
    mut v_h__1_253_: *mut leanh::LeanObject,
    mut v_h__2_254_: *mut leanh::LeanObject,
    mut v_h__3_255_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_252_) {
        0 => {
            let mut v_it_256_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_257_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_258_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_255_);
            leanh::lean_dec(v_h__2_254_);
            v_it_256_ = leanh::lean_ctor_get(v_x_252_, 0);
            leanh::lean_inc(v_it_256_);
            v_out_257_ = leanh::lean_ctor_get(v_x_252_, 1);
            leanh::lean_inc(v_out_257_);
            leanh::lean_dec_ref_known(v_x_252_, 2);
            v___x_258_ = leanh::lean_apply_3(
                v_h__1_253_,
                v_it_256_,
                v_out_257_,
                leanh::lean_box(0),
            );
            return v___x_258_;
        }
        1 => {
            let mut v_it_259_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_260_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_255_);
            leanh::lean_dec(v_h__1_253_);
            v_it_259_ = leanh::lean_ctor_get(v_x_252_, 0);
            leanh::lean_inc(v_it_259_);
            leanh::lean_dec_ref_known(v_x_252_, 1);
            v___x_260_ =
                leanh::lean_apply_2(v_h__2_254_, v_it_259_, leanh::lean_box(0));
            return v___x_260_;
        }
        _ => {
            let mut v___x_261_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_254_);
            leanh::lean_dec(v_h__1_253_);
            v___x_261_ = leanh::lean_apply_1(v_h__3_255_, leanh::lean_box(0));
            return v___x_261_;
        }
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_step__intermediateDropWhile_match__3_splitter(
    mut v_00_u03b1_262_: *mut leanh::LeanObject,
    mut v_00_u03b2_263_: *mut leanh::LeanObject,
    mut v_inst_264_: *mut leanh::LeanObject,
    mut v_it_265_: *mut leanh::LeanObject,
    mut v_motive_266_: *mut leanh::LeanObject,
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
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_step__intermediateDropWhile_match__3_splitter___boxed(
    mut v_00_u03b1_277_: *mut leanh::LeanObject,
    mut v_00_u03b2_278_: *mut leanh::LeanObject,
    mut v_inst_279_: *mut leanh::LeanObject,
    mut v_it_280_: *mut leanh::LeanObject,
    mut v_motive_281_: *mut leanh::LeanObject,
    mut v_x_282_: *mut leanh::LeanObject,
    mut v_h__1_283_: *mut leanh::LeanObject,
    mut v_h__2_284_: *mut leanh::LeanObject,
    mut v_h__3_285_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_286_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_286_ = l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_step__intermediateDropWhile_match__3_splitter(v_00_u03b1_277_, v_00_u03b2_278_, v_inst_279_, v_it_280_, v_motive_281_, v_x_282_, v_h__1_283_, v_h__2_284_, v_h__3_285_);
    leanh::lean_dec(v_it_280_);
    leanh::lean_dec(v_inst_279_);
    return v_res_286_;
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_step__intermediateDropWhile_match__1_splitter___redArg(
    mut v_x_287_: u8,
    mut v_h__1_288_: *mut leanh::LeanObject,
    mut v_h__2_289_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if v_x_287_ == 0 {
        let mut v___x_290_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_288_);
        v___x_290_ = leanh::lean_apply_1(v_h__2_289_, leanh::lean_box(0));
        return v___x_290_;
    } else {
        let mut v___x_291_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_289_);
        v___x_291_ = leanh::lean_apply_1(v_h__1_288_, leanh::lean_box(0));
        return v___x_291_;
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_step__intermediateDropWhile_match__1_splitter___redArg___boxed(
    mut v_x_292_: *mut leanh::LeanObject,
    mut v_h__1_293_: *mut leanh::LeanObject,
    mut v_h__2_294_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_26__boxed_295_: u8 = 0;
    let mut v_res_296_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_26__boxed_295_ = (leanh::lean_unbox(v_x_292_) as u8);
    v_res_296_ = l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_step__intermediateDropWhile_match__1_splitter___redArg(v_x_26__boxed_295_, v_h__1_293_, v_h__2_294_);
    return v_res_296_;
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_step__intermediateDropWhile_match__1_splitter(
    mut v_motive_297_: *mut leanh::LeanObject,
    mut v_x_298_: u8,
    mut v_h__1_299_: *mut leanh::LeanObject,
    mut v_h__2_300_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if v_x_298_ == 0 {
        let mut v___x_301_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_299_);
        v___x_301_ = leanh::lean_apply_1(v_h__2_300_, leanh::lean_box(0));
        return v___x_301_;
    } else {
        let mut v___x_302_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_300_);
        v___x_302_ = leanh::lean_apply_1(v_h__1_299_, leanh::lean_box(0));
        return v___x_302_;
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_step__intermediateDropWhile_match__1_splitter___boxed(
    mut v_motive_303_: *mut leanh::LeanObject,
    mut v_x_304_: *mut leanh::LeanObject,
    mut v_h__1_305_: *mut leanh::LeanObject,
    mut v_h__2_306_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_33__boxed_307_: u8 = 0;
    let mut v_res_308_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_33__boxed_307_ = (leanh::lean_unbox(v_x_304_) as u8);
    v_res_308_ = l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_step__intermediateDropWhile_match__1_splitter(v_motive_303_, v_x_33__boxed_307_, v_h__1_305_, v_h__2_306_);
    return v_res_308_;
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_val__step__intermediateDropWhile_match__1_splitter___redArg(
    mut v_x_309_: u8,
    mut v_h__1_310_: *mut leanh::LeanObject,
    mut v_h__2_311_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if v_x_309_ == 0 {
        let mut v___x_312_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_313_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_310_);
        v___x_312_ = leanh::lean_box(0);
        v___x_313_ = leanh::lean_apply_1(v_h__2_311_, v___x_312_);
        return v___x_313_;
    } else {
        let mut v___x_314_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_315_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_311_);
        v___x_314_ = leanh::lean_box(0);
        v___x_315_ = leanh::lean_apply_1(v_h__1_310_, v___x_314_);
        return v___x_315_;
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_val__step__intermediateDropWhile_match__1_splitter___redArg___boxed(
    mut v_x_316_: *mut leanh::LeanObject,
    mut v_h__1_317_: *mut leanh::LeanObject,
    mut v_h__2_318_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_26__boxed_319_: u8 = 0;
    let mut v_res_320_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_26__boxed_319_ = (leanh::lean_unbox(v_x_316_) as u8);
    v_res_320_ = l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_val__step__intermediateDropWhile_match__1_splitter___redArg(v_x_26__boxed_319_, v_h__1_317_, v_h__2_318_);
    return v_res_320_;
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_val__step__intermediateDropWhile_match__1_splitter(
    mut v_motive_321_: *mut leanh::LeanObject,
    mut v_x_322_: u8,
    mut v_h__1_323_: *mut leanh::LeanObject,
    mut v_h__2_324_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if v_x_322_ == 0 {
        let mut v___x_325_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_326_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_323_);
        v___x_325_ = leanh::lean_box(0);
        v___x_326_ = leanh::lean_apply_1(v_h__2_324_, v___x_325_);
        return v___x_326_;
    } else {
        let mut v___x_327_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_328_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_324_);
        v___x_327_ = leanh::lean_box(0);
        v___x_328_ = leanh::lean_apply_1(v_h__1_323_, v___x_327_);
        return v___x_328_;
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_val__step__intermediateDropWhile_match__1_splitter___boxed(
    mut v_motive_329_: *mut leanh::LeanObject,
    mut v_x_330_: *mut leanh::LeanObject,
    mut v_h__1_331_: *mut leanh::LeanObject,
    mut v_h__2_332_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_37__boxed_333_: u8 = 0;
    let mut v_res_334_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_37__boxed_333_ = (leanh::lean_unbox(v_x_330_) as u8);
    v_res_334_ = l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_val__step__intermediateDropWhile_match__1_splitter(v_motive_329_, v_x_37__boxed_333_, v_h__1_331_, v_h__2_332_);
    return v_res_334_;
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_val__step__intermediateDropWhile_match__3_splitter___redArg(
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
            v___x_341_ = leanh::lean_apply_2(v_h__1_336_, v_it_339_, v_out_340_);
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
            v___x_343_ = leanh::lean_apply_1(v_h__2_337_, v_it_342_);
            return v___x_343_;
        }
        _ => {
            let mut v___x_344_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_345_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_337_);
            leanh::lean_dec(v_h__1_336_);
            v___x_344_ = leanh::lean_box(0);
            v___x_345_ = leanh::lean_apply_1(v_h__3_338_, v___x_344_);
            return v___x_345_;
        }
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_val__step__intermediateDropWhile_match__3_splitter(
    mut v_00_u03b1_346_: *mut leanh::LeanObject,
    mut v_00_u03b2_347_: *mut leanh::LeanObject,
    mut v_motive_348_: *mut leanh::LeanObject,
    mut v_x_349_: *mut leanh::LeanObject,
    mut v_h__1_350_: *mut leanh::LeanObject,
    mut v_h__2_351_: *mut leanh::LeanObject,
    mut v_h__3_352_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_349_) {
        0 => {
            let mut v_it_353_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_354_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_355_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_352_);
            leanh::lean_dec(v_h__2_351_);
            v_it_353_ = leanh::lean_ctor_get(v_x_349_, 0);
            leanh::lean_inc(v_it_353_);
            v_out_354_ = leanh::lean_ctor_get(v_x_349_, 1);
            leanh::lean_inc(v_out_354_);
            leanh::lean_dec_ref_known(v_x_349_, 2);
            v___x_355_ = leanh::lean_apply_2(v_h__1_350_, v_it_353_, v_out_354_);
            return v___x_355_;
        }
        1 => {
            let mut v_it_356_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_357_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_352_);
            leanh::lean_dec(v_h__1_350_);
            v_it_356_ = leanh::lean_ctor_get(v_x_349_, 0);
            leanh::lean_inc(v_it_356_);
            leanh::lean_dec_ref_known(v_x_349_, 1);
            v___x_357_ = leanh::lean_apply_1(v_h__2_351_, v_it_356_);
            return v___x_357_;
        }
        _ => {
            let mut v___x_358_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_359_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_351_);
            leanh::lean_dec(v_h__1_350_);
            v___x_358_ = leanh::lean_box(0);
            v___x_359_ = leanh::lean_apply_1(v_h__3_352_, v___x_358_);
            return v___x_359_;
        }
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_toArray__eq__match__step_match__1_splitter___redArg(
    mut v_x_360_: *mut leanh::LeanObject,
    mut v_h__1_361_: *mut leanh::LeanObject,
    mut v_h__2_362_: *mut leanh::LeanObject,
    mut v_h__3_363_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_360_) {
        0 => {
            let mut v_it_364_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_365_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_366_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_363_);
            leanh::lean_dec(v_h__2_362_);
            v_it_364_ = leanh::lean_ctor_get(v_x_360_, 0);
            leanh::lean_inc(v_it_364_);
            v_out_365_ = leanh::lean_ctor_get(v_x_360_, 1);
            leanh::lean_inc(v_out_365_);
            leanh::lean_dec_ref_known(v_x_360_, 2);
            v___x_366_ = leanh::lean_apply_2(v_h__1_361_, v_it_364_, v_out_365_);
            return v___x_366_;
        }
        1 => {
            let mut v_it_367_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_368_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_363_);
            leanh::lean_dec(v_h__1_361_);
            v_it_367_ = leanh::lean_ctor_get(v_x_360_, 0);
            leanh::lean_inc(v_it_367_);
            leanh::lean_dec_ref_known(v_x_360_, 1);
            v___x_368_ = leanh::lean_apply_1(v_h__2_362_, v_it_367_);
            return v___x_368_;
        }
        _ => {
            let mut v___x_369_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_370_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_362_);
            leanh::lean_dec(v_h__1_361_);
            v___x_369_ = leanh::lean_box(0);
            v___x_370_ = leanh::lean_apply_1(v_h__3_363_, v___x_369_);
            return v___x_370_;
        }
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_toArray__eq__match__step_match__1_splitter(
    mut v_00_u03b1_371_: *mut leanh::LeanObject,
    mut v_00_u03b2_372_: *mut leanh::LeanObject,
    mut v_motive_373_: *mut leanh::LeanObject,
    mut v_x_374_: *mut leanh::LeanObject,
    mut v_h__1_375_: *mut leanh::LeanObject,
    mut v_h__2_376_: *mut leanh::LeanObject,
    mut v_h__3_377_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_374_) {
        0 => {
            let mut v_it_378_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_379_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_380_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_377_);
            leanh::lean_dec(v_h__2_376_);
            v_it_378_ = leanh::lean_ctor_get(v_x_374_, 0);
            leanh::lean_inc(v_it_378_);
            v_out_379_ = leanh::lean_ctor_get(v_x_374_, 1);
            leanh::lean_inc(v_out_379_);
            leanh::lean_dec_ref_known(v_x_374_, 2);
            v___x_380_ = leanh::lean_apply_2(v_h__1_375_, v_it_378_, v_out_379_);
            return v___x_380_;
        }
        1 => {
            let mut v_it_381_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_382_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_377_);
            leanh::lean_dec(v_h__1_375_);
            v_it_381_ = leanh::lean_ctor_get(v_x_374_, 0);
            leanh::lean_inc(v_it_381_);
            leanh::lean_dec_ref_known(v_x_374_, 1);
            v___x_382_ = leanh::lean_apply_1(v_h__2_376_, v_it_381_);
            return v___x_382_;
        }
        _ => {
            let mut v___x_383_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_384_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_376_);
            leanh::lean_dec(v_h__1_375_);
            v___x_383_ = leanh::lean_box(0);
            v___x_384_ = leanh::lean_apply_1(v_h__3_377_, v___x_383_);
            return v___x_384_;
        }
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_Iterators_Lemmas_Combinators_DropWhile(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_Iterators_Combinators_DropWhile(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_DropWhile(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Bool(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_TakeDrop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_Iterators_Lemmas_Combinators_DropWhile(
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
pub unsafe fn initialize_Std_Data_Iterators_Lemmas_Combinators_DropWhile(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_Iterators_Combinators_DropWhile(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_DropWhile(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Consumers(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Bool(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_TakeDrop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Lemmas_Combinators_DropWhile(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Data_Iterators_Lemmas_Combinators_DropWhile(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Data_Iterators_Lemmas_Combinators_DropWhile(builtin);
}