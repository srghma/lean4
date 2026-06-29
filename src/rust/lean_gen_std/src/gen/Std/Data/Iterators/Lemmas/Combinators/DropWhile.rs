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
    mut v_x_193_: *mut crate::leanh::LeanObject,
    mut v_h__1_194_: *mut crate::leanh::LeanObject,
    mut v_h__2_195_: *mut crate::leanh::LeanObject,
    mut v_h__3_196_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_193_) {
        0 => {
            let mut v_it_197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_196_);
            crate::leanh::lean_dec(v_h__2_195_);
            v_it_197_ = crate::leanh::lean_ctor_get(v_x_193_, 0);
            crate::leanh::lean_inc(v_it_197_);
            v_out_198_ = crate::leanh::lean_ctor_get(v_x_193_, 1);
            crate::leanh::lean_inc(v_out_198_);
            crate::leanh::lean_dec_ref_known(v_x_193_, 2);
            v___x_199_ = crate::leanh::lean_apply_3(
                v_h__1_194_,
                v_it_197_,
                v_out_198_,
                crate::leanh::lean_box(0),
            );
            return v___x_199_;
        }
        1 => {
            let mut v_it_200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_196_);
            crate::leanh::lean_dec(v_h__1_194_);
            v_it_200_ = crate::leanh::lean_ctor_get(v_x_193_, 0);
            crate::leanh::lean_inc(v_it_200_);
            crate::leanh::lean_dec_ref_known(v_x_193_, 1);
            v___x_201_ =
                crate::leanh::lean_apply_2(v_h__2_195_, v_it_200_, crate::leanh::lean_box(0));
            return v___x_201_;
        }
        _ => {
            let mut v___x_202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_195_);
            crate::leanh::lean_dec(v_h__1_194_);
            v___x_202_ = crate::leanh::lean_apply_1(v_h__3_196_, crate::leanh::lean_box(0));
            return v___x_202_;
        }
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_IterM_step__intermediateDropWhileWithPostcondition_match__3_splitter(
    mut v_00_u03b1_203_: *mut crate::leanh::LeanObject,
    mut v_m_204_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_205_: *mut crate::leanh::LeanObject,
    mut v_inst_206_: *mut crate::leanh::LeanObject,
    mut v_it_207_: *mut crate::leanh::LeanObject,
    mut v_motive_208_: *mut crate::leanh::LeanObject,
    mut v_x_209_: *mut crate::leanh::LeanObject,
    mut v_h__1_210_: *mut crate::leanh::LeanObject,
    mut v_h__2_211_: *mut crate::leanh::LeanObject,
    mut v_h__3_212_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_209_) {
        0 => {
            let mut v_it_213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_212_);
            crate::leanh::lean_dec(v_h__2_211_);
            v_it_213_ = crate::leanh::lean_ctor_get(v_x_209_, 0);
            crate::leanh::lean_inc(v_it_213_);
            v_out_214_ = crate::leanh::lean_ctor_get(v_x_209_, 1);
            crate::leanh::lean_inc(v_out_214_);
            crate::leanh::lean_dec_ref_known(v_x_209_, 2);
            v___x_215_ = crate::leanh::lean_apply_3(
                v_h__1_210_,
                v_it_213_,
                v_out_214_,
                crate::leanh::lean_box(0),
            );
            return v___x_215_;
        }
        1 => {
            let mut v_it_216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_212_);
            crate::leanh::lean_dec(v_h__1_210_);
            v_it_216_ = crate::leanh::lean_ctor_get(v_x_209_, 0);
            crate::leanh::lean_inc(v_it_216_);
            crate::leanh::lean_dec_ref_known(v_x_209_, 1);
            v___x_217_ =
                crate::leanh::lean_apply_2(v_h__2_211_, v_it_216_, crate::leanh::lean_box(0));
            return v___x_217_;
        }
        _ => {
            let mut v___x_218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_211_);
            crate::leanh::lean_dec(v_h__1_210_);
            v___x_218_ = crate::leanh::lean_apply_1(v_h__3_212_, crate::leanh::lean_box(0));
            return v___x_218_;
        }
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_IterM_step__intermediateDropWhileWithPostcondition_match__3_splitter___boxed(
    mut v_00_u03b1_219_: *mut crate::leanh::LeanObject,
    mut v_m_220_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_221_: *mut crate::leanh::LeanObject,
    mut v_inst_222_: *mut crate::leanh::LeanObject,
    mut v_it_223_: *mut crate::leanh::LeanObject,
    mut v_motive_224_: *mut crate::leanh::LeanObject,
    mut v_x_225_: *mut crate::leanh::LeanObject,
    mut v_h__1_226_: *mut crate::leanh::LeanObject,
    mut v_h__2_227_: *mut crate::leanh::LeanObject,
    mut v_h__3_228_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_229_ = l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_IterM_step__intermediateDropWhileWithPostcondition_match__3_splitter(v_00_u03b1_219_, v_m_220_, v_00_u03b2_221_, v_inst_222_, v_it_223_, v_motive_224_, v_x_225_, v_h__1_226_, v_h__2_227_, v_h__3_228_);
    crate::leanh::lean_dec(v_it_223_);
    crate::leanh::lean_dec(v_inst_222_);
    return v_res_229_;
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_IterM_step__intermediateDropWhile_match__1_splitter___redArg(
    mut v_x_230_: u8,
    mut v_h__1_231_: *mut crate::leanh::LeanObject,
    mut v_h__2_232_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if v_x_230_ == 0 {
        let mut v___x_233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_231_);
        v___x_233_ = crate::leanh::lean_apply_1(v_h__2_232_, crate::leanh::lean_box(0));
        return v___x_233_;
    } else {
        let mut v___x_234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_232_);
        v___x_234_ = crate::leanh::lean_apply_1(v_h__1_231_, crate::leanh::lean_box(0));
        return v___x_234_;
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_IterM_step__intermediateDropWhile_match__1_splitter___redArg___boxed(
    mut v_x_235_: *mut crate::leanh::LeanObject,
    mut v_h__1_236_: *mut crate::leanh::LeanObject,
    mut v_h__2_237_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_26__boxed_238_: u8 = 0;
    let mut v_res_239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_26__boxed_238_ = (crate::leanh::lean_unbox(v_x_235_) as u8);
    v_res_239_ = l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_IterM_step__intermediateDropWhile_match__1_splitter___redArg(v_x_26__boxed_238_, v_h__1_236_, v_h__2_237_);
    return v_res_239_;
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_IterM_step__intermediateDropWhile_match__1_splitter(
    mut v_motive_240_: *mut crate::leanh::LeanObject,
    mut v_x_241_: u8,
    mut v_h__1_242_: *mut crate::leanh::LeanObject,
    mut v_h__2_243_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if v_x_241_ == 0 {
        let mut v___x_244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_242_);
        v___x_244_ = crate::leanh::lean_apply_1(v_h__2_243_, crate::leanh::lean_box(0));
        return v___x_244_;
    } else {
        let mut v___x_245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_243_);
        v___x_245_ = crate::leanh::lean_apply_1(v_h__1_242_, crate::leanh::lean_box(0));
        return v___x_245_;
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_IterM_step__intermediateDropWhile_match__1_splitter___boxed(
    mut v_motive_246_: *mut crate::leanh::LeanObject,
    mut v_x_247_: *mut crate::leanh::LeanObject,
    mut v_h__1_248_: *mut crate::leanh::LeanObject,
    mut v_h__2_249_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_33__boxed_250_: u8 = 0;
    let mut v_res_251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_33__boxed_250_ = (crate::leanh::lean_unbox(v_x_247_) as u8);
    v_res_251_ = l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_IterM_step__intermediateDropWhile_match__1_splitter(v_motive_246_, v_x_33__boxed_250_, v_h__1_248_, v_h__2_249_);
    return v_res_251_;
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_step__intermediateDropWhile_match__3_splitter___redArg(
    mut v_x_252_: *mut crate::leanh::LeanObject,
    mut v_h__1_253_: *mut crate::leanh::LeanObject,
    mut v_h__2_254_: *mut crate::leanh::LeanObject,
    mut v_h__3_255_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_252_) {
        0 => {
            let mut v_it_256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_255_);
            crate::leanh::lean_dec(v_h__2_254_);
            v_it_256_ = crate::leanh::lean_ctor_get(v_x_252_, 0);
            crate::leanh::lean_inc(v_it_256_);
            v_out_257_ = crate::leanh::lean_ctor_get(v_x_252_, 1);
            crate::leanh::lean_inc(v_out_257_);
            crate::leanh::lean_dec_ref_known(v_x_252_, 2);
            v___x_258_ = crate::leanh::lean_apply_3(
                v_h__1_253_,
                v_it_256_,
                v_out_257_,
                crate::leanh::lean_box(0),
            );
            return v___x_258_;
        }
        1 => {
            let mut v_it_259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_255_);
            crate::leanh::lean_dec(v_h__1_253_);
            v_it_259_ = crate::leanh::lean_ctor_get(v_x_252_, 0);
            crate::leanh::lean_inc(v_it_259_);
            crate::leanh::lean_dec_ref_known(v_x_252_, 1);
            v___x_260_ =
                crate::leanh::lean_apply_2(v_h__2_254_, v_it_259_, crate::leanh::lean_box(0));
            return v___x_260_;
        }
        _ => {
            let mut v___x_261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_254_);
            crate::leanh::lean_dec(v_h__1_253_);
            v___x_261_ = crate::leanh::lean_apply_1(v_h__3_255_, crate::leanh::lean_box(0));
            return v___x_261_;
        }
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_step__intermediateDropWhile_match__3_splitter(
    mut v_00_u03b1_262_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_263_: *mut crate::leanh::LeanObject,
    mut v_inst_264_: *mut crate::leanh::LeanObject,
    mut v_it_265_: *mut crate::leanh::LeanObject,
    mut v_motive_266_: *mut crate::leanh::LeanObject,
    mut v_x_267_: *mut crate::leanh::LeanObject,
    mut v_h__1_268_: *mut crate::leanh::LeanObject,
    mut v_h__2_269_: *mut crate::leanh::LeanObject,
    mut v_h__3_270_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_267_) {
        0 => {
            let mut v_it_271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_270_);
            crate::leanh::lean_dec(v_h__2_269_);
            v_it_271_ = crate::leanh::lean_ctor_get(v_x_267_, 0);
            crate::leanh::lean_inc(v_it_271_);
            v_out_272_ = crate::leanh::lean_ctor_get(v_x_267_, 1);
            crate::leanh::lean_inc(v_out_272_);
            crate::leanh::lean_dec_ref_known(v_x_267_, 2);
            v___x_273_ = crate::leanh::lean_apply_3(
                v_h__1_268_,
                v_it_271_,
                v_out_272_,
                crate::leanh::lean_box(0),
            );
            return v___x_273_;
        }
        1 => {
            let mut v_it_274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_270_);
            crate::leanh::lean_dec(v_h__1_268_);
            v_it_274_ = crate::leanh::lean_ctor_get(v_x_267_, 0);
            crate::leanh::lean_inc(v_it_274_);
            crate::leanh::lean_dec_ref_known(v_x_267_, 1);
            v___x_275_ =
                crate::leanh::lean_apply_2(v_h__2_269_, v_it_274_, crate::leanh::lean_box(0));
            return v___x_275_;
        }
        _ => {
            let mut v___x_276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_269_);
            crate::leanh::lean_dec(v_h__1_268_);
            v___x_276_ = crate::leanh::lean_apply_1(v_h__3_270_, crate::leanh::lean_box(0));
            return v___x_276_;
        }
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_step__intermediateDropWhile_match__3_splitter___boxed(
    mut v_00_u03b1_277_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_278_: *mut crate::leanh::LeanObject,
    mut v_inst_279_: *mut crate::leanh::LeanObject,
    mut v_it_280_: *mut crate::leanh::LeanObject,
    mut v_motive_281_: *mut crate::leanh::LeanObject,
    mut v_x_282_: *mut crate::leanh::LeanObject,
    mut v_h__1_283_: *mut crate::leanh::LeanObject,
    mut v_h__2_284_: *mut crate::leanh::LeanObject,
    mut v_h__3_285_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_286_ = l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_step__intermediateDropWhile_match__3_splitter(v_00_u03b1_277_, v_00_u03b2_278_, v_inst_279_, v_it_280_, v_motive_281_, v_x_282_, v_h__1_283_, v_h__2_284_, v_h__3_285_);
    crate::leanh::lean_dec(v_it_280_);
    crate::leanh::lean_dec(v_inst_279_);
    return v_res_286_;
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_step__intermediateDropWhile_match__1_splitter___redArg(
    mut v_x_287_: u8,
    mut v_h__1_288_: *mut crate::leanh::LeanObject,
    mut v_h__2_289_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if v_x_287_ == 0 {
        let mut v___x_290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_288_);
        v___x_290_ = crate::leanh::lean_apply_1(v_h__2_289_, crate::leanh::lean_box(0));
        return v___x_290_;
    } else {
        let mut v___x_291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_289_);
        v___x_291_ = crate::leanh::lean_apply_1(v_h__1_288_, crate::leanh::lean_box(0));
        return v___x_291_;
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_step__intermediateDropWhile_match__1_splitter___redArg___boxed(
    mut v_x_292_: *mut crate::leanh::LeanObject,
    mut v_h__1_293_: *mut crate::leanh::LeanObject,
    mut v_h__2_294_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_26__boxed_295_: u8 = 0;
    let mut v_res_296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_26__boxed_295_ = (crate::leanh::lean_unbox(v_x_292_) as u8);
    v_res_296_ = l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_step__intermediateDropWhile_match__1_splitter___redArg(v_x_26__boxed_295_, v_h__1_293_, v_h__2_294_);
    return v_res_296_;
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_step__intermediateDropWhile_match__1_splitter(
    mut v_motive_297_: *mut crate::leanh::LeanObject,
    mut v_x_298_: u8,
    mut v_h__1_299_: *mut crate::leanh::LeanObject,
    mut v_h__2_300_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if v_x_298_ == 0 {
        let mut v___x_301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_299_);
        v___x_301_ = crate::leanh::lean_apply_1(v_h__2_300_, crate::leanh::lean_box(0));
        return v___x_301_;
    } else {
        let mut v___x_302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_300_);
        v___x_302_ = crate::leanh::lean_apply_1(v_h__1_299_, crate::leanh::lean_box(0));
        return v___x_302_;
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_step__intermediateDropWhile_match__1_splitter___boxed(
    mut v_motive_303_: *mut crate::leanh::LeanObject,
    mut v_x_304_: *mut crate::leanh::LeanObject,
    mut v_h__1_305_: *mut crate::leanh::LeanObject,
    mut v_h__2_306_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_33__boxed_307_: u8 = 0;
    let mut v_res_308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_33__boxed_307_ = (crate::leanh::lean_unbox(v_x_304_) as u8);
    v_res_308_ = l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_step__intermediateDropWhile_match__1_splitter(v_motive_303_, v_x_33__boxed_307_, v_h__1_305_, v_h__2_306_);
    return v_res_308_;
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_val__step__intermediateDropWhile_match__1_splitter___redArg(
    mut v_x_309_: u8,
    mut v_h__1_310_: *mut crate::leanh::LeanObject,
    mut v_h__2_311_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if v_x_309_ == 0 {
        let mut v___x_312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_310_);
        v___x_312_ = crate::leanh::lean_box(0);
        v___x_313_ = crate::leanh::lean_apply_1(v_h__2_311_, v___x_312_);
        return v___x_313_;
    } else {
        let mut v___x_314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_311_);
        v___x_314_ = crate::leanh::lean_box(0);
        v___x_315_ = crate::leanh::lean_apply_1(v_h__1_310_, v___x_314_);
        return v___x_315_;
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_val__step__intermediateDropWhile_match__1_splitter___redArg___boxed(
    mut v_x_316_: *mut crate::leanh::LeanObject,
    mut v_h__1_317_: *mut crate::leanh::LeanObject,
    mut v_h__2_318_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_26__boxed_319_: u8 = 0;
    let mut v_res_320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_26__boxed_319_ = (crate::leanh::lean_unbox(v_x_316_) as u8);
    v_res_320_ = l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_val__step__intermediateDropWhile_match__1_splitter___redArg(v_x_26__boxed_319_, v_h__1_317_, v_h__2_318_);
    return v_res_320_;
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_val__step__intermediateDropWhile_match__1_splitter(
    mut v_motive_321_: *mut crate::leanh::LeanObject,
    mut v_x_322_: u8,
    mut v_h__1_323_: *mut crate::leanh::LeanObject,
    mut v_h__2_324_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if v_x_322_ == 0 {
        let mut v___x_325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_323_);
        v___x_325_ = crate::leanh::lean_box(0);
        v___x_326_ = crate::leanh::lean_apply_1(v_h__2_324_, v___x_325_);
        return v___x_326_;
    } else {
        let mut v___x_327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_324_);
        v___x_327_ = crate::leanh::lean_box(0);
        v___x_328_ = crate::leanh::lean_apply_1(v_h__1_323_, v___x_327_);
        return v___x_328_;
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_val__step__intermediateDropWhile_match__1_splitter___boxed(
    mut v_motive_329_: *mut crate::leanh::LeanObject,
    mut v_x_330_: *mut crate::leanh::LeanObject,
    mut v_h__1_331_: *mut crate::leanh::LeanObject,
    mut v_h__2_332_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_37__boxed_333_: u8 = 0;
    let mut v_res_334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_37__boxed_333_ = (crate::leanh::lean_unbox(v_x_330_) as u8);
    v_res_334_ = l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_val__step__intermediateDropWhile_match__1_splitter(v_motive_329_, v_x_37__boxed_333_, v_h__1_331_, v_h__2_332_);
    return v_res_334_;
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_val__step__intermediateDropWhile_match__3_splitter___redArg(
    mut v_x_335_: *mut crate::leanh::LeanObject,
    mut v_h__1_336_: *mut crate::leanh::LeanObject,
    mut v_h__2_337_: *mut crate::leanh::LeanObject,
    mut v_h__3_338_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_335_) {
        0 => {
            let mut v_it_339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_338_);
            crate::leanh::lean_dec(v_h__2_337_);
            v_it_339_ = crate::leanh::lean_ctor_get(v_x_335_, 0);
            crate::leanh::lean_inc(v_it_339_);
            v_out_340_ = crate::leanh::lean_ctor_get(v_x_335_, 1);
            crate::leanh::lean_inc(v_out_340_);
            crate::leanh::lean_dec_ref_known(v_x_335_, 2);
            v___x_341_ = crate::leanh::lean_apply_2(v_h__1_336_, v_it_339_, v_out_340_);
            return v___x_341_;
        }
        1 => {
            let mut v_it_342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_338_);
            crate::leanh::lean_dec(v_h__1_336_);
            v_it_342_ = crate::leanh::lean_ctor_get(v_x_335_, 0);
            crate::leanh::lean_inc(v_it_342_);
            crate::leanh::lean_dec_ref_known(v_x_335_, 1);
            v___x_343_ = crate::leanh::lean_apply_1(v_h__2_337_, v_it_342_);
            return v___x_343_;
        }
        _ => {
            let mut v___x_344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_337_);
            crate::leanh::lean_dec(v_h__1_336_);
            v___x_344_ = crate::leanh::lean_box(0);
            v___x_345_ = crate::leanh::lean_apply_1(v_h__3_338_, v___x_344_);
            return v___x_345_;
        }
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_val__step__intermediateDropWhile_match__3_splitter(
    mut v_00_u03b1_346_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_347_: *mut crate::leanh::LeanObject,
    mut v_motive_348_: *mut crate::leanh::LeanObject,
    mut v_x_349_: *mut crate::leanh::LeanObject,
    mut v_h__1_350_: *mut crate::leanh::LeanObject,
    mut v_h__2_351_: *mut crate::leanh::LeanObject,
    mut v_h__3_352_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_349_) {
        0 => {
            let mut v_it_353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_352_);
            crate::leanh::lean_dec(v_h__2_351_);
            v_it_353_ = crate::leanh::lean_ctor_get(v_x_349_, 0);
            crate::leanh::lean_inc(v_it_353_);
            v_out_354_ = crate::leanh::lean_ctor_get(v_x_349_, 1);
            crate::leanh::lean_inc(v_out_354_);
            crate::leanh::lean_dec_ref_known(v_x_349_, 2);
            v___x_355_ = crate::leanh::lean_apply_2(v_h__1_350_, v_it_353_, v_out_354_);
            return v___x_355_;
        }
        1 => {
            let mut v_it_356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_352_);
            crate::leanh::lean_dec(v_h__1_350_);
            v_it_356_ = crate::leanh::lean_ctor_get(v_x_349_, 0);
            crate::leanh::lean_inc(v_it_356_);
            crate::leanh::lean_dec_ref_known(v_x_349_, 1);
            v___x_357_ = crate::leanh::lean_apply_1(v_h__2_351_, v_it_356_);
            return v___x_357_;
        }
        _ => {
            let mut v___x_358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_351_);
            crate::leanh::lean_dec(v_h__1_350_);
            v___x_358_ = crate::leanh::lean_box(0);
            v___x_359_ = crate::leanh::lean_apply_1(v_h__3_352_, v___x_358_);
            return v___x_359_;
        }
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_toArray__eq__match__step_match__1_splitter___redArg(
    mut v_x_360_: *mut crate::leanh::LeanObject,
    mut v_h__1_361_: *mut crate::leanh::LeanObject,
    mut v_h__2_362_: *mut crate::leanh::LeanObject,
    mut v_h__3_363_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_360_) {
        0 => {
            let mut v_it_364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_363_);
            crate::leanh::lean_dec(v_h__2_362_);
            v_it_364_ = crate::leanh::lean_ctor_get(v_x_360_, 0);
            crate::leanh::lean_inc(v_it_364_);
            v_out_365_ = crate::leanh::lean_ctor_get(v_x_360_, 1);
            crate::leanh::lean_inc(v_out_365_);
            crate::leanh::lean_dec_ref_known(v_x_360_, 2);
            v___x_366_ = crate::leanh::lean_apply_2(v_h__1_361_, v_it_364_, v_out_365_);
            return v___x_366_;
        }
        1 => {
            let mut v_it_367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_363_);
            crate::leanh::lean_dec(v_h__1_361_);
            v_it_367_ = crate::leanh::lean_ctor_get(v_x_360_, 0);
            crate::leanh::lean_inc(v_it_367_);
            crate::leanh::lean_dec_ref_known(v_x_360_, 1);
            v___x_368_ = crate::leanh::lean_apply_1(v_h__2_362_, v_it_367_);
            return v___x_368_;
        }
        _ => {
            let mut v___x_369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_362_);
            crate::leanh::lean_dec(v_h__1_361_);
            v___x_369_ = crate::leanh::lean_box(0);
            v___x_370_ = crate::leanh::lean_apply_1(v_h__3_363_, v___x_369_);
            return v___x_370_;
        }
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_DropWhile_0__Std_Iter_toArray__eq__match__step_match__1_splitter(
    mut v_00_u03b1_371_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_372_: *mut crate::leanh::LeanObject,
    mut v_motive_373_: *mut crate::leanh::LeanObject,
    mut v_x_374_: *mut crate::leanh::LeanObject,
    mut v_h__1_375_: *mut crate::leanh::LeanObject,
    mut v_h__2_376_: *mut crate::leanh::LeanObject,
    mut v_h__3_377_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_374_) {
        0 => {
            let mut v_it_378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_377_);
            crate::leanh::lean_dec(v_h__2_376_);
            v_it_378_ = crate::leanh::lean_ctor_get(v_x_374_, 0);
            crate::leanh::lean_inc(v_it_378_);
            v_out_379_ = crate::leanh::lean_ctor_get(v_x_374_, 1);
            crate::leanh::lean_inc(v_out_379_);
            crate::leanh::lean_dec_ref_known(v_x_374_, 2);
            v___x_380_ = crate::leanh::lean_apply_2(v_h__1_375_, v_it_378_, v_out_379_);
            return v___x_380_;
        }
        1 => {
            let mut v_it_381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_377_);
            crate::leanh::lean_dec(v_h__1_375_);
            v_it_381_ = crate::leanh::lean_ctor_get(v_x_374_, 0);
            crate::leanh::lean_inc(v_it_381_);
            crate::leanh::lean_dec_ref_known(v_x_374_, 1);
            v___x_382_ = crate::leanh::lean_apply_1(v_h__2_376_, v_it_381_);
            return v___x_382_;
        }
        _ => {
            let mut v___x_383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_376_);
            crate::leanh::lean_dec(v_h__1_375_);
            v___x_383_ = crate::leanh::lean_box(0);
            v___x_384_ = crate::leanh::lean_apply_1(v_h__3_377_, v___x_383_);
            return v___x_384_;
        }
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_Iterators_Lemmas_Combinators_DropWhile(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_Iterators_Combinators_DropWhile(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_DropWhile(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Bool(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_TakeDrop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_Iterators_Lemmas_Combinators_DropWhile(
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
pub unsafe fn initialize_Std_Data_Iterators_Lemmas_Combinators_DropWhile(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_Iterators_Combinators_DropWhile(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_DropWhile(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Consumers(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Bool(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_TakeDrop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Lemmas_Combinators_DropWhile(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Data_Iterators_Lemmas_Combinators_DropWhile(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Data_Iterators_Lemmas_Combinators_DropWhile(builtin);
}
