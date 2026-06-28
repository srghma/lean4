// Lean compiler output
// Module: Std.Data.Iterators.Lemmas.Combinators.Monadic.TakeWhile
// Imports: Std.Data.Iterators.Combinators.Monadic.TakeWhile Std.Data.Iterators.Lemmas.Consumers.Monadic
use crate::r#gen::Std::Data::Iterators::Combinators::Monadic::TakeWhile::{
    initialize_Std_Data_Iterators_Combinators_Monadic_TakeWhile,
    runtime_initialize_Std_Data_Iterators_Combinators_Monadic_TakeWhile,
};
use crate::r#gen::Std::Data::Iterators::Lemmas::Consumers::Monadic::{
    initialize_Std_Data_Iterators_Lemmas_Consumers_Monadic,
    runtime_initialize_Std_Data_Iterators_Lemmas_Consumers_Monadic,
};
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_TakeWhile_0__Std_Iterators_Types_TakeWhile_instIterator_match__3_splitter___redArg(
    mut v_x_191_: *mut crate::leanh::LeanObject,
    mut v_h__1_192_: *mut crate::leanh::LeanObject,
    mut v_h__2_193_: *mut crate::leanh::LeanObject,
    mut v_h__3_194_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_191_) {
        0 => {
            let mut v_it_195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_194_);
            crate::leanh::lean_dec(v_h__2_193_);
            v_it_195_ = crate::leanh::lean_ctor_get(v_x_191_, 0);
            crate::leanh::lean_inc(v_it_195_);
            v_out_196_ = crate::leanh::lean_ctor_get(v_x_191_, 1);
            crate::leanh::lean_inc(v_out_196_);
            crate::leanh::lean_dec_ref_known(v_x_191_, 2);
            v___x_197_ = crate::leanh::lean_apply_3(
                v_h__1_192_,
                v_it_195_,
                v_out_196_,
                crate::leanh::lean_box(0),
            );
            return v___x_197_;
        }
        1 => {
            let mut v_it_198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_194_);
            crate::leanh::lean_dec(v_h__1_192_);
            v_it_198_ = crate::leanh::lean_ctor_get(v_x_191_, 0);
            crate::leanh::lean_inc(v_it_198_);
            crate::leanh::lean_dec_ref_known(v_x_191_, 1);
            v___x_199_ =
                crate::leanh::lean_apply_2(v_h__2_193_, v_it_198_, crate::leanh::lean_box(0));
            return v___x_199_;
        }
        _ => {
            let mut v___x_200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_193_);
            crate::leanh::lean_dec(v_h__1_192_);
            v___x_200_ = crate::leanh::lean_apply_1(v_h__3_194_, crate::leanh::lean_box(0));
            return v___x_200_;
        }
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_TakeWhile_0__Std_Iterators_Types_TakeWhile_instIterator_match__3_splitter(
    mut v_00_u03b1_201_: *mut crate::leanh::LeanObject,
    mut v_m_202_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_203_: *mut crate::leanh::LeanObject,
    mut v_inst_204_: *mut crate::leanh::LeanObject,
    mut v_P_205_: *mut crate::leanh::LeanObject,
    mut v_it_206_: *mut crate::leanh::LeanObject,
    mut v_motive_207_: *mut crate::leanh::LeanObject,
    mut v_x_208_: *mut crate::leanh::LeanObject,
    mut v_h__1_209_: *mut crate::leanh::LeanObject,
    mut v_h__2_210_: *mut crate::leanh::LeanObject,
    mut v_h__3_211_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_208_) {
        0 => {
            let mut v_it_212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_211_);
            crate::leanh::lean_dec(v_h__2_210_);
            v_it_212_ = crate::leanh::lean_ctor_get(v_x_208_, 0);
            crate::leanh::lean_inc(v_it_212_);
            v_out_213_ = crate::leanh::lean_ctor_get(v_x_208_, 1);
            crate::leanh::lean_inc(v_out_213_);
            crate::leanh::lean_dec_ref_known(v_x_208_, 2);
            v___x_214_ = crate::leanh::lean_apply_3(
                v_h__1_209_,
                v_it_212_,
                v_out_213_,
                crate::leanh::lean_box(0),
            );
            return v___x_214_;
        }
        1 => {
            let mut v_it_215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_211_);
            crate::leanh::lean_dec(v_h__1_209_);
            v_it_215_ = crate::leanh::lean_ctor_get(v_x_208_, 0);
            crate::leanh::lean_inc(v_it_215_);
            crate::leanh::lean_dec_ref_known(v_x_208_, 1);
            v___x_216_ =
                crate::leanh::lean_apply_2(v_h__2_210_, v_it_215_, crate::leanh::lean_box(0));
            return v___x_216_;
        }
        _ => {
            let mut v___x_217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_210_);
            crate::leanh::lean_dec(v_h__1_209_);
            v___x_217_ = crate::leanh::lean_apply_1(v_h__3_211_, crate::leanh::lean_box(0));
            return v___x_217_;
        }
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_TakeWhile_0__Std_Iterators_Types_TakeWhile_instIterator_match__3_splitter___boxed(
    mut v_00_u03b1_218_: *mut crate::leanh::LeanObject,
    mut v_m_219_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_220_: *mut crate::leanh::LeanObject,
    mut v_inst_221_: *mut crate::leanh::LeanObject,
    mut v_P_222_: *mut crate::leanh::LeanObject,
    mut v_it_223_: *mut crate::leanh::LeanObject,
    mut v_motive_224_: *mut crate::leanh::LeanObject,
    mut v_x_225_: *mut crate::leanh::LeanObject,
    mut v_h__1_226_: *mut crate::leanh::LeanObject,
    mut v_h__2_227_: *mut crate::leanh::LeanObject,
    mut v_h__3_228_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_229_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_TakeWhile_0__Std_Iterators_Types_TakeWhile_instIterator_match__3_splitter(v_00_u03b1_218_, v_m_219_, v_00_u03b2_220_, v_inst_221_, v_P_222_, v_it_223_, v_motive_224_, v_x_225_, v_h__1_226_, v_h__2_227_, v_h__3_228_);
    crate::leanh::lean_dec(v_it_223_);
    crate::leanh::lean_dec(v_P_222_);
    crate::leanh::lean_dec(v_inst_221_);
    return v_res_229_;
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_TakeWhile_0__Std_Iterators_Types_TakeWhile_instIterator_match__1_splitter___redArg(
    mut v_____do__lift_230_: u8,
    mut v_h__1_231_: *mut crate::leanh::LeanObject,
    mut v_h__2_232_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if v_____do__lift_230_ == 0 {
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
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_TakeWhile_0__Std_Iterators_Types_TakeWhile_instIterator_match__1_splitter___redArg___boxed(
    mut v_____do__lift_235_: *mut crate::leanh::LeanObject,
    mut v_h__1_236_: *mut crate::leanh::LeanObject,
    mut v_h__2_237_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_____do__lift_72__boxed_238_: u8 = 0;
    let mut v_res_239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_____do__lift_72__boxed_238_ = (crate::leanh::lean_unbox(v_____do__lift_235_) as u8);
    v_res_239_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_TakeWhile_0__Std_Iterators_Types_TakeWhile_instIterator_match__1_splitter___redArg(v_____do__lift_72__boxed_238_, v_h__1_236_, v_h__2_237_);
    return v_res_239_;
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_TakeWhile_0__Std_Iterators_Types_TakeWhile_instIterator_match__1_splitter(
    mut v_m_240_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_241_: *mut crate::leanh::LeanObject,
    mut v_P_242_: *mut crate::leanh::LeanObject,
    mut v_out_243_: *mut crate::leanh::LeanObject,
    mut v_motive_244_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_245_: u8,
    mut v_h__1_246_: *mut crate::leanh::LeanObject,
    mut v_h__2_247_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if v_____do__lift_245_ == 0 {
        let mut v___x_248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_246_);
        v___x_248_ = crate::leanh::lean_apply_1(v_h__2_247_, crate::leanh::lean_box(0));
        return v___x_248_;
    } else {
        let mut v___x_249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_247_);
        v___x_249_ = crate::leanh::lean_apply_1(v_h__1_246_, crate::leanh::lean_box(0));
        return v___x_249_;
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_TakeWhile_0__Std_Iterators_Types_TakeWhile_instIterator_match__1_splitter___boxed(
    mut v_m_250_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_251_: *mut crate::leanh::LeanObject,
    mut v_P_252_: *mut crate::leanh::LeanObject,
    mut v_out_253_: *mut crate::leanh::LeanObject,
    mut v_motive_254_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_255_: *mut crate::leanh::LeanObject,
    mut v_h__1_256_: *mut crate::leanh::LeanObject,
    mut v_h__2_257_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_____do__lift_79__boxed_258_: u8 = 0;
    let mut v_res_259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_____do__lift_79__boxed_258_ = (crate::leanh::lean_unbox(v_____do__lift_255_) as u8);
    v_res_259_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_TakeWhile_0__Std_Iterators_Types_TakeWhile_instIterator_match__1_splitter(v_m_250_, v_00_u03b2_251_, v_P_252_, v_out_253_, v_motive_254_, v_____do__lift_79__boxed_258_, v_h__1_256_, v_h__2_257_);
    crate::leanh::lean_dec(v_out_253_);
    crate::leanh::lean_dec(v_P_252_);
    return v_res_259_;
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_TakeWhile_0__Std_IterM_step__takeWhileWithPostcondition_match__3_splitter___redArg(
    mut v_x_260_: *mut crate::leanh::LeanObject,
    mut v_h__1_261_: *mut crate::leanh::LeanObject,
    mut v_h__2_262_: *mut crate::leanh::LeanObject,
    mut v_h__3_263_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_260_) {
        0 => {
            let mut v_it_264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_263_);
            crate::leanh::lean_dec(v_h__2_262_);
            v_it_264_ = crate::leanh::lean_ctor_get(v_x_260_, 0);
            crate::leanh::lean_inc(v_it_264_);
            v_out_265_ = crate::leanh::lean_ctor_get(v_x_260_, 1);
            crate::leanh::lean_inc(v_out_265_);
            crate::leanh::lean_dec_ref_known(v_x_260_, 2);
            v___x_266_ = crate::leanh::lean_apply_3(
                v_h__1_261_,
                v_it_264_,
                v_out_265_,
                crate::leanh::lean_box(0),
            );
            return v___x_266_;
        }
        1 => {
            let mut v_it_267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_263_);
            crate::leanh::lean_dec(v_h__1_261_);
            v_it_267_ = crate::leanh::lean_ctor_get(v_x_260_, 0);
            crate::leanh::lean_inc(v_it_267_);
            crate::leanh::lean_dec_ref_known(v_x_260_, 1);
            v___x_268_ =
                crate::leanh::lean_apply_2(v_h__2_262_, v_it_267_, crate::leanh::lean_box(0));
            return v___x_268_;
        }
        _ => {
            let mut v___x_269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_262_);
            crate::leanh::lean_dec(v_h__1_261_);
            v___x_269_ = crate::leanh::lean_apply_1(v_h__3_263_, crate::leanh::lean_box(0));
            return v___x_269_;
        }
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_TakeWhile_0__Std_IterM_step__takeWhileWithPostcondition_match__3_splitter(
    mut v_00_u03b1_270_: *mut crate::leanh::LeanObject,
    mut v_m_271_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_272_: *mut crate::leanh::LeanObject,
    mut v_inst_273_: *mut crate::leanh::LeanObject,
    mut v_it_274_: *mut crate::leanh::LeanObject,
    mut v_motive_275_: *mut crate::leanh::LeanObject,
    mut v_x_276_: *mut crate::leanh::LeanObject,
    mut v_h__1_277_: *mut crate::leanh::LeanObject,
    mut v_h__2_278_: *mut crate::leanh::LeanObject,
    mut v_h__3_279_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_276_) {
        0 => {
            let mut v_it_280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_279_);
            crate::leanh::lean_dec(v_h__2_278_);
            v_it_280_ = crate::leanh::lean_ctor_get(v_x_276_, 0);
            crate::leanh::lean_inc(v_it_280_);
            v_out_281_ = crate::leanh::lean_ctor_get(v_x_276_, 1);
            crate::leanh::lean_inc(v_out_281_);
            crate::leanh::lean_dec_ref_known(v_x_276_, 2);
            v___x_282_ = crate::leanh::lean_apply_3(
                v_h__1_277_,
                v_it_280_,
                v_out_281_,
                crate::leanh::lean_box(0),
            );
            return v___x_282_;
        }
        1 => {
            let mut v_it_283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_279_);
            crate::leanh::lean_dec(v_h__1_277_);
            v_it_283_ = crate::leanh::lean_ctor_get(v_x_276_, 0);
            crate::leanh::lean_inc(v_it_283_);
            crate::leanh::lean_dec_ref_known(v_x_276_, 1);
            v___x_284_ =
                crate::leanh::lean_apply_2(v_h__2_278_, v_it_283_, crate::leanh::lean_box(0));
            return v___x_284_;
        }
        _ => {
            let mut v___x_285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_278_);
            crate::leanh::lean_dec(v_h__1_277_);
            v___x_285_ = crate::leanh::lean_apply_1(v_h__3_279_, crate::leanh::lean_box(0));
            return v___x_285_;
        }
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_TakeWhile_0__Std_IterM_step__takeWhileWithPostcondition_match__3_splitter___boxed(
    mut v_00_u03b1_286_: *mut crate::leanh::LeanObject,
    mut v_m_287_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_288_: *mut crate::leanh::LeanObject,
    mut v_inst_289_: *mut crate::leanh::LeanObject,
    mut v_it_290_: *mut crate::leanh::LeanObject,
    mut v_motive_291_: *mut crate::leanh::LeanObject,
    mut v_x_292_: *mut crate::leanh::LeanObject,
    mut v_h__1_293_: *mut crate::leanh::LeanObject,
    mut v_h__2_294_: *mut crate::leanh::LeanObject,
    mut v_h__3_295_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_296_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_TakeWhile_0__Std_IterM_step__takeWhileWithPostcondition_match__3_splitter(v_00_u03b1_286_, v_m_287_, v_00_u03b2_288_, v_inst_289_, v_it_290_, v_motive_291_, v_x_292_, v_h__1_293_, v_h__2_294_, v_h__3_295_);
    crate::leanh::lean_dec(v_it_290_);
    crate::leanh::lean_dec(v_inst_289_);
    return v_res_296_;
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_TakeWhile_0__Std_IterM_step__takeWhileWithPostcondition_match__1_splitter___redArg(
    mut v_____do__lift_297_: u8,
    mut v_h__1_298_: *mut crate::leanh::LeanObject,
    mut v_h__2_299_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if v_____do__lift_297_ == 0 {
        let mut v___x_300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_298_);
        v___x_300_ = crate::leanh::lean_apply_1(v_h__2_299_, crate::leanh::lean_box(0));
        return v___x_300_;
    } else {
        let mut v___x_301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_299_);
        v___x_301_ = crate::leanh::lean_apply_1(v_h__1_298_, crate::leanh::lean_box(0));
        return v___x_301_;
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_TakeWhile_0__Std_IterM_step__takeWhileWithPostcondition_match__1_splitter___redArg___boxed(
    mut v_____do__lift_302_: *mut crate::leanh::LeanObject,
    mut v_h__1_303_: *mut crate::leanh::LeanObject,
    mut v_h__2_304_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_____do__lift_72__boxed_305_: u8 = 0;
    let mut v_res_306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_____do__lift_72__boxed_305_ = (crate::leanh::lean_unbox(v_____do__lift_302_) as u8);
    v_res_306_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_TakeWhile_0__Std_IterM_step__takeWhileWithPostcondition_match__1_splitter___redArg(v_____do__lift_72__boxed_305_, v_h__1_303_, v_h__2_304_);
    return v_res_306_;
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_TakeWhile_0__Std_IterM_step__takeWhileWithPostcondition_match__1_splitter(
    mut v_m_307_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_308_: *mut crate::leanh::LeanObject,
    mut v_P_309_: *mut crate::leanh::LeanObject,
    mut v_out_310_: *mut crate::leanh::LeanObject,
    mut v_motive_311_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_312_: u8,
    mut v_h__1_313_: *mut crate::leanh::LeanObject,
    mut v_h__2_314_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if v_____do__lift_312_ == 0 {
        let mut v___x_315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_313_);
        v___x_315_ = crate::leanh::lean_apply_1(v_h__2_314_, crate::leanh::lean_box(0));
        return v___x_315_;
    } else {
        let mut v___x_316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_314_);
        v___x_316_ = crate::leanh::lean_apply_1(v_h__1_313_, crate::leanh::lean_box(0));
        return v___x_316_;
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_TakeWhile_0__Std_IterM_step__takeWhileWithPostcondition_match__1_splitter___boxed(
    mut v_m_317_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_318_: *mut crate::leanh::LeanObject,
    mut v_P_319_: *mut crate::leanh::LeanObject,
    mut v_out_320_: *mut crate::leanh::LeanObject,
    mut v_motive_321_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_322_: *mut crate::leanh::LeanObject,
    mut v_h__1_323_: *mut crate::leanh::LeanObject,
    mut v_h__2_324_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_____do__lift_79__boxed_325_: u8 = 0;
    let mut v_res_326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_____do__lift_79__boxed_325_ = (crate::leanh::lean_unbox(v_____do__lift_322_) as u8);
    v_res_326_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_TakeWhile_0__Std_IterM_step__takeWhileWithPostcondition_match__1_splitter(v_m_317_, v_00_u03b2_318_, v_P_319_, v_out_320_, v_motive_321_, v_____do__lift_79__boxed_325_, v_h__1_323_, v_h__2_324_);
    crate::leanh::lean_dec(v_out_320_);
    crate::leanh::lean_dec(v_P_319_);
    return v_res_326_;
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_TakeWhile_0__Std_IterM_step__takeWhileM_match__1_splitter___redArg(
    mut v_____do__lift_327_: u8,
    mut v_h__1_328_: *mut crate::leanh::LeanObject,
    mut v_h__2_329_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if v_____do__lift_327_ == 0 {
        let mut v___x_330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_328_);
        v___x_330_ = crate::leanh::lean_apply_1(v_h__2_329_, crate::leanh::lean_box(0));
        return v___x_330_;
    } else {
        let mut v___x_331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_329_);
        v___x_331_ = crate::leanh::lean_apply_1(v_h__1_328_, crate::leanh::lean_box(0));
        return v___x_331_;
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_TakeWhile_0__Std_IterM_step__takeWhileM_match__1_splitter___redArg___boxed(
    mut v_____do__lift_332_: *mut crate::leanh::LeanObject,
    mut v_h__1_333_: *mut crate::leanh::LeanObject,
    mut v_h__2_334_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_____do__lift_74__boxed_335_: u8 = 0;
    let mut v_res_336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_____do__lift_74__boxed_335_ = (crate::leanh::lean_unbox(v_____do__lift_332_) as u8);
    v_res_336_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_TakeWhile_0__Std_IterM_step__takeWhileM_match__1_splitter___redArg(v_____do__lift_74__boxed_335_, v_h__1_333_, v_h__2_334_);
    return v_res_336_;
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_TakeWhile_0__Std_IterM_step__takeWhileM_match__1_splitter(
    mut v_m_337_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_338_: *mut crate::leanh::LeanObject,
    mut v_inst_339_: *mut crate::leanh::LeanObject,
    mut v_P_340_: *mut crate::leanh::LeanObject,
    mut v_out_341_: *mut crate::leanh::LeanObject,
    mut v_motive_342_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_343_: u8,
    mut v_h__1_344_: *mut crate::leanh::LeanObject,
    mut v_h__2_345_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if v_____do__lift_343_ == 0 {
        let mut v___x_346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_344_);
        v___x_346_ = crate::leanh::lean_apply_1(v_h__2_345_, crate::leanh::lean_box(0));
        return v___x_346_;
    } else {
        let mut v___x_347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_345_);
        v___x_347_ = crate::leanh::lean_apply_1(v_h__1_344_, crate::leanh::lean_box(0));
        return v___x_347_;
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_TakeWhile_0__Std_IterM_step__takeWhileM_match__1_splitter___boxed(
    mut v_m_348_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_349_: *mut crate::leanh::LeanObject,
    mut v_inst_350_: *mut crate::leanh::LeanObject,
    mut v_P_351_: *mut crate::leanh::LeanObject,
    mut v_out_352_: *mut crate::leanh::LeanObject,
    mut v_motive_353_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_354_: *mut crate::leanh::LeanObject,
    mut v_h__1_355_: *mut crate::leanh::LeanObject,
    mut v_h__2_356_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_____do__lift_82__boxed_357_: u8 = 0;
    let mut v_res_358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_____do__lift_82__boxed_357_ = (crate::leanh::lean_unbox(v_____do__lift_354_) as u8);
    v_res_358_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_TakeWhile_0__Std_IterM_step__takeWhileM_match__1_splitter(v_m_348_, v_00_u03b2_349_, v_inst_350_, v_P_351_, v_out_352_, v_motive_353_, v_____do__lift_82__boxed_357_, v_h__1_355_, v_h__2_356_);
    crate::leanh::lean_dec(v_out_352_);
    crate::leanh::lean_dec(v_P_351_);
    crate::leanh::lean_dec(v_inst_350_);
    return v_res_358_;
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_TakeWhile_0__Std_IterM_step__takeWhile_match__1_splitter___redArg(
    mut v_x_359_: u8,
    mut v_h__1_360_: *mut crate::leanh::LeanObject,
    mut v_h__2_361_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if v_x_359_ == 0 {
        let mut v___x_362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_360_);
        v___x_362_ = crate::leanh::lean_apply_1(v_h__2_361_, crate::leanh::lean_box(0));
        return v___x_362_;
    } else {
        let mut v___x_363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_361_);
        v___x_363_ = crate::leanh::lean_apply_1(v_h__1_360_, crate::leanh::lean_box(0));
        return v___x_363_;
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_TakeWhile_0__Std_IterM_step__takeWhile_match__1_splitter___redArg___boxed(
    mut v_x_364_: *mut crate::leanh::LeanObject,
    mut v_h__1_365_: *mut crate::leanh::LeanObject,
    mut v_h__2_366_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_26__boxed_367_: u8 = 0;
    let mut v_res_368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_26__boxed_367_ = (crate::leanh::lean_unbox(v_x_364_) as u8);
    v_res_368_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_TakeWhile_0__Std_IterM_step__takeWhile_match__1_splitter___redArg(v_x_26__boxed_367_, v_h__1_365_, v_h__2_366_);
    return v_res_368_;
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_TakeWhile_0__Std_IterM_step__takeWhile_match__1_splitter(
    mut v_motive_369_: *mut crate::leanh::LeanObject,
    mut v_x_370_: u8,
    mut v_h__1_371_: *mut crate::leanh::LeanObject,
    mut v_h__2_372_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if v_x_370_ == 0 {
        let mut v___x_373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_371_);
        v___x_373_ = crate::leanh::lean_apply_1(v_h__2_372_, crate::leanh::lean_box(0));
        return v___x_373_;
    } else {
        let mut v___x_374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_372_);
        v___x_374_ = crate::leanh::lean_apply_1(v_h__1_371_, crate::leanh::lean_box(0));
        return v___x_374_;
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_TakeWhile_0__Std_IterM_step__takeWhile_match__1_splitter___boxed(
    mut v_motive_375_: *mut crate::leanh::LeanObject,
    mut v_x_376_: *mut crate::leanh::LeanObject,
    mut v_h__1_377_: *mut crate::leanh::LeanObject,
    mut v_h__2_378_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_33__boxed_379_: u8 = 0;
    let mut v_res_380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_33__boxed_379_ = (crate::leanh::lean_unbox(v_x_376_) as u8);
    v_res_380_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_TakeWhile_0__Std_IterM_step__takeWhile_match__1_splitter(v_motive_375_, v_x_33__boxed_379_, v_h__1_377_, v_h__2_378_);
    return v_res_380_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_TakeWhile(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_Iterators_Combinators_Monadic_TakeWhile(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Lemmas_Consumers_Monadic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_TakeWhile(
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
pub unsafe fn initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_TakeWhile(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_Iterators_Combinators_Monadic_TakeWhile(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Data_Iterators_Lemmas_Consumers_Monadic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_TakeWhile(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_TakeWhile(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_TakeWhile(builtin);
}
