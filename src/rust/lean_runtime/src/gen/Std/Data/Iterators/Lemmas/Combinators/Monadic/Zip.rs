// Lean compiler output
// Module: Std.Data.Iterators.Lemmas.Combinators.Monadic.Zip
// Imports: Std.Data.Iterators.Combinators.Monadic.Zip Init.Data.Iterators.Lemmas.Consumers.Monadic
use crate::r#gen::Init::Data::Iterators::Lemmas::Consumers::Monadic::{
    initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic,
    runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic,
};
use crate::r#gen::Std::Data::Iterators::Combinators::Monadic::Zip::{
    initialize_Std_Data_Iterators_Combinators_Monadic_Zip,
    runtime_initialize_Std_Data_Iterators_Combinators_Monadic_Zip,
};
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_Zip_0__Std_Iterators_Types_Zip_instIterator_match__5_splitter___redArg(
    mut v_x_176_: *mut crate::leanh::LeanObject,
    mut v_h__1_177_: *mut crate::leanh::LeanObject,
    mut v_h__2_178_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_176_) == 0 {
        let mut v___x_179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_178_);
        v___x_179_ = crate::leanh::lean_apply_1(v_h__1_177_, crate::leanh::lean_box(0));
        return v___x_179_;
    } else {
        let mut v_val_180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_177_);
        v_val_180_ = crate::leanh::lean_ctor_get(v_x_176_, 0);
        crate::leanh::lean_inc(v_val_180_);
        crate::leanh::lean_dec_ref_known(v_x_176_, 1);
        v___x_181_ = crate::leanh::lean_apply_2(v_h__2_178_, v_val_180_, crate::leanh::lean_box(0));
        return v___x_181_;
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_Zip_0__Std_Iterators_Types_Zip_instIterator_match__5_splitter(
    mut v_m_182_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_u2081_183_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_u2081_184_: *mut crate::leanh::LeanObject,
    mut v_inst_185_: *mut crate::leanh::LeanObject,
    mut v_motive_186_: *mut crate::leanh::LeanObject,
    mut v_x_187_: *mut crate::leanh::LeanObject,
    mut v_h__1_188_: *mut crate::leanh::LeanObject,
    mut v_h__2_189_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_187_) == 0 {
        let mut v___x_190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_189_);
        v___x_190_ = crate::leanh::lean_apply_1(v_h__1_188_, crate::leanh::lean_box(0));
        return v___x_190_;
    } else {
        let mut v_val_191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_188_);
        v_val_191_ = crate::leanh::lean_ctor_get(v_x_187_, 0);
        crate::leanh::lean_inc(v_val_191_);
        crate::leanh::lean_dec_ref_known(v_x_187_, 1);
        v___x_192_ = crate::leanh::lean_apply_2(v_h__2_189_, v_val_191_, crate::leanh::lean_box(0));
        return v___x_192_;
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_Zip_0__Std_Iterators_Types_Zip_instIterator_match__5_splitter___boxed(
    mut v_m_193_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_u2081_194_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_u2081_195_: *mut crate::leanh::LeanObject,
    mut v_inst_196_: *mut crate::leanh::LeanObject,
    mut v_motive_197_: *mut crate::leanh::LeanObject,
    mut v_x_198_: *mut crate::leanh::LeanObject,
    mut v_h__1_199_: *mut crate::leanh::LeanObject,
    mut v_h__2_200_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_201_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_Zip_0__Std_Iterators_Types_Zip_instIterator_match__5_splitter(v_m_193_, v_00_u03b1_u2081_194_, v_00_u03b2_u2081_195_, v_inst_196_, v_motive_197_, v_x_198_, v_h__1_199_, v_h__2_200_);
    crate::leanh::lean_dec(v_inst_196_);
    return v_res_201_;
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_Zip_0__Std_Iterators_Types_Zip_instIterator_match__1_splitter___redArg(
    mut v_x_202_: *mut crate::leanh::LeanObject,
    mut v_h__1_203_: *mut crate::leanh::LeanObject,
    mut v_h__2_204_: *mut crate::leanh::LeanObject,
    mut v_h__3_205_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_202_) {
        0 => {
            let mut v_it_206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_205_);
            crate::leanh::lean_dec(v_h__2_204_);
            v_it_206_ = crate::leanh::lean_ctor_get(v_x_202_, 0);
            crate::leanh::lean_inc(v_it_206_);
            v_out_207_ = crate::leanh::lean_ctor_get(v_x_202_, 1);
            crate::leanh::lean_inc(v_out_207_);
            crate::leanh::lean_dec_ref_known(v_x_202_, 2);
            v___x_208_ = crate::leanh::lean_apply_3(
                v_h__1_203_,
                v_it_206_,
                v_out_207_,
                crate::leanh::lean_box(0),
            );
            return v___x_208_;
        }
        1 => {
            let mut v_it_209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_205_);
            crate::leanh::lean_dec(v_h__1_203_);
            v_it_209_ = crate::leanh::lean_ctor_get(v_x_202_, 0);
            crate::leanh::lean_inc(v_it_209_);
            crate::leanh::lean_dec_ref_known(v_x_202_, 1);
            v___x_210_ =
                crate::leanh::lean_apply_2(v_h__2_204_, v_it_209_, crate::leanh::lean_box(0));
            return v___x_210_;
        }
        _ => {
            let mut v___x_211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_204_);
            crate::leanh::lean_dec(v_h__1_203_);
            v___x_211_ = crate::leanh::lean_apply_1(v_h__3_205_, crate::leanh::lean_box(0));
            return v___x_211_;
        }
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_Zip_0__Std_Iterators_Types_Zip_instIterator_match__1_splitter(
    mut v_m_212_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_u2081_213_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_u2081_214_: *mut crate::leanh::LeanObject,
    mut v_inst_215_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_u2082_216_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_u2082_217_: *mut crate::leanh::LeanObject,
    mut v_it_218_: *mut crate::leanh::LeanObject,
    mut v_motive_219_: *mut crate::leanh::LeanObject,
    mut v_x_220_: *mut crate::leanh::LeanObject,
    mut v_h__1_221_: *mut crate::leanh::LeanObject,
    mut v_h__2_222_: *mut crate::leanh::LeanObject,
    mut v_h__3_223_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_220_) {
        0 => {
            let mut v_it_224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_223_);
            crate::leanh::lean_dec(v_h__2_222_);
            v_it_224_ = crate::leanh::lean_ctor_get(v_x_220_, 0);
            crate::leanh::lean_inc(v_it_224_);
            v_out_225_ = crate::leanh::lean_ctor_get(v_x_220_, 1);
            crate::leanh::lean_inc(v_out_225_);
            crate::leanh::lean_dec_ref_known(v_x_220_, 2);
            v___x_226_ = crate::leanh::lean_apply_3(
                v_h__1_221_,
                v_it_224_,
                v_out_225_,
                crate::leanh::lean_box(0),
            );
            return v___x_226_;
        }
        1 => {
            let mut v_it_227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_223_);
            crate::leanh::lean_dec(v_h__1_221_);
            v_it_227_ = crate::leanh::lean_ctor_get(v_x_220_, 0);
            crate::leanh::lean_inc(v_it_227_);
            crate::leanh::lean_dec_ref_known(v_x_220_, 1);
            v___x_228_ =
                crate::leanh::lean_apply_2(v_h__2_222_, v_it_227_, crate::leanh::lean_box(0));
            return v___x_228_;
        }
        _ => {
            let mut v___x_229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_222_);
            crate::leanh::lean_dec(v_h__1_221_);
            v___x_229_ = crate::leanh::lean_apply_1(v_h__3_223_, crate::leanh::lean_box(0));
            return v___x_229_;
        }
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_Zip_0__Std_Iterators_Types_Zip_instIterator_match__1_splitter___boxed(
    mut v_m_230_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_u2081_231_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_u2081_232_: *mut crate::leanh::LeanObject,
    mut v_inst_233_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_u2082_234_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_u2082_235_: *mut crate::leanh::LeanObject,
    mut v_it_236_: *mut crate::leanh::LeanObject,
    mut v_motive_237_: *mut crate::leanh::LeanObject,
    mut v_x_238_: *mut crate::leanh::LeanObject,
    mut v_h__1_239_: *mut crate::leanh::LeanObject,
    mut v_h__2_240_: *mut crate::leanh::LeanObject,
    mut v_h__3_241_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_242_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_Zip_0__Std_Iterators_Types_Zip_instIterator_match__1_splitter(v_m_230_, v_00_u03b1_u2081_231_, v_00_u03b2_u2081_232_, v_inst_233_, v_00_u03b1_u2082_234_, v_00_u03b2_u2082_235_, v_it_236_, v_motive_237_, v_x_238_, v_h__1_239_, v_h__2_240_, v_h__3_241_);
    crate::leanh::lean_dec_ref(v_it_236_);
    crate::leanh::lean_dec(v_inst_233_);
    return v_res_242_;
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_Zip_0__Std_Iterators_Types_Zip_instIterator_match__3_splitter___redArg(
    mut v_x_243_: *mut crate::leanh::LeanObject,
    mut v_h__1_244_: *mut crate::leanh::LeanObject,
    mut v_h__2_245_: *mut crate::leanh::LeanObject,
    mut v_h__3_246_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_243_) {
        0 => {
            let mut v_it_247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_246_);
            crate::leanh::lean_dec(v_h__2_245_);
            v_it_247_ = crate::leanh::lean_ctor_get(v_x_243_, 0);
            crate::leanh::lean_inc(v_it_247_);
            v_out_248_ = crate::leanh::lean_ctor_get(v_x_243_, 1);
            crate::leanh::lean_inc(v_out_248_);
            crate::leanh::lean_dec_ref_known(v_x_243_, 2);
            v___x_249_ = crate::leanh::lean_apply_3(
                v_h__1_244_,
                v_it_247_,
                v_out_248_,
                crate::leanh::lean_box(0),
            );
            return v___x_249_;
        }
        1 => {
            let mut v_it_250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_246_);
            crate::leanh::lean_dec(v_h__1_244_);
            v_it_250_ = crate::leanh::lean_ctor_get(v_x_243_, 0);
            crate::leanh::lean_inc(v_it_250_);
            crate::leanh::lean_dec_ref_known(v_x_243_, 1);
            v___x_251_ =
                crate::leanh::lean_apply_2(v_h__2_245_, v_it_250_, crate::leanh::lean_box(0));
            return v___x_251_;
        }
        _ => {
            let mut v___x_252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_245_);
            crate::leanh::lean_dec(v_h__1_244_);
            v___x_252_ = crate::leanh::lean_apply_1(v_h__3_246_, crate::leanh::lean_box(0));
            return v___x_252_;
        }
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_Zip_0__Std_Iterators_Types_Zip_instIterator_match__3_splitter(
    mut v_m_253_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_u2081_254_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_u2081_255_: *mut crate::leanh::LeanObject,
    mut v_inst_256_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_u2082_257_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_u2082_258_: *mut crate::leanh::LeanObject,
    mut v_inst_259_: *mut crate::leanh::LeanObject,
    mut v_it_260_: *mut crate::leanh::LeanObject,
    mut v_motive_261_: *mut crate::leanh::LeanObject,
    mut v_x_262_: *mut crate::leanh::LeanObject,
    mut v_h__1_263_: *mut crate::leanh::LeanObject,
    mut v_h__2_264_: *mut crate::leanh::LeanObject,
    mut v_h__3_265_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_262_) {
        0 => {
            let mut v_it_266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_265_);
            crate::leanh::lean_dec(v_h__2_264_);
            v_it_266_ = crate::leanh::lean_ctor_get(v_x_262_, 0);
            crate::leanh::lean_inc(v_it_266_);
            v_out_267_ = crate::leanh::lean_ctor_get(v_x_262_, 1);
            crate::leanh::lean_inc(v_out_267_);
            crate::leanh::lean_dec_ref_known(v_x_262_, 2);
            v___x_268_ = crate::leanh::lean_apply_3(
                v_h__1_263_,
                v_it_266_,
                v_out_267_,
                crate::leanh::lean_box(0),
            );
            return v___x_268_;
        }
        1 => {
            let mut v_it_269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_265_);
            crate::leanh::lean_dec(v_h__1_263_);
            v_it_269_ = crate::leanh::lean_ctor_get(v_x_262_, 0);
            crate::leanh::lean_inc(v_it_269_);
            crate::leanh::lean_dec_ref_known(v_x_262_, 1);
            v___x_270_ =
                crate::leanh::lean_apply_2(v_h__2_264_, v_it_269_, crate::leanh::lean_box(0));
            return v___x_270_;
        }
        _ => {
            let mut v___x_271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_264_);
            crate::leanh::lean_dec(v_h__1_263_);
            v___x_271_ = crate::leanh::lean_apply_1(v_h__3_265_, crate::leanh::lean_box(0));
            return v___x_271_;
        }
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_Zip_0__Std_Iterators_Types_Zip_instIterator_match__3_splitter___boxed(
    mut v_m_272_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_u2081_273_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_u2081_274_: *mut crate::leanh::LeanObject,
    mut v_inst_275_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_u2082_276_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_u2082_277_: *mut crate::leanh::LeanObject,
    mut v_inst_278_: *mut crate::leanh::LeanObject,
    mut v_it_279_: *mut crate::leanh::LeanObject,
    mut v_motive_280_: *mut crate::leanh::LeanObject,
    mut v_x_281_: *mut crate::leanh::LeanObject,
    mut v_h__1_282_: *mut crate::leanh::LeanObject,
    mut v_h__2_283_: *mut crate::leanh::LeanObject,
    mut v_h__3_284_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_285_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_Zip_0__Std_Iterators_Types_Zip_instIterator_match__3_splitter(v_m_272_, v_00_u03b1_u2081_273_, v_00_u03b2_u2081_274_, v_inst_275_, v_00_u03b1_u2082_276_, v_00_u03b2_u2082_277_, v_inst_278_, v_it_279_, v_motive_280_, v_x_281_, v_h__1_282_, v_h__2_283_, v_h__3_284_);
    crate::leanh::lean_dec_ref(v_it_279_);
    crate::leanh::lean_dec(v_inst_278_);
    crate::leanh::lean_dec(v_inst_275_);
    return v_res_285_;
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_Zip_0__Std_IterM_step__intermediateZip_match__3_splitter___redArg(
    mut v_memo_286_: *mut crate::leanh::LeanObject,
    mut v_h__1_287_: *mut crate::leanh::LeanObject,
    mut v_h__2_288_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_memo_286_) == 0 {
        let mut v___x_289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_288_);
        v___x_289_ = crate::leanh::lean_box(0);
        v___x_290_ = crate::leanh::lean_apply_1(v_h__1_287_, v___x_289_);
        return v___x_290_;
    } else {
        let mut v_val_291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_287_);
        v_val_291_ = crate::leanh::lean_ctor_get(v_memo_286_, 0);
        crate::leanh::lean_inc(v_val_291_);
        crate::leanh::lean_dec_ref_known(v_memo_286_, 1);
        v___x_292_ = crate::leanh::lean_apply_1(v_h__2_288_, v_val_291_);
        return v___x_292_;
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_Zip_0__Std_IterM_step__intermediateZip_match__3_splitter(
    mut v_00_u03b1_u2081_293_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_u2081_294_: *mut crate::leanh::LeanObject,
    mut v_m_295_: *mut crate::leanh::LeanObject,
    mut v_inst_296_: *mut crate::leanh::LeanObject,
    mut v_motive_297_: *mut crate::leanh::LeanObject,
    mut v_memo_298_: *mut crate::leanh::LeanObject,
    mut v_h__1_299_: *mut crate::leanh::LeanObject,
    mut v_h__2_300_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_memo_298_) == 0 {
        let mut v___x_301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_300_);
        v___x_301_ = crate::leanh::lean_box(0);
        v___x_302_ = crate::leanh::lean_apply_1(v_h__1_299_, v___x_301_);
        return v___x_302_;
    } else {
        let mut v_val_303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_299_);
        v_val_303_ = crate::leanh::lean_ctor_get(v_memo_298_, 0);
        crate::leanh::lean_inc(v_val_303_);
        crate::leanh::lean_dec_ref_known(v_memo_298_, 1);
        v___x_304_ = crate::leanh::lean_apply_1(v_h__2_300_, v_val_303_);
        return v___x_304_;
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_Zip_0__Std_IterM_step__intermediateZip_match__3_splitter___boxed(
    mut v_00_u03b1_u2081_305_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_u2081_306_: *mut crate::leanh::LeanObject,
    mut v_m_307_: *mut crate::leanh::LeanObject,
    mut v_inst_308_: *mut crate::leanh::LeanObject,
    mut v_motive_309_: *mut crate::leanh::LeanObject,
    mut v_memo_310_: *mut crate::leanh::LeanObject,
    mut v_h__1_311_: *mut crate::leanh::LeanObject,
    mut v_h__2_312_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_313_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_Zip_0__Std_IterM_step__intermediateZip_match__3_splitter(v_00_u03b1_u2081_305_, v_00_u03b2_u2081_306_, v_m_307_, v_inst_308_, v_motive_309_, v_memo_310_, v_h__1_311_, v_h__2_312_);
    crate::leanh::lean_dec(v_inst_308_);
    return v_res_313_;
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_Zip_0__Std_IterM_step__intermediateZip_match__1_splitter___redArg(
    mut v_x_314_: *mut crate::leanh::LeanObject,
    mut v_h__1_315_: *mut crate::leanh::LeanObject,
    mut v_h__2_316_: *mut crate::leanh::LeanObject,
    mut v_h__3_317_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_314_) {
        0 => {
            let mut v_it_318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_317_);
            crate::leanh::lean_dec(v_h__2_316_);
            v_it_318_ = crate::leanh::lean_ctor_get(v_x_314_, 0);
            crate::leanh::lean_inc(v_it_318_);
            v_out_319_ = crate::leanh::lean_ctor_get(v_x_314_, 1);
            crate::leanh::lean_inc(v_out_319_);
            crate::leanh::lean_dec_ref_known(v_x_314_, 2);
            v___x_320_ = crate::leanh::lean_apply_3(
                v_h__1_315_,
                v_it_318_,
                v_out_319_,
                crate::leanh::lean_box(0),
            );
            return v___x_320_;
        }
        1 => {
            let mut v_it_321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_317_);
            crate::leanh::lean_dec(v_h__1_315_);
            v_it_321_ = crate::leanh::lean_ctor_get(v_x_314_, 0);
            crate::leanh::lean_inc(v_it_321_);
            crate::leanh::lean_dec_ref_known(v_x_314_, 1);
            v___x_322_ =
                crate::leanh::lean_apply_2(v_h__2_316_, v_it_321_, crate::leanh::lean_box(0));
            return v___x_322_;
        }
        _ => {
            let mut v___x_323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_316_);
            crate::leanh::lean_dec(v_h__1_315_);
            v___x_323_ = crate::leanh::lean_apply_1(v_h__3_317_, crate::leanh::lean_box(0));
            return v___x_323_;
        }
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_Zip_0__Std_IterM_step__intermediateZip_match__1_splitter(
    mut v_00_u03b1_u2081_324_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_u2081_325_: *mut crate::leanh::LeanObject,
    mut v_m_326_: *mut crate::leanh::LeanObject,
    mut v_inst_327_: *mut crate::leanh::LeanObject,
    mut v_it_u2081_328_: *mut crate::leanh::LeanObject,
    mut v_motive_329_: *mut crate::leanh::LeanObject,
    mut v_x_330_: *mut crate::leanh::LeanObject,
    mut v_h__1_331_: *mut crate::leanh::LeanObject,
    mut v_h__2_332_: *mut crate::leanh::LeanObject,
    mut v_h__3_333_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_330_) {
        0 => {
            let mut v_it_334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_333_);
            crate::leanh::lean_dec(v_h__2_332_);
            v_it_334_ = crate::leanh::lean_ctor_get(v_x_330_, 0);
            crate::leanh::lean_inc(v_it_334_);
            v_out_335_ = crate::leanh::lean_ctor_get(v_x_330_, 1);
            crate::leanh::lean_inc(v_out_335_);
            crate::leanh::lean_dec_ref_known(v_x_330_, 2);
            v___x_336_ = crate::leanh::lean_apply_3(
                v_h__1_331_,
                v_it_334_,
                v_out_335_,
                crate::leanh::lean_box(0),
            );
            return v___x_336_;
        }
        1 => {
            let mut v_it_337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_333_);
            crate::leanh::lean_dec(v_h__1_331_);
            v_it_337_ = crate::leanh::lean_ctor_get(v_x_330_, 0);
            crate::leanh::lean_inc(v_it_337_);
            crate::leanh::lean_dec_ref_known(v_x_330_, 1);
            v___x_338_ =
                crate::leanh::lean_apply_2(v_h__2_332_, v_it_337_, crate::leanh::lean_box(0));
            return v___x_338_;
        }
        _ => {
            let mut v___x_339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_332_);
            crate::leanh::lean_dec(v_h__1_331_);
            v___x_339_ = crate::leanh::lean_apply_1(v_h__3_333_, crate::leanh::lean_box(0));
            return v___x_339_;
        }
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_Zip_0__Std_IterM_step__intermediateZip_match__1_splitter___boxed(
    mut v_00_u03b1_u2081_340_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_u2081_341_: *mut crate::leanh::LeanObject,
    mut v_m_342_: *mut crate::leanh::LeanObject,
    mut v_inst_343_: *mut crate::leanh::LeanObject,
    mut v_it_u2081_344_: *mut crate::leanh::LeanObject,
    mut v_motive_345_: *mut crate::leanh::LeanObject,
    mut v_x_346_: *mut crate::leanh::LeanObject,
    mut v_h__1_347_: *mut crate::leanh::LeanObject,
    mut v_h__2_348_: *mut crate::leanh::LeanObject,
    mut v_h__3_349_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_350_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_Zip_0__Std_IterM_step__intermediateZip_match__1_splitter(v_00_u03b1_u2081_340_, v_00_u03b2_u2081_341_, v_m_342_, v_inst_343_, v_it_u2081_344_, v_motive_345_, v_x_346_, v_h__1_347_, v_h__2_348_, v_h__3_349_);
    crate::leanh::lean_dec(v_it_u2081_344_);
    crate::leanh::lean_dec(v_inst_343_);
    return v_res_350_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_Zip(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_Iterators_Combinators_Monadic_Zip(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_Zip(
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
pub unsafe fn initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_Zip(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_Iterators_Combinators_Monadic_Zip(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_Zip(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_Zip(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_Zip(builtin);
}
