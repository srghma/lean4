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
    mut v_x_176_: *mut leanh::LeanObject,
    mut v_h__1_177_: *mut leanh::LeanObject,
    mut v_h__2_178_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_176_) == 0 {
        let mut v___x_179_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_178_);
        v___x_179_ = leanh::lean_apply_1(v_h__1_177_, leanh::lean_box(0));
        return v___x_179_;
    } else {
        let mut v_val_180_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_181_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_177_);
        v_val_180_ = leanh::lean_ctor_get(v_x_176_, 0);
        leanh::lean_inc(v_val_180_);
        leanh::lean_dec_ref_known(v_x_176_, 1);
        v___x_181_ = leanh::lean_apply_2(v_h__2_178_, v_val_180_, leanh::lean_box(0));
        return v___x_181_;
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_Zip_0__Std_Iterators_Types_Zip_instIterator_match__5_splitter(
    mut v_m_182_: *mut leanh::LeanObject,
    mut v_00_u03b1_u2081_183_: *mut leanh::LeanObject,
    mut v_00_u03b2_u2081_184_: *mut leanh::LeanObject,
    mut v_inst_185_: *mut leanh::LeanObject,
    mut v_motive_186_: *mut leanh::LeanObject,
    mut v_x_187_: *mut leanh::LeanObject,
    mut v_h__1_188_: *mut leanh::LeanObject,
    mut v_h__2_189_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_187_) == 0 {
        let mut v___x_190_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_189_);
        v___x_190_ = leanh::lean_apply_1(v_h__1_188_, leanh::lean_box(0));
        return v___x_190_;
    } else {
        let mut v_val_191_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_192_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_188_);
        v_val_191_ = leanh::lean_ctor_get(v_x_187_, 0);
        leanh::lean_inc(v_val_191_);
        leanh::lean_dec_ref_known(v_x_187_, 1);
        v___x_192_ = leanh::lean_apply_2(v_h__2_189_, v_val_191_, leanh::lean_box(0));
        return v___x_192_;
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_Zip_0__Std_Iterators_Types_Zip_instIterator_match__5_splitter___boxed(
    mut v_m_193_: *mut leanh::LeanObject,
    mut v_00_u03b1_u2081_194_: *mut leanh::LeanObject,
    mut v_00_u03b2_u2081_195_: *mut leanh::LeanObject,
    mut v_inst_196_: *mut leanh::LeanObject,
    mut v_motive_197_: *mut leanh::LeanObject,
    mut v_x_198_: *mut leanh::LeanObject,
    mut v_h__1_199_: *mut leanh::LeanObject,
    mut v_h__2_200_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_201_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_201_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_Zip_0__Std_Iterators_Types_Zip_instIterator_match__5_splitter(v_m_193_, v_00_u03b1_u2081_194_, v_00_u03b2_u2081_195_, v_inst_196_, v_motive_197_, v_x_198_, v_h__1_199_, v_h__2_200_);
    leanh::lean_dec(v_inst_196_);
    return v_res_201_;
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_Zip_0__Std_Iterators_Types_Zip_instIterator_match__1_splitter___redArg(
    mut v_x_202_: *mut leanh::LeanObject,
    mut v_h__1_203_: *mut leanh::LeanObject,
    mut v_h__2_204_: *mut leanh::LeanObject,
    mut v_h__3_205_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_202_) {
        0 => {
            let mut v_it_206_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_207_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_208_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_205_);
            leanh::lean_dec(v_h__2_204_);
            v_it_206_ = leanh::lean_ctor_get(v_x_202_, 0);
            leanh::lean_inc(v_it_206_);
            v_out_207_ = leanh::lean_ctor_get(v_x_202_, 1);
            leanh::lean_inc(v_out_207_);
            leanh::lean_dec_ref_known(v_x_202_, 2);
            v___x_208_ = leanh::lean_apply_3(
                v_h__1_203_,
                v_it_206_,
                v_out_207_,
                leanh::lean_box(0),
            );
            return v___x_208_;
        }
        1 => {
            let mut v_it_209_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_210_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_205_);
            leanh::lean_dec(v_h__1_203_);
            v_it_209_ = leanh::lean_ctor_get(v_x_202_, 0);
            leanh::lean_inc(v_it_209_);
            leanh::lean_dec_ref_known(v_x_202_, 1);
            v___x_210_ =
                leanh::lean_apply_2(v_h__2_204_, v_it_209_, leanh::lean_box(0));
            return v___x_210_;
        }
        _ => {
            let mut v___x_211_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_204_);
            leanh::lean_dec(v_h__1_203_);
            v___x_211_ = leanh::lean_apply_1(v_h__3_205_, leanh::lean_box(0));
            return v___x_211_;
        }
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_Zip_0__Std_Iterators_Types_Zip_instIterator_match__1_splitter(
    mut v_m_212_: *mut leanh::LeanObject,
    mut v_00_u03b1_u2081_213_: *mut leanh::LeanObject,
    mut v_00_u03b2_u2081_214_: *mut leanh::LeanObject,
    mut v_inst_215_: *mut leanh::LeanObject,
    mut v_00_u03b1_u2082_216_: *mut leanh::LeanObject,
    mut v_00_u03b2_u2082_217_: *mut leanh::LeanObject,
    mut v_it_218_: *mut leanh::LeanObject,
    mut v_motive_219_: *mut leanh::LeanObject,
    mut v_x_220_: *mut leanh::LeanObject,
    mut v_h__1_221_: *mut leanh::LeanObject,
    mut v_h__2_222_: *mut leanh::LeanObject,
    mut v_h__3_223_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_220_) {
        0 => {
            let mut v_it_224_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_225_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_226_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_223_);
            leanh::lean_dec(v_h__2_222_);
            v_it_224_ = leanh::lean_ctor_get(v_x_220_, 0);
            leanh::lean_inc(v_it_224_);
            v_out_225_ = leanh::lean_ctor_get(v_x_220_, 1);
            leanh::lean_inc(v_out_225_);
            leanh::lean_dec_ref_known(v_x_220_, 2);
            v___x_226_ = leanh::lean_apply_3(
                v_h__1_221_,
                v_it_224_,
                v_out_225_,
                leanh::lean_box(0),
            );
            return v___x_226_;
        }
        1 => {
            let mut v_it_227_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_228_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_223_);
            leanh::lean_dec(v_h__1_221_);
            v_it_227_ = leanh::lean_ctor_get(v_x_220_, 0);
            leanh::lean_inc(v_it_227_);
            leanh::lean_dec_ref_known(v_x_220_, 1);
            v___x_228_ =
                leanh::lean_apply_2(v_h__2_222_, v_it_227_, leanh::lean_box(0));
            return v___x_228_;
        }
        _ => {
            let mut v___x_229_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_222_);
            leanh::lean_dec(v_h__1_221_);
            v___x_229_ = leanh::lean_apply_1(v_h__3_223_, leanh::lean_box(0));
            return v___x_229_;
        }
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_Zip_0__Std_Iterators_Types_Zip_instIterator_match__1_splitter___boxed(
    mut v_m_230_: *mut leanh::LeanObject,
    mut v_00_u03b1_u2081_231_: *mut leanh::LeanObject,
    mut v_00_u03b2_u2081_232_: *mut leanh::LeanObject,
    mut v_inst_233_: *mut leanh::LeanObject,
    mut v_00_u03b1_u2082_234_: *mut leanh::LeanObject,
    mut v_00_u03b2_u2082_235_: *mut leanh::LeanObject,
    mut v_it_236_: *mut leanh::LeanObject,
    mut v_motive_237_: *mut leanh::LeanObject,
    mut v_x_238_: *mut leanh::LeanObject,
    mut v_h__1_239_: *mut leanh::LeanObject,
    mut v_h__2_240_: *mut leanh::LeanObject,
    mut v_h__3_241_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_242_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_242_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_Zip_0__Std_Iterators_Types_Zip_instIterator_match__1_splitter(v_m_230_, v_00_u03b1_u2081_231_, v_00_u03b2_u2081_232_, v_inst_233_, v_00_u03b1_u2082_234_, v_00_u03b2_u2082_235_, v_it_236_, v_motive_237_, v_x_238_, v_h__1_239_, v_h__2_240_, v_h__3_241_);
    leanh::lean_dec_ref(v_it_236_);
    leanh::lean_dec(v_inst_233_);
    return v_res_242_;
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_Zip_0__Std_Iterators_Types_Zip_instIterator_match__3_splitter___redArg(
    mut v_x_243_: *mut leanh::LeanObject,
    mut v_h__1_244_: *mut leanh::LeanObject,
    mut v_h__2_245_: *mut leanh::LeanObject,
    mut v_h__3_246_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_243_) {
        0 => {
            let mut v_it_247_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_248_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_249_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_246_);
            leanh::lean_dec(v_h__2_245_);
            v_it_247_ = leanh::lean_ctor_get(v_x_243_, 0);
            leanh::lean_inc(v_it_247_);
            v_out_248_ = leanh::lean_ctor_get(v_x_243_, 1);
            leanh::lean_inc(v_out_248_);
            leanh::lean_dec_ref_known(v_x_243_, 2);
            v___x_249_ = leanh::lean_apply_3(
                v_h__1_244_,
                v_it_247_,
                v_out_248_,
                leanh::lean_box(0),
            );
            return v___x_249_;
        }
        1 => {
            let mut v_it_250_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_251_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_246_);
            leanh::lean_dec(v_h__1_244_);
            v_it_250_ = leanh::lean_ctor_get(v_x_243_, 0);
            leanh::lean_inc(v_it_250_);
            leanh::lean_dec_ref_known(v_x_243_, 1);
            v___x_251_ =
                leanh::lean_apply_2(v_h__2_245_, v_it_250_, leanh::lean_box(0));
            return v___x_251_;
        }
        _ => {
            let mut v___x_252_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_245_);
            leanh::lean_dec(v_h__1_244_);
            v___x_252_ = leanh::lean_apply_1(v_h__3_246_, leanh::lean_box(0));
            return v___x_252_;
        }
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_Zip_0__Std_Iterators_Types_Zip_instIterator_match__3_splitter(
    mut v_m_253_: *mut leanh::LeanObject,
    mut v_00_u03b1_u2081_254_: *mut leanh::LeanObject,
    mut v_00_u03b2_u2081_255_: *mut leanh::LeanObject,
    mut v_inst_256_: *mut leanh::LeanObject,
    mut v_00_u03b1_u2082_257_: *mut leanh::LeanObject,
    mut v_00_u03b2_u2082_258_: *mut leanh::LeanObject,
    mut v_inst_259_: *mut leanh::LeanObject,
    mut v_it_260_: *mut leanh::LeanObject,
    mut v_motive_261_: *mut leanh::LeanObject,
    mut v_x_262_: *mut leanh::LeanObject,
    mut v_h__1_263_: *mut leanh::LeanObject,
    mut v_h__2_264_: *mut leanh::LeanObject,
    mut v_h__3_265_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_262_) {
        0 => {
            let mut v_it_266_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_267_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_268_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_265_);
            leanh::lean_dec(v_h__2_264_);
            v_it_266_ = leanh::lean_ctor_get(v_x_262_, 0);
            leanh::lean_inc(v_it_266_);
            v_out_267_ = leanh::lean_ctor_get(v_x_262_, 1);
            leanh::lean_inc(v_out_267_);
            leanh::lean_dec_ref_known(v_x_262_, 2);
            v___x_268_ = leanh::lean_apply_3(
                v_h__1_263_,
                v_it_266_,
                v_out_267_,
                leanh::lean_box(0),
            );
            return v___x_268_;
        }
        1 => {
            let mut v_it_269_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_270_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_265_);
            leanh::lean_dec(v_h__1_263_);
            v_it_269_ = leanh::lean_ctor_get(v_x_262_, 0);
            leanh::lean_inc(v_it_269_);
            leanh::lean_dec_ref_known(v_x_262_, 1);
            v___x_270_ =
                leanh::lean_apply_2(v_h__2_264_, v_it_269_, leanh::lean_box(0));
            return v___x_270_;
        }
        _ => {
            let mut v___x_271_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_264_);
            leanh::lean_dec(v_h__1_263_);
            v___x_271_ = leanh::lean_apply_1(v_h__3_265_, leanh::lean_box(0));
            return v___x_271_;
        }
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_Zip_0__Std_Iterators_Types_Zip_instIterator_match__3_splitter___boxed(
    mut v_m_272_: *mut leanh::LeanObject,
    mut v_00_u03b1_u2081_273_: *mut leanh::LeanObject,
    mut v_00_u03b2_u2081_274_: *mut leanh::LeanObject,
    mut v_inst_275_: *mut leanh::LeanObject,
    mut v_00_u03b1_u2082_276_: *mut leanh::LeanObject,
    mut v_00_u03b2_u2082_277_: *mut leanh::LeanObject,
    mut v_inst_278_: *mut leanh::LeanObject,
    mut v_it_279_: *mut leanh::LeanObject,
    mut v_motive_280_: *mut leanh::LeanObject,
    mut v_x_281_: *mut leanh::LeanObject,
    mut v_h__1_282_: *mut leanh::LeanObject,
    mut v_h__2_283_: *mut leanh::LeanObject,
    mut v_h__3_284_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_285_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_285_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_Zip_0__Std_Iterators_Types_Zip_instIterator_match__3_splitter(v_m_272_, v_00_u03b1_u2081_273_, v_00_u03b2_u2081_274_, v_inst_275_, v_00_u03b1_u2082_276_, v_00_u03b2_u2082_277_, v_inst_278_, v_it_279_, v_motive_280_, v_x_281_, v_h__1_282_, v_h__2_283_, v_h__3_284_);
    leanh::lean_dec_ref(v_it_279_);
    leanh::lean_dec(v_inst_278_);
    leanh::lean_dec(v_inst_275_);
    return v_res_285_;
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_Zip_0__Std_IterM_step__intermediateZip_match__3_splitter___redArg(
    mut v_memo_286_: *mut leanh::LeanObject,
    mut v_h__1_287_: *mut leanh::LeanObject,
    mut v_h__2_288_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_memo_286_) == 0 {
        let mut v___x_289_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_290_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_288_);
        v___x_289_ = leanh::lean_box(0);
        v___x_290_ = leanh::lean_apply_1(v_h__1_287_, v___x_289_);
        return v___x_290_;
    } else {
        let mut v_val_291_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_292_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_287_);
        v_val_291_ = leanh::lean_ctor_get(v_memo_286_, 0);
        leanh::lean_inc(v_val_291_);
        leanh::lean_dec_ref_known(v_memo_286_, 1);
        v___x_292_ = leanh::lean_apply_1(v_h__2_288_, v_val_291_);
        return v___x_292_;
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_Zip_0__Std_IterM_step__intermediateZip_match__3_splitter(
    mut v_00_u03b1_u2081_293_: *mut leanh::LeanObject,
    mut v_00_u03b2_u2081_294_: *mut leanh::LeanObject,
    mut v_m_295_: *mut leanh::LeanObject,
    mut v_inst_296_: *mut leanh::LeanObject,
    mut v_motive_297_: *mut leanh::LeanObject,
    mut v_memo_298_: *mut leanh::LeanObject,
    mut v_h__1_299_: *mut leanh::LeanObject,
    mut v_h__2_300_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_memo_298_) == 0 {
        let mut v___x_301_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_302_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_300_);
        v___x_301_ = leanh::lean_box(0);
        v___x_302_ = leanh::lean_apply_1(v_h__1_299_, v___x_301_);
        return v___x_302_;
    } else {
        let mut v_val_303_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_304_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_299_);
        v_val_303_ = leanh::lean_ctor_get(v_memo_298_, 0);
        leanh::lean_inc(v_val_303_);
        leanh::lean_dec_ref_known(v_memo_298_, 1);
        v___x_304_ = leanh::lean_apply_1(v_h__2_300_, v_val_303_);
        return v___x_304_;
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_Zip_0__Std_IterM_step__intermediateZip_match__3_splitter___boxed(
    mut v_00_u03b1_u2081_305_: *mut leanh::LeanObject,
    mut v_00_u03b2_u2081_306_: *mut leanh::LeanObject,
    mut v_m_307_: *mut leanh::LeanObject,
    mut v_inst_308_: *mut leanh::LeanObject,
    mut v_motive_309_: *mut leanh::LeanObject,
    mut v_memo_310_: *mut leanh::LeanObject,
    mut v_h__1_311_: *mut leanh::LeanObject,
    mut v_h__2_312_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_313_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_313_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_Zip_0__Std_IterM_step__intermediateZip_match__3_splitter(v_00_u03b1_u2081_305_, v_00_u03b2_u2081_306_, v_m_307_, v_inst_308_, v_motive_309_, v_memo_310_, v_h__1_311_, v_h__2_312_);
    leanh::lean_dec(v_inst_308_);
    return v_res_313_;
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_Zip_0__Std_IterM_step__intermediateZip_match__1_splitter___redArg(
    mut v_x_314_: *mut leanh::LeanObject,
    mut v_h__1_315_: *mut leanh::LeanObject,
    mut v_h__2_316_: *mut leanh::LeanObject,
    mut v_h__3_317_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_314_) {
        0 => {
            let mut v_it_318_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_319_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_320_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_317_);
            leanh::lean_dec(v_h__2_316_);
            v_it_318_ = leanh::lean_ctor_get(v_x_314_, 0);
            leanh::lean_inc(v_it_318_);
            v_out_319_ = leanh::lean_ctor_get(v_x_314_, 1);
            leanh::lean_inc(v_out_319_);
            leanh::lean_dec_ref_known(v_x_314_, 2);
            v___x_320_ = leanh::lean_apply_3(
                v_h__1_315_,
                v_it_318_,
                v_out_319_,
                leanh::lean_box(0),
            );
            return v___x_320_;
        }
        1 => {
            let mut v_it_321_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_322_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_317_);
            leanh::lean_dec(v_h__1_315_);
            v_it_321_ = leanh::lean_ctor_get(v_x_314_, 0);
            leanh::lean_inc(v_it_321_);
            leanh::lean_dec_ref_known(v_x_314_, 1);
            v___x_322_ =
                leanh::lean_apply_2(v_h__2_316_, v_it_321_, leanh::lean_box(0));
            return v___x_322_;
        }
        _ => {
            let mut v___x_323_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_316_);
            leanh::lean_dec(v_h__1_315_);
            v___x_323_ = leanh::lean_apply_1(v_h__3_317_, leanh::lean_box(0));
            return v___x_323_;
        }
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_Zip_0__Std_IterM_step__intermediateZip_match__1_splitter(
    mut v_00_u03b1_u2081_324_: *mut leanh::LeanObject,
    mut v_00_u03b2_u2081_325_: *mut leanh::LeanObject,
    mut v_m_326_: *mut leanh::LeanObject,
    mut v_inst_327_: *mut leanh::LeanObject,
    mut v_it_u2081_328_: *mut leanh::LeanObject,
    mut v_motive_329_: *mut leanh::LeanObject,
    mut v_x_330_: *mut leanh::LeanObject,
    mut v_h__1_331_: *mut leanh::LeanObject,
    mut v_h__2_332_: *mut leanh::LeanObject,
    mut v_h__3_333_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_330_) {
        0 => {
            let mut v_it_334_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_335_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_336_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_333_);
            leanh::lean_dec(v_h__2_332_);
            v_it_334_ = leanh::lean_ctor_get(v_x_330_, 0);
            leanh::lean_inc(v_it_334_);
            v_out_335_ = leanh::lean_ctor_get(v_x_330_, 1);
            leanh::lean_inc(v_out_335_);
            leanh::lean_dec_ref_known(v_x_330_, 2);
            v___x_336_ = leanh::lean_apply_3(
                v_h__1_331_,
                v_it_334_,
                v_out_335_,
                leanh::lean_box(0),
            );
            return v___x_336_;
        }
        1 => {
            let mut v_it_337_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_338_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_333_);
            leanh::lean_dec(v_h__1_331_);
            v_it_337_ = leanh::lean_ctor_get(v_x_330_, 0);
            leanh::lean_inc(v_it_337_);
            leanh::lean_dec_ref_known(v_x_330_, 1);
            v___x_338_ =
                leanh::lean_apply_2(v_h__2_332_, v_it_337_, leanh::lean_box(0));
            return v___x_338_;
        }
        _ => {
            let mut v___x_339_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_332_);
            leanh::lean_dec(v_h__1_331_);
            v___x_339_ = leanh::lean_apply_1(v_h__3_333_, leanh::lean_box(0));
            return v___x_339_;
        }
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_Zip_0__Std_IterM_step__intermediateZip_match__1_splitter___boxed(
    mut v_00_u03b1_u2081_340_: *mut leanh::LeanObject,
    mut v_00_u03b2_u2081_341_: *mut leanh::LeanObject,
    mut v_m_342_: *mut leanh::LeanObject,
    mut v_inst_343_: *mut leanh::LeanObject,
    mut v_it_u2081_344_: *mut leanh::LeanObject,
    mut v_motive_345_: *mut leanh::LeanObject,
    mut v_x_346_: *mut leanh::LeanObject,
    mut v_h__1_347_: *mut leanh::LeanObject,
    mut v_h__2_348_: *mut leanh::LeanObject,
    mut v_h__3_349_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_350_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_350_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_Zip_0__Std_IterM_step__intermediateZip_match__1_splitter(v_00_u03b1_u2081_340_, v_00_u03b2_u2081_341_, v_m_342_, v_inst_343_, v_it_u2081_344_, v_motive_345_, v_x_346_, v_h__1_347_, v_h__2_348_, v_h__3_349_);
    leanh::lean_dec(v_it_u2081_344_);
    leanh::lean_dec(v_inst_343_);
    return v_res_350_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_Zip(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_Iterators_Combinators_Monadic_Zip(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_Zip(
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
pub unsafe fn initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_Zip(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_Iterators_Combinators_Monadic_Zip(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_Zip(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_Zip(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_Zip(builtin);
}