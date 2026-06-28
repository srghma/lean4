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
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_apply_1, lean_apply_2, lean_apply_3, lean_box,
    lean_ctor_get, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_obj_tag,
};
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_Zip_0__Std_Iterators_Types_Zip_instIterator_match__5_splitter___redArg(
    mut v_x_176_: *mut LeanObject,
    mut v_h__1_177_: *mut LeanObject,
    mut v_h__2_178_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_176_) == 0 {
        let mut v___x_179_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_178_);
        v___x_179_ = lean_apply_1(v_h__1_177_, lean_box(0));
        return v___x_179_;
    } else {
        let mut v_val_180_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_181_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_177_);
        v_val_180_ = lean_ctor_get(v_x_176_, 0);
        lean_inc(v_val_180_);
        lean_dec_ref_known(v_x_176_, 1);
        v___x_181_ = lean_apply_2(v_h__2_178_, v_val_180_, lean_box(0));
        return v___x_181_;
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_Zip_0__Std_Iterators_Types_Zip_instIterator_match__5_splitter(
    mut v_m_182_: *mut LeanObject,
    mut v_00_u03b1_u2081_183_: *mut LeanObject,
    mut v_00_u03b2_u2081_184_: *mut LeanObject,
    mut v_inst_185_: *mut LeanObject,
    mut v_motive_186_: *mut LeanObject,
    mut v_x_187_: *mut LeanObject,
    mut v_h__1_188_: *mut LeanObject,
    mut v_h__2_189_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_187_) == 0 {
        let mut v___x_190_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_189_);
        v___x_190_ = lean_apply_1(v_h__1_188_, lean_box(0));
        return v___x_190_;
    } else {
        let mut v_val_191_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_192_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_188_);
        v_val_191_ = lean_ctor_get(v_x_187_, 0);
        lean_inc(v_val_191_);
        lean_dec_ref_known(v_x_187_, 1);
        v___x_192_ = lean_apply_2(v_h__2_189_, v_val_191_, lean_box(0));
        return v___x_192_;
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_Zip_0__Std_Iterators_Types_Zip_instIterator_match__5_splitter___boxed(
    mut v_m_193_: *mut LeanObject,
    mut v_00_u03b1_u2081_194_: *mut LeanObject,
    mut v_00_u03b2_u2081_195_: *mut LeanObject,
    mut v_inst_196_: *mut LeanObject,
    mut v_motive_197_: *mut LeanObject,
    mut v_x_198_: *mut LeanObject,
    mut v_h__1_199_: *mut LeanObject,
    mut v_h__2_200_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_201_: *mut LeanObject = core::ptr::null_mut();
    v_res_201_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_Zip_0__Std_Iterators_Types_Zip_instIterator_match__5_splitter(v_m_193_, v_00_u03b1_u2081_194_, v_00_u03b2_u2081_195_, v_inst_196_, v_motive_197_, v_x_198_, v_h__1_199_, v_h__2_200_);
    lean_dec(v_inst_196_);
    return v_res_201_;
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_Zip_0__Std_Iterators_Types_Zip_instIterator_match__1_splitter___redArg(
    mut v_x_202_: *mut LeanObject,
    mut v_h__1_203_: *mut LeanObject,
    mut v_h__2_204_: *mut LeanObject,
    mut v_h__3_205_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_202_) {
        0 => {
            let mut v_it_206_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_207_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_208_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_205_);
            lean_dec(v_h__2_204_);
            v_it_206_ = lean_ctor_get(v_x_202_, 0);
            lean_inc(v_it_206_);
            v_out_207_ = lean_ctor_get(v_x_202_, 1);
            lean_inc(v_out_207_);
            lean_dec_ref_known(v_x_202_, 2);
            v___x_208_ = lean_apply_3(v_h__1_203_, v_it_206_, v_out_207_, lean_box(0));
            return v___x_208_;
        }
        1 => {
            let mut v_it_209_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_210_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_205_);
            lean_dec(v_h__1_203_);
            v_it_209_ = lean_ctor_get(v_x_202_, 0);
            lean_inc(v_it_209_);
            lean_dec_ref_known(v_x_202_, 1);
            v___x_210_ = lean_apply_2(v_h__2_204_, v_it_209_, lean_box(0));
            return v___x_210_;
        }
        _ => {
            let mut v___x_211_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_204_);
            lean_dec(v_h__1_203_);
            v___x_211_ = lean_apply_1(v_h__3_205_, lean_box(0));
            return v___x_211_;
        }
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_Zip_0__Std_Iterators_Types_Zip_instIterator_match__1_splitter(
    mut v_m_212_: *mut LeanObject,
    mut v_00_u03b1_u2081_213_: *mut LeanObject,
    mut v_00_u03b2_u2081_214_: *mut LeanObject,
    mut v_inst_215_: *mut LeanObject,
    mut v_00_u03b1_u2082_216_: *mut LeanObject,
    mut v_00_u03b2_u2082_217_: *mut LeanObject,
    mut v_it_218_: *mut LeanObject,
    mut v_motive_219_: *mut LeanObject,
    mut v_x_220_: *mut LeanObject,
    mut v_h__1_221_: *mut LeanObject,
    mut v_h__2_222_: *mut LeanObject,
    mut v_h__3_223_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_220_) {
        0 => {
            let mut v_it_224_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_225_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_226_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_223_);
            lean_dec(v_h__2_222_);
            v_it_224_ = lean_ctor_get(v_x_220_, 0);
            lean_inc(v_it_224_);
            v_out_225_ = lean_ctor_get(v_x_220_, 1);
            lean_inc(v_out_225_);
            lean_dec_ref_known(v_x_220_, 2);
            v___x_226_ = lean_apply_3(v_h__1_221_, v_it_224_, v_out_225_, lean_box(0));
            return v___x_226_;
        }
        1 => {
            let mut v_it_227_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_228_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_223_);
            lean_dec(v_h__1_221_);
            v_it_227_ = lean_ctor_get(v_x_220_, 0);
            lean_inc(v_it_227_);
            lean_dec_ref_known(v_x_220_, 1);
            v___x_228_ = lean_apply_2(v_h__2_222_, v_it_227_, lean_box(0));
            return v___x_228_;
        }
        _ => {
            let mut v___x_229_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_222_);
            lean_dec(v_h__1_221_);
            v___x_229_ = lean_apply_1(v_h__3_223_, lean_box(0));
            return v___x_229_;
        }
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_Zip_0__Std_Iterators_Types_Zip_instIterator_match__1_splitter___boxed(
    mut v_m_230_: *mut LeanObject,
    mut v_00_u03b1_u2081_231_: *mut LeanObject,
    mut v_00_u03b2_u2081_232_: *mut LeanObject,
    mut v_inst_233_: *mut LeanObject,
    mut v_00_u03b1_u2082_234_: *mut LeanObject,
    mut v_00_u03b2_u2082_235_: *mut LeanObject,
    mut v_it_236_: *mut LeanObject,
    mut v_motive_237_: *mut LeanObject,
    mut v_x_238_: *mut LeanObject,
    mut v_h__1_239_: *mut LeanObject,
    mut v_h__2_240_: *mut LeanObject,
    mut v_h__3_241_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_242_: *mut LeanObject = core::ptr::null_mut();
    v_res_242_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_Zip_0__Std_Iterators_Types_Zip_instIterator_match__1_splitter(v_m_230_, v_00_u03b1_u2081_231_, v_00_u03b2_u2081_232_, v_inst_233_, v_00_u03b1_u2082_234_, v_00_u03b2_u2082_235_, v_it_236_, v_motive_237_, v_x_238_, v_h__1_239_, v_h__2_240_, v_h__3_241_);
    lean_dec_ref(v_it_236_);
    lean_dec(v_inst_233_);
    return v_res_242_;
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_Zip_0__Std_Iterators_Types_Zip_instIterator_match__3_splitter___redArg(
    mut v_x_243_: *mut LeanObject,
    mut v_h__1_244_: *mut LeanObject,
    mut v_h__2_245_: *mut LeanObject,
    mut v_h__3_246_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_243_) {
        0 => {
            let mut v_it_247_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_248_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_249_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_246_);
            lean_dec(v_h__2_245_);
            v_it_247_ = lean_ctor_get(v_x_243_, 0);
            lean_inc(v_it_247_);
            v_out_248_ = lean_ctor_get(v_x_243_, 1);
            lean_inc(v_out_248_);
            lean_dec_ref_known(v_x_243_, 2);
            v___x_249_ = lean_apply_3(v_h__1_244_, v_it_247_, v_out_248_, lean_box(0));
            return v___x_249_;
        }
        1 => {
            let mut v_it_250_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_251_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_246_);
            lean_dec(v_h__1_244_);
            v_it_250_ = lean_ctor_get(v_x_243_, 0);
            lean_inc(v_it_250_);
            lean_dec_ref_known(v_x_243_, 1);
            v___x_251_ = lean_apply_2(v_h__2_245_, v_it_250_, lean_box(0));
            return v___x_251_;
        }
        _ => {
            let mut v___x_252_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_245_);
            lean_dec(v_h__1_244_);
            v___x_252_ = lean_apply_1(v_h__3_246_, lean_box(0));
            return v___x_252_;
        }
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_Zip_0__Std_Iterators_Types_Zip_instIterator_match__3_splitter(
    mut v_m_253_: *mut LeanObject,
    mut v_00_u03b1_u2081_254_: *mut LeanObject,
    mut v_00_u03b2_u2081_255_: *mut LeanObject,
    mut v_inst_256_: *mut LeanObject,
    mut v_00_u03b1_u2082_257_: *mut LeanObject,
    mut v_00_u03b2_u2082_258_: *mut LeanObject,
    mut v_inst_259_: *mut LeanObject,
    mut v_it_260_: *mut LeanObject,
    mut v_motive_261_: *mut LeanObject,
    mut v_x_262_: *mut LeanObject,
    mut v_h__1_263_: *mut LeanObject,
    mut v_h__2_264_: *mut LeanObject,
    mut v_h__3_265_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_262_) {
        0 => {
            let mut v_it_266_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_267_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_268_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_265_);
            lean_dec(v_h__2_264_);
            v_it_266_ = lean_ctor_get(v_x_262_, 0);
            lean_inc(v_it_266_);
            v_out_267_ = lean_ctor_get(v_x_262_, 1);
            lean_inc(v_out_267_);
            lean_dec_ref_known(v_x_262_, 2);
            v___x_268_ = lean_apply_3(v_h__1_263_, v_it_266_, v_out_267_, lean_box(0));
            return v___x_268_;
        }
        1 => {
            let mut v_it_269_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_270_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_265_);
            lean_dec(v_h__1_263_);
            v_it_269_ = lean_ctor_get(v_x_262_, 0);
            lean_inc(v_it_269_);
            lean_dec_ref_known(v_x_262_, 1);
            v___x_270_ = lean_apply_2(v_h__2_264_, v_it_269_, lean_box(0));
            return v___x_270_;
        }
        _ => {
            let mut v___x_271_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_264_);
            lean_dec(v_h__1_263_);
            v___x_271_ = lean_apply_1(v_h__3_265_, lean_box(0));
            return v___x_271_;
        }
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_Zip_0__Std_Iterators_Types_Zip_instIterator_match__3_splitter___boxed(
    mut v_m_272_: *mut LeanObject,
    mut v_00_u03b1_u2081_273_: *mut LeanObject,
    mut v_00_u03b2_u2081_274_: *mut LeanObject,
    mut v_inst_275_: *mut LeanObject,
    mut v_00_u03b1_u2082_276_: *mut LeanObject,
    mut v_00_u03b2_u2082_277_: *mut LeanObject,
    mut v_inst_278_: *mut LeanObject,
    mut v_it_279_: *mut LeanObject,
    mut v_motive_280_: *mut LeanObject,
    mut v_x_281_: *mut LeanObject,
    mut v_h__1_282_: *mut LeanObject,
    mut v_h__2_283_: *mut LeanObject,
    mut v_h__3_284_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_285_: *mut LeanObject = core::ptr::null_mut();
    v_res_285_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_Zip_0__Std_Iterators_Types_Zip_instIterator_match__3_splitter(v_m_272_, v_00_u03b1_u2081_273_, v_00_u03b2_u2081_274_, v_inst_275_, v_00_u03b1_u2082_276_, v_00_u03b2_u2082_277_, v_inst_278_, v_it_279_, v_motive_280_, v_x_281_, v_h__1_282_, v_h__2_283_, v_h__3_284_);
    lean_dec_ref(v_it_279_);
    lean_dec(v_inst_278_);
    lean_dec(v_inst_275_);
    return v_res_285_;
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_Zip_0__Std_IterM_step__intermediateZip_match__3_splitter___redArg(
    mut v_memo_286_: *mut LeanObject,
    mut v_h__1_287_: *mut LeanObject,
    mut v_h__2_288_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_memo_286_) == 0 {
        let mut v___x_289_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_290_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_288_);
        v___x_289_ = lean_box(0);
        v___x_290_ = lean_apply_1(v_h__1_287_, v___x_289_);
        return v___x_290_;
    } else {
        let mut v_val_291_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_292_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_287_);
        v_val_291_ = lean_ctor_get(v_memo_286_, 0);
        lean_inc(v_val_291_);
        lean_dec_ref_known(v_memo_286_, 1);
        v___x_292_ = lean_apply_1(v_h__2_288_, v_val_291_);
        return v___x_292_;
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_Zip_0__Std_IterM_step__intermediateZip_match__3_splitter(
    mut v_00_u03b1_u2081_293_: *mut LeanObject,
    mut v_00_u03b2_u2081_294_: *mut LeanObject,
    mut v_m_295_: *mut LeanObject,
    mut v_inst_296_: *mut LeanObject,
    mut v_motive_297_: *mut LeanObject,
    mut v_memo_298_: *mut LeanObject,
    mut v_h__1_299_: *mut LeanObject,
    mut v_h__2_300_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_memo_298_) == 0 {
        let mut v___x_301_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_302_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_300_);
        v___x_301_ = lean_box(0);
        v___x_302_ = lean_apply_1(v_h__1_299_, v___x_301_);
        return v___x_302_;
    } else {
        let mut v_val_303_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_304_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_299_);
        v_val_303_ = lean_ctor_get(v_memo_298_, 0);
        lean_inc(v_val_303_);
        lean_dec_ref_known(v_memo_298_, 1);
        v___x_304_ = lean_apply_1(v_h__2_300_, v_val_303_);
        return v___x_304_;
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_Zip_0__Std_IterM_step__intermediateZip_match__3_splitter___boxed(
    mut v_00_u03b1_u2081_305_: *mut LeanObject,
    mut v_00_u03b2_u2081_306_: *mut LeanObject,
    mut v_m_307_: *mut LeanObject,
    mut v_inst_308_: *mut LeanObject,
    mut v_motive_309_: *mut LeanObject,
    mut v_memo_310_: *mut LeanObject,
    mut v_h__1_311_: *mut LeanObject,
    mut v_h__2_312_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_313_: *mut LeanObject = core::ptr::null_mut();
    v_res_313_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_Zip_0__Std_IterM_step__intermediateZip_match__3_splitter(v_00_u03b1_u2081_305_, v_00_u03b2_u2081_306_, v_m_307_, v_inst_308_, v_motive_309_, v_memo_310_, v_h__1_311_, v_h__2_312_);
    lean_dec(v_inst_308_);
    return v_res_313_;
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_Zip_0__Std_IterM_step__intermediateZip_match__1_splitter___redArg(
    mut v_x_314_: *mut LeanObject,
    mut v_h__1_315_: *mut LeanObject,
    mut v_h__2_316_: *mut LeanObject,
    mut v_h__3_317_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_314_) {
        0 => {
            let mut v_it_318_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_319_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_320_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_317_);
            lean_dec(v_h__2_316_);
            v_it_318_ = lean_ctor_get(v_x_314_, 0);
            lean_inc(v_it_318_);
            v_out_319_ = lean_ctor_get(v_x_314_, 1);
            lean_inc(v_out_319_);
            lean_dec_ref_known(v_x_314_, 2);
            v___x_320_ = lean_apply_3(v_h__1_315_, v_it_318_, v_out_319_, lean_box(0));
            return v___x_320_;
        }
        1 => {
            let mut v_it_321_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_322_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_317_);
            lean_dec(v_h__1_315_);
            v_it_321_ = lean_ctor_get(v_x_314_, 0);
            lean_inc(v_it_321_);
            lean_dec_ref_known(v_x_314_, 1);
            v___x_322_ = lean_apply_2(v_h__2_316_, v_it_321_, lean_box(0));
            return v___x_322_;
        }
        _ => {
            let mut v___x_323_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_316_);
            lean_dec(v_h__1_315_);
            v___x_323_ = lean_apply_1(v_h__3_317_, lean_box(0));
            return v___x_323_;
        }
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_Zip_0__Std_IterM_step__intermediateZip_match__1_splitter(
    mut v_00_u03b1_u2081_324_: *mut LeanObject,
    mut v_00_u03b2_u2081_325_: *mut LeanObject,
    mut v_m_326_: *mut LeanObject,
    mut v_inst_327_: *mut LeanObject,
    mut v_it_u2081_328_: *mut LeanObject,
    mut v_motive_329_: *mut LeanObject,
    mut v_x_330_: *mut LeanObject,
    mut v_h__1_331_: *mut LeanObject,
    mut v_h__2_332_: *mut LeanObject,
    mut v_h__3_333_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_330_) {
        0 => {
            let mut v_it_334_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_335_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_336_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_333_);
            lean_dec(v_h__2_332_);
            v_it_334_ = lean_ctor_get(v_x_330_, 0);
            lean_inc(v_it_334_);
            v_out_335_ = lean_ctor_get(v_x_330_, 1);
            lean_inc(v_out_335_);
            lean_dec_ref_known(v_x_330_, 2);
            v___x_336_ = lean_apply_3(v_h__1_331_, v_it_334_, v_out_335_, lean_box(0));
            return v___x_336_;
        }
        1 => {
            let mut v_it_337_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_338_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_333_);
            lean_dec(v_h__1_331_);
            v_it_337_ = lean_ctor_get(v_x_330_, 0);
            lean_inc(v_it_337_);
            lean_dec_ref_known(v_x_330_, 1);
            v___x_338_ = lean_apply_2(v_h__2_332_, v_it_337_, lean_box(0));
            return v___x_338_;
        }
        _ => {
            let mut v___x_339_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_332_);
            lean_dec(v_h__1_331_);
            v___x_339_ = lean_apply_1(v_h__3_333_, lean_box(0));
            return v___x_339_;
        }
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_Zip_0__Std_IterM_step__intermediateZip_match__1_splitter___boxed(
    mut v_00_u03b1_u2081_340_: *mut LeanObject,
    mut v_00_u03b2_u2081_341_: *mut LeanObject,
    mut v_m_342_: *mut LeanObject,
    mut v_inst_343_: *mut LeanObject,
    mut v_it_u2081_344_: *mut LeanObject,
    mut v_motive_345_: *mut LeanObject,
    mut v_x_346_: *mut LeanObject,
    mut v_h__1_347_: *mut LeanObject,
    mut v_h__2_348_: *mut LeanObject,
    mut v_h__3_349_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_350_: *mut LeanObject = core::ptr::null_mut();
    v_res_350_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_Zip_0__Std_IterM_step__intermediateZip_match__1_splitter(v_00_u03b1_u2081_340_, v_00_u03b2_u2081_341_, v_m_342_, v_inst_343_, v_it_u2081_344_, v_motive_345_, v_x_346_, v_h__1_347_, v_h__2_348_, v_h__3_349_);
    lean_dec(v_it_u2081_344_);
    lean_dec(v_inst_343_);
    return v_res_350_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_Zip(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_Iterators_Combinators_Monadic_Zip(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_Zip(
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
pub unsafe fn initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_Zip(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_Iterators_Combinators_Monadic_Zip(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_Zip(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_Zip(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_Zip(builtin);
}
