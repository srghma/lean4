// Lean compiler output
// Module: Std.Do.WP.SimpLemmas
// Imports: Std.Do.WP.Monad
use crate::r#gen::Std::Do::WP::Monad::{
    initialize_Std_Do_WP_Monad, runtime_initialize_Std_Do_WP_Monad,
};
pub unsafe fn l___private_Std_Do_WP_SimpLemmas_0__Std_Do_PredTrans_pushExcept_match__1_splitter___redArg(
    mut v_x_193_: *mut leanh::LeanObject,
    mut v_h__1_194_: *mut leanh::LeanObject,
    mut v_h__2_195_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_193_) == 0 {
        let mut v_a_196_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_197_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_194_);
        v_a_196_ = leanh::lean_ctor_get(v_x_193_, 0);
        leanh::lean_inc(v_a_196_);
        leanh::lean_dec_ref_known(v_x_193_, 1);
        v___x_197_ = leanh::lean_apply_1(v_h__2_195_, v_a_196_);
        return v___x_197_;
    } else {
        let mut v_a_198_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_199_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_195_);
        v_a_198_ = leanh::lean_ctor_get(v_x_193_, 0);
        leanh::lean_inc(v_a_198_);
        leanh::lean_dec_ref_known(v_x_193_, 1);
        v___x_199_ = leanh::lean_apply_1(v_h__1_194_, v_a_198_);
        return v___x_199_;
    }
}
pub unsafe fn l___private_Std_Do_WP_SimpLemmas_0__Std_Do_PredTrans_pushExcept_match__1_splitter(
    mut v_00_u03b1_200_: *mut leanh::LeanObject,
    mut v_00_u03b5_201_: *mut leanh::LeanObject,
    mut v_motive_202_: *mut leanh::LeanObject,
    mut v_x_203_: *mut leanh::LeanObject,
    mut v_h__1_204_: *mut leanh::LeanObject,
    mut v_h__2_205_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_203_) == 0 {
        let mut v_a_206_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_207_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_204_);
        v_a_206_ = leanh::lean_ctor_get(v_x_203_, 0);
        leanh::lean_inc(v_a_206_);
        leanh::lean_dec_ref_known(v_x_203_, 1);
        v___x_207_ = leanh::lean_apply_1(v_h__2_205_, v_a_206_);
        return v___x_207_;
    } else {
        let mut v_a_208_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_209_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_205_);
        v_a_208_ = leanh::lean_ctor_get(v_x_203_, 0);
        leanh::lean_inc(v_a_208_);
        leanh::lean_dec_ref_known(v_x_203_, 1);
        v___x_209_ = leanh::lean_apply_1(v_h__1_204_, v_a_208_);
        return v___x_209_;
    }
}
pub unsafe fn l___private_Std_Do_WP_SimpLemmas_0__Std_Do_PredTrans_pushOption_match__1_splitter___redArg(
    mut v_x_210_: *mut leanh::LeanObject,
    mut v_h__1_211_: *mut leanh::LeanObject,
    mut v_h__2_212_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_210_) == 0 {
        let mut v___x_213_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_214_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_211_);
        v___x_213_ = leanh::lean_box(0);
        v___x_214_ = leanh::lean_apply_1(v_h__2_212_, v___x_213_);
        return v___x_214_;
    } else {
        let mut v_val_215_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_216_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_212_);
        v_val_215_ = leanh::lean_ctor_get(v_x_210_, 0);
        leanh::lean_inc(v_val_215_);
        leanh::lean_dec_ref_known(v_x_210_, 1);
        v___x_216_ = leanh::lean_apply_1(v_h__1_211_, v_val_215_);
        return v___x_216_;
    }
}
pub unsafe fn l___private_Std_Do_WP_SimpLemmas_0__Std_Do_PredTrans_pushOption_match__1_splitter(
    mut v_00_u03b1_217_: *mut leanh::LeanObject,
    mut v_motive_218_: *mut leanh::LeanObject,
    mut v_x_219_: *mut leanh::LeanObject,
    mut v_h__1_220_: *mut leanh::LeanObject,
    mut v_h__2_221_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_219_) == 0 {
        let mut v___x_222_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_223_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_220_);
        v___x_222_ = leanh::lean_box(0);
        v___x_223_ = leanh::lean_apply_1(v_h__2_221_, v___x_222_);
        return v___x_223_;
    } else {
        let mut v_val_224_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_225_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_221_);
        v_val_224_ = leanh::lean_ctor_get(v_x_219_, 0);
        leanh::lean_inc(v_val_224_);
        leanh::lean_dec_ref_known(v_x_219_, 1);
        v___x_225_ = leanh::lean_apply_1(v_h__1_220_, v_val_224_);
        return v___x_225_;
    }
}
pub unsafe fn l___private_Std_Do_WP_SimpLemmas_0__Except_map_match__1_splitter___redArg(
    mut v_x_226_: *mut leanh::LeanObject,
    mut v_h__1_227_: *mut leanh::LeanObject,
    mut v_h__2_228_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_226_) == 0 {
        let mut v_a_229_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_230_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_228_);
        v_a_229_ = leanh::lean_ctor_get(v_x_226_, 0);
        leanh::lean_inc(v_a_229_);
        leanh::lean_dec_ref_known(v_x_226_, 1);
        v___x_230_ = leanh::lean_apply_1(v_h__1_227_, v_a_229_);
        return v___x_230_;
    } else {
        let mut v_a_231_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_232_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_227_);
        v_a_231_ = leanh::lean_ctor_get(v_x_226_, 0);
        leanh::lean_inc(v_a_231_);
        leanh::lean_dec_ref_known(v_x_226_, 1);
        v___x_232_ = leanh::lean_apply_1(v_h__2_228_, v_a_231_);
        return v___x_232_;
    }
}
pub unsafe fn l___private_Std_Do_WP_SimpLemmas_0__Except_map_match__1_splitter(
    mut v_00_u03b5_233_: *mut leanh::LeanObject,
    mut v_00_u03b1_234_: *mut leanh::LeanObject,
    mut v_motive_235_: *mut leanh::LeanObject,
    mut v_x_236_: *mut leanh::LeanObject,
    mut v_h__1_237_: *mut leanh::LeanObject,
    mut v_h__2_238_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_236_) == 0 {
        let mut v_a_239_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_240_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_238_);
        v_a_239_ = leanh::lean_ctor_get(v_x_236_, 0);
        leanh::lean_inc(v_a_239_);
        leanh::lean_dec_ref_known(v_x_236_, 1);
        v___x_240_ = leanh::lean_apply_1(v_h__1_237_, v_a_239_);
        return v___x_240_;
    } else {
        let mut v_a_241_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_242_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_237_);
        v_a_241_ = leanh::lean_ctor_get(v_x_236_, 0);
        leanh::lean_inc(v_a_241_);
        leanh::lean_dec_ref_known(v_x_236_, 1);
        v___x_242_ = leanh::lean_apply_1(v_h__2_238_, v_a_241_);
        return v___x_242_;
    }
}
pub unsafe fn l___private_Std_Do_WP_SimpLemmas_0__EStateM_run__bind_match__1_splitter___redArg(
    mut v_x_243_: *mut leanh::LeanObject,
    mut v_h__1_244_: *mut leanh::LeanObject,
    mut v_h__2_245_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_243_) == 0 {
        let mut v_a_246_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_247_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_248_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_245_);
        v_a_246_ = leanh::lean_ctor_get(v_x_243_, 0);
        leanh::lean_inc(v_a_246_);
        v_a_247_ = leanh::lean_ctor_get(v_x_243_, 1);
        leanh::lean_inc(v_a_247_);
        leanh::lean_dec_ref_known(v_x_243_, 2);
        v___x_248_ = leanh::lean_apply_2(v_h__1_244_, v_a_246_, v_a_247_);
        return v___x_248_;
    } else {
        let mut v_a_249_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_250_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_251_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_244_);
        v_a_249_ = leanh::lean_ctor_get(v_x_243_, 0);
        leanh::lean_inc(v_a_249_);
        v_a_250_ = leanh::lean_ctor_get(v_x_243_, 1);
        leanh::lean_inc(v_a_250_);
        leanh::lean_dec_ref_known(v_x_243_, 2);
        v___x_251_ = leanh::lean_apply_2(v_h__2_245_, v_a_249_, v_a_250_);
        return v___x_251_;
    }
}
pub unsafe fn l___private_Std_Do_WP_SimpLemmas_0__EStateM_run__bind_match__1_splitter(
    mut v_00_u03b5_252_: *mut leanh::LeanObject,
    mut v_00_u03c3_253_: *mut leanh::LeanObject,
    mut v_00_u03b1_254_: *mut leanh::LeanObject,
    mut v_motive_255_: *mut leanh::LeanObject,
    mut v_x_256_: *mut leanh::LeanObject,
    mut v_h__1_257_: *mut leanh::LeanObject,
    mut v_h__2_258_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_256_) == 0 {
        let mut v_a_259_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_260_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_261_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_258_);
        v_a_259_ = leanh::lean_ctor_get(v_x_256_, 0);
        leanh::lean_inc(v_a_259_);
        v_a_260_ = leanh::lean_ctor_get(v_x_256_, 1);
        leanh::lean_inc(v_a_260_);
        leanh::lean_dec_ref_known(v_x_256_, 2);
        v___x_261_ = leanh::lean_apply_2(v_h__1_257_, v_a_259_, v_a_260_);
        return v___x_261_;
    } else {
        let mut v_a_262_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_263_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_264_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_257_);
        v_a_262_ = leanh::lean_ctor_get(v_x_256_, 0);
        leanh::lean_inc(v_a_262_);
        v_a_263_ = leanh::lean_ctor_get(v_x_256_, 1);
        leanh::lean_inc(v_a_263_);
        leanh::lean_dec_ref_known(v_x_256_, 2);
        v___x_264_ = leanh::lean_apply_2(v_h__2_258_, v_a_262_, v_a_263_);
        return v___x_264_;
    }
}
pub unsafe fn l___private_Std_Do_WP_SimpLemmas_0__Std_Do_EStateM_instWP_match__1_splitter___redArg(
    mut v_x_265_: *mut leanh::LeanObject,
    mut v_h__1_266_: *mut leanh::LeanObject,
    mut v_h__2_267_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_265_) == 0 {
        let mut v_a_268_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_269_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_270_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_267_);
        v_a_268_ = leanh::lean_ctor_get(v_x_265_, 0);
        leanh::lean_inc(v_a_268_);
        v_a_269_ = leanh::lean_ctor_get(v_x_265_, 1);
        leanh::lean_inc(v_a_269_);
        leanh::lean_dec_ref_known(v_x_265_, 2);
        v___x_270_ = leanh::lean_apply_2(v_h__1_266_, v_a_268_, v_a_269_);
        return v___x_270_;
    } else {
        let mut v_a_271_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_272_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_273_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_266_);
        v_a_271_ = leanh::lean_ctor_get(v_x_265_, 0);
        leanh::lean_inc(v_a_271_);
        v_a_272_ = leanh::lean_ctor_get(v_x_265_, 1);
        leanh::lean_inc(v_a_272_);
        leanh::lean_dec_ref_known(v_x_265_, 2);
        v___x_273_ = leanh::lean_apply_2(v_h__2_267_, v_a_271_, v_a_272_);
        return v___x_273_;
    }
}
pub unsafe fn l___private_Std_Do_WP_SimpLemmas_0__Std_Do_EStateM_instWP_match__1_splitter(
    mut v_00_u03b5_274_: *mut leanh::LeanObject,
    mut v_00_u03c3_275_: *mut leanh::LeanObject,
    mut v_00_u03b1_276_: *mut leanh::LeanObject,
    mut v_motive_277_: *mut leanh::LeanObject,
    mut v_x_278_: *mut leanh::LeanObject,
    mut v_h__1_279_: *mut leanh::LeanObject,
    mut v_h__2_280_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_278_) == 0 {
        let mut v_a_281_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_282_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_283_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_280_);
        v_a_281_ = leanh::lean_ctor_get(v_x_278_, 0);
        leanh::lean_inc(v_a_281_);
        v_a_282_ = leanh::lean_ctor_get(v_x_278_, 1);
        leanh::lean_inc(v_a_282_);
        leanh::lean_dec_ref_known(v_x_278_, 2);
        v___x_283_ = leanh::lean_apply_2(v_h__1_279_, v_a_281_, v_a_282_);
        return v___x_283_;
    } else {
        let mut v_a_284_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_285_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_286_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_279_);
        v_a_284_ = leanh::lean_ctor_get(v_x_278_, 0);
        leanh::lean_inc(v_a_284_);
        v_a_285_ = leanh::lean_ctor_get(v_x_278_, 1);
        leanh::lean_inc(v_a_285_);
        leanh::lean_dec_ref_known(v_x_278_, 2);
        v___x_286_ = leanh::lean_apply_2(v_h__2_280_, v_a_284_, v_a_285_);
        return v___x_286_;
    }
}
pub unsafe fn l___private_Std_Do_WP_SimpLemmas_0__Except_toBool_match__1_splitter___redArg(
    mut v_x_287_: *mut leanh::LeanObject,
    mut v_h__1_288_: *mut leanh::LeanObject,
    mut v_h__2_289_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_287_) == 0 {
        let mut v_a_290_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_291_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_288_);
        v_a_290_ = leanh::lean_ctor_get(v_x_287_, 0);
        leanh::lean_inc(v_a_290_);
        leanh::lean_dec_ref_known(v_x_287_, 1);
        v___x_291_ = leanh::lean_apply_1(v_h__2_289_, v_a_290_);
        return v___x_291_;
    } else {
        let mut v_a_292_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_293_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_289_);
        v_a_292_ = leanh::lean_ctor_get(v_x_287_, 0);
        leanh::lean_inc(v_a_292_);
        leanh::lean_dec_ref_known(v_x_287_, 1);
        v___x_293_ = leanh::lean_apply_1(v_h__1_288_, v_a_292_);
        return v___x_293_;
    }
}
pub unsafe fn l___private_Std_Do_WP_SimpLemmas_0__Except_toBool_match__1_splitter(
    mut v_00_u03b5_294_: *mut leanh::LeanObject,
    mut v_00_u03b1_295_: *mut leanh::LeanObject,
    mut v_motive_296_: *mut leanh::LeanObject,
    mut v_x_297_: *mut leanh::LeanObject,
    mut v_h__1_298_: *mut leanh::LeanObject,
    mut v_h__2_299_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_297_) == 0 {
        let mut v_a_300_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_301_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_298_);
        v_a_300_ = leanh::lean_ctor_get(v_x_297_, 0);
        leanh::lean_inc(v_a_300_);
        leanh::lean_dec_ref_known(v_x_297_, 1);
        v___x_301_ = leanh::lean_apply_1(v_h__2_299_, v_a_300_);
        return v___x_301_;
    } else {
        let mut v_a_302_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_303_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_299_);
        v_a_302_ = leanh::lean_ctor_get(v_x_297_, 0);
        leanh::lean_inc(v_a_302_);
        leanh::lean_dec_ref_known(v_x_297_, 1);
        v___x_303_ = leanh::lean_apply_1(v_h__1_298_, v_a_302_);
        return v___x_303_;
    }
}
pub unsafe fn l___private_Std_Do_WP_SimpLemmas_0__ExceptT_bindCont_match__1_splitter___redArg(
    mut v_x_304_: *mut leanh::LeanObject,
    mut v_h__1_305_: *mut leanh::LeanObject,
    mut v_h__2_306_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_304_) == 0 {
        let mut v_a_307_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_308_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_305_);
        v_a_307_ = leanh::lean_ctor_get(v_x_304_, 0);
        leanh::lean_inc(v_a_307_);
        leanh::lean_dec_ref_known(v_x_304_, 1);
        v___x_308_ = leanh::lean_apply_1(v_h__2_306_, v_a_307_);
        return v___x_308_;
    } else {
        let mut v_a_309_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_310_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_306_);
        v_a_309_ = leanh::lean_ctor_get(v_x_304_, 0);
        leanh::lean_inc(v_a_309_);
        leanh::lean_dec_ref_known(v_x_304_, 1);
        v___x_310_ = leanh::lean_apply_1(v_h__1_305_, v_a_309_);
        return v___x_310_;
    }
}
pub unsafe fn l___private_Std_Do_WP_SimpLemmas_0__ExceptT_bindCont_match__1_splitter(
    mut v_00_u03b5_311_: *mut leanh::LeanObject,
    mut v_00_u03b1_312_: *mut leanh::LeanObject,
    mut v_motive_313_: *mut leanh::LeanObject,
    mut v_x_314_: *mut leanh::LeanObject,
    mut v_h__1_315_: *mut leanh::LeanObject,
    mut v_h__2_316_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_314_) == 0 {
        let mut v_a_317_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_318_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_315_);
        v_a_317_ = leanh::lean_ctor_get(v_x_314_, 0);
        leanh::lean_inc(v_a_317_);
        leanh::lean_dec_ref_known(v_x_314_, 1);
        v___x_318_ = leanh::lean_apply_1(v_h__2_316_, v_a_317_);
        return v___x_318_;
    } else {
        let mut v_a_319_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_320_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_316_);
        v_a_319_ = leanh::lean_ctor_get(v_x_314_, 0);
        leanh::lean_inc(v_a_319_);
        leanh::lean_dec_ref_known(v_x_314_, 1);
        v___x_320_ = leanh::lean_apply_1(v_h__1_315_, v_a_319_);
        return v___x_320_;
    }
}
pub unsafe fn l___private_Std_Do_WP_SimpLemmas_0__Option_isSome_match__1_splitter___redArg(
    mut v_x_321_: *mut leanh::LeanObject,
    mut v_h__1_322_: *mut leanh::LeanObject,
    mut v_h__2_323_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_321_) == 0 {
        let mut v___x_324_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_325_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_322_);
        v___x_324_ = leanh::lean_box(0);
        v___x_325_ = leanh::lean_apply_1(v_h__2_323_, v___x_324_);
        return v___x_325_;
    } else {
        let mut v_val_326_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_327_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_323_);
        v_val_326_ = leanh::lean_ctor_get(v_x_321_, 0);
        leanh::lean_inc(v_val_326_);
        leanh::lean_dec_ref_known(v_x_321_, 1);
        v___x_327_ = leanh::lean_apply_1(v_h__1_322_, v_val_326_);
        return v___x_327_;
    }
}
pub unsafe fn l___private_Std_Do_WP_SimpLemmas_0__Option_isSome_match__1_splitter(
    mut v_00_u03b1_328_: *mut leanh::LeanObject,
    mut v_motive_329_: *mut leanh::LeanObject,
    mut v_x_330_: *mut leanh::LeanObject,
    mut v_h__1_331_: *mut leanh::LeanObject,
    mut v_h__2_332_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_330_) == 0 {
        let mut v___x_333_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_334_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_331_);
        v___x_333_ = leanh::lean_box(0);
        v___x_334_ = leanh::lean_apply_1(v_h__2_332_, v___x_333_);
        return v___x_334_;
    } else {
        let mut v_val_335_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_336_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_332_);
        v_val_335_ = leanh::lean_ctor_get(v_x_330_, 0);
        leanh::lean_inc(v_val_335_);
        leanh::lean_dec_ref_known(v_x_330_, 1);
        v___x_336_ = leanh::lean_apply_1(v_h__1_331_, v_val_335_);
        return v___x_336_;
    }
}
pub unsafe fn l___private_Std_Do_WP_SimpLemmas_0__OptionT_orElse_match__1_splitter___redArg(
    mut v_____do__lift_337_: *mut leanh::LeanObject,
    mut v_h__1_338_: *mut leanh::LeanObject,
    mut v_h__2_339_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_337_) == 1 {
        let mut v_val_340_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_341_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_339_);
        v_val_340_ = leanh::lean_ctor_get(v_____do__lift_337_, 0);
        leanh::lean_inc(v_val_340_);
        leanh::lean_dec_ref_known(v_____do__lift_337_, 1);
        v___x_341_ = leanh::lean_apply_1(v_h__1_338_, v_val_340_);
        return v___x_341_;
    } else {
        let mut v___x_342_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_338_);
        v___x_342_ =
            leanh::lean_apply_2(v_h__2_339_, v_____do__lift_337_, leanh::lean_box(0));
        return v___x_342_;
    }
}
pub unsafe fn l___private_Std_Do_WP_SimpLemmas_0__OptionT_orElse_match__1_splitter(
    mut v_00_u03b1_343_: *mut leanh::LeanObject,
    mut v_motive_344_: *mut leanh::LeanObject,
    mut v_____do__lift_345_: *mut leanh::LeanObject,
    mut v_h__1_346_: *mut leanh::LeanObject,
    mut v_h__2_347_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_345_) == 1 {
        let mut v_val_348_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_349_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_347_);
        v_val_348_ = leanh::lean_ctor_get(v_____do__lift_345_, 0);
        leanh::lean_inc(v_val_348_);
        leanh::lean_dec_ref_known(v_____do__lift_345_, 1);
        v___x_349_ = leanh::lean_apply_1(v_h__1_346_, v_val_348_);
        return v___x_349_;
    } else {
        let mut v___x_350_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_346_);
        v___x_350_ =
            leanh::lean_apply_2(v_h__2_347_, v_____do__lift_345_, leanh::lean_box(0));
        return v___x_350_;
    }
}
pub unsafe fn l___private_Std_Do_WP_SimpLemmas_0__EStateM_tryCatch_match__1_splitter___redArg(
    mut v_x_351_: *mut leanh::LeanObject,
    mut v_h__1_352_: *mut leanh::LeanObject,
    mut v_h__2_353_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_351_) == 1 {
        let mut v_a_354_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_355_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_356_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_353_);
        v_a_354_ = leanh::lean_ctor_get(v_x_351_, 0);
        leanh::lean_inc(v_a_354_);
        v_a_355_ = leanh::lean_ctor_get(v_x_351_, 1);
        leanh::lean_inc(v_a_355_);
        leanh::lean_dec_ref_known(v_x_351_, 2);
        v___x_356_ = leanh::lean_apply_2(v_h__1_352_, v_a_354_, v_a_355_);
        return v___x_356_;
    } else {
        let mut v___x_357_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_352_);
        v___x_357_ = leanh::lean_apply_2(v_h__2_353_, v_x_351_, leanh::lean_box(0));
        return v___x_357_;
    }
}
pub unsafe fn l___private_Std_Do_WP_SimpLemmas_0__EStateM_tryCatch_match__1_splitter(
    mut v_00_u03b5_358_: *mut leanh::LeanObject,
    mut v_00_u03c3_359_: *mut leanh::LeanObject,
    mut v_00_u03b1_360_: *mut leanh::LeanObject,
    mut v_motive_361_: *mut leanh::LeanObject,
    mut v_x_362_: *mut leanh::LeanObject,
    mut v_h__1_363_: *mut leanh::LeanObject,
    mut v_h__2_364_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_362_) == 1 {
        let mut v_a_365_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_366_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_367_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_364_);
        v_a_365_ = leanh::lean_ctor_get(v_x_362_, 0);
        leanh::lean_inc(v_a_365_);
        v_a_366_ = leanh::lean_ctor_get(v_x_362_, 1);
        leanh::lean_inc(v_a_366_);
        leanh::lean_dec_ref_known(v_x_362_, 2);
        v___x_367_ = leanh::lean_apply_2(v_h__1_363_, v_a_365_, v_a_366_);
        return v___x_367_;
    } else {
        let mut v___x_368_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_363_);
        v___x_368_ = leanh::lean_apply_2(v_h__2_364_, v_x_362_, leanh::lean_box(0));
        return v___x_368_;
    }
}
pub unsafe fn l___private_Std_Do_WP_SimpLemmas_0__Option_orElse_match__1_splitter___redArg(
    mut v_x_369_: *mut leanh::LeanObject,
    mut v_x_370_: *mut leanh::LeanObject,
    mut v_h__1_371_: *mut leanh::LeanObject,
    mut v_h__2_372_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_369_) == 0 {
        let mut v___x_373_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_371_);
        v___x_373_ = leanh::lean_apply_1(v_h__2_372_, v_x_370_);
        return v___x_373_;
    } else {
        let mut v_val_374_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_375_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_372_);
        v_val_374_ = leanh::lean_ctor_get(v_x_369_, 0);
        leanh::lean_inc(v_val_374_);
        leanh::lean_dec_ref_known(v_x_369_, 1);
        v___x_375_ = leanh::lean_apply_2(v_h__1_371_, v_val_374_, v_x_370_);
        return v___x_375_;
    }
}
pub unsafe fn l___private_Std_Do_WP_SimpLemmas_0__Option_orElse_match__1_splitter(
    mut v_00_u03b1_376_: *mut leanh::LeanObject,
    mut v_motive_377_: *mut leanh::LeanObject,
    mut v_x_378_: *mut leanh::LeanObject,
    mut v_x_379_: *mut leanh::LeanObject,
    mut v_h__1_380_: *mut leanh::LeanObject,
    mut v_h__2_381_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_378_) == 0 {
        let mut v___x_382_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_380_);
        v___x_382_ = leanh::lean_apply_1(v_h__2_381_, v_x_379_);
        return v___x_382_;
    } else {
        let mut v_val_383_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_384_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_381_);
        v_val_383_ = leanh::lean_ctor_get(v_x_378_, 0);
        leanh::lean_inc(v_val_383_);
        leanh::lean_dec_ref_known(v_x_378_, 1);
        v___x_384_ = leanh::lean_apply_2(v_h__1_380_, v_val_383_, v_x_379_);
        return v___x_384_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Do_WP_SimpLemmas(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Do_WP_Monad(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Do_WP_SimpLemmas(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Do_WP_SimpLemmas(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Do_WP_Monad(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Do_WP_SimpLemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Do_WP_SimpLemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Do_WP_SimpLemmas(builtin);
}