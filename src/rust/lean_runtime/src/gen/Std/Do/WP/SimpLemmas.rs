// Lean compiler output
// Module: Std.Do.WP.SimpLemmas
// Imports: Std.Do.WP.Monad
use crate::r#gen::Std::Do::WP::Monad::{
    initialize_Std_Do_WP_Monad, runtime_initialize_Std_Do_WP_Monad,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_apply_1, lean_apply_2, lean_box, lean_ctor_get, lean_dec,
    lean_dec_ref, lean_dec_ref_known, lean_inc, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_obj_tag,
};
pub unsafe fn l___private_Std_Do_WP_SimpLemmas_0__Std_Do_PredTrans_pushExcept_match__1_splitter___redArg(
    mut v_x_193_: *mut LeanObject,
    mut v_h__1_194_: *mut LeanObject,
    mut v_h__2_195_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_193_) == 0 {
        let mut v_a_196_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_197_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_194_);
        v_a_196_ = lean_ctor_get(v_x_193_, 0);
        lean_inc(v_a_196_);
        lean_dec_ref_known(v_x_193_, 1);
        v___x_197_ = lean_apply_1(v_h__2_195_, v_a_196_);
        return v___x_197_;
    } else {
        let mut v_a_198_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_199_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_195_);
        v_a_198_ = lean_ctor_get(v_x_193_, 0);
        lean_inc(v_a_198_);
        lean_dec_ref_known(v_x_193_, 1);
        v___x_199_ = lean_apply_1(v_h__1_194_, v_a_198_);
        return v___x_199_;
    }
}
pub unsafe fn l___private_Std_Do_WP_SimpLemmas_0__Std_Do_PredTrans_pushExcept_match__1_splitter(
    mut v_00_u03b1_200_: *mut LeanObject,
    mut v_00_u03b5_201_: *mut LeanObject,
    mut v_motive_202_: *mut LeanObject,
    mut v_x_203_: *mut LeanObject,
    mut v_h__1_204_: *mut LeanObject,
    mut v_h__2_205_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_203_) == 0 {
        let mut v_a_206_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_207_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_204_);
        v_a_206_ = lean_ctor_get(v_x_203_, 0);
        lean_inc(v_a_206_);
        lean_dec_ref_known(v_x_203_, 1);
        v___x_207_ = lean_apply_1(v_h__2_205_, v_a_206_);
        return v___x_207_;
    } else {
        let mut v_a_208_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_209_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_205_);
        v_a_208_ = lean_ctor_get(v_x_203_, 0);
        lean_inc(v_a_208_);
        lean_dec_ref_known(v_x_203_, 1);
        v___x_209_ = lean_apply_1(v_h__1_204_, v_a_208_);
        return v___x_209_;
    }
}
pub unsafe fn l___private_Std_Do_WP_SimpLemmas_0__Std_Do_PredTrans_pushOption_match__1_splitter___redArg(
    mut v_x_210_: *mut LeanObject,
    mut v_h__1_211_: *mut LeanObject,
    mut v_h__2_212_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_210_) == 0 {
        let mut v___x_213_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_214_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_211_);
        v___x_213_ = lean_box(0);
        v___x_214_ = lean_apply_1(v_h__2_212_, v___x_213_);
        return v___x_214_;
    } else {
        let mut v_val_215_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_216_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_212_);
        v_val_215_ = lean_ctor_get(v_x_210_, 0);
        lean_inc(v_val_215_);
        lean_dec_ref_known(v_x_210_, 1);
        v___x_216_ = lean_apply_1(v_h__1_211_, v_val_215_);
        return v___x_216_;
    }
}
pub unsafe fn l___private_Std_Do_WP_SimpLemmas_0__Std_Do_PredTrans_pushOption_match__1_splitter(
    mut v_00_u03b1_217_: *mut LeanObject,
    mut v_motive_218_: *mut LeanObject,
    mut v_x_219_: *mut LeanObject,
    mut v_h__1_220_: *mut LeanObject,
    mut v_h__2_221_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_219_) == 0 {
        let mut v___x_222_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_223_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_220_);
        v___x_222_ = lean_box(0);
        v___x_223_ = lean_apply_1(v_h__2_221_, v___x_222_);
        return v___x_223_;
    } else {
        let mut v_val_224_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_225_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_221_);
        v_val_224_ = lean_ctor_get(v_x_219_, 0);
        lean_inc(v_val_224_);
        lean_dec_ref_known(v_x_219_, 1);
        v___x_225_ = lean_apply_1(v_h__1_220_, v_val_224_);
        return v___x_225_;
    }
}
pub unsafe fn l___private_Std_Do_WP_SimpLemmas_0__Except_map_match__1_splitter___redArg(
    mut v_x_226_: *mut LeanObject,
    mut v_h__1_227_: *mut LeanObject,
    mut v_h__2_228_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_226_) == 0 {
        let mut v_a_229_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_230_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_228_);
        v_a_229_ = lean_ctor_get(v_x_226_, 0);
        lean_inc(v_a_229_);
        lean_dec_ref_known(v_x_226_, 1);
        v___x_230_ = lean_apply_1(v_h__1_227_, v_a_229_);
        return v___x_230_;
    } else {
        let mut v_a_231_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_232_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_227_);
        v_a_231_ = lean_ctor_get(v_x_226_, 0);
        lean_inc(v_a_231_);
        lean_dec_ref_known(v_x_226_, 1);
        v___x_232_ = lean_apply_1(v_h__2_228_, v_a_231_);
        return v___x_232_;
    }
}
pub unsafe fn l___private_Std_Do_WP_SimpLemmas_0__Except_map_match__1_splitter(
    mut v_00_u03b5_233_: *mut LeanObject,
    mut v_00_u03b1_234_: *mut LeanObject,
    mut v_motive_235_: *mut LeanObject,
    mut v_x_236_: *mut LeanObject,
    mut v_h__1_237_: *mut LeanObject,
    mut v_h__2_238_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_236_) == 0 {
        let mut v_a_239_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_240_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_238_);
        v_a_239_ = lean_ctor_get(v_x_236_, 0);
        lean_inc(v_a_239_);
        lean_dec_ref_known(v_x_236_, 1);
        v___x_240_ = lean_apply_1(v_h__1_237_, v_a_239_);
        return v___x_240_;
    } else {
        let mut v_a_241_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_242_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_237_);
        v_a_241_ = lean_ctor_get(v_x_236_, 0);
        lean_inc(v_a_241_);
        lean_dec_ref_known(v_x_236_, 1);
        v___x_242_ = lean_apply_1(v_h__2_238_, v_a_241_);
        return v___x_242_;
    }
}
pub unsafe fn l___private_Std_Do_WP_SimpLemmas_0__EStateM_run__bind_match__1_splitter___redArg(
    mut v_x_243_: *mut LeanObject,
    mut v_h__1_244_: *mut LeanObject,
    mut v_h__2_245_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_243_) == 0 {
        let mut v_a_246_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_247_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_248_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_245_);
        v_a_246_ = lean_ctor_get(v_x_243_, 0);
        lean_inc(v_a_246_);
        v_a_247_ = lean_ctor_get(v_x_243_, 1);
        lean_inc(v_a_247_);
        lean_dec_ref_known(v_x_243_, 2);
        v___x_248_ = lean_apply_2(v_h__1_244_, v_a_246_, v_a_247_);
        return v___x_248_;
    } else {
        let mut v_a_249_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_250_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_251_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_244_);
        v_a_249_ = lean_ctor_get(v_x_243_, 0);
        lean_inc(v_a_249_);
        v_a_250_ = lean_ctor_get(v_x_243_, 1);
        lean_inc(v_a_250_);
        lean_dec_ref_known(v_x_243_, 2);
        v___x_251_ = lean_apply_2(v_h__2_245_, v_a_249_, v_a_250_);
        return v___x_251_;
    }
}
pub unsafe fn l___private_Std_Do_WP_SimpLemmas_0__EStateM_run__bind_match__1_splitter(
    mut v_00_u03b5_252_: *mut LeanObject,
    mut v_00_u03c3_253_: *mut LeanObject,
    mut v_00_u03b1_254_: *mut LeanObject,
    mut v_motive_255_: *mut LeanObject,
    mut v_x_256_: *mut LeanObject,
    mut v_h__1_257_: *mut LeanObject,
    mut v_h__2_258_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_256_) == 0 {
        let mut v_a_259_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_260_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_261_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_258_);
        v_a_259_ = lean_ctor_get(v_x_256_, 0);
        lean_inc(v_a_259_);
        v_a_260_ = lean_ctor_get(v_x_256_, 1);
        lean_inc(v_a_260_);
        lean_dec_ref_known(v_x_256_, 2);
        v___x_261_ = lean_apply_2(v_h__1_257_, v_a_259_, v_a_260_);
        return v___x_261_;
    } else {
        let mut v_a_262_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_263_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_264_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_257_);
        v_a_262_ = lean_ctor_get(v_x_256_, 0);
        lean_inc(v_a_262_);
        v_a_263_ = lean_ctor_get(v_x_256_, 1);
        lean_inc(v_a_263_);
        lean_dec_ref_known(v_x_256_, 2);
        v___x_264_ = lean_apply_2(v_h__2_258_, v_a_262_, v_a_263_);
        return v___x_264_;
    }
}
pub unsafe fn l___private_Std_Do_WP_SimpLemmas_0__Std_Do_EStateM_instWP_match__1_splitter___redArg(
    mut v_x_265_: *mut LeanObject,
    mut v_h__1_266_: *mut LeanObject,
    mut v_h__2_267_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_265_) == 0 {
        let mut v_a_268_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_269_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_270_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_267_);
        v_a_268_ = lean_ctor_get(v_x_265_, 0);
        lean_inc(v_a_268_);
        v_a_269_ = lean_ctor_get(v_x_265_, 1);
        lean_inc(v_a_269_);
        lean_dec_ref_known(v_x_265_, 2);
        v___x_270_ = lean_apply_2(v_h__1_266_, v_a_268_, v_a_269_);
        return v___x_270_;
    } else {
        let mut v_a_271_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_272_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_273_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_266_);
        v_a_271_ = lean_ctor_get(v_x_265_, 0);
        lean_inc(v_a_271_);
        v_a_272_ = lean_ctor_get(v_x_265_, 1);
        lean_inc(v_a_272_);
        lean_dec_ref_known(v_x_265_, 2);
        v___x_273_ = lean_apply_2(v_h__2_267_, v_a_271_, v_a_272_);
        return v___x_273_;
    }
}
pub unsafe fn l___private_Std_Do_WP_SimpLemmas_0__Std_Do_EStateM_instWP_match__1_splitter(
    mut v_00_u03b5_274_: *mut LeanObject,
    mut v_00_u03c3_275_: *mut LeanObject,
    mut v_00_u03b1_276_: *mut LeanObject,
    mut v_motive_277_: *mut LeanObject,
    mut v_x_278_: *mut LeanObject,
    mut v_h__1_279_: *mut LeanObject,
    mut v_h__2_280_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_278_) == 0 {
        let mut v_a_281_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_282_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_283_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_280_);
        v_a_281_ = lean_ctor_get(v_x_278_, 0);
        lean_inc(v_a_281_);
        v_a_282_ = lean_ctor_get(v_x_278_, 1);
        lean_inc(v_a_282_);
        lean_dec_ref_known(v_x_278_, 2);
        v___x_283_ = lean_apply_2(v_h__1_279_, v_a_281_, v_a_282_);
        return v___x_283_;
    } else {
        let mut v_a_284_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_285_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_286_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_279_);
        v_a_284_ = lean_ctor_get(v_x_278_, 0);
        lean_inc(v_a_284_);
        v_a_285_ = lean_ctor_get(v_x_278_, 1);
        lean_inc(v_a_285_);
        lean_dec_ref_known(v_x_278_, 2);
        v___x_286_ = lean_apply_2(v_h__2_280_, v_a_284_, v_a_285_);
        return v___x_286_;
    }
}
pub unsafe fn l___private_Std_Do_WP_SimpLemmas_0__Except_toBool_match__1_splitter___redArg(
    mut v_x_287_: *mut LeanObject,
    mut v_h__1_288_: *mut LeanObject,
    mut v_h__2_289_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_287_) == 0 {
        let mut v_a_290_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_291_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_288_);
        v_a_290_ = lean_ctor_get(v_x_287_, 0);
        lean_inc(v_a_290_);
        lean_dec_ref_known(v_x_287_, 1);
        v___x_291_ = lean_apply_1(v_h__2_289_, v_a_290_);
        return v___x_291_;
    } else {
        let mut v_a_292_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_293_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_289_);
        v_a_292_ = lean_ctor_get(v_x_287_, 0);
        lean_inc(v_a_292_);
        lean_dec_ref_known(v_x_287_, 1);
        v___x_293_ = lean_apply_1(v_h__1_288_, v_a_292_);
        return v___x_293_;
    }
}
pub unsafe fn l___private_Std_Do_WP_SimpLemmas_0__Except_toBool_match__1_splitter(
    mut v_00_u03b5_294_: *mut LeanObject,
    mut v_00_u03b1_295_: *mut LeanObject,
    mut v_motive_296_: *mut LeanObject,
    mut v_x_297_: *mut LeanObject,
    mut v_h__1_298_: *mut LeanObject,
    mut v_h__2_299_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_297_) == 0 {
        let mut v_a_300_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_301_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_298_);
        v_a_300_ = lean_ctor_get(v_x_297_, 0);
        lean_inc(v_a_300_);
        lean_dec_ref_known(v_x_297_, 1);
        v___x_301_ = lean_apply_1(v_h__2_299_, v_a_300_);
        return v___x_301_;
    } else {
        let mut v_a_302_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_303_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_299_);
        v_a_302_ = lean_ctor_get(v_x_297_, 0);
        lean_inc(v_a_302_);
        lean_dec_ref_known(v_x_297_, 1);
        v___x_303_ = lean_apply_1(v_h__1_298_, v_a_302_);
        return v___x_303_;
    }
}
pub unsafe fn l___private_Std_Do_WP_SimpLemmas_0__ExceptT_bindCont_match__1_splitter___redArg(
    mut v_x_304_: *mut LeanObject,
    mut v_h__1_305_: *mut LeanObject,
    mut v_h__2_306_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_304_) == 0 {
        let mut v_a_307_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_308_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_305_);
        v_a_307_ = lean_ctor_get(v_x_304_, 0);
        lean_inc(v_a_307_);
        lean_dec_ref_known(v_x_304_, 1);
        v___x_308_ = lean_apply_1(v_h__2_306_, v_a_307_);
        return v___x_308_;
    } else {
        let mut v_a_309_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_310_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_306_);
        v_a_309_ = lean_ctor_get(v_x_304_, 0);
        lean_inc(v_a_309_);
        lean_dec_ref_known(v_x_304_, 1);
        v___x_310_ = lean_apply_1(v_h__1_305_, v_a_309_);
        return v___x_310_;
    }
}
pub unsafe fn l___private_Std_Do_WP_SimpLemmas_0__ExceptT_bindCont_match__1_splitter(
    mut v_00_u03b5_311_: *mut LeanObject,
    mut v_00_u03b1_312_: *mut LeanObject,
    mut v_motive_313_: *mut LeanObject,
    mut v_x_314_: *mut LeanObject,
    mut v_h__1_315_: *mut LeanObject,
    mut v_h__2_316_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_314_) == 0 {
        let mut v_a_317_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_318_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_315_);
        v_a_317_ = lean_ctor_get(v_x_314_, 0);
        lean_inc(v_a_317_);
        lean_dec_ref_known(v_x_314_, 1);
        v___x_318_ = lean_apply_1(v_h__2_316_, v_a_317_);
        return v___x_318_;
    } else {
        let mut v_a_319_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_320_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_316_);
        v_a_319_ = lean_ctor_get(v_x_314_, 0);
        lean_inc(v_a_319_);
        lean_dec_ref_known(v_x_314_, 1);
        v___x_320_ = lean_apply_1(v_h__1_315_, v_a_319_);
        return v___x_320_;
    }
}
pub unsafe fn l___private_Std_Do_WP_SimpLemmas_0__Option_isSome_match__1_splitter___redArg(
    mut v_x_321_: *mut LeanObject,
    mut v_h__1_322_: *mut LeanObject,
    mut v_h__2_323_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_321_) == 0 {
        let mut v___x_324_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_325_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_322_);
        v___x_324_ = lean_box(0);
        v___x_325_ = lean_apply_1(v_h__2_323_, v___x_324_);
        return v___x_325_;
    } else {
        let mut v_val_326_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_327_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_323_);
        v_val_326_ = lean_ctor_get(v_x_321_, 0);
        lean_inc(v_val_326_);
        lean_dec_ref_known(v_x_321_, 1);
        v___x_327_ = lean_apply_1(v_h__1_322_, v_val_326_);
        return v___x_327_;
    }
}
pub unsafe fn l___private_Std_Do_WP_SimpLemmas_0__Option_isSome_match__1_splitter(
    mut v_00_u03b1_328_: *mut LeanObject,
    mut v_motive_329_: *mut LeanObject,
    mut v_x_330_: *mut LeanObject,
    mut v_h__1_331_: *mut LeanObject,
    mut v_h__2_332_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_330_) == 0 {
        let mut v___x_333_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_334_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_331_);
        v___x_333_ = lean_box(0);
        v___x_334_ = lean_apply_1(v_h__2_332_, v___x_333_);
        return v___x_334_;
    } else {
        let mut v_val_335_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_336_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_332_);
        v_val_335_ = lean_ctor_get(v_x_330_, 0);
        lean_inc(v_val_335_);
        lean_dec_ref_known(v_x_330_, 1);
        v___x_336_ = lean_apply_1(v_h__1_331_, v_val_335_);
        return v___x_336_;
    }
}
pub unsafe fn l___private_Std_Do_WP_SimpLemmas_0__OptionT_orElse_match__1_splitter___redArg(
    mut v_____do__lift_337_: *mut LeanObject,
    mut v_h__1_338_: *mut LeanObject,
    mut v_h__2_339_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_337_) == 1 {
        let mut v_val_340_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_341_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_339_);
        v_val_340_ = lean_ctor_get(v_____do__lift_337_, 0);
        lean_inc(v_val_340_);
        lean_dec_ref_known(v_____do__lift_337_, 1);
        v___x_341_ = lean_apply_1(v_h__1_338_, v_val_340_);
        return v___x_341_;
    } else {
        let mut v___x_342_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_338_);
        v___x_342_ = lean_apply_2(v_h__2_339_, v_____do__lift_337_, lean_box(0));
        return v___x_342_;
    }
}
pub unsafe fn l___private_Std_Do_WP_SimpLemmas_0__OptionT_orElse_match__1_splitter(
    mut v_00_u03b1_343_: *mut LeanObject,
    mut v_motive_344_: *mut LeanObject,
    mut v_____do__lift_345_: *mut LeanObject,
    mut v_h__1_346_: *mut LeanObject,
    mut v_h__2_347_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_345_) == 1 {
        let mut v_val_348_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_349_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_347_);
        v_val_348_ = lean_ctor_get(v_____do__lift_345_, 0);
        lean_inc(v_val_348_);
        lean_dec_ref_known(v_____do__lift_345_, 1);
        v___x_349_ = lean_apply_1(v_h__1_346_, v_val_348_);
        return v___x_349_;
    } else {
        let mut v___x_350_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_346_);
        v___x_350_ = lean_apply_2(v_h__2_347_, v_____do__lift_345_, lean_box(0));
        return v___x_350_;
    }
}
pub unsafe fn l___private_Std_Do_WP_SimpLemmas_0__EStateM_tryCatch_match__1_splitter___redArg(
    mut v_x_351_: *mut LeanObject,
    mut v_h__1_352_: *mut LeanObject,
    mut v_h__2_353_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_351_) == 1 {
        let mut v_a_354_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_355_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_356_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_353_);
        v_a_354_ = lean_ctor_get(v_x_351_, 0);
        lean_inc(v_a_354_);
        v_a_355_ = lean_ctor_get(v_x_351_, 1);
        lean_inc(v_a_355_);
        lean_dec_ref_known(v_x_351_, 2);
        v___x_356_ = lean_apply_2(v_h__1_352_, v_a_354_, v_a_355_);
        return v___x_356_;
    } else {
        let mut v___x_357_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_352_);
        v___x_357_ = lean_apply_2(v_h__2_353_, v_x_351_, lean_box(0));
        return v___x_357_;
    }
}
pub unsafe fn l___private_Std_Do_WP_SimpLemmas_0__EStateM_tryCatch_match__1_splitter(
    mut v_00_u03b5_358_: *mut LeanObject,
    mut v_00_u03c3_359_: *mut LeanObject,
    mut v_00_u03b1_360_: *mut LeanObject,
    mut v_motive_361_: *mut LeanObject,
    mut v_x_362_: *mut LeanObject,
    mut v_h__1_363_: *mut LeanObject,
    mut v_h__2_364_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_362_) == 1 {
        let mut v_a_365_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_366_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_367_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_364_);
        v_a_365_ = lean_ctor_get(v_x_362_, 0);
        lean_inc(v_a_365_);
        v_a_366_ = lean_ctor_get(v_x_362_, 1);
        lean_inc(v_a_366_);
        lean_dec_ref_known(v_x_362_, 2);
        v___x_367_ = lean_apply_2(v_h__1_363_, v_a_365_, v_a_366_);
        return v___x_367_;
    } else {
        let mut v___x_368_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_363_);
        v___x_368_ = lean_apply_2(v_h__2_364_, v_x_362_, lean_box(0));
        return v___x_368_;
    }
}
pub unsafe fn l___private_Std_Do_WP_SimpLemmas_0__Option_orElse_match__1_splitter___redArg(
    mut v_x_369_: *mut LeanObject,
    mut v_x_370_: *mut LeanObject,
    mut v_h__1_371_: *mut LeanObject,
    mut v_h__2_372_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_369_) == 0 {
        let mut v___x_373_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_371_);
        v___x_373_ = lean_apply_1(v_h__2_372_, v_x_370_);
        return v___x_373_;
    } else {
        let mut v_val_374_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_375_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_372_);
        v_val_374_ = lean_ctor_get(v_x_369_, 0);
        lean_inc(v_val_374_);
        lean_dec_ref_known(v_x_369_, 1);
        v___x_375_ = lean_apply_2(v_h__1_371_, v_val_374_, v_x_370_);
        return v___x_375_;
    }
}
pub unsafe fn l___private_Std_Do_WP_SimpLemmas_0__Option_orElse_match__1_splitter(
    mut v_00_u03b1_376_: *mut LeanObject,
    mut v_motive_377_: *mut LeanObject,
    mut v_x_378_: *mut LeanObject,
    mut v_x_379_: *mut LeanObject,
    mut v_h__1_380_: *mut LeanObject,
    mut v_h__2_381_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_378_) == 0 {
        let mut v___x_382_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_380_);
        v___x_382_ = lean_apply_1(v_h__2_381_, v_x_379_);
        return v___x_382_;
    } else {
        let mut v_val_383_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_384_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_381_);
        v_val_383_ = lean_ctor_get(v_x_378_, 0);
        lean_inc(v_val_383_);
        lean_dec_ref_known(v_x_378_, 1);
        v___x_384_ = lean_apply_2(v_h__1_380_, v_val_383_, v_x_379_);
        return v___x_384_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Do_WP_SimpLemmas(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Do_WP_Monad(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Do_WP_SimpLemmas(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Do_WP_SimpLemmas(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Do_WP_Monad(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Do_WP_SimpLemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Do_WP_SimpLemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Do_WP_SimpLemmas(builtin);
}
