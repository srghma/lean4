// Lean compiler output
// Module: Std.Internal.Do.WP.Lemmas
// Imports: Std.Internal.Do.WP.Basic
use crate::r#gen::Std::Internal::Do::WP::Basic::{
    initialize_Std_Internal_Do_WP_Basic, runtime_initialize_Std_Internal_Do_WP_Basic,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_apply_1, lean_apply_2, lean_box, lean_ctor_get, lean_dec,
    lean_dec_ref, lean_dec_ref_known, lean_inc, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_obj_tag,
};
pub unsafe fn l___private_Std_Internal_Do_WP_Lemmas_0__Except_toBool_match__1_splitter___redArg(
    mut v_x_177_: *mut LeanObject,
    mut v_h__1_178_: *mut LeanObject,
    mut v_h__2_179_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_177_) == 0 {
        let mut v_a_180_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_181_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_178_);
        v_a_180_ = lean_ctor_get(v_x_177_, 0);
        lean_inc(v_a_180_);
        lean_dec_ref_known(v_x_177_, 1);
        v___x_181_ = lean_apply_1(v_h__2_179_, v_a_180_);
        return v___x_181_;
    } else {
        let mut v_a_182_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_183_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_179_);
        v_a_182_ = lean_ctor_get(v_x_177_, 0);
        lean_inc(v_a_182_);
        lean_dec_ref_known(v_x_177_, 1);
        v___x_183_ = lean_apply_1(v_h__1_178_, v_a_182_);
        return v___x_183_;
    }
}
pub unsafe fn l___private_Std_Internal_Do_WP_Lemmas_0__Except_toBool_match__1_splitter(
    mut v_00_u03b5_184_: *mut LeanObject,
    mut v_00_u03b1_185_: *mut LeanObject,
    mut v_motive_186_: *mut LeanObject,
    mut v_x_187_: *mut LeanObject,
    mut v_h__1_188_: *mut LeanObject,
    mut v_h__2_189_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_187_) == 0 {
        let mut v_a_190_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_191_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_188_);
        v_a_190_ = lean_ctor_get(v_x_187_, 0);
        lean_inc(v_a_190_);
        lean_dec_ref_known(v_x_187_, 1);
        v___x_191_ = lean_apply_1(v_h__2_189_, v_a_190_);
        return v___x_191_;
    } else {
        let mut v_a_192_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_193_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_189_);
        v_a_192_ = lean_ctor_get(v_x_187_, 0);
        lean_inc(v_a_192_);
        lean_dec_ref_known(v_x_187_, 1);
        v___x_193_ = lean_apply_1(v_h__1_188_, v_a_192_);
        return v___x_193_;
    }
}
pub unsafe fn l___private_Std_Internal_Do_WP_Lemmas_0__Std_Internal_Do_Except_instWPMonad_match__1_splitter___redArg(
    mut v_x_194_: *mut LeanObject,
    mut v_h__1_195_: *mut LeanObject,
    mut v_h__2_196_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_194_) == 0 {
        let mut v_a_197_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_198_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_195_);
        v_a_197_ = lean_ctor_get(v_x_194_, 0);
        lean_inc(v_a_197_);
        lean_dec_ref_known(v_x_194_, 1);
        v___x_198_ = lean_apply_1(v_h__2_196_, v_a_197_);
        return v___x_198_;
    } else {
        let mut v_a_199_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_200_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_196_);
        v_a_199_ = lean_ctor_get(v_x_194_, 0);
        lean_inc(v_a_199_);
        lean_dec_ref_known(v_x_194_, 1);
        v___x_200_ = lean_apply_1(v_h__1_195_, v_a_199_);
        return v___x_200_;
    }
}
pub unsafe fn l___private_Std_Internal_Do_WP_Lemmas_0__Std_Internal_Do_Except_instWPMonad_match__1_splitter(
    mut v_00_u03b5_201_: *mut LeanObject,
    mut v_00_u03b1_202_: *mut LeanObject,
    mut v_motive_203_: *mut LeanObject,
    mut v_x_204_: *mut LeanObject,
    mut v_h__1_205_: *mut LeanObject,
    mut v_h__2_206_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_204_) == 0 {
        let mut v_a_207_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_208_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_205_);
        v_a_207_ = lean_ctor_get(v_x_204_, 0);
        lean_inc(v_a_207_);
        lean_dec_ref_known(v_x_204_, 1);
        v___x_208_ = lean_apply_1(v_h__2_206_, v_a_207_);
        return v___x_208_;
    } else {
        let mut v_a_209_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_210_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_206_);
        v_a_209_ = lean_ctor_get(v_x_204_, 0);
        lean_inc(v_a_209_);
        lean_dec_ref_known(v_x_204_, 1);
        v___x_210_ = lean_apply_1(v_h__1_205_, v_a_209_);
        return v___x_210_;
    }
}
pub unsafe fn l___private_Std_Internal_Do_WP_Lemmas_0__ExceptT_bindCont_match__1_splitter___redArg(
    mut v_x_211_: *mut LeanObject,
    mut v_h__1_212_: *mut LeanObject,
    mut v_h__2_213_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_211_) == 0 {
        let mut v_a_214_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_215_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_212_);
        v_a_214_ = lean_ctor_get(v_x_211_, 0);
        lean_inc(v_a_214_);
        lean_dec_ref_known(v_x_211_, 1);
        v___x_215_ = lean_apply_1(v_h__2_213_, v_a_214_);
        return v___x_215_;
    } else {
        let mut v_a_216_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_217_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_213_);
        v_a_216_ = lean_ctor_get(v_x_211_, 0);
        lean_inc(v_a_216_);
        lean_dec_ref_known(v_x_211_, 1);
        v___x_217_ = lean_apply_1(v_h__1_212_, v_a_216_);
        return v___x_217_;
    }
}
pub unsafe fn l___private_Std_Internal_Do_WP_Lemmas_0__ExceptT_bindCont_match__1_splitter(
    mut v_00_u03b5_218_: *mut LeanObject,
    mut v_00_u03b1_219_: *mut LeanObject,
    mut v_motive_220_: *mut LeanObject,
    mut v_x_221_: *mut LeanObject,
    mut v_h__1_222_: *mut LeanObject,
    mut v_h__2_223_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_221_) == 0 {
        let mut v_a_224_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_225_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_222_);
        v_a_224_ = lean_ctor_get(v_x_221_, 0);
        lean_inc(v_a_224_);
        lean_dec_ref_known(v_x_221_, 1);
        v___x_225_ = lean_apply_1(v_h__2_223_, v_a_224_);
        return v___x_225_;
    } else {
        let mut v_a_226_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_227_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_223_);
        v_a_226_ = lean_ctor_get(v_x_221_, 0);
        lean_inc(v_a_226_);
        lean_dec_ref_known(v_x_221_, 1);
        v___x_227_ = lean_apply_1(v_h__1_222_, v_a_226_);
        return v___x_227_;
    }
}
pub unsafe fn l___private_Std_Internal_Do_WP_Lemmas_0__ExceptT_run__tryCatch_match__1_splitter___redArg(
    mut v_r_228_: *mut LeanObject,
    mut v_h__1_229_: *mut LeanObject,
    mut v_h__2_230_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_r_228_) == 0 {
        let mut v_a_231_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_232_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_229_);
        v_a_231_ = lean_ctor_get(v_r_228_, 0);
        lean_inc(v_a_231_);
        lean_dec_ref_known(v_r_228_, 1);
        v___x_232_ = lean_apply_1(v_h__2_230_, v_a_231_);
        return v___x_232_;
    } else {
        let mut v_a_233_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_234_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_230_);
        v_a_233_ = lean_ctor_get(v_r_228_, 0);
        lean_inc(v_a_233_);
        lean_dec_ref_known(v_r_228_, 1);
        v___x_234_ = lean_apply_1(v_h__1_229_, v_a_233_);
        return v___x_234_;
    }
}
pub unsafe fn l___private_Std_Internal_Do_WP_Lemmas_0__ExceptT_run__tryCatch_match__1_splitter(
    mut v_00_u03b5_235_: *mut LeanObject,
    mut v_00_u03b1_236_: *mut LeanObject,
    mut v_motive_237_: *mut LeanObject,
    mut v_r_238_: *mut LeanObject,
    mut v_h__1_239_: *mut LeanObject,
    mut v_h__2_240_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_r_238_) == 0 {
        let mut v_a_241_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_242_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_239_);
        v_a_241_ = lean_ctor_get(v_r_238_, 0);
        lean_inc(v_a_241_);
        lean_dec_ref_known(v_r_238_, 1);
        v___x_242_ = lean_apply_1(v_h__2_240_, v_a_241_);
        return v___x_242_;
    } else {
        let mut v_a_243_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_244_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_240_);
        v_a_243_ = lean_ctor_get(v_r_238_, 0);
        lean_inc(v_a_243_);
        lean_dec_ref_known(v_r_238_, 1);
        v___x_244_ = lean_apply_1(v_h__1_239_, v_a_243_);
        return v___x_244_;
    }
}
pub unsafe fn l___private_Std_Internal_Do_WP_Lemmas_0__Option_isSome_match__1_splitter___redArg(
    mut v_x_245_: *mut LeanObject,
    mut v_h__1_246_: *mut LeanObject,
    mut v_h__2_247_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_245_) == 0 {
        let mut v___x_248_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_249_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_246_);
        v___x_248_ = lean_box(0);
        v___x_249_ = lean_apply_1(v_h__2_247_, v___x_248_);
        return v___x_249_;
    } else {
        let mut v_val_250_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_251_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_247_);
        v_val_250_ = lean_ctor_get(v_x_245_, 0);
        lean_inc(v_val_250_);
        lean_dec_ref_known(v_x_245_, 1);
        v___x_251_ = lean_apply_1(v_h__1_246_, v_val_250_);
        return v___x_251_;
    }
}
pub unsafe fn l___private_Std_Internal_Do_WP_Lemmas_0__Option_isSome_match__1_splitter(
    mut v_00_u03b1_252_: *mut LeanObject,
    mut v_motive_253_: *mut LeanObject,
    mut v_x_254_: *mut LeanObject,
    mut v_h__1_255_: *mut LeanObject,
    mut v_h__2_256_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_254_) == 0 {
        let mut v___x_257_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_258_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_255_);
        v___x_257_ = lean_box(0);
        v___x_258_ = lean_apply_1(v_h__2_256_, v___x_257_);
        return v___x_258_;
    } else {
        let mut v_val_259_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_260_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_256_);
        v_val_259_ = lean_ctor_get(v_x_254_, 0);
        lean_inc(v_val_259_);
        lean_dec_ref_known(v_x_254_, 1);
        v___x_260_ = lean_apply_1(v_h__1_255_, v_val_259_);
        return v___x_260_;
    }
}
pub unsafe fn l___private_Std_Internal_Do_WP_Lemmas_0__EStateM_tryCatch_match__1_splitter___redArg(
    mut v_x_261_: *mut LeanObject,
    mut v_h__1_262_: *mut LeanObject,
    mut v_h__2_263_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_261_) == 1 {
        let mut v_a_264_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_265_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_266_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_263_);
        v_a_264_ = lean_ctor_get(v_x_261_, 0);
        lean_inc(v_a_264_);
        v_a_265_ = lean_ctor_get(v_x_261_, 1);
        lean_inc(v_a_265_);
        lean_dec_ref_known(v_x_261_, 2);
        v___x_266_ = lean_apply_2(v_h__1_262_, v_a_264_, v_a_265_);
        return v___x_266_;
    } else {
        let mut v___x_267_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_262_);
        v___x_267_ = lean_apply_2(v_h__2_263_, v_x_261_, lean_box(0));
        return v___x_267_;
    }
}
pub unsafe fn l___private_Std_Internal_Do_WP_Lemmas_0__EStateM_tryCatch_match__1_splitter(
    mut v_00_u03b5_268_: *mut LeanObject,
    mut v_00_u03c3_269_: *mut LeanObject,
    mut v_00_u03b1_270_: *mut LeanObject,
    mut v_motive_271_: *mut LeanObject,
    mut v_x_272_: *mut LeanObject,
    mut v_h__1_273_: *mut LeanObject,
    mut v_h__2_274_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_272_) == 1 {
        let mut v_a_275_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_276_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_277_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_274_);
        v_a_275_ = lean_ctor_get(v_x_272_, 0);
        lean_inc(v_a_275_);
        v_a_276_ = lean_ctor_get(v_x_272_, 1);
        lean_inc(v_a_276_);
        lean_dec_ref_known(v_x_272_, 2);
        v___x_277_ = lean_apply_2(v_h__1_273_, v_a_275_, v_a_276_);
        return v___x_277_;
    } else {
        let mut v___x_278_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_273_);
        v___x_278_ = lean_apply_2(v_h__2_274_, v_x_272_, lean_box(0));
        return v___x_278_;
    }
}
pub unsafe fn l___private_Std_Internal_Do_WP_Lemmas_0__Std_Internal_Do_EStateM_instWPMonad_match__1_splitter___redArg(
    mut v_x_279_: *mut LeanObject,
    mut v_h__1_280_: *mut LeanObject,
    mut v_h__2_281_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_279_) == 0 {
        let mut v_a_282_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_283_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_284_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_281_);
        v_a_282_ = lean_ctor_get(v_x_279_, 0);
        lean_inc(v_a_282_);
        v_a_283_ = lean_ctor_get(v_x_279_, 1);
        lean_inc(v_a_283_);
        lean_dec_ref_known(v_x_279_, 2);
        v___x_284_ = lean_apply_2(v_h__1_280_, v_a_282_, v_a_283_);
        return v___x_284_;
    } else {
        let mut v_a_285_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_286_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_287_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_280_);
        v_a_285_ = lean_ctor_get(v_x_279_, 0);
        lean_inc(v_a_285_);
        v_a_286_ = lean_ctor_get(v_x_279_, 1);
        lean_inc(v_a_286_);
        lean_dec_ref_known(v_x_279_, 2);
        v___x_287_ = lean_apply_2(v_h__2_281_, v_a_285_, v_a_286_);
        return v___x_287_;
    }
}
pub unsafe fn l___private_Std_Internal_Do_WP_Lemmas_0__Std_Internal_Do_EStateM_instWPMonad_match__1_splitter(
    mut v_00_u03b5_288_: *mut LeanObject,
    mut v_00_u03c3_289_: *mut LeanObject,
    mut v_00_u03b1_290_: *mut LeanObject,
    mut v_motive_291_: *mut LeanObject,
    mut v_x_292_: *mut LeanObject,
    mut v_h__1_293_: *mut LeanObject,
    mut v_h__2_294_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_292_) == 0 {
        let mut v_a_295_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_296_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_297_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_294_);
        v_a_295_ = lean_ctor_get(v_x_292_, 0);
        lean_inc(v_a_295_);
        v_a_296_ = lean_ctor_get(v_x_292_, 1);
        lean_inc(v_a_296_);
        lean_dec_ref_known(v_x_292_, 2);
        v___x_297_ = lean_apply_2(v_h__1_293_, v_a_295_, v_a_296_);
        return v___x_297_;
    } else {
        let mut v_a_298_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_299_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_300_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_293_);
        v_a_298_ = lean_ctor_get(v_x_292_, 0);
        lean_inc(v_a_298_);
        v_a_299_ = lean_ctor_get(v_x_292_, 1);
        lean_inc(v_a_299_);
        lean_dec_ref_known(v_x_292_, 2);
        v___x_300_ = lean_apply_2(v_h__2_294_, v_a_298_, v_a_299_);
        return v___x_300_;
    }
}
pub unsafe fn l___private_Std_Internal_Do_WP_Lemmas_0__OptionT_orElse_match__1_splitter___redArg(
    mut v_____do__lift_301_: *mut LeanObject,
    mut v_h__1_302_: *mut LeanObject,
    mut v_h__2_303_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_301_) == 1 {
        let mut v_val_304_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_305_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_303_);
        v_val_304_ = lean_ctor_get(v_____do__lift_301_, 0);
        lean_inc(v_val_304_);
        lean_dec_ref_known(v_____do__lift_301_, 1);
        v___x_305_ = lean_apply_1(v_h__1_302_, v_val_304_);
        return v___x_305_;
    } else {
        let mut v___x_306_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_302_);
        v___x_306_ = lean_apply_2(v_h__2_303_, v_____do__lift_301_, lean_box(0));
        return v___x_306_;
    }
}
pub unsafe fn l___private_Std_Internal_Do_WP_Lemmas_0__OptionT_orElse_match__1_splitter(
    mut v_00_u03b1_307_: *mut LeanObject,
    mut v_motive_308_: *mut LeanObject,
    mut v_____do__lift_309_: *mut LeanObject,
    mut v_h__1_310_: *mut LeanObject,
    mut v_h__2_311_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_309_) == 1 {
        let mut v_val_312_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_313_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_311_);
        v_val_312_ = lean_ctor_get(v_____do__lift_309_, 0);
        lean_inc(v_val_312_);
        lean_dec_ref_known(v_____do__lift_309_, 1);
        v___x_313_ = lean_apply_1(v_h__1_310_, v_val_312_);
        return v___x_313_;
    } else {
        let mut v___x_314_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_310_);
        v___x_314_ = lean_apply_2(v_h__2_311_, v_____do__lift_309_, lean_box(0));
        return v___x_314_;
    }
}
pub unsafe fn l___private_Std_Internal_Do_WP_Lemmas_0__EStateM_adaptExcept_match__1_splitter___redArg(
    mut v_x_315_: *mut LeanObject,
    mut v_h__1_316_: *mut LeanObject,
    mut v_h__2_317_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_315_) == 0 {
        let mut v_a_318_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_319_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_320_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_316_);
        v_a_318_ = lean_ctor_get(v_x_315_, 0);
        lean_inc(v_a_318_);
        v_a_319_ = lean_ctor_get(v_x_315_, 1);
        lean_inc(v_a_319_);
        lean_dec_ref_known(v_x_315_, 2);
        v___x_320_ = lean_apply_2(v_h__2_317_, v_a_318_, v_a_319_);
        return v___x_320_;
    } else {
        let mut v_a_321_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_322_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_323_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_317_);
        v_a_321_ = lean_ctor_get(v_x_315_, 0);
        lean_inc(v_a_321_);
        v_a_322_ = lean_ctor_get(v_x_315_, 1);
        lean_inc(v_a_322_);
        lean_dec_ref_known(v_x_315_, 2);
        v___x_323_ = lean_apply_2(v_h__1_316_, v_a_321_, v_a_322_);
        return v___x_323_;
    }
}
pub unsafe fn l___private_Std_Internal_Do_WP_Lemmas_0__EStateM_adaptExcept_match__1_splitter(
    mut v_00_u03b5_324_: *mut LeanObject,
    mut v_00_u03c3_325_: *mut LeanObject,
    mut v_00_u03b1_326_: *mut LeanObject,
    mut v_motive_327_: *mut LeanObject,
    mut v_x_328_: *mut LeanObject,
    mut v_h__1_329_: *mut LeanObject,
    mut v_h__2_330_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_328_) == 0 {
        let mut v_a_331_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_332_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_333_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_329_);
        v_a_331_ = lean_ctor_get(v_x_328_, 0);
        lean_inc(v_a_331_);
        v_a_332_ = lean_ctor_get(v_x_328_, 1);
        lean_inc(v_a_332_);
        lean_dec_ref_known(v_x_328_, 2);
        v___x_333_ = lean_apply_2(v_h__2_330_, v_a_331_, v_a_332_);
        return v___x_333_;
    } else {
        let mut v_a_334_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_335_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_336_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_330_);
        v_a_334_ = lean_ctor_get(v_x_328_, 0);
        lean_inc(v_a_334_);
        v_a_335_ = lean_ctor_get(v_x_328_, 1);
        lean_inc(v_a_335_);
        lean_dec_ref_known(v_x_328_, 2);
        v___x_336_ = lean_apply_2(v_h__1_329_, v_a_334_, v_a_335_);
        return v___x_336_;
    }
}
pub unsafe fn l___private_Std_Internal_Do_WP_Lemmas_0__Option_orElse_match__1_splitter___redArg(
    mut v_x_337_: *mut LeanObject,
    mut v_x_338_: *mut LeanObject,
    mut v_h__1_339_: *mut LeanObject,
    mut v_h__2_340_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_337_) == 0 {
        let mut v___x_341_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_339_);
        v___x_341_ = lean_apply_1(v_h__2_340_, v_x_338_);
        return v___x_341_;
    } else {
        let mut v_val_342_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_343_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_340_);
        v_val_342_ = lean_ctor_get(v_x_337_, 0);
        lean_inc(v_val_342_);
        lean_dec_ref_known(v_x_337_, 1);
        v___x_343_ = lean_apply_2(v_h__1_339_, v_val_342_, v_x_338_);
        return v___x_343_;
    }
}
pub unsafe fn l___private_Std_Internal_Do_WP_Lemmas_0__Option_orElse_match__1_splitter(
    mut v_00_u03b1_344_: *mut LeanObject,
    mut v_motive_345_: *mut LeanObject,
    mut v_x_346_: *mut LeanObject,
    mut v_x_347_: *mut LeanObject,
    mut v_h__1_348_: *mut LeanObject,
    mut v_h__2_349_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_346_) == 0 {
        let mut v___x_350_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_348_);
        v___x_350_ = lean_apply_1(v_h__2_349_, v_x_347_);
        return v___x_350_;
    } else {
        let mut v_val_351_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_352_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_349_);
        v_val_351_ = lean_ctor_get(v_x_346_, 0);
        lean_inc(v_val_351_);
        lean_dec_ref_known(v_x_346_, 1);
        v___x_352_ = lean_apply_2(v_h__1_348_, v_val_351_, v_x_347_);
        return v___x_352_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Internal_Do_WP_Lemmas(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Internal_Do_WP_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Internal_Do_WP_Lemmas(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Internal_Do_WP_Lemmas(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Internal_Do_WP_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Internal_Do_WP_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Internal_Do_WP_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Internal_Do_WP_Lemmas(builtin);
}
