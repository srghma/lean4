// Lean compiler output
// Module: Init.Data.Option.Lemmas
// Imports: Init.Data.Option.BasicAux Init.Data.Option.Instances Init.Data.Option.Instances Init.Ext Init.Data.Option.BasicAux Init.PropLemmas Init.Classical Init.Data.BEq Init.Data.Bool
use crate::r#gen::Init::Classical::{initialize_Init_Classical, runtime_initialize_Init_Classical};
use crate::r#gen::Init::Data::BEq::{initialize_Init_Data_BEq, runtime_initialize_Init_Data_BEq};
use crate::r#gen::Init::Data::Bool::{
    initialize_Init_Data_Bool, runtime_initialize_Init_Data_Bool,
};
use crate::r#gen::Init::Data::Option::BasicAux::{
    initialize_Init_Data_Option_BasicAux, runtime_initialize_Init_Data_Option_BasicAux,
};
use crate::r#gen::Init::Data::Option::Instances::{
    initialize_Init_Data_Option_Instances, runtime_initialize_Init_Data_Option_Instances,
};
use crate::r#gen::Init::Ext::{initialize_Init_Ext, runtime_initialize_Init_Ext};
use crate::r#gen::Init::PropLemmas::{
    initialize_Init_PropLemmas, runtime_initialize_Init_PropLemmas,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_apply_1, lean_apply_2, lean_apply_4, lean_box,
    lean_ctor_get, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_obj_tag,
};
pub unsafe fn l___private_Init_Data_Option_Lemmas_0__Option_isSome_match__1_splitter___redArg(
    mut v_x_174_: *mut LeanObject,
    mut v_h__1_175_: *mut LeanObject,
    mut v_h__2_176_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_174_) == 0 {
        let mut v___x_177_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_178_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_175_);
        v___x_177_ = lean_box(0);
        v___x_178_ = lean_apply_1(v_h__2_176_, v___x_177_);
        return v___x_178_;
    } else {
        let mut v_val_179_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_180_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_176_);
        v_val_179_ = lean_ctor_get(v_x_174_, 0);
        lean_inc(v_val_179_);
        lean_dec_ref_known(v_x_174_, 1);
        v___x_180_ = lean_apply_1(v_h__1_175_, v_val_179_);
        return v___x_180_;
    }
}
pub unsafe fn l___private_Init_Data_Option_Lemmas_0__Option_isSome_match__1_splitter(
    mut v_00_u03b1_181_: *mut LeanObject,
    mut v_motive_182_: *mut LeanObject,
    mut v_x_183_: *mut LeanObject,
    mut v_h__1_184_: *mut LeanObject,
    mut v_h__2_185_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_183_) == 0 {
        let mut v___x_186_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_187_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_184_);
        v___x_186_ = lean_box(0);
        v___x_187_ = lean_apply_1(v_h__2_185_, v___x_186_);
        return v___x_187_;
    } else {
        let mut v_val_188_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_189_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_185_);
        v_val_188_ = lean_ctor_get(v_x_183_, 0);
        lean_inc(v_val_188_);
        lean_dec_ref_known(v_x_183_, 1);
        v___x_189_ = lean_apply_1(v_h__1_184_, v_val_188_);
        return v___x_189_;
    }
}
pub unsafe fn l___private_Init_Data_Option_Lemmas_0__Option_bind_match__1_splitter___redArg(
    mut v_x_190_: *mut LeanObject,
    mut v_x_191_: *mut LeanObject,
    mut v_h__1_192_: *mut LeanObject,
    mut v_h__2_193_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_190_) == 0 {
        let mut v___x_194_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_193_);
        v___x_194_ = lean_apply_1(v_h__1_192_, v_x_191_);
        return v___x_194_;
    } else {
        let mut v_val_195_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_196_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_192_);
        v_val_195_ = lean_ctor_get(v_x_190_, 0);
        lean_inc(v_val_195_);
        lean_dec_ref_known(v_x_190_, 1);
        v___x_196_ = lean_apply_2(v_h__2_193_, v_val_195_, v_x_191_);
        return v___x_196_;
    }
}
pub unsafe fn l___private_Init_Data_Option_Lemmas_0__Option_bind_match__1_splitter(
    mut v_00_u03b1_197_: *mut LeanObject,
    mut v_00_u03b2_198_: *mut LeanObject,
    mut v_motive_199_: *mut LeanObject,
    mut v_x_200_: *mut LeanObject,
    mut v_x_201_: *mut LeanObject,
    mut v_h__1_202_: *mut LeanObject,
    mut v_h__2_203_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_200_) == 0 {
        let mut v___x_204_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_203_);
        v___x_204_ = lean_apply_1(v_h__1_202_, v_x_201_);
        return v___x_204_;
    } else {
        let mut v_val_205_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_206_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_202_);
        v_val_205_ = lean_ctor_get(v_x_200_, 0);
        lean_inc(v_val_205_);
        lean_dec_ref_known(v_x_200_, 1);
        v___x_206_ = lean_apply_2(v_h__2_203_, v_val_205_, v_x_201_);
        return v___x_206_;
    }
}
pub unsafe fn l___private_Init_Data_Option_Lemmas_0__Option_merge_match__1_splitter___redArg(
    mut v_x_207_: *mut LeanObject,
    mut v_x_208_: *mut LeanObject,
    mut v_h__1_209_: *mut LeanObject,
    mut v_h__2_210_: *mut LeanObject,
    mut v_h__3_211_: *mut LeanObject,
    mut v_h__4_212_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_207_) == 0 {
        lean_dec(v_h__4_212_);
        lean_dec(v_h__2_210_);
        if lean_obj_tag(v_x_208_) == 0 {
            let mut v___x_213_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_214_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_211_);
            v___x_213_ = lean_box(0);
            v___x_214_ = lean_apply_1(v_h__1_209_, v___x_213_);
            return v___x_214_;
        } else {
            let mut v_val_215_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_216_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__1_209_);
            v_val_215_ = lean_ctor_get(v_x_208_, 0);
            lean_inc(v_val_215_);
            lean_dec_ref_known(v_x_208_, 1);
            v___x_216_ = lean_apply_1(v_h__3_211_, v_val_215_);
            return v___x_216_;
        }
    } else {
        lean_dec(v_h__3_211_);
        lean_dec(v_h__1_209_);
        if lean_obj_tag(v_x_208_) == 0 {
            let mut v_val_217_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_218_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__4_212_);
            v_val_217_ = lean_ctor_get(v_x_207_, 0);
            lean_inc(v_val_217_);
            lean_dec_ref_known(v_x_207_, 1);
            v___x_218_ = lean_apply_1(v_h__2_210_, v_val_217_);
            return v___x_218_;
        } else {
            let mut v_val_219_: *mut LeanObject = core::ptr::null_mut();
            let mut v_val_220_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_221_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_210_);
            v_val_219_ = lean_ctor_get(v_x_207_, 0);
            lean_inc(v_val_219_);
            lean_dec_ref_known(v_x_207_, 1);
            v_val_220_ = lean_ctor_get(v_x_208_, 0);
            lean_inc(v_val_220_);
            lean_dec_ref_known(v_x_208_, 1);
            v___x_221_ = lean_apply_2(v_h__4_212_, v_val_219_, v_val_220_);
            return v___x_221_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Option_Lemmas_0__Option_merge_match__1_splitter(
    mut v_00_u03b1_222_: *mut LeanObject,
    mut v_motive_223_: *mut LeanObject,
    mut v_x_224_: *mut LeanObject,
    mut v_x_225_: *mut LeanObject,
    mut v_h__1_226_: *mut LeanObject,
    mut v_h__2_227_: *mut LeanObject,
    mut v_h__3_228_: *mut LeanObject,
    mut v_h__4_229_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_224_) == 0 {
        lean_dec(v_h__4_229_);
        lean_dec(v_h__2_227_);
        if lean_obj_tag(v_x_225_) == 0 {
            let mut v___x_230_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_231_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_228_);
            v___x_230_ = lean_box(0);
            v___x_231_ = lean_apply_1(v_h__1_226_, v___x_230_);
            return v___x_231_;
        } else {
            let mut v_val_232_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_233_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__1_226_);
            v_val_232_ = lean_ctor_get(v_x_225_, 0);
            lean_inc(v_val_232_);
            lean_dec_ref_known(v_x_225_, 1);
            v___x_233_ = lean_apply_1(v_h__3_228_, v_val_232_);
            return v___x_233_;
        }
    } else {
        lean_dec(v_h__3_228_);
        lean_dec(v_h__1_226_);
        if lean_obj_tag(v_x_225_) == 0 {
            let mut v_val_234_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_235_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__4_229_);
            v_val_234_ = lean_ctor_get(v_x_224_, 0);
            lean_inc(v_val_234_);
            lean_dec_ref_known(v_x_224_, 1);
            v___x_235_ = lean_apply_1(v_h__2_227_, v_val_234_);
            return v___x_235_;
        } else {
            let mut v_val_236_: *mut LeanObject = core::ptr::null_mut();
            let mut v_val_237_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_238_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_227_);
            v_val_236_ = lean_ctor_get(v_x_224_, 0);
            lean_inc(v_val_236_);
            lean_dec_ref_known(v_x_224_, 1);
            v_val_237_ = lean_ctor_get(v_x_225_, 0);
            lean_inc(v_val_237_);
            lean_dec_ref_known(v_x_225_, 1);
            v___x_238_ = lean_apply_2(v_h__4_229_, v_val_236_, v_val_237_);
            return v___x_238_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Option_Lemmas_0__Option_isEqSome_match__1_splitter___redArg(
    mut v_x_239_: *mut LeanObject,
    mut v_x_240_: *mut LeanObject,
    mut v_h__1_241_: *mut LeanObject,
    mut v_h__2_242_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_239_) == 0 {
        let mut v___x_243_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_241_);
        v___x_243_ = lean_apply_1(v_h__2_242_, v_x_240_);
        return v___x_243_;
    } else {
        let mut v_val_244_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_245_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_242_);
        v_val_244_ = lean_ctor_get(v_x_239_, 0);
        lean_inc(v_val_244_);
        lean_dec_ref_known(v_x_239_, 1);
        v___x_245_ = lean_apply_2(v_h__1_241_, v_val_244_, v_x_240_);
        return v___x_245_;
    }
}
pub unsafe fn l___private_Init_Data_Option_Lemmas_0__Option_isEqSome_match__1_splitter(
    mut v_00_u03b1_246_: *mut LeanObject,
    mut v_motive_247_: *mut LeanObject,
    mut v_x_248_: *mut LeanObject,
    mut v_x_249_: *mut LeanObject,
    mut v_h__1_250_: *mut LeanObject,
    mut v_h__2_251_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_248_) == 0 {
        let mut v___x_252_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_250_);
        v___x_252_ = lean_apply_1(v_h__2_251_, v_x_249_);
        return v___x_252_;
    } else {
        let mut v_val_253_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_254_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_251_);
        v_val_253_ = lean_ctor_get(v_x_248_, 0);
        lean_inc(v_val_253_);
        lean_dec_ref_known(v_x_248_, 1);
        v___x_254_ = lean_apply_2(v_h__1_250_, v_val_253_, v_x_249_);
        return v___x_254_;
    }
}
pub unsafe fn l___private_Init_Data_Option_Lemmas_0__Option_pmap_match__1_splitter___redArg(
    mut v_x_255_: *mut LeanObject,
    mut v_h__1_256_: *mut LeanObject,
    mut v_h__2_257_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_255_) == 0 {
        let mut v___x_258_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_257_);
        v___x_258_ = lean_apply_1(v_h__1_256_, lean_box(0));
        return v___x_258_;
    } else {
        let mut v_val_259_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_260_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_256_);
        v_val_259_ = lean_ctor_get(v_x_255_, 0);
        lean_inc(v_val_259_);
        lean_dec_ref_known(v_x_255_, 1);
        v___x_260_ = lean_apply_2(v_h__2_257_, v_val_259_, lean_box(0));
        return v___x_260_;
    }
}
pub unsafe fn l___private_Init_Data_Option_Lemmas_0__Option_pmap_match__1_splitter(
    mut v_00_u03b1_261_: *mut LeanObject,
    mut v_p_262_: *mut LeanObject,
    mut v_motive_263_: *mut LeanObject,
    mut v_x_264_: *mut LeanObject,
    mut v_x_265_: *mut LeanObject,
    mut v_h__1_266_: *mut LeanObject,
    mut v_h__2_267_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_264_) == 0 {
        let mut v___x_268_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_267_);
        v___x_268_ = lean_apply_1(v_h__1_266_, lean_box(0));
        return v___x_268_;
    } else {
        let mut v_val_269_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_270_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_266_);
        v_val_269_ = lean_ctor_get(v_x_264_, 0);
        lean_inc(v_val_269_);
        lean_dec_ref_known(v_x_264_, 1);
        v___x_270_ = lean_apply_2(v_h__2_267_, v_val_269_, lean_box(0));
        return v___x_270_;
    }
}
pub unsafe fn l___private_Init_Data_Option_Lemmas_0__Option_pfilter_match__1_splitter___redArg(
    mut v_o_271_: *mut LeanObject,
    mut v_p_272_: *mut LeanObject,
    mut v_h__1_273_: *mut LeanObject,
    mut v_h__2_274_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_o_271_) == 0 {
        let mut v___x_275_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_274_);
        v___x_275_ = lean_apply_1(v_h__1_273_, v_p_272_);
        return v___x_275_;
    } else {
        let mut v_val_276_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_277_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_273_);
        v_val_276_ = lean_ctor_get(v_o_271_, 0);
        lean_inc(v_val_276_);
        lean_dec_ref_known(v_o_271_, 1);
        v___x_277_ = lean_apply_2(v_h__2_274_, v_val_276_, v_p_272_);
        return v___x_277_;
    }
}
pub unsafe fn l___private_Init_Data_Option_Lemmas_0__Option_pfilter_match__1_splitter(
    mut v_00_u03b1_278_: *mut LeanObject,
    mut v_motive_279_: *mut LeanObject,
    mut v_o_280_: *mut LeanObject,
    mut v_p_281_: *mut LeanObject,
    mut v_h__1_282_: *mut LeanObject,
    mut v_h__2_283_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_o_280_) == 0 {
        let mut v___x_284_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_283_);
        v___x_284_ = lean_apply_1(v_h__1_282_, v_p_281_);
        return v___x_284_;
    } else {
        let mut v_val_285_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_286_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_282_);
        v_val_285_ = lean_ctor_get(v_o_280_, 0);
        lean_inc(v_val_285_);
        lean_dec_ref_known(v_o_280_, 1);
        v___x_286_ = lean_apply_2(v_h__2_283_, v_val_285_, v_p_281_);
        return v___x_286_;
    }
}
pub unsafe fn l___private_Init_Data_Option_Lemmas_0__Option_lt_match__1_splitter___redArg(
    mut v_x_287_: *mut LeanObject,
    mut v_x_288_: *mut LeanObject,
    mut v_h__1_289_: *mut LeanObject,
    mut v_h__2_290_: *mut LeanObject,
    mut v_h__3_291_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_287_) == 0 {
        lean_dec(v_h__2_290_);
        if lean_obj_tag(v_x_288_) == 1 {
            let mut v_val_292_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_293_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_291_);
            v_val_292_ = lean_ctor_get(v_x_288_, 0);
            lean_inc(v_val_292_);
            lean_dec_ref_known(v_x_288_, 1);
            v___x_293_ = lean_apply_1(v_h__1_289_, v_val_292_);
            return v___x_293_;
        } else {
            let mut v___x_294_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__1_289_);
            v___x_294_ = lean_apply_4(v_h__3_291_, v_x_287_, v_x_288_, lean_box(0), lean_box(0));
            return v___x_294_;
        }
    } else {
        lean_dec(v_h__1_289_);
        if lean_obj_tag(v_x_288_) == 1 {
            let mut v_val_295_: *mut LeanObject = core::ptr::null_mut();
            let mut v_val_296_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_297_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_291_);
            v_val_295_ = lean_ctor_get(v_x_287_, 0);
            lean_inc(v_val_295_);
            lean_dec_ref_known(v_x_287_, 1);
            v_val_296_ = lean_ctor_get(v_x_288_, 0);
            lean_inc(v_val_296_);
            lean_dec_ref_known(v_x_288_, 1);
            v___x_297_ = lean_apply_2(v_h__2_290_, v_val_295_, v_val_296_);
            return v___x_297_;
        } else {
            let mut v___x_298_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_290_);
            v___x_298_ = lean_apply_4(v_h__3_291_, v_x_287_, v_x_288_, lean_box(0), lean_box(0));
            return v___x_298_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Option_Lemmas_0__Option_lt_match__1_splitter(
    mut v_00_u03b1_299_: *mut LeanObject,
    mut v_00_u03b2_300_: *mut LeanObject,
    mut v_motive_301_: *mut LeanObject,
    mut v_x_302_: *mut LeanObject,
    mut v_x_303_: *mut LeanObject,
    mut v_h__1_304_: *mut LeanObject,
    mut v_h__2_305_: *mut LeanObject,
    mut v_h__3_306_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_302_) == 0 {
        lean_dec(v_h__2_305_);
        if lean_obj_tag(v_x_303_) == 1 {
            let mut v_val_307_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_308_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_306_);
            v_val_307_ = lean_ctor_get(v_x_303_, 0);
            lean_inc(v_val_307_);
            lean_dec_ref_known(v_x_303_, 1);
            v___x_308_ = lean_apply_1(v_h__1_304_, v_val_307_);
            return v___x_308_;
        } else {
            let mut v___x_309_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__1_304_);
            v___x_309_ = lean_apply_4(v_h__3_306_, v_x_302_, v_x_303_, lean_box(0), lean_box(0));
            return v___x_309_;
        }
    } else {
        lean_dec(v_h__1_304_);
        if lean_obj_tag(v_x_303_) == 1 {
            let mut v_val_310_: *mut LeanObject = core::ptr::null_mut();
            let mut v_val_311_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_312_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_306_);
            v_val_310_ = lean_ctor_get(v_x_302_, 0);
            lean_inc(v_val_310_);
            lean_dec_ref_known(v_x_302_, 1);
            v_val_311_ = lean_ctor_get(v_x_303_, 0);
            lean_inc(v_val_311_);
            lean_dec_ref_known(v_x_303_, 1);
            v___x_312_ = lean_apply_2(v_h__2_305_, v_val_310_, v_val_311_);
            return v___x_312_;
        } else {
            let mut v___x_313_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_305_);
            v___x_313_ = lean_apply_4(v_h__3_306_, v_x_302_, v_x_303_, lean_box(0), lean_box(0));
            return v___x_313_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Option_Lemmas_0__Option_le_match__1_splitter___redArg(
    mut v_x_314_: *mut LeanObject,
    mut v_x_315_: *mut LeanObject,
    mut v_h__1_316_: *mut LeanObject,
    mut v_h__2_317_: *mut LeanObject,
    mut v_h__3_318_: *mut LeanObject,
    mut v_h__4_319_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_314_) == 0 {
        lean_dec(v_h__4_319_);
        lean_dec(v_h__3_318_);
        if lean_obj_tag(v_x_315_) == 0 {
            let mut v___x_320_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_321_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__1_316_);
            v___x_320_ = lean_box(0);
            v___x_321_ = lean_apply_1(v_h__2_317_, v___x_320_);
            return v___x_321_;
        } else {
            let mut v_val_322_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_323_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_317_);
            v_val_322_ = lean_ctor_get(v_x_315_, 0);
            lean_inc(v_val_322_);
            lean_dec_ref_known(v_x_315_, 1);
            v___x_323_ = lean_apply_1(v_h__1_316_, v_val_322_);
            return v___x_323_;
        }
    } else {
        lean_dec(v_h__2_317_);
        lean_dec(v_h__1_316_);
        if lean_obj_tag(v_x_315_) == 0 {
            let mut v_val_324_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_325_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__4_319_);
            v_val_324_ = lean_ctor_get(v_x_314_, 0);
            lean_inc(v_val_324_);
            lean_dec_ref_known(v_x_314_, 1);
            v___x_325_ = lean_apply_1(v_h__3_318_, v_val_324_);
            return v___x_325_;
        } else {
            let mut v_val_326_: *mut LeanObject = core::ptr::null_mut();
            let mut v_val_327_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_328_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_318_);
            v_val_326_ = lean_ctor_get(v_x_314_, 0);
            lean_inc(v_val_326_);
            lean_dec_ref_known(v_x_314_, 1);
            v_val_327_ = lean_ctor_get(v_x_315_, 0);
            lean_inc(v_val_327_);
            lean_dec_ref_known(v_x_315_, 1);
            v___x_328_ = lean_apply_2(v_h__4_319_, v_val_326_, v_val_327_);
            return v___x_328_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Option_Lemmas_0__Option_le_match__1_splitter(
    mut v_00_u03b1_329_: *mut LeanObject,
    mut v_00_u03b2_330_: *mut LeanObject,
    mut v_motive_331_: *mut LeanObject,
    mut v_x_332_: *mut LeanObject,
    mut v_x_333_: *mut LeanObject,
    mut v_h__1_334_: *mut LeanObject,
    mut v_h__2_335_: *mut LeanObject,
    mut v_h__3_336_: *mut LeanObject,
    mut v_h__4_337_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_332_) == 0 {
        lean_dec(v_h__4_337_);
        lean_dec(v_h__3_336_);
        if lean_obj_tag(v_x_333_) == 0 {
            let mut v___x_338_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_339_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__1_334_);
            v___x_338_ = lean_box(0);
            v___x_339_ = lean_apply_1(v_h__2_335_, v___x_338_);
            return v___x_339_;
        } else {
            let mut v_val_340_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_341_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_335_);
            v_val_340_ = lean_ctor_get(v_x_333_, 0);
            lean_inc(v_val_340_);
            lean_dec_ref_known(v_x_333_, 1);
            v___x_341_ = lean_apply_1(v_h__1_334_, v_val_340_);
            return v___x_341_;
        }
    } else {
        lean_dec(v_h__2_335_);
        lean_dec(v_h__1_334_);
        if lean_obj_tag(v_x_333_) == 0 {
            let mut v_val_342_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_343_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__4_337_);
            v_val_342_ = lean_ctor_get(v_x_332_, 0);
            lean_inc(v_val_342_);
            lean_dec_ref_known(v_x_332_, 1);
            v___x_343_ = lean_apply_1(v_h__3_336_, v_val_342_);
            return v___x_343_;
        } else {
            let mut v_val_344_: *mut LeanObject = core::ptr::null_mut();
            let mut v_val_345_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_346_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_336_);
            v_val_344_ = lean_ctor_get(v_x_332_, 0);
            lean_inc(v_val_344_);
            lean_dec_ref_known(v_x_332_, 1);
            v_val_345_ = lean_ctor_get(v_x_333_, 0);
            lean_inc(v_val_345_);
            lean_dec_ref_known(v_x_333_, 1);
            v___x_346_ = lean_apply_2(v_h__4_337_, v_val_344_, v_val_345_);
            return v___x_346_;
        }
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Option_Lemmas(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Option_BasicAux(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Instances(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Ext(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_PropLemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Classical(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_BEq(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Bool(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Option_Lemmas(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Option_Lemmas(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Option_BasicAux(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Option_Instances(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Ext(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_PropLemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Classical(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_BEq(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Bool(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_Option_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_Option_Lemmas(builtin);
}
