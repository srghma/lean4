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
pub unsafe fn l___private_Init_Data_Option_Lemmas_0__Option_isSome_match__1_splitter___redArg(
    mut v_x_174_: *mut leanh::LeanObject,
    mut v_h__1_175_: *mut leanh::LeanObject,
    mut v_h__2_176_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_174_) == 0 {
        let mut v___x_177_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_178_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_175_);
        v___x_177_ = leanh::lean_box(0);
        v___x_178_ = leanh::lean_apply_1(v_h__2_176_, v___x_177_);
        return v___x_178_;
    } else {
        let mut v_val_179_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_180_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_176_);
        v_val_179_ = leanh::lean_ctor_get(v_x_174_, 0);
        leanh::lean_inc(v_val_179_);
        leanh::lean_dec_ref_known(v_x_174_, 1);
        v___x_180_ = leanh::lean_apply_1(v_h__1_175_, v_val_179_);
        return v___x_180_;
    }
}
pub unsafe fn l___private_Init_Data_Option_Lemmas_0__Option_isSome_match__1_splitter(
    mut v_00_u03b1_181_: *mut leanh::LeanObject,
    mut v_motive_182_: *mut leanh::LeanObject,
    mut v_x_183_: *mut leanh::LeanObject,
    mut v_h__1_184_: *mut leanh::LeanObject,
    mut v_h__2_185_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_183_) == 0 {
        let mut v___x_186_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_187_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_184_);
        v___x_186_ = leanh::lean_box(0);
        v___x_187_ = leanh::lean_apply_1(v_h__2_185_, v___x_186_);
        return v___x_187_;
    } else {
        let mut v_val_188_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_189_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_185_);
        v_val_188_ = leanh::lean_ctor_get(v_x_183_, 0);
        leanh::lean_inc(v_val_188_);
        leanh::lean_dec_ref_known(v_x_183_, 1);
        v___x_189_ = leanh::lean_apply_1(v_h__1_184_, v_val_188_);
        return v___x_189_;
    }
}
pub unsafe fn l___private_Init_Data_Option_Lemmas_0__Option_bind_match__1_splitter___redArg(
    mut v_x_190_: *mut leanh::LeanObject,
    mut v_x_191_: *mut leanh::LeanObject,
    mut v_h__1_192_: *mut leanh::LeanObject,
    mut v_h__2_193_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_190_) == 0 {
        let mut v___x_194_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_193_);
        v___x_194_ = leanh::lean_apply_1(v_h__1_192_, v_x_191_);
        return v___x_194_;
    } else {
        let mut v_val_195_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_196_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_192_);
        v_val_195_ = leanh::lean_ctor_get(v_x_190_, 0);
        leanh::lean_inc(v_val_195_);
        leanh::lean_dec_ref_known(v_x_190_, 1);
        v___x_196_ = leanh::lean_apply_2(v_h__2_193_, v_val_195_, v_x_191_);
        return v___x_196_;
    }
}
pub unsafe fn l___private_Init_Data_Option_Lemmas_0__Option_bind_match__1_splitter(
    mut v_00_u03b1_197_: *mut leanh::LeanObject,
    mut v_00_u03b2_198_: *mut leanh::LeanObject,
    mut v_motive_199_: *mut leanh::LeanObject,
    mut v_x_200_: *mut leanh::LeanObject,
    mut v_x_201_: *mut leanh::LeanObject,
    mut v_h__1_202_: *mut leanh::LeanObject,
    mut v_h__2_203_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_200_) == 0 {
        let mut v___x_204_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_203_);
        v___x_204_ = leanh::lean_apply_1(v_h__1_202_, v_x_201_);
        return v___x_204_;
    } else {
        let mut v_val_205_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_206_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_202_);
        v_val_205_ = leanh::lean_ctor_get(v_x_200_, 0);
        leanh::lean_inc(v_val_205_);
        leanh::lean_dec_ref_known(v_x_200_, 1);
        v___x_206_ = leanh::lean_apply_2(v_h__2_203_, v_val_205_, v_x_201_);
        return v___x_206_;
    }
}
pub unsafe fn l___private_Init_Data_Option_Lemmas_0__Option_merge_match__1_splitter___redArg(
    mut v_x_207_: *mut leanh::LeanObject,
    mut v_x_208_: *mut leanh::LeanObject,
    mut v_h__1_209_: *mut leanh::LeanObject,
    mut v_h__2_210_: *mut leanh::LeanObject,
    mut v_h__3_211_: *mut leanh::LeanObject,
    mut v_h__4_212_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_207_) == 0 {
        leanh::lean_dec(v_h__4_212_);
        leanh::lean_dec(v_h__2_210_);
        if leanh::lean_obj_tag(v_x_208_) == 0 {
            let mut v___x_213_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_214_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_211_);
            v___x_213_ = leanh::lean_box(0);
            v___x_214_ = leanh::lean_apply_1(v_h__1_209_, v___x_213_);
            return v___x_214_;
        } else {
            let mut v_val_215_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_216_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__1_209_);
            v_val_215_ = leanh::lean_ctor_get(v_x_208_, 0);
            leanh::lean_inc(v_val_215_);
            leanh::lean_dec_ref_known(v_x_208_, 1);
            v___x_216_ = leanh::lean_apply_1(v_h__3_211_, v_val_215_);
            return v___x_216_;
        }
    } else {
        leanh::lean_dec(v_h__3_211_);
        leanh::lean_dec(v_h__1_209_);
        if leanh::lean_obj_tag(v_x_208_) == 0 {
            let mut v_val_217_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_218_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__4_212_);
            v_val_217_ = leanh::lean_ctor_get(v_x_207_, 0);
            leanh::lean_inc(v_val_217_);
            leanh::lean_dec_ref_known(v_x_207_, 1);
            v___x_218_ = leanh::lean_apply_1(v_h__2_210_, v_val_217_);
            return v___x_218_;
        } else {
            let mut v_val_219_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_220_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_221_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_210_);
            v_val_219_ = leanh::lean_ctor_get(v_x_207_, 0);
            leanh::lean_inc(v_val_219_);
            leanh::lean_dec_ref_known(v_x_207_, 1);
            v_val_220_ = leanh::lean_ctor_get(v_x_208_, 0);
            leanh::lean_inc(v_val_220_);
            leanh::lean_dec_ref_known(v_x_208_, 1);
            v___x_221_ = leanh::lean_apply_2(v_h__4_212_, v_val_219_, v_val_220_);
            return v___x_221_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Option_Lemmas_0__Option_merge_match__1_splitter(
    mut v_00_u03b1_222_: *mut leanh::LeanObject,
    mut v_motive_223_: *mut leanh::LeanObject,
    mut v_x_224_: *mut leanh::LeanObject,
    mut v_x_225_: *mut leanh::LeanObject,
    mut v_h__1_226_: *mut leanh::LeanObject,
    mut v_h__2_227_: *mut leanh::LeanObject,
    mut v_h__3_228_: *mut leanh::LeanObject,
    mut v_h__4_229_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_224_) == 0 {
        leanh::lean_dec(v_h__4_229_);
        leanh::lean_dec(v_h__2_227_);
        if leanh::lean_obj_tag(v_x_225_) == 0 {
            let mut v___x_230_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_231_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_228_);
            v___x_230_ = leanh::lean_box(0);
            v___x_231_ = leanh::lean_apply_1(v_h__1_226_, v___x_230_);
            return v___x_231_;
        } else {
            let mut v_val_232_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_233_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__1_226_);
            v_val_232_ = leanh::lean_ctor_get(v_x_225_, 0);
            leanh::lean_inc(v_val_232_);
            leanh::lean_dec_ref_known(v_x_225_, 1);
            v___x_233_ = leanh::lean_apply_1(v_h__3_228_, v_val_232_);
            return v___x_233_;
        }
    } else {
        leanh::lean_dec(v_h__3_228_);
        leanh::lean_dec(v_h__1_226_);
        if leanh::lean_obj_tag(v_x_225_) == 0 {
            let mut v_val_234_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_235_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__4_229_);
            v_val_234_ = leanh::lean_ctor_get(v_x_224_, 0);
            leanh::lean_inc(v_val_234_);
            leanh::lean_dec_ref_known(v_x_224_, 1);
            v___x_235_ = leanh::lean_apply_1(v_h__2_227_, v_val_234_);
            return v___x_235_;
        } else {
            let mut v_val_236_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_237_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_238_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_227_);
            v_val_236_ = leanh::lean_ctor_get(v_x_224_, 0);
            leanh::lean_inc(v_val_236_);
            leanh::lean_dec_ref_known(v_x_224_, 1);
            v_val_237_ = leanh::lean_ctor_get(v_x_225_, 0);
            leanh::lean_inc(v_val_237_);
            leanh::lean_dec_ref_known(v_x_225_, 1);
            v___x_238_ = leanh::lean_apply_2(v_h__4_229_, v_val_236_, v_val_237_);
            return v___x_238_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Option_Lemmas_0__Option_isEqSome_match__1_splitter___redArg(
    mut v_x_239_: *mut leanh::LeanObject,
    mut v_x_240_: *mut leanh::LeanObject,
    mut v_h__1_241_: *mut leanh::LeanObject,
    mut v_h__2_242_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_239_) == 0 {
        let mut v___x_243_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_241_);
        v___x_243_ = leanh::lean_apply_1(v_h__2_242_, v_x_240_);
        return v___x_243_;
    } else {
        let mut v_val_244_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_245_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_242_);
        v_val_244_ = leanh::lean_ctor_get(v_x_239_, 0);
        leanh::lean_inc(v_val_244_);
        leanh::lean_dec_ref_known(v_x_239_, 1);
        v___x_245_ = leanh::lean_apply_2(v_h__1_241_, v_val_244_, v_x_240_);
        return v___x_245_;
    }
}
pub unsafe fn l___private_Init_Data_Option_Lemmas_0__Option_isEqSome_match__1_splitter(
    mut v_00_u03b1_246_: *mut leanh::LeanObject,
    mut v_motive_247_: *mut leanh::LeanObject,
    mut v_x_248_: *mut leanh::LeanObject,
    mut v_x_249_: *mut leanh::LeanObject,
    mut v_h__1_250_: *mut leanh::LeanObject,
    mut v_h__2_251_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_248_) == 0 {
        let mut v___x_252_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_250_);
        v___x_252_ = leanh::lean_apply_1(v_h__2_251_, v_x_249_);
        return v___x_252_;
    } else {
        let mut v_val_253_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_254_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_251_);
        v_val_253_ = leanh::lean_ctor_get(v_x_248_, 0);
        leanh::lean_inc(v_val_253_);
        leanh::lean_dec_ref_known(v_x_248_, 1);
        v___x_254_ = leanh::lean_apply_2(v_h__1_250_, v_val_253_, v_x_249_);
        return v___x_254_;
    }
}
pub unsafe fn l___private_Init_Data_Option_Lemmas_0__Option_pmap_match__1_splitter___redArg(
    mut v_x_255_: *mut leanh::LeanObject,
    mut v_h__1_256_: *mut leanh::LeanObject,
    mut v_h__2_257_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_255_) == 0 {
        let mut v___x_258_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_257_);
        v___x_258_ = leanh::lean_apply_1(v_h__1_256_, leanh::lean_box(0));
        return v___x_258_;
    } else {
        let mut v_val_259_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_260_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_256_);
        v_val_259_ = leanh::lean_ctor_get(v_x_255_, 0);
        leanh::lean_inc(v_val_259_);
        leanh::lean_dec_ref_known(v_x_255_, 1);
        v___x_260_ = leanh::lean_apply_2(v_h__2_257_, v_val_259_, leanh::lean_box(0));
        return v___x_260_;
    }
}
pub unsafe fn l___private_Init_Data_Option_Lemmas_0__Option_pmap_match__1_splitter(
    mut v_00_u03b1_261_: *mut leanh::LeanObject,
    mut v_p_262_: *mut leanh::LeanObject,
    mut v_motive_263_: *mut leanh::LeanObject,
    mut v_x_264_: *mut leanh::LeanObject,
    mut v_x_265_: *mut leanh::LeanObject,
    mut v_h__1_266_: *mut leanh::LeanObject,
    mut v_h__2_267_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_264_) == 0 {
        let mut v___x_268_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_267_);
        v___x_268_ = leanh::lean_apply_1(v_h__1_266_, leanh::lean_box(0));
        return v___x_268_;
    } else {
        let mut v_val_269_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_270_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_266_);
        v_val_269_ = leanh::lean_ctor_get(v_x_264_, 0);
        leanh::lean_inc(v_val_269_);
        leanh::lean_dec_ref_known(v_x_264_, 1);
        v___x_270_ = leanh::lean_apply_2(v_h__2_267_, v_val_269_, leanh::lean_box(0));
        return v___x_270_;
    }
}
pub unsafe fn l___private_Init_Data_Option_Lemmas_0__Option_pfilter_match__1_splitter___redArg(
    mut v_o_271_: *mut leanh::LeanObject,
    mut v_p_272_: *mut leanh::LeanObject,
    mut v_h__1_273_: *mut leanh::LeanObject,
    mut v_h__2_274_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_o_271_) == 0 {
        let mut v___x_275_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_274_);
        v___x_275_ = leanh::lean_apply_1(v_h__1_273_, v_p_272_);
        return v___x_275_;
    } else {
        let mut v_val_276_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_277_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_273_);
        v_val_276_ = leanh::lean_ctor_get(v_o_271_, 0);
        leanh::lean_inc(v_val_276_);
        leanh::lean_dec_ref_known(v_o_271_, 1);
        v___x_277_ = leanh::lean_apply_2(v_h__2_274_, v_val_276_, v_p_272_);
        return v___x_277_;
    }
}
pub unsafe fn l___private_Init_Data_Option_Lemmas_0__Option_pfilter_match__1_splitter(
    mut v_00_u03b1_278_: *mut leanh::LeanObject,
    mut v_motive_279_: *mut leanh::LeanObject,
    mut v_o_280_: *mut leanh::LeanObject,
    mut v_p_281_: *mut leanh::LeanObject,
    mut v_h__1_282_: *mut leanh::LeanObject,
    mut v_h__2_283_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_o_280_) == 0 {
        let mut v___x_284_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_283_);
        v___x_284_ = leanh::lean_apply_1(v_h__1_282_, v_p_281_);
        return v___x_284_;
    } else {
        let mut v_val_285_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_286_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_282_);
        v_val_285_ = leanh::lean_ctor_get(v_o_280_, 0);
        leanh::lean_inc(v_val_285_);
        leanh::lean_dec_ref_known(v_o_280_, 1);
        v___x_286_ = leanh::lean_apply_2(v_h__2_283_, v_val_285_, v_p_281_);
        return v___x_286_;
    }
}
pub unsafe fn l___private_Init_Data_Option_Lemmas_0__Option_lt_match__1_splitter___redArg(
    mut v_x_287_: *mut leanh::LeanObject,
    mut v_x_288_: *mut leanh::LeanObject,
    mut v_h__1_289_: *mut leanh::LeanObject,
    mut v_h__2_290_: *mut leanh::LeanObject,
    mut v_h__3_291_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_287_) == 0 {
        leanh::lean_dec(v_h__2_290_);
        if leanh::lean_obj_tag(v_x_288_) == 1 {
            let mut v_val_292_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_293_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_291_);
            v_val_292_ = leanh::lean_ctor_get(v_x_288_, 0);
            leanh::lean_inc(v_val_292_);
            leanh::lean_dec_ref_known(v_x_288_, 1);
            v___x_293_ = leanh::lean_apply_1(v_h__1_289_, v_val_292_);
            return v___x_293_;
        } else {
            let mut v___x_294_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__1_289_);
            v___x_294_ = leanh::lean_apply_4(
                v_h__3_291_,
                v_x_287_,
                v_x_288_,
                leanh::lean_box(0),
                leanh::lean_box(0),
            );
            return v___x_294_;
        }
    } else {
        leanh::lean_dec(v_h__1_289_);
        if leanh::lean_obj_tag(v_x_288_) == 1 {
            let mut v_val_295_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_296_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_297_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_291_);
            v_val_295_ = leanh::lean_ctor_get(v_x_287_, 0);
            leanh::lean_inc(v_val_295_);
            leanh::lean_dec_ref_known(v_x_287_, 1);
            v_val_296_ = leanh::lean_ctor_get(v_x_288_, 0);
            leanh::lean_inc(v_val_296_);
            leanh::lean_dec_ref_known(v_x_288_, 1);
            v___x_297_ = leanh::lean_apply_2(v_h__2_290_, v_val_295_, v_val_296_);
            return v___x_297_;
        } else {
            let mut v___x_298_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_290_);
            v___x_298_ = leanh::lean_apply_4(
                v_h__3_291_,
                v_x_287_,
                v_x_288_,
                leanh::lean_box(0),
                leanh::lean_box(0),
            );
            return v___x_298_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Option_Lemmas_0__Option_lt_match__1_splitter(
    mut v_00_u03b1_299_: *mut leanh::LeanObject,
    mut v_00_u03b2_300_: *mut leanh::LeanObject,
    mut v_motive_301_: *mut leanh::LeanObject,
    mut v_x_302_: *mut leanh::LeanObject,
    mut v_x_303_: *mut leanh::LeanObject,
    mut v_h__1_304_: *mut leanh::LeanObject,
    mut v_h__2_305_: *mut leanh::LeanObject,
    mut v_h__3_306_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_302_) == 0 {
        leanh::lean_dec(v_h__2_305_);
        if leanh::lean_obj_tag(v_x_303_) == 1 {
            let mut v_val_307_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_308_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_306_);
            v_val_307_ = leanh::lean_ctor_get(v_x_303_, 0);
            leanh::lean_inc(v_val_307_);
            leanh::lean_dec_ref_known(v_x_303_, 1);
            v___x_308_ = leanh::lean_apply_1(v_h__1_304_, v_val_307_);
            return v___x_308_;
        } else {
            let mut v___x_309_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__1_304_);
            v___x_309_ = leanh::lean_apply_4(
                v_h__3_306_,
                v_x_302_,
                v_x_303_,
                leanh::lean_box(0),
                leanh::lean_box(0),
            );
            return v___x_309_;
        }
    } else {
        leanh::lean_dec(v_h__1_304_);
        if leanh::lean_obj_tag(v_x_303_) == 1 {
            let mut v_val_310_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_311_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_312_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_306_);
            v_val_310_ = leanh::lean_ctor_get(v_x_302_, 0);
            leanh::lean_inc(v_val_310_);
            leanh::lean_dec_ref_known(v_x_302_, 1);
            v_val_311_ = leanh::lean_ctor_get(v_x_303_, 0);
            leanh::lean_inc(v_val_311_);
            leanh::lean_dec_ref_known(v_x_303_, 1);
            v___x_312_ = leanh::lean_apply_2(v_h__2_305_, v_val_310_, v_val_311_);
            return v___x_312_;
        } else {
            let mut v___x_313_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_305_);
            v___x_313_ = leanh::lean_apply_4(
                v_h__3_306_,
                v_x_302_,
                v_x_303_,
                leanh::lean_box(0),
                leanh::lean_box(0),
            );
            return v___x_313_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Option_Lemmas_0__Option_le_match__1_splitter___redArg(
    mut v_x_314_: *mut leanh::LeanObject,
    mut v_x_315_: *mut leanh::LeanObject,
    mut v_h__1_316_: *mut leanh::LeanObject,
    mut v_h__2_317_: *mut leanh::LeanObject,
    mut v_h__3_318_: *mut leanh::LeanObject,
    mut v_h__4_319_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_314_) == 0 {
        leanh::lean_dec(v_h__4_319_);
        leanh::lean_dec(v_h__3_318_);
        if leanh::lean_obj_tag(v_x_315_) == 0 {
            let mut v___x_320_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_321_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__1_316_);
            v___x_320_ = leanh::lean_box(0);
            v___x_321_ = leanh::lean_apply_1(v_h__2_317_, v___x_320_);
            return v___x_321_;
        } else {
            let mut v_val_322_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_323_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_317_);
            v_val_322_ = leanh::lean_ctor_get(v_x_315_, 0);
            leanh::lean_inc(v_val_322_);
            leanh::lean_dec_ref_known(v_x_315_, 1);
            v___x_323_ = leanh::lean_apply_1(v_h__1_316_, v_val_322_);
            return v___x_323_;
        }
    } else {
        leanh::lean_dec(v_h__2_317_);
        leanh::lean_dec(v_h__1_316_);
        if leanh::lean_obj_tag(v_x_315_) == 0 {
            let mut v_val_324_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_325_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__4_319_);
            v_val_324_ = leanh::lean_ctor_get(v_x_314_, 0);
            leanh::lean_inc(v_val_324_);
            leanh::lean_dec_ref_known(v_x_314_, 1);
            v___x_325_ = leanh::lean_apply_1(v_h__3_318_, v_val_324_);
            return v___x_325_;
        } else {
            let mut v_val_326_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_327_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_328_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_318_);
            v_val_326_ = leanh::lean_ctor_get(v_x_314_, 0);
            leanh::lean_inc(v_val_326_);
            leanh::lean_dec_ref_known(v_x_314_, 1);
            v_val_327_ = leanh::lean_ctor_get(v_x_315_, 0);
            leanh::lean_inc(v_val_327_);
            leanh::lean_dec_ref_known(v_x_315_, 1);
            v___x_328_ = leanh::lean_apply_2(v_h__4_319_, v_val_326_, v_val_327_);
            return v___x_328_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Option_Lemmas_0__Option_le_match__1_splitter(
    mut v_00_u03b1_329_: *mut leanh::LeanObject,
    mut v_00_u03b2_330_: *mut leanh::LeanObject,
    mut v_motive_331_: *mut leanh::LeanObject,
    mut v_x_332_: *mut leanh::LeanObject,
    mut v_x_333_: *mut leanh::LeanObject,
    mut v_h__1_334_: *mut leanh::LeanObject,
    mut v_h__2_335_: *mut leanh::LeanObject,
    mut v_h__3_336_: *mut leanh::LeanObject,
    mut v_h__4_337_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_332_) == 0 {
        leanh::lean_dec(v_h__4_337_);
        leanh::lean_dec(v_h__3_336_);
        if leanh::lean_obj_tag(v_x_333_) == 0 {
            let mut v___x_338_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_339_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__1_334_);
            v___x_338_ = leanh::lean_box(0);
            v___x_339_ = leanh::lean_apply_1(v_h__2_335_, v___x_338_);
            return v___x_339_;
        } else {
            let mut v_val_340_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_341_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_335_);
            v_val_340_ = leanh::lean_ctor_get(v_x_333_, 0);
            leanh::lean_inc(v_val_340_);
            leanh::lean_dec_ref_known(v_x_333_, 1);
            v___x_341_ = leanh::lean_apply_1(v_h__1_334_, v_val_340_);
            return v___x_341_;
        }
    } else {
        leanh::lean_dec(v_h__2_335_);
        leanh::lean_dec(v_h__1_334_);
        if leanh::lean_obj_tag(v_x_333_) == 0 {
            let mut v_val_342_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_343_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__4_337_);
            v_val_342_ = leanh::lean_ctor_get(v_x_332_, 0);
            leanh::lean_inc(v_val_342_);
            leanh::lean_dec_ref_known(v_x_332_, 1);
            v___x_343_ = leanh::lean_apply_1(v_h__3_336_, v_val_342_);
            return v___x_343_;
        } else {
            let mut v_val_344_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_345_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_346_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_336_);
            v_val_344_ = leanh::lean_ctor_get(v_x_332_, 0);
            leanh::lean_inc(v_val_344_);
            leanh::lean_dec_ref_known(v_x_332_, 1);
            v_val_345_ = leanh::lean_ctor_get(v_x_333_, 0);
            leanh::lean_inc(v_val_345_);
            leanh::lean_dec_ref_known(v_x_333_, 1);
            v___x_346_ = leanh::lean_apply_2(v_h__4_337_, v_val_344_, v_val_345_);
            return v___x_346_;
        }
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Option_Lemmas(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Option_BasicAux(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Instances(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Instances(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Ext(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_BasicAux(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_PropLemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Classical(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_BEq(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Bool(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Option_Lemmas(
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
pub unsafe fn initialize_Init_Data_Option_Lemmas(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Option_BasicAux(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Option_Instances(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Option_Instances(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Ext(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Option_BasicAux(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_PropLemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Classical(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_BEq(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Bool(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Option_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_Option_Lemmas(builtin);
}