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
    mut v_x_174_: *mut crate::leanh::LeanObject,
    mut v_h__1_175_: *mut crate::leanh::LeanObject,
    mut v_h__2_176_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_174_) == 0 {
        let mut v___x_177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_175_);
        v___x_177_ = crate::leanh::lean_box(0);
        v___x_178_ = crate::leanh::lean_apply_1(v_h__2_176_, v___x_177_);
        return v___x_178_;
    } else {
        let mut v_val_179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_176_);
        v_val_179_ = crate::leanh::lean_ctor_get(v_x_174_, 0);
        crate::leanh::lean_inc(v_val_179_);
        crate::leanh::lean_dec_ref_known(v_x_174_, 1);
        v___x_180_ = crate::leanh::lean_apply_1(v_h__1_175_, v_val_179_);
        return v___x_180_;
    }
}
pub unsafe fn l___private_Init_Data_Option_Lemmas_0__Option_isSome_match__1_splitter(
    mut v_00_u03b1_181_: *mut crate::leanh::LeanObject,
    mut v_motive_182_: *mut crate::leanh::LeanObject,
    mut v_x_183_: *mut crate::leanh::LeanObject,
    mut v_h__1_184_: *mut crate::leanh::LeanObject,
    mut v_h__2_185_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_183_) == 0 {
        let mut v___x_186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_184_);
        v___x_186_ = crate::leanh::lean_box(0);
        v___x_187_ = crate::leanh::lean_apply_1(v_h__2_185_, v___x_186_);
        return v___x_187_;
    } else {
        let mut v_val_188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_185_);
        v_val_188_ = crate::leanh::lean_ctor_get(v_x_183_, 0);
        crate::leanh::lean_inc(v_val_188_);
        crate::leanh::lean_dec_ref_known(v_x_183_, 1);
        v___x_189_ = crate::leanh::lean_apply_1(v_h__1_184_, v_val_188_);
        return v___x_189_;
    }
}
pub unsafe fn l___private_Init_Data_Option_Lemmas_0__Option_bind_match__1_splitter___redArg(
    mut v_x_190_: *mut crate::leanh::LeanObject,
    mut v_x_191_: *mut crate::leanh::LeanObject,
    mut v_h__1_192_: *mut crate::leanh::LeanObject,
    mut v_h__2_193_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_190_) == 0 {
        let mut v___x_194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_193_);
        v___x_194_ = crate::leanh::lean_apply_1(v_h__1_192_, v_x_191_);
        return v___x_194_;
    } else {
        let mut v_val_195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_192_);
        v_val_195_ = crate::leanh::lean_ctor_get(v_x_190_, 0);
        crate::leanh::lean_inc(v_val_195_);
        crate::leanh::lean_dec_ref_known(v_x_190_, 1);
        v___x_196_ = crate::leanh::lean_apply_2(v_h__2_193_, v_val_195_, v_x_191_);
        return v___x_196_;
    }
}
pub unsafe fn l___private_Init_Data_Option_Lemmas_0__Option_bind_match__1_splitter(
    mut v_00_u03b1_197_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_198_: *mut crate::leanh::LeanObject,
    mut v_motive_199_: *mut crate::leanh::LeanObject,
    mut v_x_200_: *mut crate::leanh::LeanObject,
    mut v_x_201_: *mut crate::leanh::LeanObject,
    mut v_h__1_202_: *mut crate::leanh::LeanObject,
    mut v_h__2_203_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_200_) == 0 {
        let mut v___x_204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_203_);
        v___x_204_ = crate::leanh::lean_apply_1(v_h__1_202_, v_x_201_);
        return v___x_204_;
    } else {
        let mut v_val_205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_202_);
        v_val_205_ = crate::leanh::lean_ctor_get(v_x_200_, 0);
        crate::leanh::lean_inc(v_val_205_);
        crate::leanh::lean_dec_ref_known(v_x_200_, 1);
        v___x_206_ = crate::leanh::lean_apply_2(v_h__2_203_, v_val_205_, v_x_201_);
        return v___x_206_;
    }
}
pub unsafe fn l___private_Init_Data_Option_Lemmas_0__Option_merge_match__1_splitter___redArg(
    mut v_x_207_: *mut crate::leanh::LeanObject,
    mut v_x_208_: *mut crate::leanh::LeanObject,
    mut v_h__1_209_: *mut crate::leanh::LeanObject,
    mut v_h__2_210_: *mut crate::leanh::LeanObject,
    mut v_h__3_211_: *mut crate::leanh::LeanObject,
    mut v_h__4_212_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_207_) == 0 {
        crate::leanh::lean_dec(v_h__4_212_);
        crate::leanh::lean_dec(v_h__2_210_);
        if crate::leanh::lean_obj_tag(v_x_208_) == 0 {
            let mut v___x_213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_211_);
            v___x_213_ = crate::leanh::lean_box(0);
            v___x_214_ = crate::leanh::lean_apply_1(v_h__1_209_, v___x_213_);
            return v___x_214_;
        } else {
            let mut v_val_215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__1_209_);
            v_val_215_ = crate::leanh::lean_ctor_get(v_x_208_, 0);
            crate::leanh::lean_inc(v_val_215_);
            crate::leanh::lean_dec_ref_known(v_x_208_, 1);
            v___x_216_ = crate::leanh::lean_apply_1(v_h__3_211_, v_val_215_);
            return v___x_216_;
        }
    } else {
        crate::leanh::lean_dec(v_h__3_211_);
        crate::leanh::lean_dec(v_h__1_209_);
        if crate::leanh::lean_obj_tag(v_x_208_) == 0 {
            let mut v_val_217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__4_212_);
            v_val_217_ = crate::leanh::lean_ctor_get(v_x_207_, 0);
            crate::leanh::lean_inc(v_val_217_);
            crate::leanh::lean_dec_ref_known(v_x_207_, 1);
            v___x_218_ = crate::leanh::lean_apply_1(v_h__2_210_, v_val_217_);
            return v___x_218_;
        } else {
            let mut v_val_219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_210_);
            v_val_219_ = crate::leanh::lean_ctor_get(v_x_207_, 0);
            crate::leanh::lean_inc(v_val_219_);
            crate::leanh::lean_dec_ref_known(v_x_207_, 1);
            v_val_220_ = crate::leanh::lean_ctor_get(v_x_208_, 0);
            crate::leanh::lean_inc(v_val_220_);
            crate::leanh::lean_dec_ref_known(v_x_208_, 1);
            v___x_221_ = crate::leanh::lean_apply_2(v_h__4_212_, v_val_219_, v_val_220_);
            return v___x_221_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Option_Lemmas_0__Option_merge_match__1_splitter(
    mut v_00_u03b1_222_: *mut crate::leanh::LeanObject,
    mut v_motive_223_: *mut crate::leanh::LeanObject,
    mut v_x_224_: *mut crate::leanh::LeanObject,
    mut v_x_225_: *mut crate::leanh::LeanObject,
    mut v_h__1_226_: *mut crate::leanh::LeanObject,
    mut v_h__2_227_: *mut crate::leanh::LeanObject,
    mut v_h__3_228_: *mut crate::leanh::LeanObject,
    mut v_h__4_229_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_224_) == 0 {
        crate::leanh::lean_dec(v_h__4_229_);
        crate::leanh::lean_dec(v_h__2_227_);
        if crate::leanh::lean_obj_tag(v_x_225_) == 0 {
            let mut v___x_230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_228_);
            v___x_230_ = crate::leanh::lean_box(0);
            v___x_231_ = crate::leanh::lean_apply_1(v_h__1_226_, v___x_230_);
            return v___x_231_;
        } else {
            let mut v_val_232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__1_226_);
            v_val_232_ = crate::leanh::lean_ctor_get(v_x_225_, 0);
            crate::leanh::lean_inc(v_val_232_);
            crate::leanh::lean_dec_ref_known(v_x_225_, 1);
            v___x_233_ = crate::leanh::lean_apply_1(v_h__3_228_, v_val_232_);
            return v___x_233_;
        }
    } else {
        crate::leanh::lean_dec(v_h__3_228_);
        crate::leanh::lean_dec(v_h__1_226_);
        if crate::leanh::lean_obj_tag(v_x_225_) == 0 {
            let mut v_val_234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__4_229_);
            v_val_234_ = crate::leanh::lean_ctor_get(v_x_224_, 0);
            crate::leanh::lean_inc(v_val_234_);
            crate::leanh::lean_dec_ref_known(v_x_224_, 1);
            v___x_235_ = crate::leanh::lean_apply_1(v_h__2_227_, v_val_234_);
            return v___x_235_;
        } else {
            let mut v_val_236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_227_);
            v_val_236_ = crate::leanh::lean_ctor_get(v_x_224_, 0);
            crate::leanh::lean_inc(v_val_236_);
            crate::leanh::lean_dec_ref_known(v_x_224_, 1);
            v_val_237_ = crate::leanh::lean_ctor_get(v_x_225_, 0);
            crate::leanh::lean_inc(v_val_237_);
            crate::leanh::lean_dec_ref_known(v_x_225_, 1);
            v___x_238_ = crate::leanh::lean_apply_2(v_h__4_229_, v_val_236_, v_val_237_);
            return v___x_238_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Option_Lemmas_0__Option_isEqSome_match__1_splitter___redArg(
    mut v_x_239_: *mut crate::leanh::LeanObject,
    mut v_x_240_: *mut crate::leanh::LeanObject,
    mut v_h__1_241_: *mut crate::leanh::LeanObject,
    mut v_h__2_242_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_239_) == 0 {
        let mut v___x_243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_241_);
        v___x_243_ = crate::leanh::lean_apply_1(v_h__2_242_, v_x_240_);
        return v___x_243_;
    } else {
        let mut v_val_244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_242_);
        v_val_244_ = crate::leanh::lean_ctor_get(v_x_239_, 0);
        crate::leanh::lean_inc(v_val_244_);
        crate::leanh::lean_dec_ref_known(v_x_239_, 1);
        v___x_245_ = crate::leanh::lean_apply_2(v_h__1_241_, v_val_244_, v_x_240_);
        return v___x_245_;
    }
}
pub unsafe fn l___private_Init_Data_Option_Lemmas_0__Option_isEqSome_match__1_splitter(
    mut v_00_u03b1_246_: *mut crate::leanh::LeanObject,
    mut v_motive_247_: *mut crate::leanh::LeanObject,
    mut v_x_248_: *mut crate::leanh::LeanObject,
    mut v_x_249_: *mut crate::leanh::LeanObject,
    mut v_h__1_250_: *mut crate::leanh::LeanObject,
    mut v_h__2_251_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_248_) == 0 {
        let mut v___x_252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_250_);
        v___x_252_ = crate::leanh::lean_apply_1(v_h__2_251_, v_x_249_);
        return v___x_252_;
    } else {
        let mut v_val_253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_251_);
        v_val_253_ = crate::leanh::lean_ctor_get(v_x_248_, 0);
        crate::leanh::lean_inc(v_val_253_);
        crate::leanh::lean_dec_ref_known(v_x_248_, 1);
        v___x_254_ = crate::leanh::lean_apply_2(v_h__1_250_, v_val_253_, v_x_249_);
        return v___x_254_;
    }
}
pub unsafe fn l___private_Init_Data_Option_Lemmas_0__Option_pmap_match__1_splitter___redArg(
    mut v_x_255_: *mut crate::leanh::LeanObject,
    mut v_h__1_256_: *mut crate::leanh::LeanObject,
    mut v_h__2_257_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_255_) == 0 {
        let mut v___x_258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_257_);
        v___x_258_ = crate::leanh::lean_apply_1(v_h__1_256_, crate::leanh::lean_box(0));
        return v___x_258_;
    } else {
        let mut v_val_259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_256_);
        v_val_259_ = crate::leanh::lean_ctor_get(v_x_255_, 0);
        crate::leanh::lean_inc(v_val_259_);
        crate::leanh::lean_dec_ref_known(v_x_255_, 1);
        v___x_260_ = crate::leanh::lean_apply_2(v_h__2_257_, v_val_259_, crate::leanh::lean_box(0));
        return v___x_260_;
    }
}
pub unsafe fn l___private_Init_Data_Option_Lemmas_0__Option_pmap_match__1_splitter(
    mut v_00_u03b1_261_: *mut crate::leanh::LeanObject,
    mut v_p_262_: *mut crate::leanh::LeanObject,
    mut v_motive_263_: *mut crate::leanh::LeanObject,
    mut v_x_264_: *mut crate::leanh::LeanObject,
    mut v_x_265_: *mut crate::leanh::LeanObject,
    mut v_h__1_266_: *mut crate::leanh::LeanObject,
    mut v_h__2_267_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_264_) == 0 {
        let mut v___x_268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_267_);
        v___x_268_ = crate::leanh::lean_apply_1(v_h__1_266_, crate::leanh::lean_box(0));
        return v___x_268_;
    } else {
        let mut v_val_269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_266_);
        v_val_269_ = crate::leanh::lean_ctor_get(v_x_264_, 0);
        crate::leanh::lean_inc(v_val_269_);
        crate::leanh::lean_dec_ref_known(v_x_264_, 1);
        v___x_270_ = crate::leanh::lean_apply_2(v_h__2_267_, v_val_269_, crate::leanh::lean_box(0));
        return v___x_270_;
    }
}
pub unsafe fn l___private_Init_Data_Option_Lemmas_0__Option_pfilter_match__1_splitter___redArg(
    mut v_o_271_: *mut crate::leanh::LeanObject,
    mut v_p_272_: *mut crate::leanh::LeanObject,
    mut v_h__1_273_: *mut crate::leanh::LeanObject,
    mut v_h__2_274_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_o_271_) == 0 {
        let mut v___x_275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_274_);
        v___x_275_ = crate::leanh::lean_apply_1(v_h__1_273_, v_p_272_);
        return v___x_275_;
    } else {
        let mut v_val_276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_273_);
        v_val_276_ = crate::leanh::lean_ctor_get(v_o_271_, 0);
        crate::leanh::lean_inc(v_val_276_);
        crate::leanh::lean_dec_ref_known(v_o_271_, 1);
        v___x_277_ = crate::leanh::lean_apply_2(v_h__2_274_, v_val_276_, v_p_272_);
        return v___x_277_;
    }
}
pub unsafe fn l___private_Init_Data_Option_Lemmas_0__Option_pfilter_match__1_splitter(
    mut v_00_u03b1_278_: *mut crate::leanh::LeanObject,
    mut v_motive_279_: *mut crate::leanh::LeanObject,
    mut v_o_280_: *mut crate::leanh::LeanObject,
    mut v_p_281_: *mut crate::leanh::LeanObject,
    mut v_h__1_282_: *mut crate::leanh::LeanObject,
    mut v_h__2_283_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_o_280_) == 0 {
        let mut v___x_284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_283_);
        v___x_284_ = crate::leanh::lean_apply_1(v_h__1_282_, v_p_281_);
        return v___x_284_;
    } else {
        let mut v_val_285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_282_);
        v_val_285_ = crate::leanh::lean_ctor_get(v_o_280_, 0);
        crate::leanh::lean_inc(v_val_285_);
        crate::leanh::lean_dec_ref_known(v_o_280_, 1);
        v___x_286_ = crate::leanh::lean_apply_2(v_h__2_283_, v_val_285_, v_p_281_);
        return v___x_286_;
    }
}
pub unsafe fn l___private_Init_Data_Option_Lemmas_0__Option_lt_match__1_splitter___redArg(
    mut v_x_287_: *mut crate::leanh::LeanObject,
    mut v_x_288_: *mut crate::leanh::LeanObject,
    mut v_h__1_289_: *mut crate::leanh::LeanObject,
    mut v_h__2_290_: *mut crate::leanh::LeanObject,
    mut v_h__3_291_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_287_) == 0 {
        crate::leanh::lean_dec(v_h__2_290_);
        if crate::leanh::lean_obj_tag(v_x_288_) == 1 {
            let mut v_val_292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_291_);
            v_val_292_ = crate::leanh::lean_ctor_get(v_x_288_, 0);
            crate::leanh::lean_inc(v_val_292_);
            crate::leanh::lean_dec_ref_known(v_x_288_, 1);
            v___x_293_ = crate::leanh::lean_apply_1(v_h__1_289_, v_val_292_);
            return v___x_293_;
        } else {
            let mut v___x_294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__1_289_);
            v___x_294_ = crate::leanh::lean_apply_4(
                v_h__3_291_,
                v_x_287_,
                v_x_288_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
            );
            return v___x_294_;
        }
    } else {
        crate::leanh::lean_dec(v_h__1_289_);
        if crate::leanh::lean_obj_tag(v_x_288_) == 1 {
            let mut v_val_295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_291_);
            v_val_295_ = crate::leanh::lean_ctor_get(v_x_287_, 0);
            crate::leanh::lean_inc(v_val_295_);
            crate::leanh::lean_dec_ref_known(v_x_287_, 1);
            v_val_296_ = crate::leanh::lean_ctor_get(v_x_288_, 0);
            crate::leanh::lean_inc(v_val_296_);
            crate::leanh::lean_dec_ref_known(v_x_288_, 1);
            v___x_297_ = crate::leanh::lean_apply_2(v_h__2_290_, v_val_295_, v_val_296_);
            return v___x_297_;
        } else {
            let mut v___x_298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_290_);
            v___x_298_ = crate::leanh::lean_apply_4(
                v_h__3_291_,
                v_x_287_,
                v_x_288_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
            );
            return v___x_298_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Option_Lemmas_0__Option_lt_match__1_splitter(
    mut v_00_u03b1_299_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_300_: *mut crate::leanh::LeanObject,
    mut v_motive_301_: *mut crate::leanh::LeanObject,
    mut v_x_302_: *mut crate::leanh::LeanObject,
    mut v_x_303_: *mut crate::leanh::LeanObject,
    mut v_h__1_304_: *mut crate::leanh::LeanObject,
    mut v_h__2_305_: *mut crate::leanh::LeanObject,
    mut v_h__3_306_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_302_) == 0 {
        crate::leanh::lean_dec(v_h__2_305_);
        if crate::leanh::lean_obj_tag(v_x_303_) == 1 {
            let mut v_val_307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_306_);
            v_val_307_ = crate::leanh::lean_ctor_get(v_x_303_, 0);
            crate::leanh::lean_inc(v_val_307_);
            crate::leanh::lean_dec_ref_known(v_x_303_, 1);
            v___x_308_ = crate::leanh::lean_apply_1(v_h__1_304_, v_val_307_);
            return v___x_308_;
        } else {
            let mut v___x_309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__1_304_);
            v___x_309_ = crate::leanh::lean_apply_4(
                v_h__3_306_,
                v_x_302_,
                v_x_303_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
            );
            return v___x_309_;
        }
    } else {
        crate::leanh::lean_dec(v_h__1_304_);
        if crate::leanh::lean_obj_tag(v_x_303_) == 1 {
            let mut v_val_310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_306_);
            v_val_310_ = crate::leanh::lean_ctor_get(v_x_302_, 0);
            crate::leanh::lean_inc(v_val_310_);
            crate::leanh::lean_dec_ref_known(v_x_302_, 1);
            v_val_311_ = crate::leanh::lean_ctor_get(v_x_303_, 0);
            crate::leanh::lean_inc(v_val_311_);
            crate::leanh::lean_dec_ref_known(v_x_303_, 1);
            v___x_312_ = crate::leanh::lean_apply_2(v_h__2_305_, v_val_310_, v_val_311_);
            return v___x_312_;
        } else {
            let mut v___x_313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_305_);
            v___x_313_ = crate::leanh::lean_apply_4(
                v_h__3_306_,
                v_x_302_,
                v_x_303_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
            );
            return v___x_313_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Option_Lemmas_0__Option_le_match__1_splitter___redArg(
    mut v_x_314_: *mut crate::leanh::LeanObject,
    mut v_x_315_: *mut crate::leanh::LeanObject,
    mut v_h__1_316_: *mut crate::leanh::LeanObject,
    mut v_h__2_317_: *mut crate::leanh::LeanObject,
    mut v_h__3_318_: *mut crate::leanh::LeanObject,
    mut v_h__4_319_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_314_) == 0 {
        crate::leanh::lean_dec(v_h__4_319_);
        crate::leanh::lean_dec(v_h__3_318_);
        if crate::leanh::lean_obj_tag(v_x_315_) == 0 {
            let mut v___x_320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__1_316_);
            v___x_320_ = crate::leanh::lean_box(0);
            v___x_321_ = crate::leanh::lean_apply_1(v_h__2_317_, v___x_320_);
            return v___x_321_;
        } else {
            let mut v_val_322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_317_);
            v_val_322_ = crate::leanh::lean_ctor_get(v_x_315_, 0);
            crate::leanh::lean_inc(v_val_322_);
            crate::leanh::lean_dec_ref_known(v_x_315_, 1);
            v___x_323_ = crate::leanh::lean_apply_1(v_h__1_316_, v_val_322_);
            return v___x_323_;
        }
    } else {
        crate::leanh::lean_dec(v_h__2_317_);
        crate::leanh::lean_dec(v_h__1_316_);
        if crate::leanh::lean_obj_tag(v_x_315_) == 0 {
            let mut v_val_324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__4_319_);
            v_val_324_ = crate::leanh::lean_ctor_get(v_x_314_, 0);
            crate::leanh::lean_inc(v_val_324_);
            crate::leanh::lean_dec_ref_known(v_x_314_, 1);
            v___x_325_ = crate::leanh::lean_apply_1(v_h__3_318_, v_val_324_);
            return v___x_325_;
        } else {
            let mut v_val_326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_318_);
            v_val_326_ = crate::leanh::lean_ctor_get(v_x_314_, 0);
            crate::leanh::lean_inc(v_val_326_);
            crate::leanh::lean_dec_ref_known(v_x_314_, 1);
            v_val_327_ = crate::leanh::lean_ctor_get(v_x_315_, 0);
            crate::leanh::lean_inc(v_val_327_);
            crate::leanh::lean_dec_ref_known(v_x_315_, 1);
            v___x_328_ = crate::leanh::lean_apply_2(v_h__4_319_, v_val_326_, v_val_327_);
            return v___x_328_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Option_Lemmas_0__Option_le_match__1_splitter(
    mut v_00_u03b1_329_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_330_: *mut crate::leanh::LeanObject,
    mut v_motive_331_: *mut crate::leanh::LeanObject,
    mut v_x_332_: *mut crate::leanh::LeanObject,
    mut v_x_333_: *mut crate::leanh::LeanObject,
    mut v_h__1_334_: *mut crate::leanh::LeanObject,
    mut v_h__2_335_: *mut crate::leanh::LeanObject,
    mut v_h__3_336_: *mut crate::leanh::LeanObject,
    mut v_h__4_337_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_332_) == 0 {
        crate::leanh::lean_dec(v_h__4_337_);
        crate::leanh::lean_dec(v_h__3_336_);
        if crate::leanh::lean_obj_tag(v_x_333_) == 0 {
            let mut v___x_338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__1_334_);
            v___x_338_ = crate::leanh::lean_box(0);
            v___x_339_ = crate::leanh::lean_apply_1(v_h__2_335_, v___x_338_);
            return v___x_339_;
        } else {
            let mut v_val_340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_335_);
            v_val_340_ = crate::leanh::lean_ctor_get(v_x_333_, 0);
            crate::leanh::lean_inc(v_val_340_);
            crate::leanh::lean_dec_ref_known(v_x_333_, 1);
            v___x_341_ = crate::leanh::lean_apply_1(v_h__1_334_, v_val_340_);
            return v___x_341_;
        }
    } else {
        crate::leanh::lean_dec(v_h__2_335_);
        crate::leanh::lean_dec(v_h__1_334_);
        if crate::leanh::lean_obj_tag(v_x_333_) == 0 {
            let mut v_val_342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__4_337_);
            v_val_342_ = crate::leanh::lean_ctor_get(v_x_332_, 0);
            crate::leanh::lean_inc(v_val_342_);
            crate::leanh::lean_dec_ref_known(v_x_332_, 1);
            v___x_343_ = crate::leanh::lean_apply_1(v_h__3_336_, v_val_342_);
            return v___x_343_;
        } else {
            let mut v_val_344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_336_);
            v_val_344_ = crate::leanh::lean_ctor_get(v_x_332_, 0);
            crate::leanh::lean_inc(v_val_344_);
            crate::leanh::lean_dec_ref_known(v_x_332_, 1);
            v_val_345_ = crate::leanh::lean_ctor_get(v_x_333_, 0);
            crate::leanh::lean_inc(v_val_345_);
            crate::leanh::lean_dec_ref_known(v_x_333_, 1);
            v___x_346_ = crate::leanh::lean_apply_2(v_h__4_337_, v_val_344_, v_val_345_);
            return v___x_346_;
        }
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Option_Lemmas(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Option_BasicAux(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Instances(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Instances(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Ext(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_BasicAux(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_PropLemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Classical(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_BEq(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Bool(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Option_Lemmas(
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
pub unsafe fn initialize_Init_Data_Option_Lemmas(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Option_BasicAux(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Option_Instances(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Option_Instances(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Ext(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Option_BasicAux(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_PropLemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Classical(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_BEq(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Bool(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Option_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_Option_Lemmas(builtin);
}
