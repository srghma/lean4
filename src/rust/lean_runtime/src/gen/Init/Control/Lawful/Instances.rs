// Lean compiler output
// Module: Init.Control.Lawful.Instances
// Imports: Init.Control.Lawful.Basic Init.Control.Except Init.Control.Option Init.Control.Option Init.Control.State Init.Control.StateRef Init.Control.State Init.Ext
use crate::r#gen::Init::Control::Except::{
    initialize_Init_Control_Except, runtime_initialize_Init_Control_Except,
};
use crate::r#gen::Init::Control::Lawful::Basic::{
    initialize_Init_Control_Lawful_Basic, runtime_initialize_Init_Control_Lawful_Basic,
};
use crate::r#gen::Init::Control::Option::{
    initialize_Init_Control_Option, runtime_initialize_Init_Control_Option,
};
use crate::r#gen::Init::Control::State::{
    initialize_Init_Control_State, runtime_initialize_Init_Control_State,
};
use crate::r#gen::Init::Control::StateRef::{
    initialize_Init_Control_StateRef, runtime_initialize_Init_Control_StateRef,
};
use crate::r#gen::Init::Ext::{initialize_Init_Ext, runtime_initialize_Init_Ext};
pub unsafe fn l___private_Init_Control_Lawful_Instances_0__ExceptT_bindCont_match__1_splitter___redArg(
    mut v_x_152_: *mut crate::leanh::LeanObject,
    mut v_h__1_153_: *mut crate::leanh::LeanObject,
    mut v_h__2_154_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_152_) == 0 {
        let mut v_a_155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_153_);
        v_a_155_ = crate::leanh::lean_ctor_get(v_x_152_, 0);
        crate::leanh::lean_inc(v_a_155_);
        crate::leanh::lean_dec_ref_known(v_x_152_, 1);
        v___x_156_ = crate::leanh::lean_apply_1(v_h__2_154_, v_a_155_);
        return v___x_156_;
    } else {
        let mut v_a_157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_154_);
        v_a_157_ = crate::leanh::lean_ctor_get(v_x_152_, 0);
        crate::leanh::lean_inc(v_a_157_);
        crate::leanh::lean_dec_ref_known(v_x_152_, 1);
        v___x_158_ = crate::leanh::lean_apply_1(v_h__1_153_, v_a_157_);
        return v___x_158_;
    }
}
pub unsafe fn l___private_Init_Control_Lawful_Instances_0__ExceptT_bindCont_match__1_splitter(
    mut v_00_u03b5_159_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_160_: *mut crate::leanh::LeanObject,
    mut v_motive_161_: *mut crate::leanh::LeanObject,
    mut v_x_162_: *mut crate::leanh::LeanObject,
    mut v_h__1_163_: *mut crate::leanh::LeanObject,
    mut v_h__2_164_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_162_) == 0 {
        let mut v_a_165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_163_);
        v_a_165_ = crate::leanh::lean_ctor_get(v_x_162_, 0);
        crate::leanh::lean_inc(v_a_165_);
        crate::leanh::lean_dec_ref_known(v_x_162_, 1);
        v___x_166_ = crate::leanh::lean_apply_1(v_h__2_164_, v_a_165_);
        return v___x_166_;
    } else {
        let mut v_a_167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_164_);
        v_a_167_ = crate::leanh::lean_ctor_get(v_x_162_, 0);
        crate::leanh::lean_inc(v_a_167_);
        crate::leanh::lean_dec_ref_known(v_x_162_, 1);
        v___x_168_ = crate::leanh::lean_apply_1(v_h__1_163_, v_a_167_);
        return v___x_168_;
    }
}
pub unsafe fn l___private_Init_Control_Lawful_Instances_0__ExceptT_run__bind_match__1_splitter___redArg(
    mut v_x_169_: *mut crate::leanh::LeanObject,
    mut v_h__1_170_: *mut crate::leanh::LeanObject,
    mut v_h__2_171_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_169_) == 0 {
        let mut v_a_172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_170_);
        v_a_172_ = crate::leanh::lean_ctor_get(v_x_169_, 0);
        crate::leanh::lean_inc(v_a_172_);
        crate::leanh::lean_dec_ref_known(v_x_169_, 1);
        v___x_173_ = crate::leanh::lean_apply_1(v_h__2_171_, v_a_172_);
        return v___x_173_;
    } else {
        let mut v_a_174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_171_);
        v_a_174_ = crate::leanh::lean_ctor_get(v_x_169_, 0);
        crate::leanh::lean_inc(v_a_174_);
        crate::leanh::lean_dec_ref_known(v_x_169_, 1);
        v___x_175_ = crate::leanh::lean_apply_1(v_h__1_170_, v_a_174_);
        return v___x_175_;
    }
}
pub unsafe fn l___private_Init_Control_Lawful_Instances_0__ExceptT_run__bind_match__1_splitter(
    mut v_00_u03b5_176_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_177_: *mut crate::leanh::LeanObject,
    mut v_motive_178_: *mut crate::leanh::LeanObject,
    mut v_x_179_: *mut crate::leanh::LeanObject,
    mut v_h__1_180_: *mut crate::leanh::LeanObject,
    mut v_h__2_181_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_179_) == 0 {
        let mut v_a_182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_180_);
        v_a_182_ = crate::leanh::lean_ctor_get(v_x_179_, 0);
        crate::leanh::lean_inc(v_a_182_);
        crate::leanh::lean_dec_ref_known(v_x_179_, 1);
        v___x_183_ = crate::leanh::lean_apply_1(v_h__2_181_, v_a_182_);
        return v___x_183_;
    } else {
        let mut v_a_184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_181_);
        v_a_184_ = crate::leanh::lean_ctor_get(v_x_179_, 0);
        crate::leanh::lean_inc(v_a_184_);
        crate::leanh::lean_dec_ref_known(v_x_179_, 1);
        v___x_185_ = crate::leanh::lean_apply_1(v_h__1_180_, v_a_184_);
        return v___x_185_;
    }
}
pub unsafe fn l___private_Init_Control_Lawful_Instances_0__OptionT_bind_match__1_splitter___redArg(
    mut v_____do__lift_186_: *mut crate::leanh::LeanObject,
    mut v_h__1_187_: *mut crate::leanh::LeanObject,
    mut v_h__2_188_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_186_) == 0 {
        let mut v___x_189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_187_);
        v___x_189_ = crate::leanh::lean_box(0);
        v___x_190_ = crate::leanh::lean_apply_1(v_h__2_188_, v___x_189_);
        return v___x_190_;
    } else {
        let mut v_val_191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_188_);
        v_val_191_ = crate::leanh::lean_ctor_get(v_____do__lift_186_, 0);
        crate::leanh::lean_inc(v_val_191_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_186_, 1);
        v___x_192_ = crate::leanh::lean_apply_1(v_h__1_187_, v_val_191_);
        return v___x_192_;
    }
}
pub unsafe fn l___private_Init_Control_Lawful_Instances_0__OptionT_bind_match__1_splitter(
    mut v_00_u03b1_193_: *mut crate::leanh::LeanObject,
    mut v_motive_194_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_195_: *mut crate::leanh::LeanObject,
    mut v_h__1_196_: *mut crate::leanh::LeanObject,
    mut v_h__2_197_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_195_) == 0 {
        let mut v___x_198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_196_);
        v___x_198_ = crate::leanh::lean_box(0);
        v___x_199_ = crate::leanh::lean_apply_1(v_h__2_197_, v___x_198_);
        return v___x_199_;
    } else {
        let mut v_val_200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_197_);
        v_val_200_ = crate::leanh::lean_ctor_get(v_____do__lift_195_, 0);
        crate::leanh::lean_inc(v_val_200_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_195_, 1);
        v___x_201_ = crate::leanh::lean_apply_1(v_h__1_196_, v_val_200_);
        return v___x_201_;
    }
}
pub unsafe fn l___private_Init_Control_Lawful_Instances_0__Option_getD_match__1_splitter___redArg(
    mut v_opt_202_: *mut crate::leanh::LeanObject,
    mut v_h__1_203_: *mut crate::leanh::LeanObject,
    mut v_h__2_204_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_opt_202_) == 0 {
        let mut v___x_205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_203_);
        v___x_205_ = crate::leanh::lean_box(0);
        v___x_206_ = crate::leanh::lean_apply_1(v_h__2_204_, v___x_205_);
        return v___x_206_;
    } else {
        let mut v_val_207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_204_);
        v_val_207_ = crate::leanh::lean_ctor_get(v_opt_202_, 0);
        crate::leanh::lean_inc(v_val_207_);
        crate::leanh::lean_dec_ref_known(v_opt_202_, 1);
        v___x_208_ = crate::leanh::lean_apply_1(v_h__1_203_, v_val_207_);
        return v___x_208_;
    }
}
pub unsafe fn l___private_Init_Control_Lawful_Instances_0__Option_getD_match__1_splitter(
    mut v_00_u03b1_209_: *mut crate::leanh::LeanObject,
    mut v_motive_210_: *mut crate::leanh::LeanObject,
    mut v_opt_211_: *mut crate::leanh::LeanObject,
    mut v_h__1_212_: *mut crate::leanh::LeanObject,
    mut v_h__2_213_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_opt_211_) == 0 {
        let mut v___x_214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_212_);
        v___x_214_ = crate::leanh::lean_box(0);
        v___x_215_ = crate::leanh::lean_apply_1(v_h__2_213_, v___x_214_);
        return v___x_215_;
    } else {
        let mut v_val_216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_213_);
        v_val_216_ = crate::leanh::lean_ctor_get(v_opt_211_, 0);
        crate::leanh::lean_inc(v_val_216_);
        crate::leanh::lean_dec_ref_known(v_opt_211_, 1);
        v___x_217_ = crate::leanh::lean_apply_1(v_h__1_212_, v_val_216_);
        return v___x_217_;
    }
}
pub unsafe fn l___private_Init_Control_Lawful_Instances_0__Option_elim_match__1_splitter___redArg(
    mut v_x_218_: *mut crate::leanh::LeanObject,
    mut v_x_219_: *mut crate::leanh::LeanObject,
    mut v_x_220_: *mut crate::leanh::LeanObject,
    mut v_h__1_221_: *mut crate::leanh::LeanObject,
    mut v_h__2_222_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_218_) == 0 {
        let mut v___x_223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_221_);
        v___x_223_ = crate::leanh::lean_apply_2(v_h__2_222_, v_x_219_, v_x_220_);
        return v___x_223_;
    } else {
        let mut v_val_224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_222_);
        v_val_224_ = crate::leanh::lean_ctor_get(v_x_218_, 0);
        crate::leanh::lean_inc(v_val_224_);
        crate::leanh::lean_dec_ref_known(v_x_218_, 1);
        v___x_225_ = crate::leanh::lean_apply_3(v_h__1_221_, v_val_224_, v_x_219_, v_x_220_);
        return v___x_225_;
    }
}
pub unsafe fn l___private_Init_Control_Lawful_Instances_0__Option_elim_match__1_splitter(
    mut v_00_u03b1_226_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_227_: *mut crate::leanh::LeanObject,
    mut v_motive_228_: *mut crate::leanh::LeanObject,
    mut v_x_229_: *mut crate::leanh::LeanObject,
    mut v_x_230_: *mut crate::leanh::LeanObject,
    mut v_x_231_: *mut crate::leanh::LeanObject,
    mut v_h__1_232_: *mut crate::leanh::LeanObject,
    mut v_h__2_233_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_229_) == 0 {
        let mut v___x_234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_232_);
        v___x_234_ = crate::leanh::lean_apply_2(v_h__2_233_, v_x_230_, v_x_231_);
        return v___x_234_;
    } else {
        let mut v_val_235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_233_);
        v_val_235_ = crate::leanh::lean_ctor_get(v_x_229_, 0);
        crate::leanh::lean_inc(v_val_235_);
        crate::leanh::lean_dec_ref_known(v_x_229_, 1);
        v___x_236_ = crate::leanh::lean_apply_3(v_h__1_232_, v_val_235_, v_x_230_, v_x_231_);
        return v___x_236_;
    }
}
pub unsafe fn l___private_Init_Control_Lawful_Instances_0__EStateM_adaptExcept_match__1_splitter___redArg(
    mut v_x_237_: *mut crate::leanh::LeanObject,
    mut v_h__1_238_: *mut crate::leanh::LeanObject,
    mut v_h__2_239_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_237_) == 0 {
        let mut v_a_240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_238_);
        v_a_240_ = crate::leanh::lean_ctor_get(v_x_237_, 0);
        crate::leanh::lean_inc(v_a_240_);
        v_a_241_ = crate::leanh::lean_ctor_get(v_x_237_, 1);
        crate::leanh::lean_inc(v_a_241_);
        crate::leanh::lean_dec_ref_known(v_x_237_, 2);
        v___x_242_ = crate::leanh::lean_apply_2(v_h__2_239_, v_a_240_, v_a_241_);
        return v___x_242_;
    } else {
        let mut v_a_243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_239_);
        v_a_243_ = crate::leanh::lean_ctor_get(v_x_237_, 0);
        crate::leanh::lean_inc(v_a_243_);
        v_a_244_ = crate::leanh::lean_ctor_get(v_x_237_, 1);
        crate::leanh::lean_inc(v_a_244_);
        crate::leanh::lean_dec_ref_known(v_x_237_, 2);
        v___x_245_ = crate::leanh::lean_apply_2(v_h__1_238_, v_a_243_, v_a_244_);
        return v___x_245_;
    }
}
pub unsafe fn l___private_Init_Control_Lawful_Instances_0__EStateM_adaptExcept_match__1_splitter(
    mut v_00_u03b5_246_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_247_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_248_: *mut crate::leanh::LeanObject,
    mut v_motive_249_: *mut crate::leanh::LeanObject,
    mut v_x_250_: *mut crate::leanh::LeanObject,
    mut v_h__1_251_: *mut crate::leanh::LeanObject,
    mut v_h__2_252_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_250_) == 0 {
        let mut v_a_253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_251_);
        v_a_253_ = crate::leanh::lean_ctor_get(v_x_250_, 0);
        crate::leanh::lean_inc(v_a_253_);
        v_a_254_ = crate::leanh::lean_ctor_get(v_x_250_, 1);
        crate::leanh::lean_inc(v_a_254_);
        crate::leanh::lean_dec_ref_known(v_x_250_, 2);
        v___x_255_ = crate::leanh::lean_apply_2(v_h__2_252_, v_a_253_, v_a_254_);
        return v___x_255_;
    } else {
        let mut v_a_256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_252_);
        v_a_256_ = crate::leanh::lean_ctor_get(v_x_250_, 0);
        crate::leanh::lean_inc(v_a_256_);
        v_a_257_ = crate::leanh::lean_ctor_get(v_x_250_, 1);
        crate::leanh::lean_inc(v_a_257_);
        crate::leanh::lean_dec_ref_known(v_x_250_, 2);
        v___x_258_ = crate::leanh::lean_apply_2(v_h__1_251_, v_a_256_, v_a_257_);
        return v___x_258_;
    }
}
pub unsafe fn l___private_Init_Control_Lawful_Instances_0__EStateM_run__bind_match__1_splitter___redArg(
    mut v_x_259_: *mut crate::leanh::LeanObject,
    mut v_h__1_260_: *mut crate::leanh::LeanObject,
    mut v_h__2_261_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_259_) == 0 {
        let mut v_a_262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_261_);
        v_a_262_ = crate::leanh::lean_ctor_get(v_x_259_, 0);
        crate::leanh::lean_inc(v_a_262_);
        v_a_263_ = crate::leanh::lean_ctor_get(v_x_259_, 1);
        crate::leanh::lean_inc(v_a_263_);
        crate::leanh::lean_dec_ref_known(v_x_259_, 2);
        v___x_264_ = crate::leanh::lean_apply_2(v_h__1_260_, v_a_262_, v_a_263_);
        return v___x_264_;
    } else {
        let mut v_a_265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_260_);
        v_a_265_ = crate::leanh::lean_ctor_get(v_x_259_, 0);
        crate::leanh::lean_inc(v_a_265_);
        v_a_266_ = crate::leanh::lean_ctor_get(v_x_259_, 1);
        crate::leanh::lean_inc(v_a_266_);
        crate::leanh::lean_dec_ref_known(v_x_259_, 2);
        v___x_267_ = crate::leanh::lean_apply_2(v_h__2_261_, v_a_265_, v_a_266_);
        return v___x_267_;
    }
}
pub unsafe fn l___private_Init_Control_Lawful_Instances_0__EStateM_run__bind_match__1_splitter(
    mut v_00_u03b5_268_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_269_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_270_: *mut crate::leanh::LeanObject,
    mut v_motive_271_: *mut crate::leanh::LeanObject,
    mut v_x_272_: *mut crate::leanh::LeanObject,
    mut v_h__1_273_: *mut crate::leanh::LeanObject,
    mut v_h__2_274_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_272_) == 0 {
        let mut v_a_275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_274_);
        v_a_275_ = crate::leanh::lean_ctor_get(v_x_272_, 0);
        crate::leanh::lean_inc(v_a_275_);
        v_a_276_ = crate::leanh::lean_ctor_get(v_x_272_, 1);
        crate::leanh::lean_inc(v_a_276_);
        crate::leanh::lean_dec_ref_known(v_x_272_, 2);
        v___x_277_ = crate::leanh::lean_apply_2(v_h__1_273_, v_a_275_, v_a_276_);
        return v___x_277_;
    } else {
        let mut v_a_278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_273_);
        v_a_278_ = crate::leanh::lean_ctor_get(v_x_272_, 0);
        crate::leanh::lean_inc(v_a_278_);
        v_a_279_ = crate::leanh::lean_ctor_get(v_x_272_, 1);
        crate::leanh::lean_inc(v_a_279_);
        crate::leanh::lean_dec_ref_known(v_x_272_, 2);
        v___x_280_ = crate::leanh::lean_apply_2(v_h__2_274_, v_a_278_, v_a_279_);
        return v___x_280_;
    }
}
pub unsafe fn l___private_Init_Control_Lawful_Instances_0__EStateM_bind_match__1_splitter___redArg(
    mut v_x_281_: *mut crate::leanh::LeanObject,
    mut v_h__1_282_: *mut crate::leanh::LeanObject,
    mut v_h__2_283_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_281_) == 0 {
        let mut v_a_284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_283_);
        v_a_284_ = crate::leanh::lean_ctor_get(v_x_281_, 0);
        crate::leanh::lean_inc(v_a_284_);
        v_a_285_ = crate::leanh::lean_ctor_get(v_x_281_, 1);
        crate::leanh::lean_inc(v_a_285_);
        crate::leanh::lean_dec_ref_known(v_x_281_, 2);
        v___x_286_ = crate::leanh::lean_apply_2(v_h__1_282_, v_a_284_, v_a_285_);
        return v___x_286_;
    } else {
        let mut v_a_287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_282_);
        v_a_287_ = crate::leanh::lean_ctor_get(v_x_281_, 0);
        crate::leanh::lean_inc(v_a_287_);
        v_a_288_ = crate::leanh::lean_ctor_get(v_x_281_, 1);
        crate::leanh::lean_inc(v_a_288_);
        crate::leanh::lean_dec_ref_known(v_x_281_, 2);
        v___x_289_ = crate::leanh::lean_apply_2(v_h__2_283_, v_a_287_, v_a_288_);
        return v___x_289_;
    }
}
pub unsafe fn l___private_Init_Control_Lawful_Instances_0__EStateM_bind_match__1_splitter(
    mut v_00_u03b5_290_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_291_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_292_: *mut crate::leanh::LeanObject,
    mut v_motive_293_: *mut crate::leanh::LeanObject,
    mut v_x_294_: *mut crate::leanh::LeanObject,
    mut v_h__1_295_: *mut crate::leanh::LeanObject,
    mut v_h__2_296_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_294_) == 0 {
        let mut v_a_297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_296_);
        v_a_297_ = crate::leanh::lean_ctor_get(v_x_294_, 0);
        crate::leanh::lean_inc(v_a_297_);
        v_a_298_ = crate::leanh::lean_ctor_get(v_x_294_, 1);
        crate::leanh::lean_inc(v_a_298_);
        crate::leanh::lean_dec_ref_known(v_x_294_, 2);
        v___x_299_ = crate::leanh::lean_apply_2(v_h__1_295_, v_a_297_, v_a_298_);
        return v___x_299_;
    } else {
        let mut v_a_300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_295_);
        v_a_300_ = crate::leanh::lean_ctor_get(v_x_294_, 0);
        crate::leanh::lean_inc(v_a_300_);
        v_a_301_ = crate::leanh::lean_ctor_get(v_x_294_, 1);
        crate::leanh::lean_inc(v_a_301_);
        crate::leanh::lean_dec_ref_known(v_x_294_, 2);
        v___x_302_ = crate::leanh::lean_apply_2(v_h__2_296_, v_a_300_, v_a_301_);
        return v___x_302_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Control_Lawful_Instances(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Control_Lawful_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Control_Except(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Control_Option(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Control_Option(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Control_State(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Control_StateRef(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Control_State(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Ext(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Control_Lawful_Instances(
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
pub unsafe fn initialize_Init_Control_Lawful_Instances(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Control_Lawful_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Control_Except(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Control_Option(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Control_Option(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Control_State(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Control_StateRef(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Control_State(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Ext(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Control_Lawful_Instances(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Control_Lawful_Instances(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Control_Lawful_Instances(builtin);
}
