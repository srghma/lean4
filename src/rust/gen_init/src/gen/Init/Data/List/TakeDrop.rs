// Lean compiler output
// Module: Init.Data.List.TakeDrop
// Imports: Init.Data.List.Basic Init.BinderPredicates Init.Ext Init.ByCases Init.Data.Bool Init.Data.List.Lemmas Init.Data.Nat.Div.Basic Init.Data.Option.Lemmas
use crate::ffi::{lean_nat_dec_eq, lean_nat_sub};
use crate::r#gen::Init::BinderPredicates::{
    initialize_Init_BinderPredicates, runtime_initialize_Init_BinderPredicates,
};
use crate::r#gen::Init::ByCases::{initialize_Init_ByCases, runtime_initialize_Init_ByCases};
use crate::r#gen::Init::Data::Bool::{
    initialize_Init_Data_Bool, runtime_initialize_Init_Data_Bool,
};
use crate::r#gen::Init::Data::List::Basic::{
    initialize_Init_Data_List_Basic, runtime_initialize_Init_Data_List_Basic,
};
use crate::r#gen::Init::Data::List::Lemmas::{
    initialize_Init_Data_List_Lemmas, runtime_initialize_Init_Data_List_Lemmas,
};
use crate::r#gen::Init::Data::Nat::Div::Basic::{
    initialize_Init_Data_Nat_Div_Basic, runtime_initialize_Init_Data_Nat_Div_Basic,
};
use crate::r#gen::Init::Data::Option::Lemmas::{
    initialize_Init_Data_Option_Lemmas, runtime_initialize_Init_Data_Option_Lemmas,
};
use crate::r#gen::Init::Ext::{initialize_Init_Ext, runtime_initialize_Init_Ext};
pub unsafe fn l___private_Init_Data_List_TakeDrop_0__List_take_match__1_splitter___redArg(
    mut v_x_137_: *mut leanh::LeanObject,
    mut v_x_138_: *mut leanh::LeanObject,
    mut v_h__1_139_: *mut leanh::LeanObject,
    mut v_h__2_140_: *mut leanh::LeanObject,
    mut v_h__3_141_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_143_: u8 = 0;
    v_zero_142_ = leanh::lean_unsigned_to_nat(0);
    v_isZero_143_ = lean_nat_dec_eq(v_x_137_, v_zero_142_);
    if v_isZero_143_ == 1 {
        let mut v___x_144_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__3_141_);
        leanh::lean_dec(v_h__2_140_);
        v___x_144_ = leanh::lean_apply_1(v_h__1_139_, v_x_138_);
        return v___x_144_;
    } else {
        let mut v_one_145_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_146_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_139_);
        v_one_145_ = leanh::lean_unsigned_to_nat(1);
        v_n_146_ = lean_nat_sub(v_x_137_, v_one_145_);
        if leanh::lean_obj_tag(v_x_138_) == 0 {
            let mut v___x_147_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_141_);
            v___x_147_ = leanh::lean_apply_1(v_h__2_140_, v_n_146_);
            return v___x_147_;
        } else {
            let mut v_head_148_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_tail_149_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_150_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_140_);
            v_head_148_ = leanh::lean_ctor_get(v_x_138_, 0);
            leanh::lean_inc(v_head_148_);
            v_tail_149_ = leanh::lean_ctor_get(v_x_138_, 1);
            leanh::lean_inc(v_tail_149_);
            leanh::lean_dec_ref_known(v_x_138_, 2);
            v___x_150_ =
                leanh::lean_apply_3(v_h__3_141_, v_n_146_, v_head_148_, v_tail_149_);
            return v___x_150_;
        }
    }
}
pub unsafe fn l___private_Init_Data_List_TakeDrop_0__List_take_match__1_splitter___redArg___boxed(
    mut v_x_151_: *mut leanh::LeanObject,
    mut v_x_152_: *mut leanh::LeanObject,
    mut v_h__1_153_: *mut leanh::LeanObject,
    mut v_h__2_154_: *mut leanh::LeanObject,
    mut v_h__3_155_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_156_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_156_ = l___private_Init_Data_List_TakeDrop_0__List_take_match__1_splitter___redArg(
        v_x_151_,
        v_x_152_,
        v_h__1_153_,
        v_h__2_154_,
        v_h__3_155_,
    );
    leanh::lean_dec(v_x_151_);
    return v_res_156_;
}
pub unsafe fn l___private_Init_Data_List_TakeDrop_0__List_take_match__1_splitter(
    mut v_00_u03b1_157_: *mut leanh::LeanObject,
    mut v_motive_158_: *mut leanh::LeanObject,
    mut v_x_159_: *mut leanh::LeanObject,
    mut v_x_160_: *mut leanh::LeanObject,
    mut v_h__1_161_: *mut leanh::LeanObject,
    mut v_h__2_162_: *mut leanh::LeanObject,
    mut v_h__3_163_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_165_: u8 = 0;
    v_zero_164_ = leanh::lean_unsigned_to_nat(0);
    v_isZero_165_ = lean_nat_dec_eq(v_x_159_, v_zero_164_);
    if v_isZero_165_ == 1 {
        let mut v___x_166_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__3_163_);
        leanh::lean_dec(v_h__2_162_);
        v___x_166_ = leanh::lean_apply_1(v_h__1_161_, v_x_160_);
        return v___x_166_;
    } else {
        let mut v_one_167_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_168_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_161_);
        v_one_167_ = leanh::lean_unsigned_to_nat(1);
        v_n_168_ = lean_nat_sub(v_x_159_, v_one_167_);
        if leanh::lean_obj_tag(v_x_160_) == 0 {
            let mut v___x_169_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_163_);
            v___x_169_ = leanh::lean_apply_1(v_h__2_162_, v_n_168_);
            return v___x_169_;
        } else {
            let mut v_head_170_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_tail_171_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_172_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_162_);
            v_head_170_ = leanh::lean_ctor_get(v_x_160_, 0);
            leanh::lean_inc(v_head_170_);
            v_tail_171_ = leanh::lean_ctor_get(v_x_160_, 1);
            leanh::lean_inc(v_tail_171_);
            leanh::lean_dec_ref_known(v_x_160_, 2);
            v___x_172_ =
                leanh::lean_apply_3(v_h__3_163_, v_n_168_, v_head_170_, v_tail_171_);
            return v___x_172_;
        }
    }
}
pub unsafe fn l___private_Init_Data_List_TakeDrop_0__List_take_match__1_splitter___boxed(
    mut v_00_u03b1_173_: *mut leanh::LeanObject,
    mut v_motive_174_: *mut leanh::LeanObject,
    mut v_x_175_: *mut leanh::LeanObject,
    mut v_x_176_: *mut leanh::LeanObject,
    mut v_h__1_177_: *mut leanh::LeanObject,
    mut v_h__2_178_: *mut leanh::LeanObject,
    mut v_h__3_179_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_180_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_180_ = l___private_Init_Data_List_TakeDrop_0__List_take_match__1_splitter(
        v_00_u03b1_173_,
        v_motive_174_,
        v_x_175_,
        v_x_176_,
        v_h__1_177_,
        v_h__2_178_,
        v_h__3_179_,
    );
    leanh::lean_dec(v_x_175_);
    return v_res_180_;
}
pub unsafe fn l___private_Init_Data_List_TakeDrop_0__Option_instDecidableEq_match__1_splitter___redArg(
    mut v_b_181_: *mut leanh::LeanObject,
    mut v_h__1_182_: *mut leanh::LeanObject,
    mut v_h__2_183_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_b_181_) == 0 {
        let mut v___x_184_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_185_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_183_);
        v___x_184_ = leanh::lean_box(0);
        v___x_185_ = leanh::lean_apply_1(v_h__1_182_, v___x_184_);
        return v___x_185_;
    } else {
        let mut v_val_186_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_187_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_182_);
        v_val_186_ = leanh::lean_ctor_get(v_b_181_, 0);
        leanh::lean_inc(v_val_186_);
        leanh::lean_dec_ref_known(v_b_181_, 1);
        v___x_187_ = leanh::lean_apply_1(v_h__2_183_, v_val_186_);
        return v___x_187_;
    }
}
pub unsafe fn l___private_Init_Data_List_TakeDrop_0__Option_instDecidableEq_match__1_splitter(
    mut v_00_u03b1_188_: *mut leanh::LeanObject,
    mut v_motive_189_: *mut leanh::LeanObject,
    mut v_b_190_: *mut leanh::LeanObject,
    mut v_h__1_191_: *mut leanh::LeanObject,
    mut v_h__2_192_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_b_190_) == 0 {
        let mut v___x_193_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_194_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_192_);
        v___x_193_ = leanh::lean_box(0);
        v___x_194_ = leanh::lean_apply_1(v_h__1_191_, v___x_193_);
        return v___x_194_;
    } else {
        let mut v_val_195_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_196_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_191_);
        v_val_195_ = leanh::lean_ctor_get(v_b_190_, 0);
        leanh::lean_inc(v_val_195_);
        leanh::lean_dec_ref_known(v_b_190_, 1);
        v___x_196_ = leanh::lean_apply_1(v_h__2_192_, v_val_195_);
        return v___x_196_;
    }
}
pub unsafe fn l___private_Init_Data_List_TakeDrop_0__List_getLast_x3f_match__1_splitter___redArg(
    mut v_x_197_: *mut leanh::LeanObject,
    mut v_h__1_198_: *mut leanh::LeanObject,
    mut v_h__2_199_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_197_) == 0 {
        let mut v___x_200_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_201_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_199_);
        v___x_200_ = leanh::lean_box(0);
        v___x_201_ = leanh::lean_apply_1(v_h__1_198_, v___x_200_);
        return v___x_201_;
    } else {
        let mut v_head_202_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_203_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_204_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_198_);
        v_head_202_ = leanh::lean_ctor_get(v_x_197_, 0);
        leanh::lean_inc(v_head_202_);
        v_tail_203_ = leanh::lean_ctor_get(v_x_197_, 1);
        leanh::lean_inc(v_tail_203_);
        leanh::lean_dec_ref_known(v_x_197_, 2);
        v___x_204_ = leanh::lean_apply_2(v_h__2_199_, v_head_202_, v_tail_203_);
        return v___x_204_;
    }
}
pub unsafe fn l___private_Init_Data_List_TakeDrop_0__List_getLast_x3f_match__1_splitter(
    mut v_00_u03b1_205_: *mut leanh::LeanObject,
    mut v_motive_206_: *mut leanh::LeanObject,
    mut v_x_207_: *mut leanh::LeanObject,
    mut v_h__1_208_: *mut leanh::LeanObject,
    mut v_h__2_209_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_207_) == 0 {
        let mut v___x_210_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_211_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_209_);
        v___x_210_ = leanh::lean_box(0);
        v___x_211_ = leanh::lean_apply_1(v_h__1_208_, v___x_210_);
        return v___x_211_;
    } else {
        let mut v_head_212_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_213_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_214_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_208_);
        v_head_212_ = leanh::lean_ctor_get(v_x_207_, 0);
        leanh::lean_inc(v_head_212_);
        v_tail_213_ = leanh::lean_ctor_get(v_x_207_, 1);
        leanh::lean_inc(v_tail_213_);
        leanh::lean_dec_ref_known(v_x_207_, 2);
        v___x_214_ = leanh::lean_apply_2(v_h__2_209_, v_head_212_, v_tail_213_);
        return v___x_214_;
    }
}
pub unsafe fn l___private_Init_Data_List_TakeDrop_0__List_filter_match__1_splitter___redArg(
    mut v_x_215_: u8,
    mut v_h__1_216_: *mut leanh::LeanObject,
    mut v_h__2_217_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if v_x_215_ == 0 {
        let mut v___x_218_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_219_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_216_);
        v___x_218_ = leanh::lean_box(0);
        v___x_219_ = leanh::lean_apply_1(v_h__2_217_, v___x_218_);
        return v___x_219_;
    } else {
        let mut v___x_220_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_221_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_217_);
        v___x_220_ = leanh::lean_box(0);
        v___x_221_ = leanh::lean_apply_1(v_h__1_216_, v___x_220_);
        return v___x_221_;
    }
}
pub unsafe fn l___private_Init_Data_List_TakeDrop_0__List_filter_match__1_splitter___redArg___boxed(
    mut v_x_222_: *mut leanh::LeanObject,
    mut v_h__1_223_: *mut leanh::LeanObject,
    mut v_h__2_224_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_26__boxed_225_: u8 = 0;
    let mut v_res_226_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_26__boxed_225_ = (leanh::lean_unbox(v_x_222_) as u8);
    v_res_226_ = l___private_Init_Data_List_TakeDrop_0__List_filter_match__1_splitter___redArg(
        v_x_26__boxed_225_,
        v_h__1_223_,
        v_h__2_224_,
    );
    return v_res_226_;
}
pub unsafe fn l___private_Init_Data_List_TakeDrop_0__List_filter_match__1_splitter(
    mut v_motive_227_: *mut leanh::LeanObject,
    mut v_x_228_: u8,
    mut v_h__1_229_: *mut leanh::LeanObject,
    mut v_h__2_230_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if v_x_228_ == 0 {
        let mut v___x_231_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_232_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_229_);
        v___x_231_ = leanh::lean_box(0);
        v___x_232_ = leanh::lean_apply_1(v_h__2_230_, v___x_231_);
        return v___x_232_;
    } else {
        let mut v___x_233_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_234_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_230_);
        v___x_233_ = leanh::lean_box(0);
        v___x_234_ = leanh::lean_apply_1(v_h__1_229_, v___x_233_);
        return v___x_234_;
    }
}
pub unsafe fn l___private_Init_Data_List_TakeDrop_0__List_filter_match__1_splitter___boxed(
    mut v_motive_235_: *mut leanh::LeanObject,
    mut v_x_236_: *mut leanh::LeanObject,
    mut v_h__1_237_: *mut leanh::LeanObject,
    mut v_h__2_238_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_37__boxed_239_: u8 = 0;
    let mut v_res_240_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_37__boxed_239_ = (leanh::lean_unbox(v_x_236_) as u8);
    v_res_240_ = l___private_Init_Data_List_TakeDrop_0__List_filter_match__1_splitter(
        v_motive_235_,
        v_x_37__boxed_239_,
        v_h__1_237_,
        v_h__2_238_,
    );
    return v_res_240_;
}
pub unsafe fn l___private_Init_Data_List_TakeDrop_0__List_head_x3f__dropWhile__not_match__1_splitter___redArg(
    mut v_x_241_: *mut leanh::LeanObject,
    mut v_h__1_242_: *mut leanh::LeanObject,
    mut v_h__2_243_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_241_) == 0 {
        let mut v___x_244_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_245_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_242_);
        v___x_244_ = leanh::lean_box(0);
        v___x_245_ = leanh::lean_apply_1(v_h__2_243_, v___x_244_);
        return v___x_245_;
    } else {
        let mut v_val_246_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_247_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_243_);
        v_val_246_ = leanh::lean_ctor_get(v_x_241_, 0);
        leanh::lean_inc(v_val_246_);
        leanh::lean_dec_ref_known(v_x_241_, 1);
        v___x_247_ = leanh::lean_apply_1(v_h__1_242_, v_val_246_);
        return v___x_247_;
    }
}
pub unsafe fn l___private_Init_Data_List_TakeDrop_0__List_head_x3f__dropWhile__not_match__1_splitter(
    mut v_00_u03b1_248_: *mut leanh::LeanObject,
    mut v_motive_249_: *mut leanh::LeanObject,
    mut v_x_250_: *mut leanh::LeanObject,
    mut v_h__1_251_: *mut leanh::LeanObject,
    mut v_h__2_252_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_250_) == 0 {
        let mut v___x_253_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_254_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_251_);
        v___x_253_ = leanh::lean_box(0);
        v___x_254_ = leanh::lean_apply_1(v_h__2_252_, v___x_253_);
        return v___x_254_;
    } else {
        let mut v_val_255_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_256_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_252_);
        v_val_255_ = leanh::lean_ctor_get(v_x_250_, 0);
        leanh::lean_inc(v_val_255_);
        leanh::lean_dec_ref_known(v_x_250_, 1);
        v___x_256_ = leanh::lean_apply_1(v_h__1_251_, v_val_255_);
        return v___x_256_;
    }
}
pub unsafe fn l___private_Init_Data_List_TakeDrop_0__List_filterMap_match__1_splitter___redArg(
    mut v_x_257_: *mut leanh::LeanObject,
    mut v_h__1_258_: *mut leanh::LeanObject,
    mut v_h__2_259_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_257_) == 0 {
        let mut v___x_260_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_261_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_259_);
        v___x_260_ = leanh::lean_box(0);
        v___x_261_ = leanh::lean_apply_1(v_h__1_258_, v___x_260_);
        return v___x_261_;
    } else {
        let mut v_val_262_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_263_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_258_);
        v_val_262_ = leanh::lean_ctor_get(v_x_257_, 0);
        leanh::lean_inc(v_val_262_);
        leanh::lean_dec_ref_known(v_x_257_, 1);
        v___x_263_ = leanh::lean_apply_1(v_h__2_259_, v_val_262_);
        return v___x_263_;
    }
}
pub unsafe fn l___private_Init_Data_List_TakeDrop_0__List_filterMap_match__1_splitter(
    mut v_00_u03b2_264_: *mut leanh::LeanObject,
    mut v_motive_265_: *mut leanh::LeanObject,
    mut v_x_266_: *mut leanh::LeanObject,
    mut v_h__1_267_: *mut leanh::LeanObject,
    mut v_h__2_268_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_266_) == 0 {
        let mut v___x_269_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_270_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_268_);
        v___x_269_ = leanh::lean_box(0);
        v___x_270_ = leanh::lean_apply_1(v_h__1_267_, v___x_269_);
        return v___x_270_;
    } else {
        let mut v_val_271_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_272_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_267_);
        v_val_271_ = leanh::lean_ctor_get(v_x_266_, 0);
        leanh::lean_inc(v_val_271_);
        leanh::lean_dec_ref_known(v_x_266_, 1);
        v___x_272_ = leanh::lean_apply_1(v_h__2_268_, v_val_271_);
        return v___x_272_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_List_TakeDrop(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_List_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_BinderPredicates(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Ext(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_ByCases(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Bool(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Div_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_List_TakeDrop(
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
pub unsafe fn initialize_Init_Data_List_TakeDrop(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_List_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_BinderPredicates(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Ext(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_ByCases(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Bool(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Div_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Option_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_TakeDrop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_List_TakeDrop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_List_TakeDrop(builtin);
}