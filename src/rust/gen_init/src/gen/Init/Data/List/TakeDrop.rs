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
    mut v_x_137_: *mut crate::leanh::LeanObject,
    mut v_x_138_: *mut crate::leanh::LeanObject,
    mut v_h__1_139_: *mut crate::leanh::LeanObject,
    mut v_h__2_140_: *mut crate::leanh::LeanObject,
    mut v_h__3_141_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_143_: u8 = 0;
    v_zero_142_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_143_ = lean_nat_dec_eq(v_x_137_, v_zero_142_);
    if v_isZero_143_ == 1 {
        let mut v___x_144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__3_141_);
        crate::leanh::lean_dec(v_h__2_140_);
        v___x_144_ = crate::leanh::lean_apply_1(v_h__1_139_, v_x_138_);
        return v___x_144_;
    } else {
        let mut v_one_145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_139_);
        v_one_145_ = crate::leanh::lean_unsigned_to_nat(1);
        v_n_146_ = lean_nat_sub(v_x_137_, v_one_145_);
        if crate::leanh::lean_obj_tag(v_x_138_) == 0 {
            let mut v___x_147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_141_);
            v___x_147_ = crate::leanh::lean_apply_1(v_h__2_140_, v_n_146_);
            return v___x_147_;
        } else {
            let mut v_head_148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_tail_149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_140_);
            v_head_148_ = crate::leanh::lean_ctor_get(v_x_138_, 0);
            crate::leanh::lean_inc(v_head_148_);
            v_tail_149_ = crate::leanh::lean_ctor_get(v_x_138_, 1);
            crate::leanh::lean_inc(v_tail_149_);
            crate::leanh::lean_dec_ref_known(v_x_138_, 2);
            v___x_150_ =
                crate::leanh::lean_apply_3(v_h__3_141_, v_n_146_, v_head_148_, v_tail_149_);
            return v___x_150_;
        }
    }
}
pub unsafe fn l___private_Init_Data_List_TakeDrop_0__List_take_match__1_splitter___redArg___boxed(
    mut v_x_151_: *mut crate::leanh::LeanObject,
    mut v_x_152_: *mut crate::leanh::LeanObject,
    mut v_h__1_153_: *mut crate::leanh::LeanObject,
    mut v_h__2_154_: *mut crate::leanh::LeanObject,
    mut v_h__3_155_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_156_ = l___private_Init_Data_List_TakeDrop_0__List_take_match__1_splitter___redArg(
        v_x_151_,
        v_x_152_,
        v_h__1_153_,
        v_h__2_154_,
        v_h__3_155_,
    );
    crate::leanh::lean_dec(v_x_151_);
    return v_res_156_;
}
pub unsafe fn l___private_Init_Data_List_TakeDrop_0__List_take_match__1_splitter(
    mut v_00_u03b1_157_: *mut crate::leanh::LeanObject,
    mut v_motive_158_: *mut crate::leanh::LeanObject,
    mut v_x_159_: *mut crate::leanh::LeanObject,
    mut v_x_160_: *mut crate::leanh::LeanObject,
    mut v_h__1_161_: *mut crate::leanh::LeanObject,
    mut v_h__2_162_: *mut crate::leanh::LeanObject,
    mut v_h__3_163_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_165_: u8 = 0;
    v_zero_164_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_165_ = lean_nat_dec_eq(v_x_159_, v_zero_164_);
    if v_isZero_165_ == 1 {
        let mut v___x_166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__3_163_);
        crate::leanh::lean_dec(v_h__2_162_);
        v___x_166_ = crate::leanh::lean_apply_1(v_h__1_161_, v_x_160_);
        return v___x_166_;
    } else {
        let mut v_one_167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_161_);
        v_one_167_ = crate::leanh::lean_unsigned_to_nat(1);
        v_n_168_ = lean_nat_sub(v_x_159_, v_one_167_);
        if crate::leanh::lean_obj_tag(v_x_160_) == 0 {
            let mut v___x_169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_163_);
            v___x_169_ = crate::leanh::lean_apply_1(v_h__2_162_, v_n_168_);
            return v___x_169_;
        } else {
            let mut v_head_170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_tail_171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_162_);
            v_head_170_ = crate::leanh::lean_ctor_get(v_x_160_, 0);
            crate::leanh::lean_inc(v_head_170_);
            v_tail_171_ = crate::leanh::lean_ctor_get(v_x_160_, 1);
            crate::leanh::lean_inc(v_tail_171_);
            crate::leanh::lean_dec_ref_known(v_x_160_, 2);
            v___x_172_ =
                crate::leanh::lean_apply_3(v_h__3_163_, v_n_168_, v_head_170_, v_tail_171_);
            return v___x_172_;
        }
    }
}
pub unsafe fn l___private_Init_Data_List_TakeDrop_0__List_take_match__1_splitter___boxed(
    mut v_00_u03b1_173_: *mut crate::leanh::LeanObject,
    mut v_motive_174_: *mut crate::leanh::LeanObject,
    mut v_x_175_: *mut crate::leanh::LeanObject,
    mut v_x_176_: *mut crate::leanh::LeanObject,
    mut v_h__1_177_: *mut crate::leanh::LeanObject,
    mut v_h__2_178_: *mut crate::leanh::LeanObject,
    mut v_h__3_179_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_180_ = l___private_Init_Data_List_TakeDrop_0__List_take_match__1_splitter(
        v_00_u03b1_173_,
        v_motive_174_,
        v_x_175_,
        v_x_176_,
        v_h__1_177_,
        v_h__2_178_,
        v_h__3_179_,
    );
    crate::leanh::lean_dec(v_x_175_);
    return v_res_180_;
}
pub unsafe fn l___private_Init_Data_List_TakeDrop_0__Option_instDecidableEq_match__1_splitter___redArg(
    mut v_b_181_: *mut crate::leanh::LeanObject,
    mut v_h__1_182_: *mut crate::leanh::LeanObject,
    mut v_h__2_183_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_b_181_) == 0 {
        let mut v___x_184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_183_);
        v___x_184_ = crate::leanh::lean_box(0);
        v___x_185_ = crate::leanh::lean_apply_1(v_h__1_182_, v___x_184_);
        return v___x_185_;
    } else {
        let mut v_val_186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_182_);
        v_val_186_ = crate::leanh::lean_ctor_get(v_b_181_, 0);
        crate::leanh::lean_inc(v_val_186_);
        crate::leanh::lean_dec_ref_known(v_b_181_, 1);
        v___x_187_ = crate::leanh::lean_apply_1(v_h__2_183_, v_val_186_);
        return v___x_187_;
    }
}
pub unsafe fn l___private_Init_Data_List_TakeDrop_0__Option_instDecidableEq_match__1_splitter(
    mut v_00_u03b1_188_: *mut crate::leanh::LeanObject,
    mut v_motive_189_: *mut crate::leanh::LeanObject,
    mut v_b_190_: *mut crate::leanh::LeanObject,
    mut v_h__1_191_: *mut crate::leanh::LeanObject,
    mut v_h__2_192_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_b_190_) == 0 {
        let mut v___x_193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_192_);
        v___x_193_ = crate::leanh::lean_box(0);
        v___x_194_ = crate::leanh::lean_apply_1(v_h__1_191_, v___x_193_);
        return v___x_194_;
    } else {
        let mut v_val_195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_191_);
        v_val_195_ = crate::leanh::lean_ctor_get(v_b_190_, 0);
        crate::leanh::lean_inc(v_val_195_);
        crate::leanh::lean_dec_ref_known(v_b_190_, 1);
        v___x_196_ = crate::leanh::lean_apply_1(v_h__2_192_, v_val_195_);
        return v___x_196_;
    }
}
pub unsafe fn l___private_Init_Data_List_TakeDrop_0__List_getLast_x3f_match__1_splitter___redArg(
    mut v_x_197_: *mut crate::leanh::LeanObject,
    mut v_h__1_198_: *mut crate::leanh::LeanObject,
    mut v_h__2_199_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_197_) == 0 {
        let mut v___x_200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_199_);
        v___x_200_ = crate::leanh::lean_box(0);
        v___x_201_ = crate::leanh::lean_apply_1(v_h__1_198_, v___x_200_);
        return v___x_201_;
    } else {
        let mut v_head_202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_198_);
        v_head_202_ = crate::leanh::lean_ctor_get(v_x_197_, 0);
        crate::leanh::lean_inc(v_head_202_);
        v_tail_203_ = crate::leanh::lean_ctor_get(v_x_197_, 1);
        crate::leanh::lean_inc(v_tail_203_);
        crate::leanh::lean_dec_ref_known(v_x_197_, 2);
        v___x_204_ = crate::leanh::lean_apply_2(v_h__2_199_, v_head_202_, v_tail_203_);
        return v___x_204_;
    }
}
pub unsafe fn l___private_Init_Data_List_TakeDrop_0__List_getLast_x3f_match__1_splitter(
    mut v_00_u03b1_205_: *mut crate::leanh::LeanObject,
    mut v_motive_206_: *mut crate::leanh::LeanObject,
    mut v_x_207_: *mut crate::leanh::LeanObject,
    mut v_h__1_208_: *mut crate::leanh::LeanObject,
    mut v_h__2_209_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_207_) == 0 {
        let mut v___x_210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_209_);
        v___x_210_ = crate::leanh::lean_box(0);
        v___x_211_ = crate::leanh::lean_apply_1(v_h__1_208_, v___x_210_);
        return v___x_211_;
    } else {
        let mut v_head_212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_208_);
        v_head_212_ = crate::leanh::lean_ctor_get(v_x_207_, 0);
        crate::leanh::lean_inc(v_head_212_);
        v_tail_213_ = crate::leanh::lean_ctor_get(v_x_207_, 1);
        crate::leanh::lean_inc(v_tail_213_);
        crate::leanh::lean_dec_ref_known(v_x_207_, 2);
        v___x_214_ = crate::leanh::lean_apply_2(v_h__2_209_, v_head_212_, v_tail_213_);
        return v___x_214_;
    }
}
pub unsafe fn l___private_Init_Data_List_TakeDrop_0__List_filter_match__1_splitter___redArg(
    mut v_x_215_: u8,
    mut v_h__1_216_: *mut crate::leanh::LeanObject,
    mut v_h__2_217_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if v_x_215_ == 0 {
        let mut v___x_218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_216_);
        v___x_218_ = crate::leanh::lean_box(0);
        v___x_219_ = crate::leanh::lean_apply_1(v_h__2_217_, v___x_218_);
        return v___x_219_;
    } else {
        let mut v___x_220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_217_);
        v___x_220_ = crate::leanh::lean_box(0);
        v___x_221_ = crate::leanh::lean_apply_1(v_h__1_216_, v___x_220_);
        return v___x_221_;
    }
}
pub unsafe fn l___private_Init_Data_List_TakeDrop_0__List_filter_match__1_splitter___redArg___boxed(
    mut v_x_222_: *mut crate::leanh::LeanObject,
    mut v_h__1_223_: *mut crate::leanh::LeanObject,
    mut v_h__2_224_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_26__boxed_225_: u8 = 0;
    let mut v_res_226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_26__boxed_225_ = (crate::leanh::lean_unbox(v_x_222_) as u8);
    v_res_226_ = l___private_Init_Data_List_TakeDrop_0__List_filter_match__1_splitter___redArg(
        v_x_26__boxed_225_,
        v_h__1_223_,
        v_h__2_224_,
    );
    return v_res_226_;
}
pub unsafe fn l___private_Init_Data_List_TakeDrop_0__List_filter_match__1_splitter(
    mut v_motive_227_: *mut crate::leanh::LeanObject,
    mut v_x_228_: u8,
    mut v_h__1_229_: *mut crate::leanh::LeanObject,
    mut v_h__2_230_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if v_x_228_ == 0 {
        let mut v___x_231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_229_);
        v___x_231_ = crate::leanh::lean_box(0);
        v___x_232_ = crate::leanh::lean_apply_1(v_h__2_230_, v___x_231_);
        return v___x_232_;
    } else {
        let mut v___x_233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_230_);
        v___x_233_ = crate::leanh::lean_box(0);
        v___x_234_ = crate::leanh::lean_apply_1(v_h__1_229_, v___x_233_);
        return v___x_234_;
    }
}
pub unsafe fn l___private_Init_Data_List_TakeDrop_0__List_filter_match__1_splitter___boxed(
    mut v_motive_235_: *mut crate::leanh::LeanObject,
    mut v_x_236_: *mut crate::leanh::LeanObject,
    mut v_h__1_237_: *mut crate::leanh::LeanObject,
    mut v_h__2_238_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_37__boxed_239_: u8 = 0;
    let mut v_res_240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_37__boxed_239_ = (crate::leanh::lean_unbox(v_x_236_) as u8);
    v_res_240_ = l___private_Init_Data_List_TakeDrop_0__List_filter_match__1_splitter(
        v_motive_235_,
        v_x_37__boxed_239_,
        v_h__1_237_,
        v_h__2_238_,
    );
    return v_res_240_;
}
pub unsafe fn l___private_Init_Data_List_TakeDrop_0__List_head_x3f__dropWhile__not_match__1_splitter___redArg(
    mut v_x_241_: *mut crate::leanh::LeanObject,
    mut v_h__1_242_: *mut crate::leanh::LeanObject,
    mut v_h__2_243_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_241_) == 0 {
        let mut v___x_244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_242_);
        v___x_244_ = crate::leanh::lean_box(0);
        v___x_245_ = crate::leanh::lean_apply_1(v_h__2_243_, v___x_244_);
        return v___x_245_;
    } else {
        let mut v_val_246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_243_);
        v_val_246_ = crate::leanh::lean_ctor_get(v_x_241_, 0);
        crate::leanh::lean_inc(v_val_246_);
        crate::leanh::lean_dec_ref_known(v_x_241_, 1);
        v___x_247_ = crate::leanh::lean_apply_1(v_h__1_242_, v_val_246_);
        return v___x_247_;
    }
}
pub unsafe fn l___private_Init_Data_List_TakeDrop_0__List_head_x3f__dropWhile__not_match__1_splitter(
    mut v_00_u03b1_248_: *mut crate::leanh::LeanObject,
    mut v_motive_249_: *mut crate::leanh::LeanObject,
    mut v_x_250_: *mut crate::leanh::LeanObject,
    mut v_h__1_251_: *mut crate::leanh::LeanObject,
    mut v_h__2_252_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_250_) == 0 {
        let mut v___x_253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_251_);
        v___x_253_ = crate::leanh::lean_box(0);
        v___x_254_ = crate::leanh::lean_apply_1(v_h__2_252_, v___x_253_);
        return v___x_254_;
    } else {
        let mut v_val_255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_252_);
        v_val_255_ = crate::leanh::lean_ctor_get(v_x_250_, 0);
        crate::leanh::lean_inc(v_val_255_);
        crate::leanh::lean_dec_ref_known(v_x_250_, 1);
        v___x_256_ = crate::leanh::lean_apply_1(v_h__1_251_, v_val_255_);
        return v___x_256_;
    }
}
pub unsafe fn l___private_Init_Data_List_TakeDrop_0__List_filterMap_match__1_splitter___redArg(
    mut v_x_257_: *mut crate::leanh::LeanObject,
    mut v_h__1_258_: *mut crate::leanh::LeanObject,
    mut v_h__2_259_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_257_) == 0 {
        let mut v___x_260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_259_);
        v___x_260_ = crate::leanh::lean_box(0);
        v___x_261_ = crate::leanh::lean_apply_1(v_h__1_258_, v___x_260_);
        return v___x_261_;
    } else {
        let mut v_val_262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_258_);
        v_val_262_ = crate::leanh::lean_ctor_get(v_x_257_, 0);
        crate::leanh::lean_inc(v_val_262_);
        crate::leanh::lean_dec_ref_known(v_x_257_, 1);
        v___x_263_ = crate::leanh::lean_apply_1(v_h__2_259_, v_val_262_);
        return v___x_263_;
    }
}
pub unsafe fn l___private_Init_Data_List_TakeDrop_0__List_filterMap_match__1_splitter(
    mut v_00_u03b2_264_: *mut crate::leanh::LeanObject,
    mut v_motive_265_: *mut crate::leanh::LeanObject,
    mut v_x_266_: *mut crate::leanh::LeanObject,
    mut v_h__1_267_: *mut crate::leanh::LeanObject,
    mut v_h__2_268_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_266_) == 0 {
        let mut v___x_269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_268_);
        v___x_269_ = crate::leanh::lean_box(0);
        v___x_270_ = crate::leanh::lean_apply_1(v_h__1_267_, v___x_269_);
        return v___x_270_;
    } else {
        let mut v_val_271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_267_);
        v_val_271_ = crate::leanh::lean_ctor_get(v_x_266_, 0);
        crate::leanh::lean_inc(v_val_271_);
        crate::leanh::lean_dec_ref_known(v_x_266_, 1);
        v___x_272_ = crate::leanh::lean_apply_1(v_h__2_268_, v_val_271_);
        return v___x_272_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_List_TakeDrop(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_List_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_BinderPredicates(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Ext(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_ByCases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Bool(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Div_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_List_TakeDrop(
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
pub unsafe fn initialize_Init_Data_List_TakeDrop(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_List_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_BinderPredicates(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Ext(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_ByCases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Bool(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Div_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Option_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_TakeDrop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_List_TakeDrop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_List_TakeDrop(builtin);
}
