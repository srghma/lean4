// Lean compiler output
// Module: Init.Data.List.TakeDrop
// Imports: Init.Data.List.Basic Init.BinderPredicates Init.Ext Init.ByCases Init.Data.Bool Init.Data.List.Lemmas Init.Data.Nat.Div.Basic Init.Data.Option.Lemmas
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
use crate::lean_imports_rs::Init::Prelude::{lean_nat_dec_eq, lean_nat_sub};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_apply_1, lean_apply_2, lean_apply_3, lean_box,
    lean_ctor_get, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_obj_tag, lean_unbox, lean_unsigned_to_nat,
};
pub unsafe fn l___private_Init_Data_List_TakeDrop_0__List_take_match__1_splitter___redArg(
    mut v_x_137_: *mut LeanObject,
    mut v_x_138_: *mut LeanObject,
    mut v_h__1_139_: *mut LeanObject,
    mut v_h__2_140_: *mut LeanObject,
    mut v_h__3_141_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_142_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_143_: u8 = 0;
    v_zero_142_ = lean_unsigned_to_nat(0);
    v_isZero_143_ = lean_nat_dec_eq(v_x_137_, v_zero_142_);
    if v_isZero_143_ == 1 {
        let mut v___x_144_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__3_141_);
        lean_dec(v_h__2_140_);
        v___x_144_ = lean_apply_1(v_h__1_139_, v_x_138_);
        return v___x_144_;
    } else {
        let mut v_one_145_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_146_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_139_);
        v_one_145_ = lean_unsigned_to_nat(1);
        v_n_146_ = lean_nat_sub(v_x_137_, v_one_145_);
        if lean_obj_tag(v_x_138_) == 0 {
            let mut v___x_147_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_141_);
            v___x_147_ = lean_apply_1(v_h__2_140_, v_n_146_);
            return v___x_147_;
        } else {
            let mut v_head_148_: *mut LeanObject = core::ptr::null_mut();
            let mut v_tail_149_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_150_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_140_);
            v_head_148_ = lean_ctor_get(v_x_138_, 0);
            lean_inc(v_head_148_);
            v_tail_149_ = lean_ctor_get(v_x_138_, 1);
            lean_inc(v_tail_149_);
            lean_dec_ref_known(v_x_138_, 2);
            v___x_150_ = lean_apply_3(v_h__3_141_, v_n_146_, v_head_148_, v_tail_149_);
            return v___x_150_;
        }
    }
}
pub unsafe fn l___private_Init_Data_List_TakeDrop_0__List_take_match__1_splitter___redArg___boxed(
    mut v_x_151_: *mut LeanObject,
    mut v_x_152_: *mut LeanObject,
    mut v_h__1_153_: *mut LeanObject,
    mut v_h__2_154_: *mut LeanObject,
    mut v_h__3_155_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_156_: *mut LeanObject = core::ptr::null_mut();
    v_res_156_ = l___private_Init_Data_List_TakeDrop_0__List_take_match__1_splitter___redArg(
        v_x_151_,
        v_x_152_,
        v_h__1_153_,
        v_h__2_154_,
        v_h__3_155_,
    );
    lean_dec(v_x_151_);
    return v_res_156_;
}
pub unsafe fn l___private_Init_Data_List_TakeDrop_0__List_take_match__1_splitter(
    mut v_00_u03b1_157_: *mut LeanObject,
    mut v_motive_158_: *mut LeanObject,
    mut v_x_159_: *mut LeanObject,
    mut v_x_160_: *mut LeanObject,
    mut v_h__1_161_: *mut LeanObject,
    mut v_h__2_162_: *mut LeanObject,
    mut v_h__3_163_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_164_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_165_: u8 = 0;
    v_zero_164_ = lean_unsigned_to_nat(0);
    v_isZero_165_ = lean_nat_dec_eq(v_x_159_, v_zero_164_);
    if v_isZero_165_ == 1 {
        let mut v___x_166_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__3_163_);
        lean_dec(v_h__2_162_);
        v___x_166_ = lean_apply_1(v_h__1_161_, v_x_160_);
        return v___x_166_;
    } else {
        let mut v_one_167_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_168_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_161_);
        v_one_167_ = lean_unsigned_to_nat(1);
        v_n_168_ = lean_nat_sub(v_x_159_, v_one_167_);
        if lean_obj_tag(v_x_160_) == 0 {
            let mut v___x_169_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_163_);
            v___x_169_ = lean_apply_1(v_h__2_162_, v_n_168_);
            return v___x_169_;
        } else {
            let mut v_head_170_: *mut LeanObject = core::ptr::null_mut();
            let mut v_tail_171_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_172_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_162_);
            v_head_170_ = lean_ctor_get(v_x_160_, 0);
            lean_inc(v_head_170_);
            v_tail_171_ = lean_ctor_get(v_x_160_, 1);
            lean_inc(v_tail_171_);
            lean_dec_ref_known(v_x_160_, 2);
            v___x_172_ = lean_apply_3(v_h__3_163_, v_n_168_, v_head_170_, v_tail_171_);
            return v___x_172_;
        }
    }
}
pub unsafe fn l___private_Init_Data_List_TakeDrop_0__List_take_match__1_splitter___boxed(
    mut v_00_u03b1_173_: *mut LeanObject,
    mut v_motive_174_: *mut LeanObject,
    mut v_x_175_: *mut LeanObject,
    mut v_x_176_: *mut LeanObject,
    mut v_h__1_177_: *mut LeanObject,
    mut v_h__2_178_: *mut LeanObject,
    mut v_h__3_179_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_180_: *mut LeanObject = core::ptr::null_mut();
    v_res_180_ = l___private_Init_Data_List_TakeDrop_0__List_take_match__1_splitter(
        v_00_u03b1_173_,
        v_motive_174_,
        v_x_175_,
        v_x_176_,
        v_h__1_177_,
        v_h__2_178_,
        v_h__3_179_,
    );
    lean_dec(v_x_175_);
    return v_res_180_;
}
pub unsafe fn l___private_Init_Data_List_TakeDrop_0__Option_instDecidableEq_match__1_splitter___redArg(
    mut v_b_181_: *mut LeanObject,
    mut v_h__1_182_: *mut LeanObject,
    mut v_h__2_183_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_b_181_) == 0 {
        let mut v___x_184_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_185_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_183_);
        v___x_184_ = lean_box(0);
        v___x_185_ = lean_apply_1(v_h__1_182_, v___x_184_);
        return v___x_185_;
    } else {
        let mut v_val_186_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_187_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_182_);
        v_val_186_ = lean_ctor_get(v_b_181_, 0);
        lean_inc(v_val_186_);
        lean_dec_ref_known(v_b_181_, 1);
        v___x_187_ = lean_apply_1(v_h__2_183_, v_val_186_);
        return v___x_187_;
    }
}
pub unsafe fn l___private_Init_Data_List_TakeDrop_0__Option_instDecidableEq_match__1_splitter(
    mut v_00_u03b1_188_: *mut LeanObject,
    mut v_motive_189_: *mut LeanObject,
    mut v_b_190_: *mut LeanObject,
    mut v_h__1_191_: *mut LeanObject,
    mut v_h__2_192_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_b_190_) == 0 {
        let mut v___x_193_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_194_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_192_);
        v___x_193_ = lean_box(0);
        v___x_194_ = lean_apply_1(v_h__1_191_, v___x_193_);
        return v___x_194_;
    } else {
        let mut v_val_195_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_196_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_191_);
        v_val_195_ = lean_ctor_get(v_b_190_, 0);
        lean_inc(v_val_195_);
        lean_dec_ref_known(v_b_190_, 1);
        v___x_196_ = lean_apply_1(v_h__2_192_, v_val_195_);
        return v___x_196_;
    }
}
pub unsafe fn l___private_Init_Data_List_TakeDrop_0__List_getLast_x3f_match__1_splitter___redArg(
    mut v_x_197_: *mut LeanObject,
    mut v_h__1_198_: *mut LeanObject,
    mut v_h__2_199_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_197_) == 0 {
        let mut v___x_200_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_201_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_199_);
        v___x_200_ = lean_box(0);
        v___x_201_ = lean_apply_1(v_h__1_198_, v___x_200_);
        return v___x_201_;
    } else {
        let mut v_head_202_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_203_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_204_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_198_);
        v_head_202_ = lean_ctor_get(v_x_197_, 0);
        lean_inc(v_head_202_);
        v_tail_203_ = lean_ctor_get(v_x_197_, 1);
        lean_inc(v_tail_203_);
        lean_dec_ref_known(v_x_197_, 2);
        v___x_204_ = lean_apply_2(v_h__2_199_, v_head_202_, v_tail_203_);
        return v___x_204_;
    }
}
pub unsafe fn l___private_Init_Data_List_TakeDrop_0__List_getLast_x3f_match__1_splitter(
    mut v_00_u03b1_205_: *mut LeanObject,
    mut v_motive_206_: *mut LeanObject,
    mut v_x_207_: *mut LeanObject,
    mut v_h__1_208_: *mut LeanObject,
    mut v_h__2_209_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_207_) == 0 {
        let mut v___x_210_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_211_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_209_);
        v___x_210_ = lean_box(0);
        v___x_211_ = lean_apply_1(v_h__1_208_, v___x_210_);
        return v___x_211_;
    } else {
        let mut v_head_212_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_213_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_214_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_208_);
        v_head_212_ = lean_ctor_get(v_x_207_, 0);
        lean_inc(v_head_212_);
        v_tail_213_ = lean_ctor_get(v_x_207_, 1);
        lean_inc(v_tail_213_);
        lean_dec_ref_known(v_x_207_, 2);
        v___x_214_ = lean_apply_2(v_h__2_209_, v_head_212_, v_tail_213_);
        return v___x_214_;
    }
}
pub unsafe fn l___private_Init_Data_List_TakeDrop_0__List_filter_match__1_splitter___redArg(
    mut v_x_215_: u8,
    mut v_h__1_216_: *mut LeanObject,
    mut v_h__2_217_: *mut LeanObject,
) -> *mut LeanObject {
    if v_x_215_ == 0 {
        let mut v___x_218_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_219_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_216_);
        v___x_218_ = lean_box(0);
        v___x_219_ = lean_apply_1(v_h__2_217_, v___x_218_);
        return v___x_219_;
    } else {
        let mut v___x_220_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_221_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_217_);
        v___x_220_ = lean_box(0);
        v___x_221_ = lean_apply_1(v_h__1_216_, v___x_220_);
        return v___x_221_;
    }
}
pub unsafe fn l___private_Init_Data_List_TakeDrop_0__List_filter_match__1_splitter___redArg___boxed(
    mut v_x_222_: *mut LeanObject,
    mut v_h__1_223_: *mut LeanObject,
    mut v_h__2_224_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_26__boxed_225_: u8 = 0;
    let mut v_res_226_: *mut LeanObject = core::ptr::null_mut();
    v_x_26__boxed_225_ = (lean_unbox(v_x_222_) as u8);
    v_res_226_ = l___private_Init_Data_List_TakeDrop_0__List_filter_match__1_splitter___redArg(
        v_x_26__boxed_225_,
        v_h__1_223_,
        v_h__2_224_,
    );
    return v_res_226_;
}
pub unsafe fn l___private_Init_Data_List_TakeDrop_0__List_filter_match__1_splitter(
    mut v_motive_227_: *mut LeanObject,
    mut v_x_228_: u8,
    mut v_h__1_229_: *mut LeanObject,
    mut v_h__2_230_: *mut LeanObject,
) -> *mut LeanObject {
    if v_x_228_ == 0 {
        let mut v___x_231_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_232_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_229_);
        v___x_231_ = lean_box(0);
        v___x_232_ = lean_apply_1(v_h__2_230_, v___x_231_);
        return v___x_232_;
    } else {
        let mut v___x_233_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_234_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_230_);
        v___x_233_ = lean_box(0);
        v___x_234_ = lean_apply_1(v_h__1_229_, v___x_233_);
        return v___x_234_;
    }
}
pub unsafe fn l___private_Init_Data_List_TakeDrop_0__List_filter_match__1_splitter___boxed(
    mut v_motive_235_: *mut LeanObject,
    mut v_x_236_: *mut LeanObject,
    mut v_h__1_237_: *mut LeanObject,
    mut v_h__2_238_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_37__boxed_239_: u8 = 0;
    let mut v_res_240_: *mut LeanObject = core::ptr::null_mut();
    v_x_37__boxed_239_ = (lean_unbox(v_x_236_) as u8);
    v_res_240_ = l___private_Init_Data_List_TakeDrop_0__List_filter_match__1_splitter(
        v_motive_235_,
        v_x_37__boxed_239_,
        v_h__1_237_,
        v_h__2_238_,
    );
    return v_res_240_;
}
pub unsafe fn l___private_Init_Data_List_TakeDrop_0__List_head_x3f__dropWhile__not_match__1_splitter___redArg(
    mut v_x_241_: *mut LeanObject,
    mut v_h__1_242_: *mut LeanObject,
    mut v_h__2_243_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_241_) == 0 {
        let mut v___x_244_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_245_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_242_);
        v___x_244_ = lean_box(0);
        v___x_245_ = lean_apply_1(v_h__2_243_, v___x_244_);
        return v___x_245_;
    } else {
        let mut v_val_246_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_247_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_243_);
        v_val_246_ = lean_ctor_get(v_x_241_, 0);
        lean_inc(v_val_246_);
        lean_dec_ref_known(v_x_241_, 1);
        v___x_247_ = lean_apply_1(v_h__1_242_, v_val_246_);
        return v___x_247_;
    }
}
pub unsafe fn l___private_Init_Data_List_TakeDrop_0__List_head_x3f__dropWhile__not_match__1_splitter(
    mut v_00_u03b1_248_: *mut LeanObject,
    mut v_motive_249_: *mut LeanObject,
    mut v_x_250_: *mut LeanObject,
    mut v_h__1_251_: *mut LeanObject,
    mut v_h__2_252_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_250_) == 0 {
        let mut v___x_253_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_254_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_251_);
        v___x_253_ = lean_box(0);
        v___x_254_ = lean_apply_1(v_h__2_252_, v___x_253_);
        return v___x_254_;
    } else {
        let mut v_val_255_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_256_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_252_);
        v_val_255_ = lean_ctor_get(v_x_250_, 0);
        lean_inc(v_val_255_);
        lean_dec_ref_known(v_x_250_, 1);
        v___x_256_ = lean_apply_1(v_h__1_251_, v_val_255_);
        return v___x_256_;
    }
}
pub unsafe fn l___private_Init_Data_List_TakeDrop_0__List_filterMap_match__1_splitter___redArg(
    mut v_x_257_: *mut LeanObject,
    mut v_h__1_258_: *mut LeanObject,
    mut v_h__2_259_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_257_) == 0 {
        let mut v___x_260_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_261_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_259_);
        v___x_260_ = lean_box(0);
        v___x_261_ = lean_apply_1(v_h__1_258_, v___x_260_);
        return v___x_261_;
    } else {
        let mut v_val_262_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_263_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_258_);
        v_val_262_ = lean_ctor_get(v_x_257_, 0);
        lean_inc(v_val_262_);
        lean_dec_ref_known(v_x_257_, 1);
        v___x_263_ = lean_apply_1(v_h__2_259_, v_val_262_);
        return v___x_263_;
    }
}
pub unsafe fn l___private_Init_Data_List_TakeDrop_0__List_filterMap_match__1_splitter(
    mut v_00_u03b2_264_: *mut LeanObject,
    mut v_motive_265_: *mut LeanObject,
    mut v_x_266_: *mut LeanObject,
    mut v_h__1_267_: *mut LeanObject,
    mut v_h__2_268_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_266_) == 0 {
        let mut v___x_269_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_270_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_268_);
        v___x_269_ = lean_box(0);
        v___x_270_ = lean_apply_1(v_h__1_267_, v___x_269_);
        return v___x_270_;
    } else {
        let mut v_val_271_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_272_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_267_);
        v_val_271_ = lean_ctor_get(v_x_266_, 0);
        lean_inc(v_val_271_);
        lean_dec_ref_known(v_x_266_, 1);
        v___x_272_ = lean_apply_1(v_h__2_268_, v_val_271_);
        return v___x_272_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_List_TakeDrop(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_List_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_BinderPredicates(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Ext(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_ByCases(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Bool(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Div_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_List_TakeDrop(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_List_TakeDrop(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_List_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_BinderPredicates(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Ext(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_ByCases(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Bool(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Div_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Option_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_TakeDrop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_List_TakeDrop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_List_TakeDrop(builtin);
}
