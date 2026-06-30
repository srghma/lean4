// Lean compiler output
// Module: Init.Data.Iterators.Lemmas.Consumers.Monadic.Collect
// Imports: Init.Data.Iterators.Consumers.Monadic.Collect Init.Data.Iterators.Consumers.Monadic.Collect Init.Data.Iterators.Consumers.Monadic.Total Init.WFExtrinsicFix Init.Control.Lawful Init.Data.Array.Bootstrap Init.Data.Array.Lemmas Init.Data.Iterators.Lemmas.Monadic.Basic
use crate::r#gen::Init::Control::Lawful::{
    initialize_Init_Control_Lawful, runtime_initialize_Init_Control_Lawful,
};
use crate::r#gen::Init::Data::Array::Bootstrap::{
    initialize_Init_Data_Array_Bootstrap, runtime_initialize_Init_Data_Array_Bootstrap,
};
use crate::r#gen::Init::Data::Array::Lemmas::{
    initialize_Init_Data_Array_Lemmas, runtime_initialize_Init_Data_Array_Lemmas,
};
use crate::r#gen::Init::Data::Iterators::Consumers::Monadic::Collect::{
    initialize_Init_Data_Iterators_Consumers_Monadic_Collect,
    runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Collect,
};
use crate::r#gen::Init::Data::Iterators::Consumers::Monadic::Total::{
    initialize_Init_Data_Iterators_Consumers_Monadic_Total,
    runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Total,
};
use crate::r#gen::Init::Data::Iterators::Lemmas::Monadic::Basic::{
    initialize_Init_Data_Iterators_Lemmas_Monadic_Basic,
    runtime_initialize_Init_Data_Iterators_Lemmas_Monadic_Basic,
};
use crate::r#gen::Init::WFExtrinsicFix::{
    initialize_Init_WFExtrinsicFix, runtime_initialize_Init_WFExtrinsicFix,
};
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect_0__Std_IterM_toArray_go_match__1_splitter___redArg(
    mut v_x_127_: *mut leanh::LeanObject,
    mut v_h__1_128_: *mut leanh::LeanObject,
    mut v_h__2_129_: *mut leanh::LeanObject,
    mut v_h__3_130_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_127_) {
        0 => {
            let mut v_it_131_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_132_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_133_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_130_);
            leanh::lean_dec(v_h__2_129_);
            v_it_131_ = leanh::lean_ctor_get(v_x_127_, 0);
            leanh::lean_inc(v_it_131_);
            v_out_132_ = leanh::lean_ctor_get(v_x_127_, 1);
            leanh::lean_inc(v_out_132_);
            leanh::lean_dec_ref_known(v_x_127_, 2);
            v___x_133_ = leanh::lean_apply_3(
                v_h__1_128_,
                v_it_131_,
                v_out_132_,
                leanh::lean_box(0),
            );
            return v___x_133_;
        }
        1 => {
            let mut v_it_134_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_135_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_130_);
            leanh::lean_dec(v_h__1_128_);
            v_it_134_ = leanh::lean_ctor_get(v_x_127_, 0);
            leanh::lean_inc(v_it_134_);
            leanh::lean_dec_ref_known(v_x_127_, 1);
            v___x_135_ =
                leanh::lean_apply_2(v_h__2_129_, v_it_134_, leanh::lean_box(0));
            return v___x_135_;
        }
        _ => {
            let mut v___x_136_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_129_);
            leanh::lean_dec(v_h__1_128_);
            v___x_136_ = leanh::lean_apply_1(v_h__3_130_, leanh::lean_box(0));
            return v___x_136_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect_0__Std_IterM_toArray_go_match__1_splitter(
    mut v_00_u03b1_137_: *mut leanh::LeanObject,
    mut v_00_u03b2_138_: *mut leanh::LeanObject,
    mut v_m_139_: *mut leanh::LeanObject,
    mut v_inst_140_: *mut leanh::LeanObject,
    mut v_it_141_: *mut leanh::LeanObject,
    mut v_motive_142_: *mut leanh::LeanObject,
    mut v_x_143_: *mut leanh::LeanObject,
    mut v_h__1_144_: *mut leanh::LeanObject,
    mut v_h__2_145_: *mut leanh::LeanObject,
    mut v_h__3_146_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_143_) {
        0 => {
            let mut v_it_147_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_148_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_149_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_146_);
            leanh::lean_dec(v_h__2_145_);
            v_it_147_ = leanh::lean_ctor_get(v_x_143_, 0);
            leanh::lean_inc(v_it_147_);
            v_out_148_ = leanh::lean_ctor_get(v_x_143_, 1);
            leanh::lean_inc(v_out_148_);
            leanh::lean_dec_ref_known(v_x_143_, 2);
            v___x_149_ = leanh::lean_apply_3(
                v_h__1_144_,
                v_it_147_,
                v_out_148_,
                leanh::lean_box(0),
            );
            return v___x_149_;
        }
        1 => {
            let mut v_it_150_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_151_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_146_);
            leanh::lean_dec(v_h__1_144_);
            v_it_150_ = leanh::lean_ctor_get(v_x_143_, 0);
            leanh::lean_inc(v_it_150_);
            leanh::lean_dec_ref_known(v_x_143_, 1);
            v___x_151_ =
                leanh::lean_apply_2(v_h__2_145_, v_it_150_, leanh::lean_box(0));
            return v___x_151_;
        }
        _ => {
            let mut v___x_152_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_145_);
            leanh::lean_dec(v_h__1_144_);
            v___x_152_ = leanh::lean_apply_1(v_h__3_146_, leanh::lean_box(0));
            return v___x_152_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect_0__Std_IterM_toArray_go_match__1_splitter___boxed(
    mut v_00_u03b1_153_: *mut leanh::LeanObject,
    mut v_00_u03b2_154_: *mut leanh::LeanObject,
    mut v_m_155_: *mut leanh::LeanObject,
    mut v_inst_156_: *mut leanh::LeanObject,
    mut v_it_157_: *mut leanh::LeanObject,
    mut v_motive_158_: *mut leanh::LeanObject,
    mut v_x_159_: *mut leanh::LeanObject,
    mut v_h__1_160_: *mut leanh::LeanObject,
    mut v_h__2_161_: *mut leanh::LeanObject,
    mut v_h__3_162_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_163_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_163_ = l___private_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect_0__Std_IterM_toArray_go_match__1_splitter(v_00_u03b1_153_, v_00_u03b2_154_, v_m_155_, v_inst_156_, v_it_157_, v_motive_158_, v_x_159_, v_h__1_160_, v_h__2_161_, v_h__3_162_);
    leanh::lean_dec(v_it_157_);
    leanh::lean_dec(v_inst_156_);
    return v_res_163_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect_0__Std_IterM_toArray_go__eq_match__1_splitter___redArg(
    mut v_x_164_: *mut leanh::LeanObject,
    mut v_h__1_165_: *mut leanh::LeanObject,
    mut v_h__2_166_: *mut leanh::LeanObject,
    mut v_h__3_167_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_164_) {
        0 => {
            let mut v_it_168_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_169_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_170_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_167_);
            leanh::lean_dec(v_h__2_166_);
            v_it_168_ = leanh::lean_ctor_get(v_x_164_, 0);
            leanh::lean_inc(v_it_168_);
            v_out_169_ = leanh::lean_ctor_get(v_x_164_, 1);
            leanh::lean_inc(v_out_169_);
            leanh::lean_dec_ref_known(v_x_164_, 2);
            v___x_170_ = leanh::lean_apply_2(v_h__1_165_, v_it_168_, v_out_169_);
            return v___x_170_;
        }
        1 => {
            let mut v_it_171_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_172_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_167_);
            leanh::lean_dec(v_h__1_165_);
            v_it_171_ = leanh::lean_ctor_get(v_x_164_, 0);
            leanh::lean_inc(v_it_171_);
            leanh::lean_dec_ref_known(v_x_164_, 1);
            v___x_172_ = leanh::lean_apply_1(v_h__2_166_, v_it_171_);
            return v___x_172_;
        }
        _ => {
            let mut v___x_173_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_174_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_166_);
            leanh::lean_dec(v_h__1_165_);
            v___x_173_ = leanh::lean_box(0);
            v___x_174_ = leanh::lean_apply_1(v_h__3_167_, v___x_173_);
            return v___x_174_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect_0__Std_IterM_toArray_go__eq_match__1_splitter(
    mut v_00_u03b1_175_: *mut leanh::LeanObject,
    mut v_00_u03b2_176_: *mut leanh::LeanObject,
    mut v_m_177_: *mut leanh::LeanObject,
    mut v_motive_178_: *mut leanh::LeanObject,
    mut v_x_179_: *mut leanh::LeanObject,
    mut v_h__1_180_: *mut leanh::LeanObject,
    mut v_h__2_181_: *mut leanh::LeanObject,
    mut v_h__3_182_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_179_) {
        0 => {
            let mut v_it_183_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_184_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_185_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_182_);
            leanh::lean_dec(v_h__2_181_);
            v_it_183_ = leanh::lean_ctor_get(v_x_179_, 0);
            leanh::lean_inc(v_it_183_);
            v_out_184_ = leanh::lean_ctor_get(v_x_179_, 1);
            leanh::lean_inc(v_out_184_);
            leanh::lean_dec_ref_known(v_x_179_, 2);
            v___x_185_ = leanh::lean_apply_2(v_h__1_180_, v_it_183_, v_out_184_);
            return v___x_185_;
        }
        1 => {
            let mut v_it_186_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_187_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_182_);
            leanh::lean_dec(v_h__1_180_);
            v_it_186_ = leanh::lean_ctor_get(v_x_179_, 0);
            leanh::lean_inc(v_it_186_);
            leanh::lean_dec_ref_known(v_x_179_, 1);
            v___x_187_ = leanh::lean_apply_1(v_h__2_181_, v_it_186_);
            return v___x_187_;
        }
        _ => {
            let mut v___x_188_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_189_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_181_);
            leanh::lean_dec(v_h__1_180_);
            v___x_188_ = leanh::lean_box(0);
            v___x_189_ = leanh::lean_apply_1(v_h__3_182_, v___x_188_);
            return v___x_189_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect_0__Std_IterM_toArray__eq__match__step_match__1_splitter___redArg(
    mut v_x_190_: *mut leanh::LeanObject,
    mut v_h__1_191_: *mut leanh::LeanObject,
    mut v_h__2_192_: *mut leanh::LeanObject,
    mut v_h__3_193_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_190_) {
        0 => {
            let mut v_it_194_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_195_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_196_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_193_);
            leanh::lean_dec(v_h__2_192_);
            v_it_194_ = leanh::lean_ctor_get(v_x_190_, 0);
            leanh::lean_inc(v_it_194_);
            v_out_195_ = leanh::lean_ctor_get(v_x_190_, 1);
            leanh::lean_inc(v_out_195_);
            leanh::lean_dec_ref_known(v_x_190_, 2);
            v___x_196_ = leanh::lean_apply_2(v_h__1_191_, v_it_194_, v_out_195_);
            return v___x_196_;
        }
        1 => {
            let mut v_it_197_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_198_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_193_);
            leanh::lean_dec(v_h__1_191_);
            v_it_197_ = leanh::lean_ctor_get(v_x_190_, 0);
            leanh::lean_inc(v_it_197_);
            leanh::lean_dec_ref_known(v_x_190_, 1);
            v___x_198_ = leanh::lean_apply_1(v_h__2_192_, v_it_197_);
            return v___x_198_;
        }
        _ => {
            let mut v___x_199_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_200_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_192_);
            leanh::lean_dec(v_h__1_191_);
            v___x_199_ = leanh::lean_box(0);
            v___x_200_ = leanh::lean_apply_1(v_h__3_193_, v___x_199_);
            return v___x_200_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect_0__Std_IterM_toArray__eq__match__step_match__1_splitter(
    mut v_00_u03b1_201_: *mut leanh::LeanObject,
    mut v_00_u03b2_202_: *mut leanh::LeanObject,
    mut v_m_203_: *mut leanh::LeanObject,
    mut v_motive_204_: *mut leanh::LeanObject,
    mut v_x_205_: *mut leanh::LeanObject,
    mut v_h__1_206_: *mut leanh::LeanObject,
    mut v_h__2_207_: *mut leanh::LeanObject,
    mut v_h__3_208_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_205_) {
        0 => {
            let mut v_it_209_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_210_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_211_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_208_);
            leanh::lean_dec(v_h__2_207_);
            v_it_209_ = leanh::lean_ctor_get(v_x_205_, 0);
            leanh::lean_inc(v_it_209_);
            v_out_210_ = leanh::lean_ctor_get(v_x_205_, 1);
            leanh::lean_inc(v_out_210_);
            leanh::lean_dec_ref_known(v_x_205_, 2);
            v___x_211_ = leanh::lean_apply_2(v_h__1_206_, v_it_209_, v_out_210_);
            return v___x_211_;
        }
        1 => {
            let mut v_it_212_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_213_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_208_);
            leanh::lean_dec(v_h__1_206_);
            v_it_212_ = leanh::lean_ctor_get(v_x_205_, 0);
            leanh::lean_inc(v_it_212_);
            leanh::lean_dec_ref_known(v_x_205_, 1);
            v___x_213_ = leanh::lean_apply_1(v_h__2_207_, v_it_212_);
            return v___x_213_;
        }
        _ => {
            let mut v___x_214_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_215_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_207_);
            leanh::lean_dec(v_h__1_206_);
            v___x_214_ = leanh::lean_box(0);
            v___x_215_ = leanh::lean_apply_1(v_h__3_208_, v___x_214_);
            return v___x_215_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect_0__Std_IterM_toListRev_match__1_splitter___redArg(
    mut v_x_216_: *mut leanh::LeanObject,
    mut v_h__1_217_: *mut leanh::LeanObject,
    mut v_h__2_218_: *mut leanh::LeanObject,
    mut v_h__3_219_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_216_) {
        0 => {
            let mut v_it_220_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_221_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_222_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_219_);
            leanh::lean_dec(v_h__2_218_);
            v_it_220_ = leanh::lean_ctor_get(v_x_216_, 0);
            leanh::lean_inc(v_it_220_);
            v_out_221_ = leanh::lean_ctor_get(v_x_216_, 1);
            leanh::lean_inc(v_out_221_);
            leanh::lean_dec_ref_known(v_x_216_, 2);
            v___x_222_ = leanh::lean_apply_3(
                v_h__1_217_,
                v_it_220_,
                v_out_221_,
                leanh::lean_box(0),
            );
            return v___x_222_;
        }
        1 => {
            let mut v_it_223_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_224_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_219_);
            leanh::lean_dec(v_h__1_217_);
            v_it_223_ = leanh::lean_ctor_get(v_x_216_, 0);
            leanh::lean_inc(v_it_223_);
            leanh::lean_dec_ref_known(v_x_216_, 1);
            v___x_224_ =
                leanh::lean_apply_2(v_h__2_218_, v_it_223_, leanh::lean_box(0));
            return v___x_224_;
        }
        _ => {
            let mut v___x_225_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_218_);
            leanh::lean_dec(v_h__1_217_);
            v___x_225_ = leanh::lean_apply_1(v_h__3_219_, leanh::lean_box(0));
            return v___x_225_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect_0__Std_IterM_toListRev_match__1_splitter(
    mut v_00_u03b1_226_: *mut leanh::LeanObject,
    mut v_m_227_: *mut leanh::LeanObject,
    mut v_00_u03b2_228_: *mut leanh::LeanObject,
    mut v_inst_229_: *mut leanh::LeanObject,
    mut v_it_230_: *mut leanh::LeanObject,
    mut v_motive_231_: *mut leanh::LeanObject,
    mut v_x_232_: *mut leanh::LeanObject,
    mut v_h__1_233_: *mut leanh::LeanObject,
    mut v_h__2_234_: *mut leanh::LeanObject,
    mut v_h__3_235_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_232_) {
        0 => {
            let mut v_it_236_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_237_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_238_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_235_);
            leanh::lean_dec(v_h__2_234_);
            v_it_236_ = leanh::lean_ctor_get(v_x_232_, 0);
            leanh::lean_inc(v_it_236_);
            v_out_237_ = leanh::lean_ctor_get(v_x_232_, 1);
            leanh::lean_inc(v_out_237_);
            leanh::lean_dec_ref_known(v_x_232_, 2);
            v___x_238_ = leanh::lean_apply_3(
                v_h__1_233_,
                v_it_236_,
                v_out_237_,
                leanh::lean_box(0),
            );
            return v___x_238_;
        }
        1 => {
            let mut v_it_239_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_240_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_235_);
            leanh::lean_dec(v_h__1_233_);
            v_it_239_ = leanh::lean_ctor_get(v_x_232_, 0);
            leanh::lean_inc(v_it_239_);
            leanh::lean_dec_ref_known(v_x_232_, 1);
            v___x_240_ =
                leanh::lean_apply_2(v_h__2_234_, v_it_239_, leanh::lean_box(0));
            return v___x_240_;
        }
        _ => {
            let mut v___x_241_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_234_);
            leanh::lean_dec(v_h__1_233_);
            v___x_241_ = leanh::lean_apply_1(v_h__3_235_, leanh::lean_box(0));
            return v___x_241_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect_0__Std_IterM_toListRev_match__1_splitter___boxed(
    mut v_00_u03b1_242_: *mut leanh::LeanObject,
    mut v_m_243_: *mut leanh::LeanObject,
    mut v_00_u03b2_244_: *mut leanh::LeanObject,
    mut v_inst_245_: *mut leanh::LeanObject,
    mut v_it_246_: *mut leanh::LeanObject,
    mut v_motive_247_: *mut leanh::LeanObject,
    mut v_x_248_: *mut leanh::LeanObject,
    mut v_h__1_249_: *mut leanh::LeanObject,
    mut v_h__2_250_: *mut leanh::LeanObject,
    mut v_h__3_251_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_252_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_252_ = l___private_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect_0__Std_IterM_toListRev_match__1_splitter(v_00_u03b1_242_, v_m_243_, v_00_u03b2_244_, v_inst_245_, v_it_246_, v_motive_247_, v_x_248_, v_h__1_249_, v_h__2_250_, v_h__3_251_);
    leanh::lean_dec(v_it_246_);
    leanh::lean_dec(v_inst_245_);
    return v_res_252_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Collect(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Collect(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Total(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_WFExtrinsicFix(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Control_Lawful(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Bootstrap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Monadic_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect(
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
pub unsafe fn initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Iterators_Consumers_Monadic_Collect(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers_Monadic_Collect(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers_Monadic_Total(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_WFExtrinsicFix(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Control_Lawful(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_Bootstrap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Monadic_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect(builtin);
}