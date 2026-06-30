// Lean compiler output
// Module: Init.Data.Iterators.Lemmas.Combinators.Monadic.ULift
// Imports: Init.Data.Iterators.Combinators.Monadic.ULift Init.Data.Array.Lemmas Init.Data.Iterators.Lemmas.Consumers.Monadic.Collect Init.Data.Iterators.Lemmas.Consumers.Monadic.Loop Init.Data.Iterators.Lemmas.Monadic.Basic
use crate::r#gen::Init::Data::Array::Lemmas::{
    initialize_Init_Data_Array_Lemmas, runtime_initialize_Init_Data_Array_Lemmas,
};
use crate::r#gen::Init::Data::Iterators::Combinators::Monadic::ULift::{
    initialize_Init_Data_Iterators_Combinators_Monadic_ULift,
    runtime_initialize_Init_Data_Iterators_Combinators_Monadic_ULift,
};
use crate::r#gen::Init::Data::Iterators::Lemmas::Consumers::Monadic::Collect::{
    initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect,
    runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect,
};
use crate::r#gen::Init::Data::Iterators::Lemmas::Consumers::Monadic::Loop::{
    initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop,
    runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop,
};
use crate::r#gen::Init::Data::Iterators::Lemmas::Monadic::Basic::{
    initialize_Init_Data_Iterators_Lemmas_Monadic_Basic,
    runtime_initialize_Init_Data_Iterators_Lemmas_Monadic_Basic,
};
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_ULift_0__Std_IterM_step__uLift_match__1_splitter___redArg(
    mut v_x_116_: *mut leanh::LeanObject,
    mut v_h__1_117_: *mut leanh::LeanObject,
    mut v_h__2_118_: *mut leanh::LeanObject,
    mut v_h__3_119_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_116_) {
        0 => {
            let mut v_it_120_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_121_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_122_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_119_);
            leanh::lean_dec(v_h__2_118_);
            v_it_120_ = leanh::lean_ctor_get(v_x_116_, 0);
            leanh::lean_inc(v_it_120_);
            v_out_121_ = leanh::lean_ctor_get(v_x_116_, 1);
            leanh::lean_inc(v_out_121_);
            leanh::lean_dec_ref_known(v_x_116_, 2);
            v___x_122_ = leanh::lean_apply_3(
                v_h__1_117_,
                v_it_120_,
                v_out_121_,
                leanh::lean_box(0),
            );
            return v___x_122_;
        }
        1 => {
            let mut v_it_123_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_124_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_119_);
            leanh::lean_dec(v_h__1_117_);
            v_it_123_ = leanh::lean_ctor_get(v_x_116_, 0);
            leanh::lean_inc(v_it_123_);
            leanh::lean_dec_ref_known(v_x_116_, 1);
            v___x_124_ =
                leanh::lean_apply_2(v_h__2_118_, v_it_123_, leanh::lean_box(0));
            return v___x_124_;
        }
        _ => {
            let mut v___x_125_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_118_);
            leanh::lean_dec(v_h__1_117_);
            v___x_125_ = leanh::lean_apply_1(v_h__3_119_, leanh::lean_box(0));
            return v___x_125_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_ULift_0__Std_IterM_step__uLift_match__1_splitter(
    mut v_00_u03b1_126_: *mut leanh::LeanObject,
    mut v_m_127_: *mut leanh::LeanObject,
    mut v_00_u03b2_128_: *mut leanh::LeanObject,
    mut v_inst_129_: *mut leanh::LeanObject,
    mut v_it_130_: *mut leanh::LeanObject,
    mut v_motive_131_: *mut leanh::LeanObject,
    mut v_x_132_: *mut leanh::LeanObject,
    mut v_h__1_133_: *mut leanh::LeanObject,
    mut v_h__2_134_: *mut leanh::LeanObject,
    mut v_h__3_135_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_132_) {
        0 => {
            let mut v_it_136_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_137_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_138_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_135_);
            leanh::lean_dec(v_h__2_134_);
            v_it_136_ = leanh::lean_ctor_get(v_x_132_, 0);
            leanh::lean_inc(v_it_136_);
            v_out_137_ = leanh::lean_ctor_get(v_x_132_, 1);
            leanh::lean_inc(v_out_137_);
            leanh::lean_dec_ref_known(v_x_132_, 2);
            v___x_138_ = leanh::lean_apply_3(
                v_h__1_133_,
                v_it_136_,
                v_out_137_,
                leanh::lean_box(0),
            );
            return v___x_138_;
        }
        1 => {
            let mut v_it_139_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_140_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_135_);
            leanh::lean_dec(v_h__1_133_);
            v_it_139_ = leanh::lean_ctor_get(v_x_132_, 0);
            leanh::lean_inc(v_it_139_);
            leanh::lean_dec_ref_known(v_x_132_, 1);
            v___x_140_ =
                leanh::lean_apply_2(v_h__2_134_, v_it_139_, leanh::lean_box(0));
            return v___x_140_;
        }
        _ => {
            let mut v___x_141_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_134_);
            leanh::lean_dec(v_h__1_133_);
            v___x_141_ = leanh::lean_apply_1(v_h__3_135_, leanh::lean_box(0));
            return v___x_141_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_ULift_0__Std_IterM_step__uLift_match__1_splitter___boxed(
    mut v_00_u03b1_142_: *mut leanh::LeanObject,
    mut v_m_143_: *mut leanh::LeanObject,
    mut v_00_u03b2_144_: *mut leanh::LeanObject,
    mut v_inst_145_: *mut leanh::LeanObject,
    mut v_it_146_: *mut leanh::LeanObject,
    mut v_motive_147_: *mut leanh::LeanObject,
    mut v_x_148_: *mut leanh::LeanObject,
    mut v_h__1_149_: *mut leanh::LeanObject,
    mut v_h__2_150_: *mut leanh::LeanObject,
    mut v_h__3_151_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_152_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_152_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_ULift_0__Std_IterM_step__uLift_match__1_splitter(v_00_u03b1_142_, v_m_143_, v_00_u03b2_144_, v_inst_145_, v_it_146_, v_motive_147_, v_x_148_, v_h__1_149_, v_h__2_150_, v_h__3_151_);
    leanh::lean_dec(v_it_146_);
    leanh::lean_dec(v_inst_145_);
    return v_res_152_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_ULift_0__Std_Iterators_Types_ULiftIterator_Monadic_modifyStep_match__1_splitter___redArg(
    mut v_step_153_: *mut leanh::LeanObject,
    mut v_h__1_154_: *mut leanh::LeanObject,
    mut v_h__2_155_: *mut leanh::LeanObject,
    mut v_h__3_156_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_step_153_) {
        0 => {
            let mut v_it_157_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_158_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_159_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_156_);
            leanh::lean_dec(v_h__2_155_);
            v_it_157_ = leanh::lean_ctor_get(v_step_153_, 0);
            leanh::lean_inc(v_it_157_);
            v_out_158_ = leanh::lean_ctor_get(v_step_153_, 1);
            leanh::lean_inc(v_out_158_);
            leanh::lean_dec_ref_known(v_step_153_, 2);
            v___x_159_ = leanh::lean_apply_2(v_h__1_154_, v_it_157_, v_out_158_);
            return v___x_159_;
        }
        1 => {
            let mut v_it_160_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_161_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_156_);
            leanh::lean_dec(v_h__1_154_);
            v_it_160_ = leanh::lean_ctor_get(v_step_153_, 0);
            leanh::lean_inc(v_it_160_);
            leanh::lean_dec_ref_known(v_step_153_, 1);
            v___x_161_ = leanh::lean_apply_1(v_h__2_155_, v_it_160_);
            return v___x_161_;
        }
        _ => {
            let mut v___x_162_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_163_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_155_);
            leanh::lean_dec(v_h__1_154_);
            v___x_162_ = leanh::lean_box(0);
            v___x_163_ = leanh::lean_apply_1(v_h__3_156_, v___x_162_);
            return v___x_163_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_ULift_0__Std_Iterators_Types_ULiftIterator_Monadic_modifyStep_match__1_splitter(
    mut v_00_u03b1_164_: *mut leanh::LeanObject,
    mut v_m_165_: *mut leanh::LeanObject,
    mut v_00_u03b2_166_: *mut leanh::LeanObject,
    mut v_motive_167_: *mut leanh::LeanObject,
    mut v_step_168_: *mut leanh::LeanObject,
    mut v_h__1_169_: *mut leanh::LeanObject,
    mut v_h__2_170_: *mut leanh::LeanObject,
    mut v_h__3_171_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_step_168_) {
        0 => {
            let mut v_it_172_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_173_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_174_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_171_);
            leanh::lean_dec(v_h__2_170_);
            v_it_172_ = leanh::lean_ctor_get(v_step_168_, 0);
            leanh::lean_inc(v_it_172_);
            v_out_173_ = leanh::lean_ctor_get(v_step_168_, 1);
            leanh::lean_inc(v_out_173_);
            leanh::lean_dec_ref_known(v_step_168_, 2);
            v___x_174_ = leanh::lean_apply_2(v_h__1_169_, v_it_172_, v_out_173_);
            return v___x_174_;
        }
        1 => {
            let mut v_it_175_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_176_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_171_);
            leanh::lean_dec(v_h__1_169_);
            v_it_175_ = leanh::lean_ctor_get(v_step_168_, 0);
            leanh::lean_inc(v_it_175_);
            leanh::lean_dec_ref_known(v_step_168_, 1);
            v___x_176_ = leanh::lean_apply_1(v_h__2_170_, v_it_175_);
            return v___x_176_;
        }
        _ => {
            let mut v___x_177_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_178_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_170_);
            leanh::lean_dec(v_h__1_169_);
            v___x_177_ = leanh::lean_box(0);
            v___x_178_ = leanh::lean_apply_1(v_h__3_171_, v___x_177_);
            return v___x_178_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_ULift_0__Std_IterM_toArray__eq__match__step_match__1_splitter___redArg(
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
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_ULift_0__Std_IterM_toArray__eq__match__step_match__1_splitter(
    mut v_00_u03b1_190_: *mut leanh::LeanObject,
    mut v_00_u03b2_191_: *mut leanh::LeanObject,
    mut v_m_192_: *mut leanh::LeanObject,
    mut v_motive_193_: *mut leanh::LeanObject,
    mut v_x_194_: *mut leanh::LeanObject,
    mut v_h__1_195_: *mut leanh::LeanObject,
    mut v_h__2_196_: *mut leanh::LeanObject,
    mut v_h__3_197_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_194_) {
        0 => {
            let mut v_it_198_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_199_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_200_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_197_);
            leanh::lean_dec(v_h__2_196_);
            v_it_198_ = leanh::lean_ctor_get(v_x_194_, 0);
            leanh::lean_inc(v_it_198_);
            v_out_199_ = leanh::lean_ctor_get(v_x_194_, 1);
            leanh::lean_inc(v_out_199_);
            leanh::lean_dec_ref_known(v_x_194_, 2);
            v___x_200_ = leanh::lean_apply_2(v_h__1_195_, v_it_198_, v_out_199_);
            return v___x_200_;
        }
        1 => {
            let mut v_it_201_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_202_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_197_);
            leanh::lean_dec(v_h__1_195_);
            v_it_201_ = leanh::lean_ctor_get(v_x_194_, 0);
            leanh::lean_inc(v_it_201_);
            leanh::lean_dec_ref_known(v_x_194_, 1);
            v___x_202_ = leanh::lean_apply_1(v_h__2_196_, v_it_201_);
            return v___x_202_;
        }
        _ => {
            let mut v___x_203_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_204_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_196_);
            leanh::lean_dec(v_h__1_195_);
            v___x_203_ = leanh::lean_box(0);
            v___x_204_ = leanh::lean_apply_1(v_h__3_197_, v___x_203_);
            return v___x_204_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_ULift_0__Std_IterM_length__eq__match__step_match__1_splitter___redArg(
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
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_ULift_0__Std_IterM_length__eq__match__step_match__1_splitter(
    mut v_00_u03b1_216_: *mut leanh::LeanObject,
    mut v_00_u03b2_217_: *mut leanh::LeanObject,
    mut v_m_218_: *mut leanh::LeanObject,
    mut v_motive_219_: *mut leanh::LeanObject,
    mut v_x_220_: *mut leanh::LeanObject,
    mut v_h__1_221_: *mut leanh::LeanObject,
    mut v_h__2_222_: *mut leanh::LeanObject,
    mut v_h__3_223_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_220_) {
        0 => {
            let mut v_it_224_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_225_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_226_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_223_);
            leanh::lean_dec(v_h__2_222_);
            v_it_224_ = leanh::lean_ctor_get(v_x_220_, 0);
            leanh::lean_inc(v_it_224_);
            v_out_225_ = leanh::lean_ctor_get(v_x_220_, 1);
            leanh::lean_inc(v_out_225_);
            leanh::lean_dec_ref_known(v_x_220_, 2);
            v___x_226_ = leanh::lean_apply_2(v_h__1_221_, v_it_224_, v_out_225_);
            return v___x_226_;
        }
        1 => {
            let mut v_it_227_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_228_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_223_);
            leanh::lean_dec(v_h__1_221_);
            v_it_227_ = leanh::lean_ctor_get(v_x_220_, 0);
            leanh::lean_inc(v_it_227_);
            leanh::lean_dec_ref_known(v_x_220_, 1);
            v___x_228_ = leanh::lean_apply_1(v_h__2_222_, v_it_227_);
            return v___x_228_;
        }
        _ => {
            let mut v___x_229_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_230_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_222_);
            leanh::lean_dec(v_h__1_221_);
            v___x_229_ = leanh::lean_box(0);
            v___x_230_ = leanh::lean_apply_1(v_h__3_223_, v___x_229_);
            return v___x_230_;
        }
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_ULift(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Iterators_Combinators_Monadic_ULift(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop(builtin);
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
pub unsafe fn meta_initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_ULift(
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
pub unsafe fn initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_ULift(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Iterators_Combinators_Monadic_ULift(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Monadic_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_ULift(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_ULift(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_ULift(builtin);
}