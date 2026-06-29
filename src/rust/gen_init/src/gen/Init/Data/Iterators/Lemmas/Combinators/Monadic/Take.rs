// Lean compiler output
// Module: Init.Data.Iterators.Lemmas.Combinators.Monadic.Take
// Imports: Init.Data.Iterators.Combinators.Monadic.Take Init.Data.Iterators.Consumers.Monadic.Collect Init.Data.Iterators.Lemmas.Consumers.Monadic.Collect Init.Data.Iterators.Lemmas.Monadic.Basic Init.Data.Nat.Lemmas
use crate::r#gen::Init::Data::Iterators::Combinators::Monadic::Take::{
    initialize_Init_Data_Iterators_Combinators_Monadic_Take,
    runtime_initialize_Init_Data_Iterators_Combinators_Monadic_Take,
};
use crate::r#gen::Init::Data::Iterators::Consumers::Monadic::Collect::{
    initialize_Init_Data_Iterators_Consumers_Monadic_Collect,
    runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Collect,
};
use crate::r#gen::Init::Data::Iterators::Lemmas::Consumers::Monadic::Collect::{
    initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect,
    runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect,
};
use crate::r#gen::Init::Data::Iterators::Lemmas::Monadic::Basic::{
    initialize_Init_Data_Iterators_Lemmas_Monadic_Basic,
    runtime_initialize_Init_Data_Iterators_Lemmas_Monadic_Basic,
};
use crate::r#gen::Init::Data::Nat::Lemmas::{
    initialize_Init_Data_Nat_Lemmas, runtime_initialize_Init_Data_Nat_Lemmas,
};
use crate::ffi::{lean_nat_dec_eq, lean_nat_sub};
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take_0__Std_Iterators_Types_Take_instIterator_match__1_splitter___redArg(
    mut v_x_131_: *mut crate::leanh::LeanObject,
    mut v_h__1_132_: *mut crate::leanh::LeanObject,
    mut v_h__2_133_: *mut crate::leanh::LeanObject,
    mut v_h__3_134_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_131_) {
        0 => {
            let mut v_it_135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_134_);
            crate::leanh::lean_dec(v_h__2_133_);
            v_it_135_ = crate::leanh::lean_ctor_get(v_x_131_, 0);
            crate::leanh::lean_inc(v_it_135_);
            v_out_136_ = crate::leanh::lean_ctor_get(v_x_131_, 1);
            crate::leanh::lean_inc(v_out_136_);
            crate::leanh::lean_dec_ref_known(v_x_131_, 2);
            v___x_137_ = crate::leanh::lean_apply_3(
                v_h__1_132_,
                v_it_135_,
                v_out_136_,
                crate::leanh::lean_box(0),
            );
            return v___x_137_;
        }
        1 => {
            let mut v_it_138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_134_);
            crate::leanh::lean_dec(v_h__1_132_);
            v_it_138_ = crate::leanh::lean_ctor_get(v_x_131_, 0);
            crate::leanh::lean_inc(v_it_138_);
            crate::leanh::lean_dec_ref_known(v_x_131_, 1);
            v___x_139_ =
                crate::leanh::lean_apply_2(v_h__2_133_, v_it_138_, crate::leanh::lean_box(0));
            return v___x_139_;
        }
        _ => {
            let mut v___x_140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_133_);
            crate::leanh::lean_dec(v_h__1_132_);
            v___x_140_ = crate::leanh::lean_apply_1(v_h__3_134_, crate::leanh::lean_box(0));
            return v___x_140_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take_0__Std_Iterators_Types_Take_instIterator_match__1_splitter(
    mut v_00_u03b1_141_: *mut crate::leanh::LeanObject,
    mut v_m_142_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_143_: *mut crate::leanh::LeanObject,
    mut v_inst_144_: *mut crate::leanh::LeanObject,
    mut v_it_145_: *mut crate::leanh::LeanObject,
    mut v_motive_146_: *mut crate::leanh::LeanObject,
    mut v_x_147_: *mut crate::leanh::LeanObject,
    mut v_h__1_148_: *mut crate::leanh::LeanObject,
    mut v_h__2_149_: *mut crate::leanh::LeanObject,
    mut v_h__3_150_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_147_) {
        0 => {
            let mut v_it_151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_150_);
            crate::leanh::lean_dec(v_h__2_149_);
            v_it_151_ = crate::leanh::lean_ctor_get(v_x_147_, 0);
            crate::leanh::lean_inc(v_it_151_);
            v_out_152_ = crate::leanh::lean_ctor_get(v_x_147_, 1);
            crate::leanh::lean_inc(v_out_152_);
            crate::leanh::lean_dec_ref_known(v_x_147_, 2);
            v___x_153_ = crate::leanh::lean_apply_3(
                v_h__1_148_,
                v_it_151_,
                v_out_152_,
                crate::leanh::lean_box(0),
            );
            return v___x_153_;
        }
        1 => {
            let mut v_it_154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_150_);
            crate::leanh::lean_dec(v_h__1_148_);
            v_it_154_ = crate::leanh::lean_ctor_get(v_x_147_, 0);
            crate::leanh::lean_inc(v_it_154_);
            crate::leanh::lean_dec_ref_known(v_x_147_, 1);
            v___x_155_ =
                crate::leanh::lean_apply_2(v_h__2_149_, v_it_154_, crate::leanh::lean_box(0));
            return v___x_155_;
        }
        _ => {
            let mut v___x_156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_149_);
            crate::leanh::lean_dec(v_h__1_148_);
            v___x_156_ = crate::leanh::lean_apply_1(v_h__3_150_, crate::leanh::lean_box(0));
            return v___x_156_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take_0__Std_Iterators_Types_Take_instIterator_match__1_splitter___boxed(
    mut v_00_u03b1_157_: *mut crate::leanh::LeanObject,
    mut v_m_158_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_159_: *mut crate::leanh::LeanObject,
    mut v_inst_160_: *mut crate::leanh::LeanObject,
    mut v_it_161_: *mut crate::leanh::LeanObject,
    mut v_motive_162_: *mut crate::leanh::LeanObject,
    mut v_x_163_: *mut crate::leanh::LeanObject,
    mut v_h__1_164_: *mut crate::leanh::LeanObject,
    mut v_h__2_165_: *mut crate::leanh::LeanObject,
    mut v_h__3_166_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_167_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take_0__Std_Iterators_Types_Take_instIterator_match__1_splitter(v_00_u03b1_157_, v_m_158_, v_00_u03b2_159_, v_inst_160_, v_it_161_, v_motive_162_, v_x_163_, v_h__1_164_, v_h__2_165_, v_h__3_166_);
    crate::leanh::lean_dec_ref(v_it_161_);
    crate::leanh::lean_dec(v_inst_160_);
    return v_res_167_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take_0__Std_IterM_step__take_match__3_splitter___redArg(
    mut v_n_168_: *mut crate::leanh::LeanObject,
    mut v_h__1_169_: *mut crate::leanh::LeanObject,
    mut v_h__2_170_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_172_: u8 = 0;
    v_zero_171_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_172_ = lean_nat_dec_eq(v_n_168_, v_zero_171_);
    if v_isZero_172_ == 1 {
        let mut v___x_173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_170_);
        v___x_173_ = crate::leanh::lean_box(0);
        v___x_174_ = crate::leanh::lean_apply_1(v_h__1_169_, v___x_173_);
        return v___x_174_;
    } else {
        let mut v_one_175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_169_);
        v_one_175_ = crate::leanh::lean_unsigned_to_nat(1);
        v_n_176_ = lean_nat_sub(v_n_168_, v_one_175_);
        v___x_177_ = crate::leanh::lean_apply_1(v_h__2_170_, v_n_176_);
        return v___x_177_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take_0__Std_IterM_step__take_match__3_splitter___redArg___boxed(
    mut v_n_178_: *mut crate::leanh::LeanObject,
    mut v_h__1_179_: *mut crate::leanh::LeanObject,
    mut v_h__2_180_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_181_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take_0__Std_IterM_step__take_match__3_splitter___redArg(v_n_178_, v_h__1_179_, v_h__2_180_);
    crate::leanh::lean_dec(v_n_178_);
    return v_res_181_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take_0__Std_IterM_step__take_match__3_splitter(
    mut v_motive_182_: *mut crate::leanh::LeanObject,
    mut v_n_183_: *mut crate::leanh::LeanObject,
    mut v_h__1_184_: *mut crate::leanh::LeanObject,
    mut v_h__2_185_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_187_: u8 = 0;
    v_zero_186_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_187_ = lean_nat_dec_eq(v_n_183_, v_zero_186_);
    if v_isZero_187_ == 1 {
        let mut v___x_188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_185_);
        v___x_188_ = crate::leanh::lean_box(0);
        v___x_189_ = crate::leanh::lean_apply_1(v_h__1_184_, v___x_188_);
        return v___x_189_;
    } else {
        let mut v_one_190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_184_);
        v_one_190_ = crate::leanh::lean_unsigned_to_nat(1);
        v_n_191_ = lean_nat_sub(v_n_183_, v_one_190_);
        v___x_192_ = crate::leanh::lean_apply_1(v_h__2_185_, v_n_191_);
        return v___x_192_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take_0__Std_IterM_step__take_match__3_splitter___boxed(
    mut v_motive_193_: *mut crate::leanh::LeanObject,
    mut v_n_194_: *mut crate::leanh::LeanObject,
    mut v_h__1_195_: *mut crate::leanh::LeanObject,
    mut v_h__2_196_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_197_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take_0__Std_IterM_step__take_match__3_splitter(v_motive_193_, v_n_194_, v_h__1_195_, v_h__2_196_);
    crate::leanh::lean_dec(v_n_194_);
    return v_res_197_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take_0__Std_IterM_step__take_match__1_splitter___redArg(
    mut v_x_198_: *mut crate::leanh::LeanObject,
    mut v_h__1_199_: *mut crate::leanh::LeanObject,
    mut v_h__2_200_: *mut crate::leanh::LeanObject,
    mut v_h__3_201_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_198_) {
        0 => {
            let mut v_it_202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_201_);
            crate::leanh::lean_dec(v_h__2_200_);
            v_it_202_ = crate::leanh::lean_ctor_get(v_x_198_, 0);
            crate::leanh::lean_inc(v_it_202_);
            v_out_203_ = crate::leanh::lean_ctor_get(v_x_198_, 1);
            crate::leanh::lean_inc(v_out_203_);
            crate::leanh::lean_dec_ref_known(v_x_198_, 2);
            v___x_204_ = crate::leanh::lean_apply_3(
                v_h__1_199_,
                v_it_202_,
                v_out_203_,
                crate::leanh::lean_box(0),
            );
            return v___x_204_;
        }
        1 => {
            let mut v_it_205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_201_);
            crate::leanh::lean_dec(v_h__1_199_);
            v_it_205_ = crate::leanh::lean_ctor_get(v_x_198_, 0);
            crate::leanh::lean_inc(v_it_205_);
            crate::leanh::lean_dec_ref_known(v_x_198_, 1);
            v___x_206_ =
                crate::leanh::lean_apply_2(v_h__2_200_, v_it_205_, crate::leanh::lean_box(0));
            return v___x_206_;
        }
        _ => {
            let mut v___x_207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_200_);
            crate::leanh::lean_dec(v_h__1_199_);
            v___x_207_ = crate::leanh::lean_apply_1(v_h__3_201_, crate::leanh::lean_box(0));
            return v___x_207_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take_0__Std_IterM_step__take_match__1_splitter(
    mut v_00_u03b1_208_: *mut crate::leanh::LeanObject,
    mut v_m_209_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_210_: *mut crate::leanh::LeanObject,
    mut v_inst_211_: *mut crate::leanh::LeanObject,
    mut v_it_212_: *mut crate::leanh::LeanObject,
    mut v_motive_213_: *mut crate::leanh::LeanObject,
    mut v_x_214_: *mut crate::leanh::LeanObject,
    mut v_h__1_215_: *mut crate::leanh::LeanObject,
    mut v_h__2_216_: *mut crate::leanh::LeanObject,
    mut v_h__3_217_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_214_) {
        0 => {
            let mut v_it_218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_217_);
            crate::leanh::lean_dec(v_h__2_216_);
            v_it_218_ = crate::leanh::lean_ctor_get(v_x_214_, 0);
            crate::leanh::lean_inc(v_it_218_);
            v_out_219_ = crate::leanh::lean_ctor_get(v_x_214_, 1);
            crate::leanh::lean_inc(v_out_219_);
            crate::leanh::lean_dec_ref_known(v_x_214_, 2);
            v___x_220_ = crate::leanh::lean_apply_3(
                v_h__1_215_,
                v_it_218_,
                v_out_219_,
                crate::leanh::lean_box(0),
            );
            return v___x_220_;
        }
        1 => {
            let mut v_it_221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_217_);
            crate::leanh::lean_dec(v_h__1_215_);
            v_it_221_ = crate::leanh::lean_ctor_get(v_x_214_, 0);
            crate::leanh::lean_inc(v_it_221_);
            crate::leanh::lean_dec_ref_known(v_x_214_, 1);
            v___x_222_ =
                crate::leanh::lean_apply_2(v_h__2_216_, v_it_221_, crate::leanh::lean_box(0));
            return v___x_222_;
        }
        _ => {
            let mut v___x_223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_216_);
            crate::leanh::lean_dec(v_h__1_215_);
            v___x_223_ = crate::leanh::lean_apply_1(v_h__3_217_, crate::leanh::lean_box(0));
            return v___x_223_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take_0__Std_IterM_step__take_match__1_splitter___boxed(
    mut v_00_u03b1_224_: *mut crate::leanh::LeanObject,
    mut v_m_225_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_226_: *mut crate::leanh::LeanObject,
    mut v_inst_227_: *mut crate::leanh::LeanObject,
    mut v_it_228_: *mut crate::leanh::LeanObject,
    mut v_motive_229_: *mut crate::leanh::LeanObject,
    mut v_x_230_: *mut crate::leanh::LeanObject,
    mut v_h__1_231_: *mut crate::leanh::LeanObject,
    mut v_h__2_232_: *mut crate::leanh::LeanObject,
    mut v_h__3_233_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_234_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take_0__Std_IterM_step__take_match__1_splitter(v_00_u03b1_224_, v_m_225_, v_00_u03b2_226_, v_inst_227_, v_it_228_, v_motive_229_, v_x_230_, v_h__1_231_, v_h__2_232_, v_h__3_233_);
    crate::leanh::lean_dec(v_it_228_);
    crate::leanh::lean_dec(v_inst_227_);
    return v_res_234_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take_0__Std_IterM_toArray__eq__match__step_match__1_splitter___redArg(
    mut v_x_235_: *mut crate::leanh::LeanObject,
    mut v_h__1_236_: *mut crate::leanh::LeanObject,
    mut v_h__2_237_: *mut crate::leanh::LeanObject,
    mut v_h__3_238_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_235_) {
        0 => {
            let mut v_it_239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_238_);
            crate::leanh::lean_dec(v_h__2_237_);
            v_it_239_ = crate::leanh::lean_ctor_get(v_x_235_, 0);
            crate::leanh::lean_inc(v_it_239_);
            v_out_240_ = crate::leanh::lean_ctor_get(v_x_235_, 1);
            crate::leanh::lean_inc(v_out_240_);
            crate::leanh::lean_dec_ref_known(v_x_235_, 2);
            v___x_241_ = crate::leanh::lean_apply_2(v_h__1_236_, v_it_239_, v_out_240_);
            return v___x_241_;
        }
        1 => {
            let mut v_it_242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_238_);
            crate::leanh::lean_dec(v_h__1_236_);
            v_it_242_ = crate::leanh::lean_ctor_get(v_x_235_, 0);
            crate::leanh::lean_inc(v_it_242_);
            crate::leanh::lean_dec_ref_known(v_x_235_, 1);
            v___x_243_ = crate::leanh::lean_apply_1(v_h__2_237_, v_it_242_);
            return v___x_243_;
        }
        _ => {
            let mut v___x_244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_237_);
            crate::leanh::lean_dec(v_h__1_236_);
            v___x_244_ = crate::leanh::lean_box(0);
            v___x_245_ = crate::leanh::lean_apply_1(v_h__3_238_, v___x_244_);
            return v___x_245_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take_0__Std_IterM_toArray__eq__match__step_match__1_splitter(
    mut v_00_u03b1_246_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_247_: *mut crate::leanh::LeanObject,
    mut v_m_248_: *mut crate::leanh::LeanObject,
    mut v_motive_249_: *mut crate::leanh::LeanObject,
    mut v_x_250_: *mut crate::leanh::LeanObject,
    mut v_h__1_251_: *mut crate::leanh::LeanObject,
    mut v_h__2_252_: *mut crate::leanh::LeanObject,
    mut v_h__3_253_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_250_) {
        0 => {
            let mut v_it_254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_253_);
            crate::leanh::lean_dec(v_h__2_252_);
            v_it_254_ = crate::leanh::lean_ctor_get(v_x_250_, 0);
            crate::leanh::lean_inc(v_it_254_);
            v_out_255_ = crate::leanh::lean_ctor_get(v_x_250_, 1);
            crate::leanh::lean_inc(v_out_255_);
            crate::leanh::lean_dec_ref_known(v_x_250_, 2);
            v___x_256_ = crate::leanh::lean_apply_2(v_h__1_251_, v_it_254_, v_out_255_);
            return v___x_256_;
        }
        1 => {
            let mut v_it_257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_253_);
            crate::leanh::lean_dec(v_h__1_251_);
            v_it_257_ = crate::leanh::lean_ctor_get(v_x_250_, 0);
            crate::leanh::lean_inc(v_it_257_);
            crate::leanh::lean_dec_ref_known(v_x_250_, 1);
            v___x_258_ = crate::leanh::lean_apply_1(v_h__2_252_, v_it_257_);
            return v___x_258_;
        }
        _ => {
            let mut v___x_259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_252_);
            crate::leanh::lean_dec(v_h__1_251_);
            v___x_259_ = crate::leanh::lean_box(0);
            v___x_260_ = crate::leanh::lean_apply_1(v_h__3_253_, v___x_259_);
            return v___x_260_;
        }
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Iterators_Combinators_Monadic_Take(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Collect(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Monadic_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take(
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
pub unsafe fn initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Iterators_Combinators_Monadic_Take(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers_Monadic_Collect(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Monadic_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take(builtin);
}
