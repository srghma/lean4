// Lean compiler output
// Module: Init.Data.Iterators.Lemmas.Combinators.Monadic.Take
// Imports: Init.Data.Iterators.Combinators.Monadic.Take Init.Data.Iterators.Consumers.Monadic.Collect Init.Data.Iterators.Lemmas.Consumers.Monadic.Collect Init.Data.Iterators.Lemmas.Monadic.Basic Init.Data.Nat.Lemmas
use crate::ffi::{lean_nat_dec_eq, lean_nat_sub};
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
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take_0__Std_Iterators_Types_Take_instIterator_match__1_splitter___redArg(
    mut v_x_131_: *mut leanh::LeanObject,
    mut v_h__1_132_: *mut leanh::LeanObject,
    mut v_h__2_133_: *mut leanh::LeanObject,
    mut v_h__3_134_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_131_) {
        0 => {
            let mut v_it_135_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_136_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_137_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_134_);
            leanh::lean_dec(v_h__2_133_);
            v_it_135_ = leanh::lean_ctor_get(v_x_131_, 0);
            leanh::lean_inc(v_it_135_);
            v_out_136_ = leanh::lean_ctor_get(v_x_131_, 1);
            leanh::lean_inc(v_out_136_);
            leanh::lean_dec_ref_known(v_x_131_, 2);
            v___x_137_ = leanh::lean_apply_3(
                v_h__1_132_,
                v_it_135_,
                v_out_136_,
                leanh::lean_box(0),
            );
            return v___x_137_;
        }
        1 => {
            let mut v_it_138_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_139_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_134_);
            leanh::lean_dec(v_h__1_132_);
            v_it_138_ = leanh::lean_ctor_get(v_x_131_, 0);
            leanh::lean_inc(v_it_138_);
            leanh::lean_dec_ref_known(v_x_131_, 1);
            v___x_139_ =
                leanh::lean_apply_2(v_h__2_133_, v_it_138_, leanh::lean_box(0));
            return v___x_139_;
        }
        _ => {
            let mut v___x_140_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_133_);
            leanh::lean_dec(v_h__1_132_);
            v___x_140_ = leanh::lean_apply_1(v_h__3_134_, leanh::lean_box(0));
            return v___x_140_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take_0__Std_Iterators_Types_Take_instIterator_match__1_splitter(
    mut v_00_u03b1_141_: *mut leanh::LeanObject,
    mut v_m_142_: *mut leanh::LeanObject,
    mut v_00_u03b2_143_: *mut leanh::LeanObject,
    mut v_inst_144_: *mut leanh::LeanObject,
    mut v_it_145_: *mut leanh::LeanObject,
    mut v_motive_146_: *mut leanh::LeanObject,
    mut v_x_147_: *mut leanh::LeanObject,
    mut v_h__1_148_: *mut leanh::LeanObject,
    mut v_h__2_149_: *mut leanh::LeanObject,
    mut v_h__3_150_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_147_) {
        0 => {
            let mut v_it_151_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_152_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_153_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_150_);
            leanh::lean_dec(v_h__2_149_);
            v_it_151_ = leanh::lean_ctor_get(v_x_147_, 0);
            leanh::lean_inc(v_it_151_);
            v_out_152_ = leanh::lean_ctor_get(v_x_147_, 1);
            leanh::lean_inc(v_out_152_);
            leanh::lean_dec_ref_known(v_x_147_, 2);
            v___x_153_ = leanh::lean_apply_3(
                v_h__1_148_,
                v_it_151_,
                v_out_152_,
                leanh::lean_box(0),
            );
            return v___x_153_;
        }
        1 => {
            let mut v_it_154_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_155_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_150_);
            leanh::lean_dec(v_h__1_148_);
            v_it_154_ = leanh::lean_ctor_get(v_x_147_, 0);
            leanh::lean_inc(v_it_154_);
            leanh::lean_dec_ref_known(v_x_147_, 1);
            v___x_155_ =
                leanh::lean_apply_2(v_h__2_149_, v_it_154_, leanh::lean_box(0));
            return v___x_155_;
        }
        _ => {
            let mut v___x_156_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_149_);
            leanh::lean_dec(v_h__1_148_);
            v___x_156_ = leanh::lean_apply_1(v_h__3_150_, leanh::lean_box(0));
            return v___x_156_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take_0__Std_Iterators_Types_Take_instIterator_match__1_splitter___boxed(
    mut v_00_u03b1_157_: *mut leanh::LeanObject,
    mut v_m_158_: *mut leanh::LeanObject,
    mut v_00_u03b2_159_: *mut leanh::LeanObject,
    mut v_inst_160_: *mut leanh::LeanObject,
    mut v_it_161_: *mut leanh::LeanObject,
    mut v_motive_162_: *mut leanh::LeanObject,
    mut v_x_163_: *mut leanh::LeanObject,
    mut v_h__1_164_: *mut leanh::LeanObject,
    mut v_h__2_165_: *mut leanh::LeanObject,
    mut v_h__3_166_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_167_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_167_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take_0__Std_Iterators_Types_Take_instIterator_match__1_splitter(v_00_u03b1_157_, v_m_158_, v_00_u03b2_159_, v_inst_160_, v_it_161_, v_motive_162_, v_x_163_, v_h__1_164_, v_h__2_165_, v_h__3_166_);
    leanh::lean_dec_ref(v_it_161_);
    leanh::lean_dec(v_inst_160_);
    return v_res_167_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take_0__Std_IterM_step__take_match__3_splitter___redArg(
    mut v_n_168_: *mut leanh::LeanObject,
    mut v_h__1_169_: *mut leanh::LeanObject,
    mut v_h__2_170_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_172_: u8 = 0;
    v_zero_171_ = leanh::lean_unsigned_to_nat(0);
    v_isZero_172_ = lean_nat_dec_eq(v_n_168_, v_zero_171_);
    if v_isZero_172_ == 1 {
        let mut v___x_173_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_174_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_170_);
        v___x_173_ = leanh::lean_box(0);
        v___x_174_ = leanh::lean_apply_1(v_h__1_169_, v___x_173_);
        return v___x_174_;
    } else {
        let mut v_one_175_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_176_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_177_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_169_);
        v_one_175_ = leanh::lean_unsigned_to_nat(1);
        v_n_176_ = lean_nat_sub(v_n_168_, v_one_175_);
        v___x_177_ = leanh::lean_apply_1(v_h__2_170_, v_n_176_);
        return v___x_177_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take_0__Std_IterM_step__take_match__3_splitter___redArg___boxed(
    mut v_n_178_: *mut leanh::LeanObject,
    mut v_h__1_179_: *mut leanh::LeanObject,
    mut v_h__2_180_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_181_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_181_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take_0__Std_IterM_step__take_match__3_splitter___redArg(v_n_178_, v_h__1_179_, v_h__2_180_);
    leanh::lean_dec(v_n_178_);
    return v_res_181_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take_0__Std_IterM_step__take_match__3_splitter(
    mut v_motive_182_: *mut leanh::LeanObject,
    mut v_n_183_: *mut leanh::LeanObject,
    mut v_h__1_184_: *mut leanh::LeanObject,
    mut v_h__2_185_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_187_: u8 = 0;
    v_zero_186_ = leanh::lean_unsigned_to_nat(0);
    v_isZero_187_ = lean_nat_dec_eq(v_n_183_, v_zero_186_);
    if v_isZero_187_ == 1 {
        let mut v___x_188_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_189_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_185_);
        v___x_188_ = leanh::lean_box(0);
        v___x_189_ = leanh::lean_apply_1(v_h__1_184_, v___x_188_);
        return v___x_189_;
    } else {
        let mut v_one_190_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_191_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_192_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_184_);
        v_one_190_ = leanh::lean_unsigned_to_nat(1);
        v_n_191_ = lean_nat_sub(v_n_183_, v_one_190_);
        v___x_192_ = leanh::lean_apply_1(v_h__2_185_, v_n_191_);
        return v___x_192_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take_0__Std_IterM_step__take_match__3_splitter___boxed(
    mut v_motive_193_: *mut leanh::LeanObject,
    mut v_n_194_: *mut leanh::LeanObject,
    mut v_h__1_195_: *mut leanh::LeanObject,
    mut v_h__2_196_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_197_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_197_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take_0__Std_IterM_step__take_match__3_splitter(v_motive_193_, v_n_194_, v_h__1_195_, v_h__2_196_);
    leanh::lean_dec(v_n_194_);
    return v_res_197_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take_0__Std_IterM_step__take_match__1_splitter___redArg(
    mut v_x_198_: *mut leanh::LeanObject,
    mut v_h__1_199_: *mut leanh::LeanObject,
    mut v_h__2_200_: *mut leanh::LeanObject,
    mut v_h__3_201_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_198_) {
        0 => {
            let mut v_it_202_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_203_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_204_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_201_);
            leanh::lean_dec(v_h__2_200_);
            v_it_202_ = leanh::lean_ctor_get(v_x_198_, 0);
            leanh::lean_inc(v_it_202_);
            v_out_203_ = leanh::lean_ctor_get(v_x_198_, 1);
            leanh::lean_inc(v_out_203_);
            leanh::lean_dec_ref_known(v_x_198_, 2);
            v___x_204_ = leanh::lean_apply_3(
                v_h__1_199_,
                v_it_202_,
                v_out_203_,
                leanh::lean_box(0),
            );
            return v___x_204_;
        }
        1 => {
            let mut v_it_205_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_206_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_201_);
            leanh::lean_dec(v_h__1_199_);
            v_it_205_ = leanh::lean_ctor_get(v_x_198_, 0);
            leanh::lean_inc(v_it_205_);
            leanh::lean_dec_ref_known(v_x_198_, 1);
            v___x_206_ =
                leanh::lean_apply_2(v_h__2_200_, v_it_205_, leanh::lean_box(0));
            return v___x_206_;
        }
        _ => {
            let mut v___x_207_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_200_);
            leanh::lean_dec(v_h__1_199_);
            v___x_207_ = leanh::lean_apply_1(v_h__3_201_, leanh::lean_box(0));
            return v___x_207_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take_0__Std_IterM_step__take_match__1_splitter(
    mut v_00_u03b1_208_: *mut leanh::LeanObject,
    mut v_m_209_: *mut leanh::LeanObject,
    mut v_00_u03b2_210_: *mut leanh::LeanObject,
    mut v_inst_211_: *mut leanh::LeanObject,
    mut v_it_212_: *mut leanh::LeanObject,
    mut v_motive_213_: *mut leanh::LeanObject,
    mut v_x_214_: *mut leanh::LeanObject,
    mut v_h__1_215_: *mut leanh::LeanObject,
    mut v_h__2_216_: *mut leanh::LeanObject,
    mut v_h__3_217_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_214_) {
        0 => {
            let mut v_it_218_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_219_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_220_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_217_);
            leanh::lean_dec(v_h__2_216_);
            v_it_218_ = leanh::lean_ctor_get(v_x_214_, 0);
            leanh::lean_inc(v_it_218_);
            v_out_219_ = leanh::lean_ctor_get(v_x_214_, 1);
            leanh::lean_inc(v_out_219_);
            leanh::lean_dec_ref_known(v_x_214_, 2);
            v___x_220_ = leanh::lean_apply_3(
                v_h__1_215_,
                v_it_218_,
                v_out_219_,
                leanh::lean_box(0),
            );
            return v___x_220_;
        }
        1 => {
            let mut v_it_221_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_222_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_217_);
            leanh::lean_dec(v_h__1_215_);
            v_it_221_ = leanh::lean_ctor_get(v_x_214_, 0);
            leanh::lean_inc(v_it_221_);
            leanh::lean_dec_ref_known(v_x_214_, 1);
            v___x_222_ =
                leanh::lean_apply_2(v_h__2_216_, v_it_221_, leanh::lean_box(0));
            return v___x_222_;
        }
        _ => {
            let mut v___x_223_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_216_);
            leanh::lean_dec(v_h__1_215_);
            v___x_223_ = leanh::lean_apply_1(v_h__3_217_, leanh::lean_box(0));
            return v___x_223_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take_0__Std_IterM_step__take_match__1_splitter___boxed(
    mut v_00_u03b1_224_: *mut leanh::LeanObject,
    mut v_m_225_: *mut leanh::LeanObject,
    mut v_00_u03b2_226_: *mut leanh::LeanObject,
    mut v_inst_227_: *mut leanh::LeanObject,
    mut v_it_228_: *mut leanh::LeanObject,
    mut v_motive_229_: *mut leanh::LeanObject,
    mut v_x_230_: *mut leanh::LeanObject,
    mut v_h__1_231_: *mut leanh::LeanObject,
    mut v_h__2_232_: *mut leanh::LeanObject,
    mut v_h__3_233_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_234_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_234_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take_0__Std_IterM_step__take_match__1_splitter(v_00_u03b1_224_, v_m_225_, v_00_u03b2_226_, v_inst_227_, v_it_228_, v_motive_229_, v_x_230_, v_h__1_231_, v_h__2_232_, v_h__3_233_);
    leanh::lean_dec(v_it_228_);
    leanh::lean_dec(v_inst_227_);
    return v_res_234_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take_0__Std_IterM_toArray__eq__match__step_match__1_splitter___redArg(
    mut v_x_235_: *mut leanh::LeanObject,
    mut v_h__1_236_: *mut leanh::LeanObject,
    mut v_h__2_237_: *mut leanh::LeanObject,
    mut v_h__3_238_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_235_) {
        0 => {
            let mut v_it_239_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_240_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_241_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_238_);
            leanh::lean_dec(v_h__2_237_);
            v_it_239_ = leanh::lean_ctor_get(v_x_235_, 0);
            leanh::lean_inc(v_it_239_);
            v_out_240_ = leanh::lean_ctor_get(v_x_235_, 1);
            leanh::lean_inc(v_out_240_);
            leanh::lean_dec_ref_known(v_x_235_, 2);
            v___x_241_ = leanh::lean_apply_2(v_h__1_236_, v_it_239_, v_out_240_);
            return v___x_241_;
        }
        1 => {
            let mut v_it_242_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_243_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_238_);
            leanh::lean_dec(v_h__1_236_);
            v_it_242_ = leanh::lean_ctor_get(v_x_235_, 0);
            leanh::lean_inc(v_it_242_);
            leanh::lean_dec_ref_known(v_x_235_, 1);
            v___x_243_ = leanh::lean_apply_1(v_h__2_237_, v_it_242_);
            return v___x_243_;
        }
        _ => {
            let mut v___x_244_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_245_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_237_);
            leanh::lean_dec(v_h__1_236_);
            v___x_244_ = leanh::lean_box(0);
            v___x_245_ = leanh::lean_apply_1(v_h__3_238_, v___x_244_);
            return v___x_245_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take_0__Std_IterM_toArray__eq__match__step_match__1_splitter(
    mut v_00_u03b1_246_: *mut leanh::LeanObject,
    mut v_00_u03b2_247_: *mut leanh::LeanObject,
    mut v_m_248_: *mut leanh::LeanObject,
    mut v_motive_249_: *mut leanh::LeanObject,
    mut v_x_250_: *mut leanh::LeanObject,
    mut v_h__1_251_: *mut leanh::LeanObject,
    mut v_h__2_252_: *mut leanh::LeanObject,
    mut v_h__3_253_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_250_) {
        0 => {
            let mut v_it_254_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_255_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_256_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_253_);
            leanh::lean_dec(v_h__2_252_);
            v_it_254_ = leanh::lean_ctor_get(v_x_250_, 0);
            leanh::lean_inc(v_it_254_);
            v_out_255_ = leanh::lean_ctor_get(v_x_250_, 1);
            leanh::lean_inc(v_out_255_);
            leanh::lean_dec_ref_known(v_x_250_, 2);
            v___x_256_ = leanh::lean_apply_2(v_h__1_251_, v_it_254_, v_out_255_);
            return v___x_256_;
        }
        1 => {
            let mut v_it_257_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_258_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_253_);
            leanh::lean_dec(v_h__1_251_);
            v_it_257_ = leanh::lean_ctor_get(v_x_250_, 0);
            leanh::lean_inc(v_it_257_);
            leanh::lean_dec_ref_known(v_x_250_, 1);
            v___x_258_ = leanh::lean_apply_1(v_h__2_252_, v_it_257_);
            return v___x_258_;
        }
        _ => {
            let mut v___x_259_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_260_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_252_);
            leanh::lean_dec(v_h__1_251_);
            v___x_259_ = leanh::lean_box(0);
            v___x_260_ = leanh::lean_apply_1(v_h__3_253_, v___x_259_);
            return v___x_260_;
        }
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Iterators_Combinators_Monadic_Take(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Collect(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Monadic_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take(
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
pub unsafe fn initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Iterators_Combinators_Monadic_Take(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers_Monadic_Collect(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Monadic_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take(builtin);
}