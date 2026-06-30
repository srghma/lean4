// Lean compiler output
// Module: Std.Data.Iterators.Lemmas.Combinators.Drop
// Imports: Std.Data.Iterators.Combinators.Drop Std.Data.Iterators.Lemmas.Combinators.Monadic.Drop Init.Data.Iterators.Lemmas.Combinators.Take Init.Data.Array.Lemmas Init.Data.Iterators.Lemmas.Basic Init.Data.Iterators.Lemmas.Consumers.Access Init.Data.Iterators.Lemmas.Consumers.Collect Init.Data.List.Nat.TakeDrop Init.Data.Option.Lemmas
use crate::ffi::{lean_nat_dec_eq, lean_nat_sub};
use crate::r#gen::Init::Data::Array::Lemmas::{
    initialize_Init_Data_Array_Lemmas, runtime_initialize_Init_Data_Array_Lemmas,
};
use crate::r#gen::Init::Data::Iterators::Lemmas::Basic::{
    initialize_Init_Data_Iterators_Lemmas_Basic,
    runtime_initialize_Init_Data_Iterators_Lemmas_Basic,
};
use crate::r#gen::Init::Data::Iterators::Lemmas::Combinators::Take::{
    initialize_Init_Data_Iterators_Lemmas_Combinators_Take,
    runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_Take,
};
use crate::r#gen::Init::Data::Iterators::Lemmas::Consumers::Access::{
    initialize_Init_Data_Iterators_Lemmas_Consumers_Access,
    runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Access,
};
use crate::r#gen::Init::Data::Iterators::Lemmas::Consumers::Collect::{
    initialize_Init_Data_Iterators_Lemmas_Consumers_Collect,
    runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Collect,
};
use crate::r#gen::Init::Data::List::Nat::TakeDrop::{
    initialize_Init_Data_List_Nat_TakeDrop, runtime_initialize_Init_Data_List_Nat_TakeDrop,
};
use crate::r#gen::Init::Data::Option::Lemmas::{
    initialize_Init_Data_Option_Lemmas, runtime_initialize_Init_Data_Option_Lemmas,
};
use crate::r#gen::Std::Data::Iterators::Combinators::Drop::{
    initialize_Std_Data_Iterators_Combinators_Drop,
    runtime_initialize_Std_Data_Iterators_Combinators_Drop,
};
use crate::r#gen::Std::Data::Iterators::Lemmas::Combinators::Monadic::Drop::{
    initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_Drop,
    runtime_initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_Drop,
};
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Drop_0__Std_IterM_step__drop_match__3_splitter___redArg(
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
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Drop_0__Std_IterM_step__drop_match__3_splitter(
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
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Drop_0__Std_IterM_step__drop_match__3_splitter___boxed(
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
    v_res_167_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Drop_0__Std_IterM_step__drop_match__3_splitter(v_00_u03b1_157_, v_m_158_, v_00_u03b2_159_, v_inst_160_, v_it_161_, v_motive_162_, v_x_163_, v_h__1_164_, v_h__2_165_, v_h__3_166_);
    leanh::lean_dec(v_it_161_);
    leanh::lean_dec(v_inst_160_);
    return v_res_167_;
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Drop_0__Std_IterM_step__drop_match__1_splitter___redArg(
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
        leanh::lean_dec(v_h__2_170_);
        v___x_173_ = leanh::lean_apply_1(v_h__1_169_, leanh::lean_box(0));
        return v___x_173_;
    } else {
        let mut v_one_174_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_175_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_176_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_169_);
        v_one_174_ = leanh::lean_unsigned_to_nat(1);
        v_n_175_ = lean_nat_sub(v_n_168_, v_one_174_);
        v___x_176_ = leanh::lean_apply_2(v_h__2_170_, v_n_175_, leanh::lean_box(0));
        return v___x_176_;
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Drop_0__Std_IterM_step__drop_match__1_splitter___redArg___boxed(
    mut v_n_177_: *mut leanh::LeanObject,
    mut v_h__1_178_: *mut leanh::LeanObject,
    mut v_h__2_179_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_180_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_180_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Drop_0__Std_IterM_step__drop_match__1_splitter___redArg(v_n_177_, v_h__1_178_, v_h__2_179_);
    leanh::lean_dec(v_n_177_);
    return v_res_180_;
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Drop_0__Std_IterM_step__drop_match__1_splitter(
    mut v_motive_181_: *mut leanh::LeanObject,
    mut v_n_182_: *mut leanh::LeanObject,
    mut v_h__1_183_: *mut leanh::LeanObject,
    mut v_h__2_184_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_186_: u8 = 0;
    v_zero_185_ = leanh::lean_unsigned_to_nat(0);
    v_isZero_186_ = lean_nat_dec_eq(v_n_182_, v_zero_185_);
    if v_isZero_186_ == 1 {
        let mut v___x_187_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_184_);
        v___x_187_ = leanh::lean_apply_1(v_h__1_183_, leanh::lean_box(0));
        return v___x_187_;
    } else {
        let mut v_one_188_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_189_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_190_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_183_);
        v_one_188_ = leanh::lean_unsigned_to_nat(1);
        v_n_189_ = lean_nat_sub(v_n_182_, v_one_188_);
        v___x_190_ = leanh::lean_apply_2(v_h__2_184_, v_n_189_, leanh::lean_box(0));
        return v___x_190_;
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Drop_0__Std_IterM_step__drop_match__1_splitter___boxed(
    mut v_motive_191_: *mut leanh::LeanObject,
    mut v_n_192_: *mut leanh::LeanObject,
    mut v_h__1_193_: *mut leanh::LeanObject,
    mut v_h__2_194_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_195_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_195_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Drop_0__Std_IterM_step__drop_match__1_splitter(v_motive_191_, v_n_192_, v_h__1_193_, v_h__2_194_);
    leanh::lean_dec(v_n_192_);
    return v_res_195_;
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Drop_0__Std_Iter_step__drop_match__3_splitter___redArg(
    mut v_x_196_: *mut leanh::LeanObject,
    mut v_h__1_197_: *mut leanh::LeanObject,
    mut v_h__2_198_: *mut leanh::LeanObject,
    mut v_h__3_199_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_196_) {
        0 => {
            let mut v_it_200_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_201_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_202_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_199_);
            leanh::lean_dec(v_h__2_198_);
            v_it_200_ = leanh::lean_ctor_get(v_x_196_, 0);
            leanh::lean_inc(v_it_200_);
            v_out_201_ = leanh::lean_ctor_get(v_x_196_, 1);
            leanh::lean_inc(v_out_201_);
            leanh::lean_dec_ref_known(v_x_196_, 2);
            v___x_202_ = leanh::lean_apply_3(
                v_h__1_197_,
                v_it_200_,
                v_out_201_,
                leanh::lean_box(0),
            );
            return v___x_202_;
        }
        1 => {
            let mut v_it_203_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_204_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_199_);
            leanh::lean_dec(v_h__1_197_);
            v_it_203_ = leanh::lean_ctor_get(v_x_196_, 0);
            leanh::lean_inc(v_it_203_);
            leanh::lean_dec_ref_known(v_x_196_, 1);
            v___x_204_ =
                leanh::lean_apply_2(v_h__2_198_, v_it_203_, leanh::lean_box(0));
            return v___x_204_;
        }
        _ => {
            let mut v___x_205_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_198_);
            leanh::lean_dec(v_h__1_197_);
            v___x_205_ = leanh::lean_apply_1(v_h__3_199_, leanh::lean_box(0));
            return v___x_205_;
        }
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Drop_0__Std_Iter_step__drop_match__3_splitter(
    mut v_00_u03b1_206_: *mut leanh::LeanObject,
    mut v_00_u03b2_207_: *mut leanh::LeanObject,
    mut v_inst_208_: *mut leanh::LeanObject,
    mut v_it_209_: *mut leanh::LeanObject,
    mut v_motive_210_: *mut leanh::LeanObject,
    mut v_x_211_: *mut leanh::LeanObject,
    mut v_h__1_212_: *mut leanh::LeanObject,
    mut v_h__2_213_: *mut leanh::LeanObject,
    mut v_h__3_214_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_211_) {
        0 => {
            let mut v_it_215_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_216_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_217_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_214_);
            leanh::lean_dec(v_h__2_213_);
            v_it_215_ = leanh::lean_ctor_get(v_x_211_, 0);
            leanh::lean_inc(v_it_215_);
            v_out_216_ = leanh::lean_ctor_get(v_x_211_, 1);
            leanh::lean_inc(v_out_216_);
            leanh::lean_dec_ref_known(v_x_211_, 2);
            v___x_217_ = leanh::lean_apply_3(
                v_h__1_212_,
                v_it_215_,
                v_out_216_,
                leanh::lean_box(0),
            );
            return v___x_217_;
        }
        1 => {
            let mut v_it_218_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_219_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_214_);
            leanh::lean_dec(v_h__1_212_);
            v_it_218_ = leanh::lean_ctor_get(v_x_211_, 0);
            leanh::lean_inc(v_it_218_);
            leanh::lean_dec_ref_known(v_x_211_, 1);
            v___x_219_ =
                leanh::lean_apply_2(v_h__2_213_, v_it_218_, leanh::lean_box(0));
            return v___x_219_;
        }
        _ => {
            let mut v___x_220_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_213_);
            leanh::lean_dec(v_h__1_212_);
            v___x_220_ = leanh::lean_apply_1(v_h__3_214_, leanh::lean_box(0));
            return v___x_220_;
        }
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Drop_0__Std_Iter_step__drop_match__3_splitter___boxed(
    mut v_00_u03b1_221_: *mut leanh::LeanObject,
    mut v_00_u03b2_222_: *mut leanh::LeanObject,
    mut v_inst_223_: *mut leanh::LeanObject,
    mut v_it_224_: *mut leanh::LeanObject,
    mut v_motive_225_: *mut leanh::LeanObject,
    mut v_x_226_: *mut leanh::LeanObject,
    mut v_h__1_227_: *mut leanh::LeanObject,
    mut v_h__2_228_: *mut leanh::LeanObject,
    mut v_h__3_229_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_230_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_230_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Drop_0__Std_Iter_step__drop_match__3_splitter(v_00_u03b1_221_, v_00_u03b2_222_, v_inst_223_, v_it_224_, v_motive_225_, v_x_226_, v_h__1_227_, v_h__2_228_, v_h__3_229_);
    leanh::lean_dec(v_it_224_);
    leanh::lean_dec(v_inst_223_);
    return v_res_230_;
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Drop_0__Std_Iter_step__drop_match__1_splitter___redArg(
    mut v_n_231_: *mut leanh::LeanObject,
    mut v_h__1_232_: *mut leanh::LeanObject,
    mut v_h__2_233_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_235_: u8 = 0;
    v_zero_234_ = leanh::lean_unsigned_to_nat(0);
    v_isZero_235_ = lean_nat_dec_eq(v_n_231_, v_zero_234_);
    if v_isZero_235_ == 1 {
        let mut v___x_236_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_237_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_233_);
        v___x_236_ = leanh::lean_box(0);
        v___x_237_ = leanh::lean_apply_1(v_h__1_232_, v___x_236_);
        return v___x_237_;
    } else {
        let mut v_one_238_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_239_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_240_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_232_);
        v_one_238_ = leanh::lean_unsigned_to_nat(1);
        v_n_239_ = lean_nat_sub(v_n_231_, v_one_238_);
        v___x_240_ = leanh::lean_apply_1(v_h__2_233_, v_n_239_);
        return v___x_240_;
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Drop_0__Std_Iter_step__drop_match__1_splitter___redArg___boxed(
    mut v_n_241_: *mut leanh::LeanObject,
    mut v_h__1_242_: *mut leanh::LeanObject,
    mut v_h__2_243_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_244_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_244_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Drop_0__Std_Iter_step__drop_match__1_splitter___redArg(v_n_241_, v_h__1_242_, v_h__2_243_);
    leanh::lean_dec(v_n_241_);
    return v_res_244_;
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Drop_0__Std_Iter_step__drop_match__1_splitter(
    mut v_motive_245_: *mut leanh::LeanObject,
    mut v_n_246_: *mut leanh::LeanObject,
    mut v_h__1_247_: *mut leanh::LeanObject,
    mut v_h__2_248_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_250_: u8 = 0;
    v_zero_249_ = leanh::lean_unsigned_to_nat(0);
    v_isZero_250_ = lean_nat_dec_eq(v_n_246_, v_zero_249_);
    if v_isZero_250_ == 1 {
        let mut v___x_251_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_252_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_248_);
        v___x_251_ = leanh::lean_box(0);
        v___x_252_ = leanh::lean_apply_1(v_h__1_247_, v___x_251_);
        return v___x_252_;
    } else {
        let mut v_one_253_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_254_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_255_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_247_);
        v_one_253_ = leanh::lean_unsigned_to_nat(1);
        v_n_254_ = lean_nat_sub(v_n_246_, v_one_253_);
        v___x_255_ = leanh::lean_apply_1(v_h__2_248_, v_n_254_);
        return v___x_255_;
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Drop_0__Std_Iter_step__drop_match__1_splitter___boxed(
    mut v_motive_256_: *mut leanh::LeanObject,
    mut v_n_257_: *mut leanh::LeanObject,
    mut v_h__1_258_: *mut leanh::LeanObject,
    mut v_h__2_259_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_260_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_260_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Drop_0__Std_Iter_step__drop_match__1_splitter(v_motive_256_, v_n_257_, v_h__1_258_, v_h__2_259_);
    leanh::lean_dec(v_n_257_);
    return v_res_260_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_Iterators_Lemmas_Combinators_Drop(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_Iterators_Combinators_Drop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_Drop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_Take(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Access(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Nat_TakeDrop(builtin);
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
pub unsafe fn meta_initialize_Std_Data_Iterators_Lemmas_Combinators_Drop(
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
pub unsafe fn initialize_Std_Data_Iterators_Lemmas_Combinators_Drop(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_Iterators_Combinators_Drop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_Drop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Combinators_Take(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Consumers_Access(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Nat_TakeDrop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Option_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Lemmas_Combinators_Drop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Data_Iterators_Lemmas_Combinators_Drop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Data_Iterators_Lemmas_Combinators_Drop(builtin);
}