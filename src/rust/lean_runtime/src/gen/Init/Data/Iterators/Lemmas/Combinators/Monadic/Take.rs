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
use crate::lean_imports_rs::Init::Prelude::{lean_nat_dec_eq, lean_nat_sub};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_apply_1, lean_apply_2, lean_apply_3, lean_box,
    lean_ctor_get, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_obj_tag, lean_unsigned_to_nat,
};
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take_0__Std_Iterators_Types_Take_instIterator_match__1_splitter___redArg(
    mut v_x_131_: *mut LeanObject,
    mut v_h__1_132_: *mut LeanObject,
    mut v_h__2_133_: *mut LeanObject,
    mut v_h__3_134_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_131_) {
        0 => {
            let mut v_it_135_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_136_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_137_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_134_);
            lean_dec(v_h__2_133_);
            v_it_135_ = lean_ctor_get(v_x_131_, 0);
            lean_inc(v_it_135_);
            v_out_136_ = lean_ctor_get(v_x_131_, 1);
            lean_inc(v_out_136_);
            lean_dec_ref_known(v_x_131_, 2);
            v___x_137_ = lean_apply_3(v_h__1_132_, v_it_135_, v_out_136_, lean_box(0));
            return v___x_137_;
        }
        1 => {
            let mut v_it_138_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_139_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_134_);
            lean_dec(v_h__1_132_);
            v_it_138_ = lean_ctor_get(v_x_131_, 0);
            lean_inc(v_it_138_);
            lean_dec_ref_known(v_x_131_, 1);
            v___x_139_ = lean_apply_2(v_h__2_133_, v_it_138_, lean_box(0));
            return v___x_139_;
        }
        _ => {
            let mut v___x_140_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_133_);
            lean_dec(v_h__1_132_);
            v___x_140_ = lean_apply_1(v_h__3_134_, lean_box(0));
            return v___x_140_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take_0__Std_Iterators_Types_Take_instIterator_match__1_splitter(
    mut v_00_u03b1_141_: *mut LeanObject,
    mut v_m_142_: *mut LeanObject,
    mut v_00_u03b2_143_: *mut LeanObject,
    mut v_inst_144_: *mut LeanObject,
    mut v_it_145_: *mut LeanObject,
    mut v_motive_146_: *mut LeanObject,
    mut v_x_147_: *mut LeanObject,
    mut v_h__1_148_: *mut LeanObject,
    mut v_h__2_149_: *mut LeanObject,
    mut v_h__3_150_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_147_) {
        0 => {
            let mut v_it_151_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_152_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_153_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_150_);
            lean_dec(v_h__2_149_);
            v_it_151_ = lean_ctor_get(v_x_147_, 0);
            lean_inc(v_it_151_);
            v_out_152_ = lean_ctor_get(v_x_147_, 1);
            lean_inc(v_out_152_);
            lean_dec_ref_known(v_x_147_, 2);
            v___x_153_ = lean_apply_3(v_h__1_148_, v_it_151_, v_out_152_, lean_box(0));
            return v___x_153_;
        }
        1 => {
            let mut v_it_154_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_155_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_150_);
            lean_dec(v_h__1_148_);
            v_it_154_ = lean_ctor_get(v_x_147_, 0);
            lean_inc(v_it_154_);
            lean_dec_ref_known(v_x_147_, 1);
            v___x_155_ = lean_apply_2(v_h__2_149_, v_it_154_, lean_box(0));
            return v___x_155_;
        }
        _ => {
            let mut v___x_156_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_149_);
            lean_dec(v_h__1_148_);
            v___x_156_ = lean_apply_1(v_h__3_150_, lean_box(0));
            return v___x_156_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take_0__Std_Iterators_Types_Take_instIterator_match__1_splitter___boxed(
    mut v_00_u03b1_157_: *mut LeanObject,
    mut v_m_158_: *mut LeanObject,
    mut v_00_u03b2_159_: *mut LeanObject,
    mut v_inst_160_: *mut LeanObject,
    mut v_it_161_: *mut LeanObject,
    mut v_motive_162_: *mut LeanObject,
    mut v_x_163_: *mut LeanObject,
    mut v_h__1_164_: *mut LeanObject,
    mut v_h__2_165_: *mut LeanObject,
    mut v_h__3_166_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_167_: *mut LeanObject = core::ptr::null_mut();
    v_res_167_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take_0__Std_Iterators_Types_Take_instIterator_match__1_splitter(v_00_u03b1_157_, v_m_158_, v_00_u03b2_159_, v_inst_160_, v_it_161_, v_motive_162_, v_x_163_, v_h__1_164_, v_h__2_165_, v_h__3_166_);
    lean_dec_ref(v_it_161_);
    lean_dec(v_inst_160_);
    return v_res_167_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take_0__Std_IterM_step__take_match__3_splitter___redArg(
    mut v_n_168_: *mut LeanObject,
    mut v_h__1_169_: *mut LeanObject,
    mut v_h__2_170_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_172_: u8 = 0;
    v_zero_171_ = lean_unsigned_to_nat(0);
    v_isZero_172_ = lean_nat_dec_eq(v_n_168_, v_zero_171_);
    if v_isZero_172_ == 1 {
        let mut v___x_173_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_174_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_170_);
        v___x_173_ = lean_box(0);
        v___x_174_ = lean_apply_1(v_h__1_169_, v___x_173_);
        return v___x_174_;
    } else {
        let mut v_one_175_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_176_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_177_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_169_);
        v_one_175_ = lean_unsigned_to_nat(1);
        v_n_176_ = lean_nat_sub(v_n_168_, v_one_175_);
        v___x_177_ = lean_apply_1(v_h__2_170_, v_n_176_);
        return v___x_177_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take_0__Std_IterM_step__take_match__3_splitter___redArg___boxed(
    mut v_n_178_: *mut LeanObject,
    mut v_h__1_179_: *mut LeanObject,
    mut v_h__2_180_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_181_: *mut LeanObject = core::ptr::null_mut();
    v_res_181_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take_0__Std_IterM_step__take_match__3_splitter___redArg(v_n_178_, v_h__1_179_, v_h__2_180_);
    lean_dec(v_n_178_);
    return v_res_181_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take_0__Std_IterM_step__take_match__3_splitter(
    mut v_motive_182_: *mut LeanObject,
    mut v_n_183_: *mut LeanObject,
    mut v_h__1_184_: *mut LeanObject,
    mut v_h__2_185_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_186_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_187_: u8 = 0;
    v_zero_186_ = lean_unsigned_to_nat(0);
    v_isZero_187_ = lean_nat_dec_eq(v_n_183_, v_zero_186_);
    if v_isZero_187_ == 1 {
        let mut v___x_188_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_189_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_185_);
        v___x_188_ = lean_box(0);
        v___x_189_ = lean_apply_1(v_h__1_184_, v___x_188_);
        return v___x_189_;
    } else {
        let mut v_one_190_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_191_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_192_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_184_);
        v_one_190_ = lean_unsigned_to_nat(1);
        v_n_191_ = lean_nat_sub(v_n_183_, v_one_190_);
        v___x_192_ = lean_apply_1(v_h__2_185_, v_n_191_);
        return v___x_192_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take_0__Std_IterM_step__take_match__3_splitter___boxed(
    mut v_motive_193_: *mut LeanObject,
    mut v_n_194_: *mut LeanObject,
    mut v_h__1_195_: *mut LeanObject,
    mut v_h__2_196_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_197_: *mut LeanObject = core::ptr::null_mut();
    v_res_197_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take_0__Std_IterM_step__take_match__3_splitter(v_motive_193_, v_n_194_, v_h__1_195_, v_h__2_196_);
    lean_dec(v_n_194_);
    return v_res_197_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take_0__Std_IterM_step__take_match__1_splitter___redArg(
    mut v_x_198_: *mut LeanObject,
    mut v_h__1_199_: *mut LeanObject,
    mut v_h__2_200_: *mut LeanObject,
    mut v_h__3_201_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_198_) {
        0 => {
            let mut v_it_202_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_203_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_204_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_201_);
            lean_dec(v_h__2_200_);
            v_it_202_ = lean_ctor_get(v_x_198_, 0);
            lean_inc(v_it_202_);
            v_out_203_ = lean_ctor_get(v_x_198_, 1);
            lean_inc(v_out_203_);
            lean_dec_ref_known(v_x_198_, 2);
            v___x_204_ = lean_apply_3(v_h__1_199_, v_it_202_, v_out_203_, lean_box(0));
            return v___x_204_;
        }
        1 => {
            let mut v_it_205_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_206_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_201_);
            lean_dec(v_h__1_199_);
            v_it_205_ = lean_ctor_get(v_x_198_, 0);
            lean_inc(v_it_205_);
            lean_dec_ref_known(v_x_198_, 1);
            v___x_206_ = lean_apply_2(v_h__2_200_, v_it_205_, lean_box(0));
            return v___x_206_;
        }
        _ => {
            let mut v___x_207_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_200_);
            lean_dec(v_h__1_199_);
            v___x_207_ = lean_apply_1(v_h__3_201_, lean_box(0));
            return v___x_207_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take_0__Std_IterM_step__take_match__1_splitter(
    mut v_00_u03b1_208_: *mut LeanObject,
    mut v_m_209_: *mut LeanObject,
    mut v_00_u03b2_210_: *mut LeanObject,
    mut v_inst_211_: *mut LeanObject,
    mut v_it_212_: *mut LeanObject,
    mut v_motive_213_: *mut LeanObject,
    mut v_x_214_: *mut LeanObject,
    mut v_h__1_215_: *mut LeanObject,
    mut v_h__2_216_: *mut LeanObject,
    mut v_h__3_217_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_214_) {
        0 => {
            let mut v_it_218_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_219_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_220_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_217_);
            lean_dec(v_h__2_216_);
            v_it_218_ = lean_ctor_get(v_x_214_, 0);
            lean_inc(v_it_218_);
            v_out_219_ = lean_ctor_get(v_x_214_, 1);
            lean_inc(v_out_219_);
            lean_dec_ref_known(v_x_214_, 2);
            v___x_220_ = lean_apply_3(v_h__1_215_, v_it_218_, v_out_219_, lean_box(0));
            return v___x_220_;
        }
        1 => {
            let mut v_it_221_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_222_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_217_);
            lean_dec(v_h__1_215_);
            v_it_221_ = lean_ctor_get(v_x_214_, 0);
            lean_inc(v_it_221_);
            lean_dec_ref_known(v_x_214_, 1);
            v___x_222_ = lean_apply_2(v_h__2_216_, v_it_221_, lean_box(0));
            return v___x_222_;
        }
        _ => {
            let mut v___x_223_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_216_);
            lean_dec(v_h__1_215_);
            v___x_223_ = lean_apply_1(v_h__3_217_, lean_box(0));
            return v___x_223_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take_0__Std_IterM_step__take_match__1_splitter___boxed(
    mut v_00_u03b1_224_: *mut LeanObject,
    mut v_m_225_: *mut LeanObject,
    mut v_00_u03b2_226_: *mut LeanObject,
    mut v_inst_227_: *mut LeanObject,
    mut v_it_228_: *mut LeanObject,
    mut v_motive_229_: *mut LeanObject,
    mut v_x_230_: *mut LeanObject,
    mut v_h__1_231_: *mut LeanObject,
    mut v_h__2_232_: *mut LeanObject,
    mut v_h__3_233_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_234_: *mut LeanObject = core::ptr::null_mut();
    v_res_234_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take_0__Std_IterM_step__take_match__1_splitter(v_00_u03b1_224_, v_m_225_, v_00_u03b2_226_, v_inst_227_, v_it_228_, v_motive_229_, v_x_230_, v_h__1_231_, v_h__2_232_, v_h__3_233_);
    lean_dec(v_it_228_);
    lean_dec(v_inst_227_);
    return v_res_234_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take_0__Std_IterM_toArray__eq__match__step_match__1_splitter___redArg(
    mut v_x_235_: *mut LeanObject,
    mut v_h__1_236_: *mut LeanObject,
    mut v_h__2_237_: *mut LeanObject,
    mut v_h__3_238_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_235_) {
        0 => {
            let mut v_it_239_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_240_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_241_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_238_);
            lean_dec(v_h__2_237_);
            v_it_239_ = lean_ctor_get(v_x_235_, 0);
            lean_inc(v_it_239_);
            v_out_240_ = lean_ctor_get(v_x_235_, 1);
            lean_inc(v_out_240_);
            lean_dec_ref_known(v_x_235_, 2);
            v___x_241_ = lean_apply_2(v_h__1_236_, v_it_239_, v_out_240_);
            return v___x_241_;
        }
        1 => {
            let mut v_it_242_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_243_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_238_);
            lean_dec(v_h__1_236_);
            v_it_242_ = lean_ctor_get(v_x_235_, 0);
            lean_inc(v_it_242_);
            lean_dec_ref_known(v_x_235_, 1);
            v___x_243_ = lean_apply_1(v_h__2_237_, v_it_242_);
            return v___x_243_;
        }
        _ => {
            let mut v___x_244_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_245_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_237_);
            lean_dec(v_h__1_236_);
            v___x_244_ = lean_box(0);
            v___x_245_ = lean_apply_1(v_h__3_238_, v___x_244_);
            return v___x_245_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take_0__Std_IterM_toArray__eq__match__step_match__1_splitter(
    mut v_00_u03b1_246_: *mut LeanObject,
    mut v_00_u03b2_247_: *mut LeanObject,
    mut v_m_248_: *mut LeanObject,
    mut v_motive_249_: *mut LeanObject,
    mut v_x_250_: *mut LeanObject,
    mut v_h__1_251_: *mut LeanObject,
    mut v_h__2_252_: *mut LeanObject,
    mut v_h__3_253_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_250_) {
        0 => {
            let mut v_it_254_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_255_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_256_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_253_);
            lean_dec(v_h__2_252_);
            v_it_254_ = lean_ctor_get(v_x_250_, 0);
            lean_inc(v_it_254_);
            v_out_255_ = lean_ctor_get(v_x_250_, 1);
            lean_inc(v_out_255_);
            lean_dec_ref_known(v_x_250_, 2);
            v___x_256_ = lean_apply_2(v_h__1_251_, v_it_254_, v_out_255_);
            return v___x_256_;
        }
        1 => {
            let mut v_it_257_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_258_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_253_);
            lean_dec(v_h__1_251_);
            v_it_257_ = lean_ctor_get(v_x_250_, 0);
            lean_inc(v_it_257_);
            lean_dec_ref_known(v_x_250_, 1);
            v___x_258_ = lean_apply_1(v_h__2_252_, v_it_257_);
            return v___x_258_;
        }
        _ => {
            let mut v___x_259_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_260_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_252_);
            lean_dec(v_h__1_251_);
            v___x_259_ = lean_box(0);
            v___x_260_ = lean_apply_1(v_h__3_253_, v___x_259_);
            return v___x_260_;
        }
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Iterators_Combinators_Monadic_Take(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Collect(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Monadic_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Iterators_Combinators_Monadic_Take(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers_Monadic_Collect(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Monadic_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_Take(builtin);
}
