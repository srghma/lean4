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
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_apply_1, lean_apply_2, lean_apply_3, lean_box,
    lean_ctor_get, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_obj_tag,
};
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect_0__Std_IterM_toArray_go_match__1_splitter___redArg(
    mut v_x_127_: *mut LeanObject,
    mut v_h__1_128_: *mut LeanObject,
    mut v_h__2_129_: *mut LeanObject,
    mut v_h__3_130_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_127_) {
        0 => {
            let mut v_it_131_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_132_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_133_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_130_);
            lean_dec(v_h__2_129_);
            v_it_131_ = lean_ctor_get(v_x_127_, 0);
            lean_inc(v_it_131_);
            v_out_132_ = lean_ctor_get(v_x_127_, 1);
            lean_inc(v_out_132_);
            lean_dec_ref_known(v_x_127_, 2);
            v___x_133_ = lean_apply_3(v_h__1_128_, v_it_131_, v_out_132_, lean_box(0));
            return v___x_133_;
        }
        1 => {
            let mut v_it_134_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_135_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_130_);
            lean_dec(v_h__1_128_);
            v_it_134_ = lean_ctor_get(v_x_127_, 0);
            lean_inc(v_it_134_);
            lean_dec_ref_known(v_x_127_, 1);
            v___x_135_ = lean_apply_2(v_h__2_129_, v_it_134_, lean_box(0));
            return v___x_135_;
        }
        _ => {
            let mut v___x_136_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_129_);
            lean_dec(v_h__1_128_);
            v___x_136_ = lean_apply_1(v_h__3_130_, lean_box(0));
            return v___x_136_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect_0__Std_IterM_toArray_go_match__1_splitter(
    mut v_00_u03b1_137_: *mut LeanObject,
    mut v_00_u03b2_138_: *mut LeanObject,
    mut v_m_139_: *mut LeanObject,
    mut v_inst_140_: *mut LeanObject,
    mut v_it_141_: *mut LeanObject,
    mut v_motive_142_: *mut LeanObject,
    mut v_x_143_: *mut LeanObject,
    mut v_h__1_144_: *mut LeanObject,
    mut v_h__2_145_: *mut LeanObject,
    mut v_h__3_146_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_143_) {
        0 => {
            let mut v_it_147_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_148_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_149_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_146_);
            lean_dec(v_h__2_145_);
            v_it_147_ = lean_ctor_get(v_x_143_, 0);
            lean_inc(v_it_147_);
            v_out_148_ = lean_ctor_get(v_x_143_, 1);
            lean_inc(v_out_148_);
            lean_dec_ref_known(v_x_143_, 2);
            v___x_149_ = lean_apply_3(v_h__1_144_, v_it_147_, v_out_148_, lean_box(0));
            return v___x_149_;
        }
        1 => {
            let mut v_it_150_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_151_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_146_);
            lean_dec(v_h__1_144_);
            v_it_150_ = lean_ctor_get(v_x_143_, 0);
            lean_inc(v_it_150_);
            lean_dec_ref_known(v_x_143_, 1);
            v___x_151_ = lean_apply_2(v_h__2_145_, v_it_150_, lean_box(0));
            return v___x_151_;
        }
        _ => {
            let mut v___x_152_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_145_);
            lean_dec(v_h__1_144_);
            v___x_152_ = lean_apply_1(v_h__3_146_, lean_box(0));
            return v___x_152_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect_0__Std_IterM_toArray_go_match__1_splitter___boxed(
    mut v_00_u03b1_153_: *mut LeanObject,
    mut v_00_u03b2_154_: *mut LeanObject,
    mut v_m_155_: *mut LeanObject,
    mut v_inst_156_: *mut LeanObject,
    mut v_it_157_: *mut LeanObject,
    mut v_motive_158_: *mut LeanObject,
    mut v_x_159_: *mut LeanObject,
    mut v_h__1_160_: *mut LeanObject,
    mut v_h__2_161_: *mut LeanObject,
    mut v_h__3_162_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_163_: *mut LeanObject = core::ptr::null_mut();
    v_res_163_ = l___private_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect_0__Std_IterM_toArray_go_match__1_splitter(v_00_u03b1_153_, v_00_u03b2_154_, v_m_155_, v_inst_156_, v_it_157_, v_motive_158_, v_x_159_, v_h__1_160_, v_h__2_161_, v_h__3_162_);
    lean_dec(v_it_157_);
    lean_dec(v_inst_156_);
    return v_res_163_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect_0__Std_IterM_toArray_go__eq_match__1_splitter___redArg(
    mut v_x_164_: *mut LeanObject,
    mut v_h__1_165_: *mut LeanObject,
    mut v_h__2_166_: *mut LeanObject,
    mut v_h__3_167_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_164_) {
        0 => {
            let mut v_it_168_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_169_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_170_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_167_);
            lean_dec(v_h__2_166_);
            v_it_168_ = lean_ctor_get(v_x_164_, 0);
            lean_inc(v_it_168_);
            v_out_169_ = lean_ctor_get(v_x_164_, 1);
            lean_inc(v_out_169_);
            lean_dec_ref_known(v_x_164_, 2);
            v___x_170_ = lean_apply_2(v_h__1_165_, v_it_168_, v_out_169_);
            return v___x_170_;
        }
        1 => {
            let mut v_it_171_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_172_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_167_);
            lean_dec(v_h__1_165_);
            v_it_171_ = lean_ctor_get(v_x_164_, 0);
            lean_inc(v_it_171_);
            lean_dec_ref_known(v_x_164_, 1);
            v___x_172_ = lean_apply_1(v_h__2_166_, v_it_171_);
            return v___x_172_;
        }
        _ => {
            let mut v___x_173_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_174_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_166_);
            lean_dec(v_h__1_165_);
            v___x_173_ = lean_box(0);
            v___x_174_ = lean_apply_1(v_h__3_167_, v___x_173_);
            return v___x_174_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect_0__Std_IterM_toArray_go__eq_match__1_splitter(
    mut v_00_u03b1_175_: *mut LeanObject,
    mut v_00_u03b2_176_: *mut LeanObject,
    mut v_m_177_: *mut LeanObject,
    mut v_motive_178_: *mut LeanObject,
    mut v_x_179_: *mut LeanObject,
    mut v_h__1_180_: *mut LeanObject,
    mut v_h__2_181_: *mut LeanObject,
    mut v_h__3_182_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_179_) {
        0 => {
            let mut v_it_183_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_184_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_185_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_182_);
            lean_dec(v_h__2_181_);
            v_it_183_ = lean_ctor_get(v_x_179_, 0);
            lean_inc(v_it_183_);
            v_out_184_ = lean_ctor_get(v_x_179_, 1);
            lean_inc(v_out_184_);
            lean_dec_ref_known(v_x_179_, 2);
            v___x_185_ = lean_apply_2(v_h__1_180_, v_it_183_, v_out_184_);
            return v___x_185_;
        }
        1 => {
            let mut v_it_186_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_187_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_182_);
            lean_dec(v_h__1_180_);
            v_it_186_ = lean_ctor_get(v_x_179_, 0);
            lean_inc(v_it_186_);
            lean_dec_ref_known(v_x_179_, 1);
            v___x_187_ = lean_apply_1(v_h__2_181_, v_it_186_);
            return v___x_187_;
        }
        _ => {
            let mut v___x_188_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_189_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_181_);
            lean_dec(v_h__1_180_);
            v___x_188_ = lean_box(0);
            v___x_189_ = lean_apply_1(v_h__3_182_, v___x_188_);
            return v___x_189_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect_0__Std_IterM_toArray__eq__match__step_match__1_splitter___redArg(
    mut v_x_190_: *mut LeanObject,
    mut v_h__1_191_: *mut LeanObject,
    mut v_h__2_192_: *mut LeanObject,
    mut v_h__3_193_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_190_) {
        0 => {
            let mut v_it_194_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_195_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_196_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_193_);
            lean_dec(v_h__2_192_);
            v_it_194_ = lean_ctor_get(v_x_190_, 0);
            lean_inc(v_it_194_);
            v_out_195_ = lean_ctor_get(v_x_190_, 1);
            lean_inc(v_out_195_);
            lean_dec_ref_known(v_x_190_, 2);
            v___x_196_ = lean_apply_2(v_h__1_191_, v_it_194_, v_out_195_);
            return v___x_196_;
        }
        1 => {
            let mut v_it_197_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_198_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_193_);
            lean_dec(v_h__1_191_);
            v_it_197_ = lean_ctor_get(v_x_190_, 0);
            lean_inc(v_it_197_);
            lean_dec_ref_known(v_x_190_, 1);
            v___x_198_ = lean_apply_1(v_h__2_192_, v_it_197_);
            return v___x_198_;
        }
        _ => {
            let mut v___x_199_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_200_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_192_);
            lean_dec(v_h__1_191_);
            v___x_199_ = lean_box(0);
            v___x_200_ = lean_apply_1(v_h__3_193_, v___x_199_);
            return v___x_200_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect_0__Std_IterM_toArray__eq__match__step_match__1_splitter(
    mut v_00_u03b1_201_: *mut LeanObject,
    mut v_00_u03b2_202_: *mut LeanObject,
    mut v_m_203_: *mut LeanObject,
    mut v_motive_204_: *mut LeanObject,
    mut v_x_205_: *mut LeanObject,
    mut v_h__1_206_: *mut LeanObject,
    mut v_h__2_207_: *mut LeanObject,
    mut v_h__3_208_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_205_) {
        0 => {
            let mut v_it_209_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_210_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_211_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_208_);
            lean_dec(v_h__2_207_);
            v_it_209_ = lean_ctor_get(v_x_205_, 0);
            lean_inc(v_it_209_);
            v_out_210_ = lean_ctor_get(v_x_205_, 1);
            lean_inc(v_out_210_);
            lean_dec_ref_known(v_x_205_, 2);
            v___x_211_ = lean_apply_2(v_h__1_206_, v_it_209_, v_out_210_);
            return v___x_211_;
        }
        1 => {
            let mut v_it_212_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_213_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_208_);
            lean_dec(v_h__1_206_);
            v_it_212_ = lean_ctor_get(v_x_205_, 0);
            lean_inc(v_it_212_);
            lean_dec_ref_known(v_x_205_, 1);
            v___x_213_ = lean_apply_1(v_h__2_207_, v_it_212_);
            return v___x_213_;
        }
        _ => {
            let mut v___x_214_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_215_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_207_);
            lean_dec(v_h__1_206_);
            v___x_214_ = lean_box(0);
            v___x_215_ = lean_apply_1(v_h__3_208_, v___x_214_);
            return v___x_215_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect_0__Std_IterM_toListRev_match__1_splitter___redArg(
    mut v_x_216_: *mut LeanObject,
    mut v_h__1_217_: *mut LeanObject,
    mut v_h__2_218_: *mut LeanObject,
    mut v_h__3_219_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_216_) {
        0 => {
            let mut v_it_220_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_221_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_222_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_219_);
            lean_dec(v_h__2_218_);
            v_it_220_ = lean_ctor_get(v_x_216_, 0);
            lean_inc(v_it_220_);
            v_out_221_ = lean_ctor_get(v_x_216_, 1);
            lean_inc(v_out_221_);
            lean_dec_ref_known(v_x_216_, 2);
            v___x_222_ = lean_apply_3(v_h__1_217_, v_it_220_, v_out_221_, lean_box(0));
            return v___x_222_;
        }
        1 => {
            let mut v_it_223_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_224_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_219_);
            lean_dec(v_h__1_217_);
            v_it_223_ = lean_ctor_get(v_x_216_, 0);
            lean_inc(v_it_223_);
            lean_dec_ref_known(v_x_216_, 1);
            v___x_224_ = lean_apply_2(v_h__2_218_, v_it_223_, lean_box(0));
            return v___x_224_;
        }
        _ => {
            let mut v___x_225_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_218_);
            lean_dec(v_h__1_217_);
            v___x_225_ = lean_apply_1(v_h__3_219_, lean_box(0));
            return v___x_225_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect_0__Std_IterM_toListRev_match__1_splitter(
    mut v_00_u03b1_226_: *mut LeanObject,
    mut v_m_227_: *mut LeanObject,
    mut v_00_u03b2_228_: *mut LeanObject,
    mut v_inst_229_: *mut LeanObject,
    mut v_it_230_: *mut LeanObject,
    mut v_motive_231_: *mut LeanObject,
    mut v_x_232_: *mut LeanObject,
    mut v_h__1_233_: *mut LeanObject,
    mut v_h__2_234_: *mut LeanObject,
    mut v_h__3_235_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_232_) {
        0 => {
            let mut v_it_236_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_237_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_238_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_235_);
            lean_dec(v_h__2_234_);
            v_it_236_ = lean_ctor_get(v_x_232_, 0);
            lean_inc(v_it_236_);
            v_out_237_ = lean_ctor_get(v_x_232_, 1);
            lean_inc(v_out_237_);
            lean_dec_ref_known(v_x_232_, 2);
            v___x_238_ = lean_apply_3(v_h__1_233_, v_it_236_, v_out_237_, lean_box(0));
            return v___x_238_;
        }
        1 => {
            let mut v_it_239_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_240_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_235_);
            lean_dec(v_h__1_233_);
            v_it_239_ = lean_ctor_get(v_x_232_, 0);
            lean_inc(v_it_239_);
            lean_dec_ref_known(v_x_232_, 1);
            v___x_240_ = lean_apply_2(v_h__2_234_, v_it_239_, lean_box(0));
            return v___x_240_;
        }
        _ => {
            let mut v___x_241_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_234_);
            lean_dec(v_h__1_233_);
            v___x_241_ = lean_apply_1(v_h__3_235_, lean_box(0));
            return v___x_241_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect_0__Std_IterM_toListRev_match__1_splitter___boxed(
    mut v_00_u03b1_242_: *mut LeanObject,
    mut v_m_243_: *mut LeanObject,
    mut v_00_u03b2_244_: *mut LeanObject,
    mut v_inst_245_: *mut LeanObject,
    mut v_it_246_: *mut LeanObject,
    mut v_motive_247_: *mut LeanObject,
    mut v_x_248_: *mut LeanObject,
    mut v_h__1_249_: *mut LeanObject,
    mut v_h__2_250_: *mut LeanObject,
    mut v_h__3_251_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_252_: *mut LeanObject = core::ptr::null_mut();
    v_res_252_ = l___private_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect_0__Std_IterM_toListRev_match__1_splitter(v_00_u03b1_242_, v_m_243_, v_00_u03b2_244_, v_inst_245_, v_it_246_, v_motive_247_, v_x_248_, v_h__1_249_, v_h__2_250_, v_h__3_251_);
    lean_dec(v_it_246_);
    lean_dec(v_inst_245_);
    return v_res_252_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Collect(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Total(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_WFExtrinsicFix(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Control_Lawful(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Bootstrap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Monadic_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect(
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
pub unsafe fn initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Iterators_Consumers_Monadic_Collect(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers_Monadic_Total(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_WFExtrinsicFix(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Control_Lawful(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Array_Bootstrap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Array_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Monadic_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect(builtin);
}
