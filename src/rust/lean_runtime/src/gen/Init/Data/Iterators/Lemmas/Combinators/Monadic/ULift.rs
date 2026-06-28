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
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_apply_1, lean_apply_2, lean_apply_3, lean_box,
    lean_ctor_get, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_obj_tag,
};
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_ULift_0__Std_IterM_step__uLift_match__1_splitter___redArg(
    mut v_x_116_: *mut LeanObject,
    mut v_h__1_117_: *mut LeanObject,
    mut v_h__2_118_: *mut LeanObject,
    mut v_h__3_119_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_116_) {
        0 => {
            let mut v_it_120_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_121_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_122_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_119_);
            lean_dec(v_h__2_118_);
            v_it_120_ = lean_ctor_get(v_x_116_, 0);
            lean_inc(v_it_120_);
            v_out_121_ = lean_ctor_get(v_x_116_, 1);
            lean_inc(v_out_121_);
            lean_dec_ref_known(v_x_116_, 2);
            v___x_122_ = lean_apply_3(v_h__1_117_, v_it_120_, v_out_121_, lean_box(0));
            return v___x_122_;
        }
        1 => {
            let mut v_it_123_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_124_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_119_);
            lean_dec(v_h__1_117_);
            v_it_123_ = lean_ctor_get(v_x_116_, 0);
            lean_inc(v_it_123_);
            lean_dec_ref_known(v_x_116_, 1);
            v___x_124_ = lean_apply_2(v_h__2_118_, v_it_123_, lean_box(0));
            return v___x_124_;
        }
        _ => {
            let mut v___x_125_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_118_);
            lean_dec(v_h__1_117_);
            v___x_125_ = lean_apply_1(v_h__3_119_, lean_box(0));
            return v___x_125_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_ULift_0__Std_IterM_step__uLift_match__1_splitter(
    mut v_00_u03b1_126_: *mut LeanObject,
    mut v_m_127_: *mut LeanObject,
    mut v_00_u03b2_128_: *mut LeanObject,
    mut v_inst_129_: *mut LeanObject,
    mut v_it_130_: *mut LeanObject,
    mut v_motive_131_: *mut LeanObject,
    mut v_x_132_: *mut LeanObject,
    mut v_h__1_133_: *mut LeanObject,
    mut v_h__2_134_: *mut LeanObject,
    mut v_h__3_135_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_132_) {
        0 => {
            let mut v_it_136_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_137_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_138_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_135_);
            lean_dec(v_h__2_134_);
            v_it_136_ = lean_ctor_get(v_x_132_, 0);
            lean_inc(v_it_136_);
            v_out_137_ = lean_ctor_get(v_x_132_, 1);
            lean_inc(v_out_137_);
            lean_dec_ref_known(v_x_132_, 2);
            v___x_138_ = lean_apply_3(v_h__1_133_, v_it_136_, v_out_137_, lean_box(0));
            return v___x_138_;
        }
        1 => {
            let mut v_it_139_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_140_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_135_);
            lean_dec(v_h__1_133_);
            v_it_139_ = lean_ctor_get(v_x_132_, 0);
            lean_inc(v_it_139_);
            lean_dec_ref_known(v_x_132_, 1);
            v___x_140_ = lean_apply_2(v_h__2_134_, v_it_139_, lean_box(0));
            return v___x_140_;
        }
        _ => {
            let mut v___x_141_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_134_);
            lean_dec(v_h__1_133_);
            v___x_141_ = lean_apply_1(v_h__3_135_, lean_box(0));
            return v___x_141_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_ULift_0__Std_IterM_step__uLift_match__1_splitter___boxed(
    mut v_00_u03b1_142_: *mut LeanObject,
    mut v_m_143_: *mut LeanObject,
    mut v_00_u03b2_144_: *mut LeanObject,
    mut v_inst_145_: *mut LeanObject,
    mut v_it_146_: *mut LeanObject,
    mut v_motive_147_: *mut LeanObject,
    mut v_x_148_: *mut LeanObject,
    mut v_h__1_149_: *mut LeanObject,
    mut v_h__2_150_: *mut LeanObject,
    mut v_h__3_151_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_152_: *mut LeanObject = core::ptr::null_mut();
    v_res_152_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_ULift_0__Std_IterM_step__uLift_match__1_splitter(v_00_u03b1_142_, v_m_143_, v_00_u03b2_144_, v_inst_145_, v_it_146_, v_motive_147_, v_x_148_, v_h__1_149_, v_h__2_150_, v_h__3_151_);
    lean_dec(v_it_146_);
    lean_dec(v_inst_145_);
    return v_res_152_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_ULift_0__Std_Iterators_Types_ULiftIterator_Monadic_modifyStep_match__1_splitter___redArg(
    mut v_step_153_: *mut LeanObject,
    mut v_h__1_154_: *mut LeanObject,
    mut v_h__2_155_: *mut LeanObject,
    mut v_h__3_156_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_step_153_) {
        0 => {
            let mut v_it_157_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_158_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_159_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_156_);
            lean_dec(v_h__2_155_);
            v_it_157_ = lean_ctor_get(v_step_153_, 0);
            lean_inc(v_it_157_);
            v_out_158_ = lean_ctor_get(v_step_153_, 1);
            lean_inc(v_out_158_);
            lean_dec_ref_known(v_step_153_, 2);
            v___x_159_ = lean_apply_2(v_h__1_154_, v_it_157_, v_out_158_);
            return v___x_159_;
        }
        1 => {
            let mut v_it_160_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_161_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_156_);
            lean_dec(v_h__1_154_);
            v_it_160_ = lean_ctor_get(v_step_153_, 0);
            lean_inc(v_it_160_);
            lean_dec_ref_known(v_step_153_, 1);
            v___x_161_ = lean_apply_1(v_h__2_155_, v_it_160_);
            return v___x_161_;
        }
        _ => {
            let mut v___x_162_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_163_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_155_);
            lean_dec(v_h__1_154_);
            v___x_162_ = lean_box(0);
            v___x_163_ = lean_apply_1(v_h__3_156_, v___x_162_);
            return v___x_163_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_ULift_0__Std_Iterators_Types_ULiftIterator_Monadic_modifyStep_match__1_splitter(
    mut v_00_u03b1_164_: *mut LeanObject,
    mut v_m_165_: *mut LeanObject,
    mut v_00_u03b2_166_: *mut LeanObject,
    mut v_motive_167_: *mut LeanObject,
    mut v_step_168_: *mut LeanObject,
    mut v_h__1_169_: *mut LeanObject,
    mut v_h__2_170_: *mut LeanObject,
    mut v_h__3_171_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_step_168_) {
        0 => {
            let mut v_it_172_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_173_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_174_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_171_);
            lean_dec(v_h__2_170_);
            v_it_172_ = lean_ctor_get(v_step_168_, 0);
            lean_inc(v_it_172_);
            v_out_173_ = lean_ctor_get(v_step_168_, 1);
            lean_inc(v_out_173_);
            lean_dec_ref_known(v_step_168_, 2);
            v___x_174_ = lean_apply_2(v_h__1_169_, v_it_172_, v_out_173_);
            return v___x_174_;
        }
        1 => {
            let mut v_it_175_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_176_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_171_);
            lean_dec(v_h__1_169_);
            v_it_175_ = lean_ctor_get(v_step_168_, 0);
            lean_inc(v_it_175_);
            lean_dec_ref_known(v_step_168_, 1);
            v___x_176_ = lean_apply_1(v_h__2_170_, v_it_175_);
            return v___x_176_;
        }
        _ => {
            let mut v___x_177_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_178_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_170_);
            lean_dec(v_h__1_169_);
            v___x_177_ = lean_box(0);
            v___x_178_ = lean_apply_1(v_h__3_171_, v___x_177_);
            return v___x_178_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_ULift_0__Std_IterM_toArray__eq__match__step_match__1_splitter___redArg(
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
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_ULift_0__Std_IterM_toArray__eq__match__step_match__1_splitter(
    mut v_00_u03b1_190_: *mut LeanObject,
    mut v_00_u03b2_191_: *mut LeanObject,
    mut v_m_192_: *mut LeanObject,
    mut v_motive_193_: *mut LeanObject,
    mut v_x_194_: *mut LeanObject,
    mut v_h__1_195_: *mut LeanObject,
    mut v_h__2_196_: *mut LeanObject,
    mut v_h__3_197_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_194_) {
        0 => {
            let mut v_it_198_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_199_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_200_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_197_);
            lean_dec(v_h__2_196_);
            v_it_198_ = lean_ctor_get(v_x_194_, 0);
            lean_inc(v_it_198_);
            v_out_199_ = lean_ctor_get(v_x_194_, 1);
            lean_inc(v_out_199_);
            lean_dec_ref_known(v_x_194_, 2);
            v___x_200_ = lean_apply_2(v_h__1_195_, v_it_198_, v_out_199_);
            return v___x_200_;
        }
        1 => {
            let mut v_it_201_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_202_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_197_);
            lean_dec(v_h__1_195_);
            v_it_201_ = lean_ctor_get(v_x_194_, 0);
            lean_inc(v_it_201_);
            lean_dec_ref_known(v_x_194_, 1);
            v___x_202_ = lean_apply_1(v_h__2_196_, v_it_201_);
            return v___x_202_;
        }
        _ => {
            let mut v___x_203_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_204_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_196_);
            lean_dec(v_h__1_195_);
            v___x_203_ = lean_box(0);
            v___x_204_ = lean_apply_1(v_h__3_197_, v___x_203_);
            return v___x_204_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_ULift_0__Std_IterM_length__eq__match__step_match__1_splitter___redArg(
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
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_ULift_0__Std_IterM_length__eq__match__step_match__1_splitter(
    mut v_00_u03b1_216_: *mut LeanObject,
    mut v_00_u03b2_217_: *mut LeanObject,
    mut v_m_218_: *mut LeanObject,
    mut v_motive_219_: *mut LeanObject,
    mut v_x_220_: *mut LeanObject,
    mut v_h__1_221_: *mut LeanObject,
    mut v_h__2_222_: *mut LeanObject,
    mut v_h__3_223_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_220_) {
        0 => {
            let mut v_it_224_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_225_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_226_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_223_);
            lean_dec(v_h__2_222_);
            v_it_224_ = lean_ctor_get(v_x_220_, 0);
            lean_inc(v_it_224_);
            v_out_225_ = lean_ctor_get(v_x_220_, 1);
            lean_inc(v_out_225_);
            lean_dec_ref_known(v_x_220_, 2);
            v___x_226_ = lean_apply_2(v_h__1_221_, v_it_224_, v_out_225_);
            return v___x_226_;
        }
        1 => {
            let mut v_it_227_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_228_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_223_);
            lean_dec(v_h__1_221_);
            v_it_227_ = lean_ctor_get(v_x_220_, 0);
            lean_inc(v_it_227_);
            lean_dec_ref_known(v_x_220_, 1);
            v___x_228_ = lean_apply_1(v_h__2_222_, v_it_227_);
            return v___x_228_;
        }
        _ => {
            let mut v___x_229_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_230_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_222_);
            lean_dec(v_h__1_221_);
            v___x_229_ = lean_box(0);
            v___x_230_ = lean_apply_1(v_h__3_223_, v___x_229_);
            return v___x_230_;
        }
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_ULift(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Iterators_Combinators_Monadic_ULift(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop(builtin);
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
pub unsafe fn meta_initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_ULift(
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
pub unsafe fn initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_ULift(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Iterators_Combinators_Monadic_ULift(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Array_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Monadic_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_ULift(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_ULift(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_ULift(builtin);
}
