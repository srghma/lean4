// Lean compiler output
// Module: Std.Data.Iterators.Lemmas.Combinators.Monadic.FilterMap
// Imports: Init.Data.Iterators.Lemmas.Combinators.Monadic.FilterMap Std.Data.Iterators.Lemmas.Equivalence.StepCongr
use crate::r#gen::Init::Data::Iterators::Lemmas::Combinators::Monadic::FilterMap::{
    initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap,
    runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap,
};
use crate::r#gen::Std::Data::Iterators::Lemmas::Equivalence::StepCongr::{
    initialize_Std_Data_Iterators_Lemmas_Equivalence_StepCongr,
    runtime_initialize_Std_Data_Iterators_Lemmas_Equivalence_StepCongr,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_apply_1, lean_apply_2, lean_apply_3, lean_box,
    lean_ctor_get, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_obj_tag,
};
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_stepAsHetT__filterMapWithPostcondition_match__3_splitter___redArg(
    mut v_x_108_: *mut LeanObject,
    mut v_h__1_109_: *mut LeanObject,
    mut v_h__2_110_: *mut LeanObject,
    mut v_h__3_111_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_108_) {
        0 => {
            let mut v_it_112_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_113_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_114_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_111_);
            lean_dec(v_h__2_110_);
            v_it_112_ = lean_ctor_get(v_x_108_, 0);
            lean_inc(v_it_112_);
            v_out_113_ = lean_ctor_get(v_x_108_, 1);
            lean_inc(v_out_113_);
            lean_dec_ref_known(v_x_108_, 2);
            v___x_114_ = lean_apply_2(v_h__1_109_, v_it_112_, v_out_113_);
            return v___x_114_;
        }
        1 => {
            let mut v_it_115_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_116_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_111_);
            lean_dec(v_h__1_109_);
            v_it_115_ = lean_ctor_get(v_x_108_, 0);
            lean_inc(v_it_115_);
            lean_dec_ref_known(v_x_108_, 1);
            v___x_116_ = lean_apply_1(v_h__2_110_, v_it_115_);
            return v___x_116_;
        }
        _ => {
            let mut v___x_117_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_118_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_110_);
            lean_dec(v_h__1_109_);
            v___x_117_ = lean_box(0);
            v___x_118_ = lean_apply_1(v_h__3_111_, v___x_117_);
            return v___x_118_;
        }
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_stepAsHetT__filterMapWithPostcondition_match__3_splitter(
    mut v_m_119_: *mut LeanObject,
    mut v_00_u03b1_120_: *mut LeanObject,
    mut v_00_u03b2_121_: *mut LeanObject,
    mut v_motive_122_: *mut LeanObject,
    mut v_x_123_: *mut LeanObject,
    mut v_h__1_124_: *mut LeanObject,
    mut v_h__2_125_: *mut LeanObject,
    mut v_h__3_126_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_123_) {
        0 => {
            let mut v_it_127_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_128_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_129_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_126_);
            lean_dec(v_h__2_125_);
            v_it_127_ = lean_ctor_get(v_x_123_, 0);
            lean_inc(v_it_127_);
            v_out_128_ = lean_ctor_get(v_x_123_, 1);
            lean_inc(v_out_128_);
            lean_dec_ref_known(v_x_123_, 2);
            v___x_129_ = lean_apply_2(v_h__1_124_, v_it_127_, v_out_128_);
            return v___x_129_;
        }
        1 => {
            let mut v_it_130_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_131_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_126_);
            lean_dec(v_h__1_124_);
            v_it_130_ = lean_ctor_get(v_x_123_, 0);
            lean_inc(v_it_130_);
            lean_dec_ref_known(v_x_123_, 1);
            v___x_131_ = lean_apply_1(v_h__2_125_, v_it_130_);
            return v___x_131_;
        }
        _ => {
            let mut v___x_132_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_133_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_125_);
            lean_dec(v_h__1_124_);
            v___x_132_ = lean_box(0);
            v___x_133_ = lean_apply_1(v_h__3_126_, v___x_132_);
            return v___x_133_;
        }
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_stepAsHetT__filterMapWithPostcondition_match__1_splitter___redArg(
    mut v_____do__lift_134_: *mut LeanObject,
    mut v_h__1_135_: *mut LeanObject,
    mut v_h__2_136_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_134_) == 0 {
        let mut v___x_137_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_138_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_135_);
        v___x_137_ = lean_box(0);
        v___x_138_ = lean_apply_1(v_h__2_136_, v___x_137_);
        return v___x_138_;
    } else {
        let mut v_val_139_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_140_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_136_);
        v_val_139_ = lean_ctor_get(v_____do__lift_134_, 0);
        lean_inc(v_val_139_);
        lean_dec_ref_known(v_____do__lift_134_, 1);
        v___x_140_ = lean_apply_1(v_h__1_135_, v_val_139_);
        return v___x_140_;
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_stepAsHetT__filterMapWithPostcondition_match__1_splitter(
    mut v_00_u03b3_141_: *mut LeanObject,
    mut v_motive_142_: *mut LeanObject,
    mut v_____do__lift_143_: *mut LeanObject,
    mut v_h__1_144_: *mut LeanObject,
    mut v_h__2_145_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_143_) == 0 {
        let mut v___x_146_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_147_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_144_);
        v___x_146_ = lean_box(0);
        v___x_147_ = lean_apply_1(v_h__2_145_, v___x_146_);
        return v___x_147_;
    } else {
        let mut v_val_148_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_149_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_145_);
        v_val_148_ = lean_ctor_get(v_____do__lift_143_, 0);
        lean_inc(v_val_148_);
        lean_dec_ref_known(v_____do__lift_143_, 1);
        v___x_149_ = lean_apply_1(v_h__1_144_, v_val_148_);
        return v___x_149_;
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__3_splitter___redArg(
    mut v_x_150_: *mut LeanObject,
    mut v_h__1_151_: *mut LeanObject,
    mut v_h__2_152_: *mut LeanObject,
    mut v_h__3_153_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_150_) {
        0 => {
            let mut v_it_154_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_155_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_156_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_153_);
            lean_dec(v_h__2_152_);
            v_it_154_ = lean_ctor_get(v_x_150_, 0);
            lean_inc(v_it_154_);
            v_out_155_ = lean_ctor_get(v_x_150_, 1);
            lean_inc(v_out_155_);
            lean_dec_ref_known(v_x_150_, 2);
            v___x_156_ = lean_apply_3(v_h__1_151_, v_it_154_, v_out_155_, lean_box(0));
            return v___x_156_;
        }
        1 => {
            let mut v_it_157_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_158_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_153_);
            lean_dec(v_h__1_151_);
            v_it_157_ = lean_ctor_get(v_x_150_, 0);
            lean_inc(v_it_157_);
            lean_dec_ref_known(v_x_150_, 1);
            v___x_158_ = lean_apply_2(v_h__2_152_, v_it_157_, lean_box(0));
            return v___x_158_;
        }
        _ => {
            let mut v___x_159_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_152_);
            lean_dec(v_h__1_151_);
            v___x_159_ = lean_apply_1(v_h__3_153_, lean_box(0));
            return v___x_159_;
        }
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__3_splitter(
    mut v_00_u03b1_160_: *mut LeanObject,
    mut v_00_u03b2_161_: *mut LeanObject,
    mut v_m_162_: *mut LeanObject,
    mut v_inst_163_: *mut LeanObject,
    mut v_it_164_: *mut LeanObject,
    mut v_motive_165_: *mut LeanObject,
    mut v_x_166_: *mut LeanObject,
    mut v_h__1_167_: *mut LeanObject,
    mut v_h__2_168_: *mut LeanObject,
    mut v_h__3_169_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_166_) {
        0 => {
            let mut v_it_170_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_171_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_172_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_169_);
            lean_dec(v_h__2_168_);
            v_it_170_ = lean_ctor_get(v_x_166_, 0);
            lean_inc(v_it_170_);
            v_out_171_ = lean_ctor_get(v_x_166_, 1);
            lean_inc(v_out_171_);
            lean_dec_ref_known(v_x_166_, 2);
            v___x_172_ = lean_apply_3(v_h__1_167_, v_it_170_, v_out_171_, lean_box(0));
            return v___x_172_;
        }
        1 => {
            let mut v_it_173_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_174_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_169_);
            lean_dec(v_h__1_167_);
            v_it_173_ = lean_ctor_get(v_x_166_, 0);
            lean_inc(v_it_173_);
            lean_dec_ref_known(v_x_166_, 1);
            v___x_174_ = lean_apply_2(v_h__2_168_, v_it_173_, lean_box(0));
            return v___x_174_;
        }
        _ => {
            let mut v___x_175_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_168_);
            lean_dec(v_h__1_167_);
            v___x_175_ = lean_apply_1(v_h__3_169_, lean_box(0));
            return v___x_175_;
        }
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__3_splitter___boxed(
    mut v_00_u03b1_176_: *mut LeanObject,
    mut v_00_u03b2_177_: *mut LeanObject,
    mut v_m_178_: *mut LeanObject,
    mut v_inst_179_: *mut LeanObject,
    mut v_it_180_: *mut LeanObject,
    mut v_motive_181_: *mut LeanObject,
    mut v_x_182_: *mut LeanObject,
    mut v_h__1_183_: *mut LeanObject,
    mut v_h__2_184_: *mut LeanObject,
    mut v_h__3_185_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_186_: *mut LeanObject = core::ptr::null_mut();
    v_res_186_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__3_splitter(v_00_u03b1_176_, v_00_u03b2_177_, v_m_178_, v_inst_179_, v_it_180_, v_motive_181_, v_x_182_, v_h__1_183_, v_h__2_184_, v_h__3_185_);
    lean_dec(v_it_180_);
    lean_dec(v_inst_179_);
    return v_res_186_;
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__1_splitter___redArg(
    mut v_____do__lift_187_: *mut LeanObject,
    mut v_h__1_188_: *mut LeanObject,
    mut v_h__2_189_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_187_) == 0 {
        let mut v___x_190_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_189_);
        v___x_190_ = lean_apply_1(v_h__1_188_, lean_box(0));
        return v___x_190_;
    } else {
        let mut v_val_191_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_192_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_188_);
        v_val_191_ = lean_ctor_get(v_____do__lift_187_, 0);
        lean_inc(v_val_191_);
        lean_dec_ref_known(v_____do__lift_187_, 1);
        v___x_192_ = lean_apply_2(v_h__2_189_, v_val_191_, lean_box(0));
        return v___x_192_;
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__1_splitter(
    mut v_00_u03b2_193_: *mut LeanObject,
    mut v_00_u03b2_x27_194_: *mut LeanObject,
    mut v_n_195_: *mut LeanObject,
    mut v_f_196_: *mut LeanObject,
    mut v_out_197_: *mut LeanObject,
    mut v_motive_198_: *mut LeanObject,
    mut v_____do__lift_199_: *mut LeanObject,
    mut v_h__1_200_: *mut LeanObject,
    mut v_h__2_201_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_199_) == 0 {
        let mut v___x_202_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_201_);
        v___x_202_ = lean_apply_1(v_h__1_200_, lean_box(0));
        return v___x_202_;
    } else {
        let mut v_val_203_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_204_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_200_);
        v_val_203_ = lean_ctor_get(v_____do__lift_199_, 0);
        lean_inc(v_val_203_);
        lean_dec_ref_known(v_____do__lift_199_, 1);
        v___x_204_ = lean_apply_2(v_h__2_201_, v_val_203_, lean_box(0));
        return v___x_204_;
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__1_splitter___boxed(
    mut v_00_u03b2_205_: *mut LeanObject,
    mut v_00_u03b2_x27_206_: *mut LeanObject,
    mut v_n_207_: *mut LeanObject,
    mut v_f_208_: *mut LeanObject,
    mut v_out_209_: *mut LeanObject,
    mut v_motive_210_: *mut LeanObject,
    mut v_____do__lift_211_: *mut LeanObject,
    mut v_h__1_212_: *mut LeanObject,
    mut v_h__2_213_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_214_: *mut LeanObject = core::ptr::null_mut();
    v_res_214_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__1_splitter(v_00_u03b2_205_, v_00_u03b2_x27_206_, v_n_207_, v_f_208_, v_out_209_, v_motive_210_, v_____do__lift_211_, v_h__1_212_, v_h__2_213_);
    lean_dec(v_out_209_);
    lean_dec(v_f_208_);
    return v_res_214_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Lemmas_Equivalence_StepCongr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap(
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
pub unsafe fn initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Data_Iterators_Lemmas_Equivalence_StepCongr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap(builtin);
}
