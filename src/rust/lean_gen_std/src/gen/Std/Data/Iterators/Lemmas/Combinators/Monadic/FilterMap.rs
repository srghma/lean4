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
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_stepAsHetT__filterMapWithPostcondition_match__3_splitter___redArg(
    mut v_x_108_: *mut crate::leanh::LeanObject,
    mut v_h__1_109_: *mut crate::leanh::LeanObject,
    mut v_h__2_110_: *mut crate::leanh::LeanObject,
    mut v_h__3_111_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_108_) {
        0 => {
            let mut v_it_112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_111_);
            crate::leanh::lean_dec(v_h__2_110_);
            v_it_112_ = crate::leanh::lean_ctor_get(v_x_108_, 0);
            crate::leanh::lean_inc(v_it_112_);
            v_out_113_ = crate::leanh::lean_ctor_get(v_x_108_, 1);
            crate::leanh::lean_inc(v_out_113_);
            crate::leanh::lean_dec_ref_known(v_x_108_, 2);
            v___x_114_ = crate::leanh::lean_apply_2(v_h__1_109_, v_it_112_, v_out_113_);
            return v___x_114_;
        }
        1 => {
            let mut v_it_115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_111_);
            crate::leanh::lean_dec(v_h__1_109_);
            v_it_115_ = crate::leanh::lean_ctor_get(v_x_108_, 0);
            crate::leanh::lean_inc(v_it_115_);
            crate::leanh::lean_dec_ref_known(v_x_108_, 1);
            v___x_116_ = crate::leanh::lean_apply_1(v_h__2_110_, v_it_115_);
            return v___x_116_;
        }
        _ => {
            let mut v___x_117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_110_);
            crate::leanh::lean_dec(v_h__1_109_);
            v___x_117_ = crate::leanh::lean_box(0);
            v___x_118_ = crate::leanh::lean_apply_1(v_h__3_111_, v___x_117_);
            return v___x_118_;
        }
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_stepAsHetT__filterMapWithPostcondition_match__3_splitter(
    mut v_m_119_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_120_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_121_: *mut crate::leanh::LeanObject,
    mut v_motive_122_: *mut crate::leanh::LeanObject,
    mut v_x_123_: *mut crate::leanh::LeanObject,
    mut v_h__1_124_: *mut crate::leanh::LeanObject,
    mut v_h__2_125_: *mut crate::leanh::LeanObject,
    mut v_h__3_126_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_123_) {
        0 => {
            let mut v_it_127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_126_);
            crate::leanh::lean_dec(v_h__2_125_);
            v_it_127_ = crate::leanh::lean_ctor_get(v_x_123_, 0);
            crate::leanh::lean_inc(v_it_127_);
            v_out_128_ = crate::leanh::lean_ctor_get(v_x_123_, 1);
            crate::leanh::lean_inc(v_out_128_);
            crate::leanh::lean_dec_ref_known(v_x_123_, 2);
            v___x_129_ = crate::leanh::lean_apply_2(v_h__1_124_, v_it_127_, v_out_128_);
            return v___x_129_;
        }
        1 => {
            let mut v_it_130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_126_);
            crate::leanh::lean_dec(v_h__1_124_);
            v_it_130_ = crate::leanh::lean_ctor_get(v_x_123_, 0);
            crate::leanh::lean_inc(v_it_130_);
            crate::leanh::lean_dec_ref_known(v_x_123_, 1);
            v___x_131_ = crate::leanh::lean_apply_1(v_h__2_125_, v_it_130_);
            return v___x_131_;
        }
        _ => {
            let mut v___x_132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_125_);
            crate::leanh::lean_dec(v_h__1_124_);
            v___x_132_ = crate::leanh::lean_box(0);
            v___x_133_ = crate::leanh::lean_apply_1(v_h__3_126_, v___x_132_);
            return v___x_133_;
        }
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_stepAsHetT__filterMapWithPostcondition_match__1_splitter___redArg(
    mut v_____do__lift_134_: *mut crate::leanh::LeanObject,
    mut v_h__1_135_: *mut crate::leanh::LeanObject,
    mut v_h__2_136_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_134_) == 0 {
        let mut v___x_137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_135_);
        v___x_137_ = crate::leanh::lean_box(0);
        v___x_138_ = crate::leanh::lean_apply_1(v_h__2_136_, v___x_137_);
        return v___x_138_;
    } else {
        let mut v_val_139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_136_);
        v_val_139_ = crate::leanh::lean_ctor_get(v_____do__lift_134_, 0);
        crate::leanh::lean_inc(v_val_139_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_134_, 1);
        v___x_140_ = crate::leanh::lean_apply_1(v_h__1_135_, v_val_139_);
        return v___x_140_;
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_stepAsHetT__filterMapWithPostcondition_match__1_splitter(
    mut v_00_u03b3_141_: *mut crate::leanh::LeanObject,
    mut v_motive_142_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_143_: *mut crate::leanh::LeanObject,
    mut v_h__1_144_: *mut crate::leanh::LeanObject,
    mut v_h__2_145_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_143_) == 0 {
        let mut v___x_146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_144_);
        v___x_146_ = crate::leanh::lean_box(0);
        v___x_147_ = crate::leanh::lean_apply_1(v_h__2_145_, v___x_146_);
        return v___x_147_;
    } else {
        let mut v_val_148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_145_);
        v_val_148_ = crate::leanh::lean_ctor_get(v_____do__lift_143_, 0);
        crate::leanh::lean_inc(v_val_148_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_143_, 1);
        v___x_149_ = crate::leanh::lean_apply_1(v_h__1_144_, v_val_148_);
        return v___x_149_;
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__3_splitter___redArg(
    mut v_x_150_: *mut crate::leanh::LeanObject,
    mut v_h__1_151_: *mut crate::leanh::LeanObject,
    mut v_h__2_152_: *mut crate::leanh::LeanObject,
    mut v_h__3_153_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_150_) {
        0 => {
            let mut v_it_154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_153_);
            crate::leanh::lean_dec(v_h__2_152_);
            v_it_154_ = crate::leanh::lean_ctor_get(v_x_150_, 0);
            crate::leanh::lean_inc(v_it_154_);
            v_out_155_ = crate::leanh::lean_ctor_get(v_x_150_, 1);
            crate::leanh::lean_inc(v_out_155_);
            crate::leanh::lean_dec_ref_known(v_x_150_, 2);
            v___x_156_ = crate::leanh::lean_apply_3(
                v_h__1_151_,
                v_it_154_,
                v_out_155_,
                crate::leanh::lean_box(0),
            );
            return v___x_156_;
        }
        1 => {
            let mut v_it_157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_153_);
            crate::leanh::lean_dec(v_h__1_151_);
            v_it_157_ = crate::leanh::lean_ctor_get(v_x_150_, 0);
            crate::leanh::lean_inc(v_it_157_);
            crate::leanh::lean_dec_ref_known(v_x_150_, 1);
            v___x_158_ =
                crate::leanh::lean_apply_2(v_h__2_152_, v_it_157_, crate::leanh::lean_box(0));
            return v___x_158_;
        }
        _ => {
            let mut v___x_159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_152_);
            crate::leanh::lean_dec(v_h__1_151_);
            v___x_159_ = crate::leanh::lean_apply_1(v_h__3_153_, crate::leanh::lean_box(0));
            return v___x_159_;
        }
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__3_splitter(
    mut v_00_u03b1_160_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_161_: *mut crate::leanh::LeanObject,
    mut v_m_162_: *mut crate::leanh::LeanObject,
    mut v_inst_163_: *mut crate::leanh::LeanObject,
    mut v_it_164_: *mut crate::leanh::LeanObject,
    mut v_motive_165_: *mut crate::leanh::LeanObject,
    mut v_x_166_: *mut crate::leanh::LeanObject,
    mut v_h__1_167_: *mut crate::leanh::LeanObject,
    mut v_h__2_168_: *mut crate::leanh::LeanObject,
    mut v_h__3_169_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_166_) {
        0 => {
            let mut v_it_170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_169_);
            crate::leanh::lean_dec(v_h__2_168_);
            v_it_170_ = crate::leanh::lean_ctor_get(v_x_166_, 0);
            crate::leanh::lean_inc(v_it_170_);
            v_out_171_ = crate::leanh::lean_ctor_get(v_x_166_, 1);
            crate::leanh::lean_inc(v_out_171_);
            crate::leanh::lean_dec_ref_known(v_x_166_, 2);
            v___x_172_ = crate::leanh::lean_apply_3(
                v_h__1_167_,
                v_it_170_,
                v_out_171_,
                crate::leanh::lean_box(0),
            );
            return v___x_172_;
        }
        1 => {
            let mut v_it_173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_169_);
            crate::leanh::lean_dec(v_h__1_167_);
            v_it_173_ = crate::leanh::lean_ctor_get(v_x_166_, 0);
            crate::leanh::lean_inc(v_it_173_);
            crate::leanh::lean_dec_ref_known(v_x_166_, 1);
            v___x_174_ =
                crate::leanh::lean_apply_2(v_h__2_168_, v_it_173_, crate::leanh::lean_box(0));
            return v___x_174_;
        }
        _ => {
            let mut v___x_175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_168_);
            crate::leanh::lean_dec(v_h__1_167_);
            v___x_175_ = crate::leanh::lean_apply_1(v_h__3_169_, crate::leanh::lean_box(0));
            return v___x_175_;
        }
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__3_splitter___boxed(
    mut v_00_u03b1_176_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_177_: *mut crate::leanh::LeanObject,
    mut v_m_178_: *mut crate::leanh::LeanObject,
    mut v_inst_179_: *mut crate::leanh::LeanObject,
    mut v_it_180_: *mut crate::leanh::LeanObject,
    mut v_motive_181_: *mut crate::leanh::LeanObject,
    mut v_x_182_: *mut crate::leanh::LeanObject,
    mut v_h__1_183_: *mut crate::leanh::LeanObject,
    mut v_h__2_184_: *mut crate::leanh::LeanObject,
    mut v_h__3_185_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_186_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__3_splitter(v_00_u03b1_176_, v_00_u03b2_177_, v_m_178_, v_inst_179_, v_it_180_, v_motive_181_, v_x_182_, v_h__1_183_, v_h__2_184_, v_h__3_185_);
    crate::leanh::lean_dec(v_it_180_);
    crate::leanh::lean_dec(v_inst_179_);
    return v_res_186_;
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__1_splitter___redArg(
    mut v_____do__lift_187_: *mut crate::leanh::LeanObject,
    mut v_h__1_188_: *mut crate::leanh::LeanObject,
    mut v_h__2_189_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_187_) == 0 {
        let mut v___x_190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_189_);
        v___x_190_ = crate::leanh::lean_apply_1(v_h__1_188_, crate::leanh::lean_box(0));
        return v___x_190_;
    } else {
        let mut v_val_191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_188_);
        v_val_191_ = crate::leanh::lean_ctor_get(v_____do__lift_187_, 0);
        crate::leanh::lean_inc(v_val_191_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_187_, 1);
        v___x_192_ = crate::leanh::lean_apply_2(v_h__2_189_, v_val_191_, crate::leanh::lean_box(0));
        return v___x_192_;
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__1_splitter(
    mut v_00_u03b2_193_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_x27_194_: *mut crate::leanh::LeanObject,
    mut v_n_195_: *mut crate::leanh::LeanObject,
    mut v_f_196_: *mut crate::leanh::LeanObject,
    mut v_out_197_: *mut crate::leanh::LeanObject,
    mut v_motive_198_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_199_: *mut crate::leanh::LeanObject,
    mut v_h__1_200_: *mut crate::leanh::LeanObject,
    mut v_h__2_201_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_199_) == 0 {
        let mut v___x_202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_201_);
        v___x_202_ = crate::leanh::lean_apply_1(v_h__1_200_, crate::leanh::lean_box(0));
        return v___x_202_;
    } else {
        let mut v_val_203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_200_);
        v_val_203_ = crate::leanh::lean_ctor_get(v_____do__lift_199_, 0);
        crate::leanh::lean_inc(v_val_203_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_199_, 1);
        v___x_204_ = crate::leanh::lean_apply_2(v_h__2_201_, v_val_203_, crate::leanh::lean_box(0));
        return v___x_204_;
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__1_splitter___boxed(
    mut v_00_u03b2_205_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_x27_206_: *mut crate::leanh::LeanObject,
    mut v_n_207_: *mut crate::leanh::LeanObject,
    mut v_f_208_: *mut crate::leanh::LeanObject,
    mut v_out_209_: *mut crate::leanh::LeanObject,
    mut v_motive_210_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_211_: *mut crate::leanh::LeanObject,
    mut v_h__1_212_: *mut crate::leanh::LeanObject,
    mut v_h__2_213_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_214_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__1_splitter(v_00_u03b2_205_, v_00_u03b2_x27_206_, v_n_207_, v_f_208_, v_out_209_, v_motive_210_, v_____do__lift_211_, v_h__1_212_, v_h__2_213_);
    crate::leanh::lean_dec(v_out_209_);
    crate::leanh::lean_dec(v_f_208_);
    return v_res_214_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Lemmas_Equivalence_StepCongr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap(
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
pub unsafe fn initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Data_Iterators_Lemmas_Equivalence_StepCongr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap(builtin);
}
