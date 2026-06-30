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
    mut v_x_108_: *mut leanh::LeanObject,
    mut v_h__1_109_: *mut leanh::LeanObject,
    mut v_h__2_110_: *mut leanh::LeanObject,
    mut v_h__3_111_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_108_) {
        0 => {
            let mut v_it_112_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_113_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_114_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_111_);
            leanh::lean_dec(v_h__2_110_);
            v_it_112_ = leanh::lean_ctor_get(v_x_108_, 0);
            leanh::lean_inc(v_it_112_);
            v_out_113_ = leanh::lean_ctor_get(v_x_108_, 1);
            leanh::lean_inc(v_out_113_);
            leanh::lean_dec_ref_known(v_x_108_, 2);
            v___x_114_ = leanh::lean_apply_2(v_h__1_109_, v_it_112_, v_out_113_);
            return v___x_114_;
        }
        1 => {
            let mut v_it_115_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_116_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_111_);
            leanh::lean_dec(v_h__1_109_);
            v_it_115_ = leanh::lean_ctor_get(v_x_108_, 0);
            leanh::lean_inc(v_it_115_);
            leanh::lean_dec_ref_known(v_x_108_, 1);
            v___x_116_ = leanh::lean_apply_1(v_h__2_110_, v_it_115_);
            return v___x_116_;
        }
        _ => {
            let mut v___x_117_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_118_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_110_);
            leanh::lean_dec(v_h__1_109_);
            v___x_117_ = leanh::lean_box(0);
            v___x_118_ = leanh::lean_apply_1(v_h__3_111_, v___x_117_);
            return v___x_118_;
        }
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_stepAsHetT__filterMapWithPostcondition_match__3_splitter(
    mut v_m_119_: *mut leanh::LeanObject,
    mut v_00_u03b1_120_: *mut leanh::LeanObject,
    mut v_00_u03b2_121_: *mut leanh::LeanObject,
    mut v_motive_122_: *mut leanh::LeanObject,
    mut v_x_123_: *mut leanh::LeanObject,
    mut v_h__1_124_: *mut leanh::LeanObject,
    mut v_h__2_125_: *mut leanh::LeanObject,
    mut v_h__3_126_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_123_) {
        0 => {
            let mut v_it_127_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_128_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_129_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_126_);
            leanh::lean_dec(v_h__2_125_);
            v_it_127_ = leanh::lean_ctor_get(v_x_123_, 0);
            leanh::lean_inc(v_it_127_);
            v_out_128_ = leanh::lean_ctor_get(v_x_123_, 1);
            leanh::lean_inc(v_out_128_);
            leanh::lean_dec_ref_known(v_x_123_, 2);
            v___x_129_ = leanh::lean_apply_2(v_h__1_124_, v_it_127_, v_out_128_);
            return v___x_129_;
        }
        1 => {
            let mut v_it_130_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_131_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_126_);
            leanh::lean_dec(v_h__1_124_);
            v_it_130_ = leanh::lean_ctor_get(v_x_123_, 0);
            leanh::lean_inc(v_it_130_);
            leanh::lean_dec_ref_known(v_x_123_, 1);
            v___x_131_ = leanh::lean_apply_1(v_h__2_125_, v_it_130_);
            return v___x_131_;
        }
        _ => {
            let mut v___x_132_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_133_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_125_);
            leanh::lean_dec(v_h__1_124_);
            v___x_132_ = leanh::lean_box(0);
            v___x_133_ = leanh::lean_apply_1(v_h__3_126_, v___x_132_);
            return v___x_133_;
        }
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_stepAsHetT__filterMapWithPostcondition_match__1_splitter___redArg(
    mut v_____do__lift_134_: *mut leanh::LeanObject,
    mut v_h__1_135_: *mut leanh::LeanObject,
    mut v_h__2_136_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_134_) == 0 {
        let mut v___x_137_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_138_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_135_);
        v___x_137_ = leanh::lean_box(0);
        v___x_138_ = leanh::lean_apply_1(v_h__2_136_, v___x_137_);
        return v___x_138_;
    } else {
        let mut v_val_139_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_140_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_136_);
        v_val_139_ = leanh::lean_ctor_get(v_____do__lift_134_, 0);
        leanh::lean_inc(v_val_139_);
        leanh::lean_dec_ref_known(v_____do__lift_134_, 1);
        v___x_140_ = leanh::lean_apply_1(v_h__1_135_, v_val_139_);
        return v___x_140_;
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_stepAsHetT__filterMapWithPostcondition_match__1_splitter(
    mut v_00_u03b3_141_: *mut leanh::LeanObject,
    mut v_motive_142_: *mut leanh::LeanObject,
    mut v_____do__lift_143_: *mut leanh::LeanObject,
    mut v_h__1_144_: *mut leanh::LeanObject,
    mut v_h__2_145_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_143_) == 0 {
        let mut v___x_146_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_147_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_144_);
        v___x_146_ = leanh::lean_box(0);
        v___x_147_ = leanh::lean_apply_1(v_h__2_145_, v___x_146_);
        return v___x_147_;
    } else {
        let mut v_val_148_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_149_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_145_);
        v_val_148_ = leanh::lean_ctor_get(v_____do__lift_143_, 0);
        leanh::lean_inc(v_val_148_);
        leanh::lean_dec_ref_known(v_____do__lift_143_, 1);
        v___x_149_ = leanh::lean_apply_1(v_h__1_144_, v_val_148_);
        return v___x_149_;
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__3_splitter___redArg(
    mut v_x_150_: *mut leanh::LeanObject,
    mut v_h__1_151_: *mut leanh::LeanObject,
    mut v_h__2_152_: *mut leanh::LeanObject,
    mut v_h__3_153_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_150_) {
        0 => {
            let mut v_it_154_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_155_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_156_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_153_);
            leanh::lean_dec(v_h__2_152_);
            v_it_154_ = leanh::lean_ctor_get(v_x_150_, 0);
            leanh::lean_inc(v_it_154_);
            v_out_155_ = leanh::lean_ctor_get(v_x_150_, 1);
            leanh::lean_inc(v_out_155_);
            leanh::lean_dec_ref_known(v_x_150_, 2);
            v___x_156_ = leanh::lean_apply_3(
                v_h__1_151_,
                v_it_154_,
                v_out_155_,
                leanh::lean_box(0),
            );
            return v___x_156_;
        }
        1 => {
            let mut v_it_157_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_158_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_153_);
            leanh::lean_dec(v_h__1_151_);
            v_it_157_ = leanh::lean_ctor_get(v_x_150_, 0);
            leanh::lean_inc(v_it_157_);
            leanh::lean_dec_ref_known(v_x_150_, 1);
            v___x_158_ =
                leanh::lean_apply_2(v_h__2_152_, v_it_157_, leanh::lean_box(0));
            return v___x_158_;
        }
        _ => {
            let mut v___x_159_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_152_);
            leanh::lean_dec(v_h__1_151_);
            v___x_159_ = leanh::lean_apply_1(v_h__3_153_, leanh::lean_box(0));
            return v___x_159_;
        }
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__3_splitter(
    mut v_00_u03b1_160_: *mut leanh::LeanObject,
    mut v_00_u03b2_161_: *mut leanh::LeanObject,
    mut v_m_162_: *mut leanh::LeanObject,
    mut v_inst_163_: *mut leanh::LeanObject,
    mut v_it_164_: *mut leanh::LeanObject,
    mut v_motive_165_: *mut leanh::LeanObject,
    mut v_x_166_: *mut leanh::LeanObject,
    mut v_h__1_167_: *mut leanh::LeanObject,
    mut v_h__2_168_: *mut leanh::LeanObject,
    mut v_h__3_169_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_166_) {
        0 => {
            let mut v_it_170_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_171_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_172_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_169_);
            leanh::lean_dec(v_h__2_168_);
            v_it_170_ = leanh::lean_ctor_get(v_x_166_, 0);
            leanh::lean_inc(v_it_170_);
            v_out_171_ = leanh::lean_ctor_get(v_x_166_, 1);
            leanh::lean_inc(v_out_171_);
            leanh::lean_dec_ref_known(v_x_166_, 2);
            v___x_172_ = leanh::lean_apply_3(
                v_h__1_167_,
                v_it_170_,
                v_out_171_,
                leanh::lean_box(0),
            );
            return v___x_172_;
        }
        1 => {
            let mut v_it_173_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_174_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_169_);
            leanh::lean_dec(v_h__1_167_);
            v_it_173_ = leanh::lean_ctor_get(v_x_166_, 0);
            leanh::lean_inc(v_it_173_);
            leanh::lean_dec_ref_known(v_x_166_, 1);
            v___x_174_ =
                leanh::lean_apply_2(v_h__2_168_, v_it_173_, leanh::lean_box(0));
            return v___x_174_;
        }
        _ => {
            let mut v___x_175_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_168_);
            leanh::lean_dec(v_h__1_167_);
            v___x_175_ = leanh::lean_apply_1(v_h__3_169_, leanh::lean_box(0));
            return v___x_175_;
        }
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__3_splitter___boxed(
    mut v_00_u03b1_176_: *mut leanh::LeanObject,
    mut v_00_u03b2_177_: *mut leanh::LeanObject,
    mut v_m_178_: *mut leanh::LeanObject,
    mut v_inst_179_: *mut leanh::LeanObject,
    mut v_it_180_: *mut leanh::LeanObject,
    mut v_motive_181_: *mut leanh::LeanObject,
    mut v_x_182_: *mut leanh::LeanObject,
    mut v_h__1_183_: *mut leanh::LeanObject,
    mut v_h__2_184_: *mut leanh::LeanObject,
    mut v_h__3_185_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_186_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_186_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__3_splitter(v_00_u03b1_176_, v_00_u03b2_177_, v_m_178_, v_inst_179_, v_it_180_, v_motive_181_, v_x_182_, v_h__1_183_, v_h__2_184_, v_h__3_185_);
    leanh::lean_dec(v_it_180_);
    leanh::lean_dec(v_inst_179_);
    return v_res_186_;
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__1_splitter___redArg(
    mut v_____do__lift_187_: *mut leanh::LeanObject,
    mut v_h__1_188_: *mut leanh::LeanObject,
    mut v_h__2_189_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_187_) == 0 {
        let mut v___x_190_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_189_);
        v___x_190_ = leanh::lean_apply_1(v_h__1_188_, leanh::lean_box(0));
        return v___x_190_;
    } else {
        let mut v_val_191_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_192_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_188_);
        v_val_191_ = leanh::lean_ctor_get(v_____do__lift_187_, 0);
        leanh::lean_inc(v_val_191_);
        leanh::lean_dec_ref_known(v_____do__lift_187_, 1);
        v___x_192_ = leanh::lean_apply_2(v_h__2_189_, v_val_191_, leanh::lean_box(0));
        return v___x_192_;
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__1_splitter(
    mut v_00_u03b2_193_: *mut leanh::LeanObject,
    mut v_00_u03b2_x27_194_: *mut leanh::LeanObject,
    mut v_n_195_: *mut leanh::LeanObject,
    mut v_f_196_: *mut leanh::LeanObject,
    mut v_out_197_: *mut leanh::LeanObject,
    mut v_motive_198_: *mut leanh::LeanObject,
    mut v_____do__lift_199_: *mut leanh::LeanObject,
    mut v_h__1_200_: *mut leanh::LeanObject,
    mut v_h__2_201_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_199_) == 0 {
        let mut v___x_202_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_201_);
        v___x_202_ = leanh::lean_apply_1(v_h__1_200_, leanh::lean_box(0));
        return v___x_202_;
    } else {
        let mut v_val_203_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_204_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_200_);
        v_val_203_ = leanh::lean_ctor_get(v_____do__lift_199_, 0);
        leanh::lean_inc(v_val_203_);
        leanh::lean_dec_ref_known(v_____do__lift_199_, 1);
        v___x_204_ = leanh::lean_apply_2(v_h__2_201_, v_val_203_, leanh::lean_box(0));
        return v___x_204_;
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__1_splitter___boxed(
    mut v_00_u03b2_205_: *mut leanh::LeanObject,
    mut v_00_u03b2_x27_206_: *mut leanh::LeanObject,
    mut v_n_207_: *mut leanh::LeanObject,
    mut v_f_208_: *mut leanh::LeanObject,
    mut v_out_209_: *mut leanh::LeanObject,
    mut v_motive_210_: *mut leanh::LeanObject,
    mut v_____do__lift_211_: *mut leanh::LeanObject,
    mut v_h__1_212_: *mut leanh::LeanObject,
    mut v_h__2_213_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_214_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_214_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap_0__Std_IterM_step__filterMapWithPostcondition_match__1_splitter(v_00_u03b2_205_, v_00_u03b2_x27_206_, v_n_207_, v_f_208_, v_out_209_, v_motive_210_, v_____do__lift_211_, v_h__1_212_, v_h__2_213_);
    leanh::lean_dec(v_out_209_);
    leanh::lean_dec(v_f_208_);
    return v_res_214_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Lemmas_Equivalence_StepCongr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap(
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
pub unsafe fn initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Data_Iterators_Lemmas_Equivalence_StepCongr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap(builtin);
}