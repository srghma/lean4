// Lean compiler output
// Module: Std.Do.WP.Adequate
// Imports: Std.Do.WP.Monad Std.Do.Internal.Ensures.Def
use crate::r#gen::Std::Do::Internal::Ensures::Def::{
    initialize_Std_Do_Internal_Ensures_Def, runtime_initialize_Std_Do_Internal_Ensures_Def,
};
use crate::r#gen::Std::Do::WP::Monad::{
    initialize_Std_Do_WP_Monad, runtime_initialize_Std_Do_WP_Monad,
};
pub unsafe fn l___private_Std_Do_WP_Adequate_0__Std_Do_PredTrans_pushExcept_match__1_splitter___redArg(
    mut v_x_118_: *mut crate::leanh::LeanObject,
    mut v_h__1_119_: *mut crate::leanh::LeanObject,
    mut v_h__2_120_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_118_) == 0 {
        let mut v_a_121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_119_);
        v_a_121_ = crate::leanh::lean_ctor_get(v_x_118_, 0);
        crate::leanh::lean_inc(v_a_121_);
        crate::leanh::lean_dec_ref_known(v_x_118_, 1);
        v___x_122_ = crate::leanh::lean_apply_1(v_h__2_120_, v_a_121_);
        return v___x_122_;
    } else {
        let mut v_a_123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_120_);
        v_a_123_ = crate::leanh::lean_ctor_get(v_x_118_, 0);
        crate::leanh::lean_inc(v_a_123_);
        crate::leanh::lean_dec_ref_known(v_x_118_, 1);
        v___x_124_ = crate::leanh::lean_apply_1(v_h__1_119_, v_a_123_);
        return v___x_124_;
    }
}
pub unsafe fn l___private_Std_Do_WP_Adequate_0__Std_Do_PredTrans_pushExcept_match__1_splitter(
    mut v_00_u03b1_125_: *mut crate::leanh::LeanObject,
    mut v_00_u03b5_126_: *mut crate::leanh::LeanObject,
    mut v_motive_127_: *mut crate::leanh::LeanObject,
    mut v_x_128_: *mut crate::leanh::LeanObject,
    mut v_h__1_129_: *mut crate::leanh::LeanObject,
    mut v_h__2_130_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_128_) == 0 {
        let mut v_a_131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_129_);
        v_a_131_ = crate::leanh::lean_ctor_get(v_x_128_, 0);
        crate::leanh::lean_inc(v_a_131_);
        crate::leanh::lean_dec_ref_known(v_x_128_, 1);
        v___x_132_ = crate::leanh::lean_apply_1(v_h__2_130_, v_a_131_);
        return v___x_132_;
    } else {
        let mut v_a_133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_130_);
        v_a_133_ = crate::leanh::lean_ctor_get(v_x_128_, 0);
        crate::leanh::lean_inc(v_a_133_);
        crate::leanh::lean_dec_ref_known(v_x_128_, 1);
        v___x_134_ = crate::leanh::lean_apply_1(v_h__1_129_, v_a_133_);
        return v___x_134_;
    }
}
pub unsafe fn l___private_Std_Do_WP_Adequate_0__Std_Do_instWPAdequateExceptTExceptPureOfLawfulMonad_match__1_splitter___redArg(
    mut v_r_135_: *mut crate::leanh::LeanObject,
    mut v_h__1_136_: *mut crate::leanh::LeanObject,
    mut v_h__2_137_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_r_135_) == 0 {
        let mut v_a_138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_136_);
        v_a_138_ = crate::leanh::lean_ctor_get(v_r_135_, 0);
        crate::leanh::lean_inc(v_a_138_);
        crate::leanh::lean_dec_ref_known(v_r_135_, 1);
        v___x_139_ = crate::leanh::lean_apply_1(v_h__2_137_, v_a_138_);
        return v___x_139_;
    } else {
        let mut v_a_140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_137_);
        v_a_140_ = crate::leanh::lean_ctor_get(v_r_135_, 0);
        crate::leanh::lean_inc(v_a_140_);
        crate::leanh::lean_dec_ref_known(v_r_135_, 1);
        v___x_141_ = crate::leanh::lean_apply_1(v_h__1_136_, v_a_140_);
        return v___x_141_;
    }
}
pub unsafe fn l___private_Std_Do_WP_Adequate_0__Std_Do_instWPAdequateExceptTExceptPureOfLawfulMonad_match__1_splitter(
    mut v_00_u03b5_142_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_143_: *mut crate::leanh::LeanObject,
    mut v_motive_144_: *mut crate::leanh::LeanObject,
    mut v_r_145_: *mut crate::leanh::LeanObject,
    mut v_h__1_146_: *mut crate::leanh::LeanObject,
    mut v_h__2_147_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_r_145_) == 0 {
        let mut v_a_148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_146_);
        v_a_148_ = crate::leanh::lean_ctor_get(v_r_145_, 0);
        crate::leanh::lean_inc(v_a_148_);
        crate::leanh::lean_dec_ref_known(v_r_145_, 1);
        v___x_149_ = crate::leanh::lean_apply_1(v_h__2_147_, v_a_148_);
        return v___x_149_;
    } else {
        let mut v_a_150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_147_);
        v_a_150_ = crate::leanh::lean_ctor_get(v_r_145_, 0);
        crate::leanh::lean_inc(v_a_150_);
        crate::leanh::lean_dec_ref_known(v_r_145_, 1);
        v___x_151_ = crate::leanh::lean_apply_1(v_h__1_146_, v_a_150_);
        return v___x_151_;
    }
}
pub unsafe fn l___private_Std_Do_WP_Adequate_0__Std_Do_instWPAdequateExceptTExceptPureOfLawfulMonad_match__5_splitter___redArg(
    mut v_r_152_: *mut crate::leanh::LeanObject,
    mut v_h__1_153_: *mut crate::leanh::LeanObject,
    mut v_h__2_154_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_r_152_) == 0 {
        let mut v_a_155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_153_);
        v_a_155_ = crate::leanh::lean_ctor_get(v_r_152_, 0);
        crate::leanh::lean_inc(v_a_155_);
        crate::leanh::lean_dec_ref_known(v_r_152_, 1);
        v___x_156_ = crate::leanh::lean_apply_2(v_h__2_154_, v_a_155_, crate::leanh::lean_box(0));
        return v___x_156_;
    } else {
        let mut v_a_157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_154_);
        v_a_157_ = crate::leanh::lean_ctor_get(v_r_152_, 0);
        crate::leanh::lean_inc(v_a_157_);
        crate::leanh::lean_dec_ref_known(v_r_152_, 1);
        v___x_158_ = crate::leanh::lean_apply_2(v_h__1_153_, v_a_157_, crate::leanh::lean_box(0));
        return v___x_158_;
    }
}
pub unsafe fn l___private_Std_Do_WP_Adequate_0__Std_Do_instWPAdequateExceptTExceptPureOfLawfulMonad_match__5_splitter(
    mut v_00_u03b5_159_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_160_: *mut crate::leanh::LeanObject,
    mut v_P_161_: *mut crate::leanh::LeanObject,
    mut v_motive_162_: *mut crate::leanh::LeanObject,
    mut v_r_163_: *mut crate::leanh::LeanObject,
    mut v_h_164_: *mut crate::leanh::LeanObject,
    mut v_h__1_165_: *mut crate::leanh::LeanObject,
    mut v_h__2_166_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_r_163_) == 0 {
        let mut v_a_167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_165_);
        v_a_167_ = crate::leanh::lean_ctor_get(v_r_163_, 0);
        crate::leanh::lean_inc(v_a_167_);
        crate::leanh::lean_dec_ref_known(v_r_163_, 1);
        v___x_168_ = crate::leanh::lean_apply_2(v_h__2_166_, v_a_167_, crate::leanh::lean_box(0));
        return v___x_168_;
    } else {
        let mut v_a_169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_166_);
        v_a_169_ = crate::leanh::lean_ctor_get(v_r_163_, 0);
        crate::leanh::lean_inc(v_a_169_);
        crate::leanh::lean_dec_ref_known(v_r_163_, 1);
        v___x_170_ = crate::leanh::lean_apply_2(v_h__1_165_, v_a_169_, crate::leanh::lean_box(0));
        return v___x_170_;
    }
}
pub unsafe fn l___private_Std_Do_WP_Adequate_0__Std_Do_PredTrans_pushOption_match__1_splitter___redArg(
    mut v_x_171_: *mut crate::leanh::LeanObject,
    mut v_h__1_172_: *mut crate::leanh::LeanObject,
    mut v_h__2_173_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_171_) == 0 {
        let mut v___x_174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_172_);
        v___x_174_ = crate::leanh::lean_box(0);
        v___x_175_ = crate::leanh::lean_apply_1(v_h__2_173_, v___x_174_);
        return v___x_175_;
    } else {
        let mut v_val_176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_173_);
        v_val_176_ = crate::leanh::lean_ctor_get(v_x_171_, 0);
        crate::leanh::lean_inc(v_val_176_);
        crate::leanh::lean_dec_ref_known(v_x_171_, 1);
        v___x_177_ = crate::leanh::lean_apply_1(v_h__1_172_, v_val_176_);
        return v___x_177_;
    }
}
pub unsafe fn l___private_Std_Do_WP_Adequate_0__Std_Do_PredTrans_pushOption_match__1_splitter(
    mut v_00_u03b1_178_: *mut crate::leanh::LeanObject,
    mut v_motive_179_: *mut crate::leanh::LeanObject,
    mut v_x_180_: *mut crate::leanh::LeanObject,
    mut v_h__1_181_: *mut crate::leanh::LeanObject,
    mut v_h__2_182_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_180_) == 0 {
        let mut v___x_183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_181_);
        v___x_183_ = crate::leanh::lean_box(0);
        v___x_184_ = crate::leanh::lean_apply_1(v_h__2_182_, v___x_183_);
        return v___x_184_;
    } else {
        let mut v_val_185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_182_);
        v_val_185_ = crate::leanh::lean_ctor_get(v_x_180_, 0);
        crate::leanh::lean_inc(v_val_185_);
        crate::leanh::lean_dec_ref_known(v_x_180_, 1);
        v___x_186_ = crate::leanh::lean_apply_1(v_h__1_181_, v_val_185_);
        return v___x_186_;
    }
}
pub unsafe fn l___private_Std_Do_WP_Adequate_0__Std_Do_instWPAdequateOptionTExceptPUnitPureOfLawfulMonad_match__1_splitter___redArg(
    mut v_r_187_: *mut crate::leanh::LeanObject,
    mut v_h__1_188_: *mut crate::leanh::LeanObject,
    mut v_h__2_189_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_r_187_) == 0 {
        let mut v___x_190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_188_);
        v___x_190_ = crate::leanh::lean_box(0);
        v___x_191_ = crate::leanh::lean_apply_1(v_h__2_189_, v___x_190_);
        return v___x_191_;
    } else {
        let mut v_val_192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_189_);
        v_val_192_ = crate::leanh::lean_ctor_get(v_r_187_, 0);
        crate::leanh::lean_inc(v_val_192_);
        crate::leanh::lean_dec_ref_known(v_r_187_, 1);
        v___x_193_ = crate::leanh::lean_apply_1(v_h__1_188_, v_val_192_);
        return v___x_193_;
    }
}
pub unsafe fn l___private_Std_Do_WP_Adequate_0__Std_Do_instWPAdequateOptionTExceptPUnitPureOfLawfulMonad_match__1_splitter(
    mut v_00_u03b1_194_: *mut crate::leanh::LeanObject,
    mut v_motive_195_: *mut crate::leanh::LeanObject,
    mut v_r_196_: *mut crate::leanh::LeanObject,
    mut v_h__1_197_: *mut crate::leanh::LeanObject,
    mut v_h__2_198_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_r_196_) == 0 {
        let mut v___x_199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_197_);
        v___x_199_ = crate::leanh::lean_box(0);
        v___x_200_ = crate::leanh::lean_apply_1(v_h__2_198_, v___x_199_);
        return v___x_200_;
    } else {
        let mut v_val_201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_198_);
        v_val_201_ = crate::leanh::lean_ctor_get(v_r_196_, 0);
        crate::leanh::lean_inc(v_val_201_);
        crate::leanh::lean_dec_ref_known(v_r_196_, 1);
        v___x_202_ = crate::leanh::lean_apply_1(v_h__1_197_, v_val_201_);
        return v___x_202_;
    }
}
pub unsafe fn l___private_Std_Do_WP_Adequate_0__Std_Do_instWPAdequateOptionTExceptPUnitPureOfLawfulMonad_match__5_splitter___redArg(
    mut v_r_203_: *mut crate::leanh::LeanObject,
    mut v_h__1_204_: *mut crate::leanh::LeanObject,
    mut v_h__2_205_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_r_203_) == 0 {
        let mut v___x_206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_204_);
        v___x_206_ = crate::leanh::lean_apply_1(v_h__2_205_, crate::leanh::lean_box(0));
        return v___x_206_;
    } else {
        let mut v_val_207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_205_);
        v_val_207_ = crate::leanh::lean_ctor_get(v_r_203_, 0);
        crate::leanh::lean_inc(v_val_207_);
        crate::leanh::lean_dec_ref_known(v_r_203_, 1);
        v___x_208_ = crate::leanh::lean_apply_2(v_h__1_204_, v_val_207_, crate::leanh::lean_box(0));
        return v___x_208_;
    }
}
pub unsafe fn l___private_Std_Do_WP_Adequate_0__Std_Do_instWPAdequateOptionTExceptPUnitPureOfLawfulMonad_match__5_splitter(
    mut v_00_u03b1_209_: *mut crate::leanh::LeanObject,
    mut v_P_210_: *mut crate::leanh::LeanObject,
    mut v_motive_211_: *mut crate::leanh::LeanObject,
    mut v_r_212_: *mut crate::leanh::LeanObject,
    mut v_h_213_: *mut crate::leanh::LeanObject,
    mut v_h__1_214_: *mut crate::leanh::LeanObject,
    mut v_h__2_215_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_r_212_) == 0 {
        let mut v___x_216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_214_);
        v___x_216_ = crate::leanh::lean_apply_1(v_h__2_215_, crate::leanh::lean_box(0));
        return v___x_216_;
    } else {
        let mut v_val_217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_215_);
        v_val_217_ = crate::leanh::lean_ctor_get(v_r_212_, 0);
        crate::leanh::lean_inc(v_val_217_);
        crate::leanh::lean_dec_ref_known(v_r_212_, 1);
        v___x_218_ = crate::leanh::lean_apply_2(v_h__1_214_, v_val_217_, crate::leanh::lean_box(0));
        return v___x_218_;
    }
}
pub unsafe fn l___private_Std_Do_WP_Adequate_0__OptionT_bind_match__1_splitter___redArg(
    mut v_____do__lift_219_: *mut crate::leanh::LeanObject,
    mut v_h__1_220_: *mut crate::leanh::LeanObject,
    mut v_h__2_221_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_219_) == 0 {
        let mut v___x_222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_220_);
        v___x_222_ = crate::leanh::lean_box(0);
        v___x_223_ = crate::leanh::lean_apply_1(v_h__2_221_, v___x_222_);
        return v___x_223_;
    } else {
        let mut v_val_224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_221_);
        v_val_224_ = crate::leanh::lean_ctor_get(v_____do__lift_219_, 0);
        crate::leanh::lean_inc(v_val_224_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_219_, 1);
        v___x_225_ = crate::leanh::lean_apply_1(v_h__1_220_, v_val_224_);
        return v___x_225_;
    }
}
pub unsafe fn l___private_Std_Do_WP_Adequate_0__OptionT_bind_match__1_splitter(
    mut v_00_u03b1_226_: *mut crate::leanh::LeanObject,
    mut v_motive_227_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_228_: *mut crate::leanh::LeanObject,
    mut v_h__1_229_: *mut crate::leanh::LeanObject,
    mut v_h__2_230_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_228_) == 0 {
        let mut v___x_231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_229_);
        v___x_231_ = crate::leanh::lean_box(0);
        v___x_232_ = crate::leanh::lean_apply_1(v_h__2_230_, v___x_231_);
        return v___x_232_;
    } else {
        let mut v_val_233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_230_);
        v_val_233_ = crate::leanh::lean_ctor_get(v_____do__lift_228_, 0);
        crate::leanh::lean_inc(v_val_233_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_228_, 1);
        v___x_234_ = crate::leanh::lean_apply_1(v_h__1_229_, v_val_233_);
        return v___x_234_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Do_WP_Adequate(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Do_WP_Monad(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Do_Internal_Ensures_Def(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Do_WP_Adequate(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Do_WP_Adequate(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Do_WP_Monad(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Do_Internal_Ensures_Def(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Do_WP_Adequate(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Do_WP_Adequate(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Do_WP_Adequate(builtin);
}
