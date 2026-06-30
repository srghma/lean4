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
    mut v_x_118_: *mut leanh::LeanObject,
    mut v_h__1_119_: *mut leanh::LeanObject,
    mut v_h__2_120_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_118_) == 0 {
        let mut v_a_121_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_122_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_119_);
        v_a_121_ = leanh::lean_ctor_get(v_x_118_, 0);
        leanh::lean_inc(v_a_121_);
        leanh::lean_dec_ref_known(v_x_118_, 1);
        v___x_122_ = leanh::lean_apply_1(v_h__2_120_, v_a_121_);
        return v___x_122_;
    } else {
        let mut v_a_123_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_124_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_120_);
        v_a_123_ = leanh::lean_ctor_get(v_x_118_, 0);
        leanh::lean_inc(v_a_123_);
        leanh::lean_dec_ref_known(v_x_118_, 1);
        v___x_124_ = leanh::lean_apply_1(v_h__1_119_, v_a_123_);
        return v___x_124_;
    }
}
pub unsafe fn l___private_Std_Do_WP_Adequate_0__Std_Do_PredTrans_pushExcept_match__1_splitter(
    mut v_00_u03b1_125_: *mut leanh::LeanObject,
    mut v_00_u03b5_126_: *mut leanh::LeanObject,
    mut v_motive_127_: *mut leanh::LeanObject,
    mut v_x_128_: *mut leanh::LeanObject,
    mut v_h__1_129_: *mut leanh::LeanObject,
    mut v_h__2_130_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_128_) == 0 {
        let mut v_a_131_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_132_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_129_);
        v_a_131_ = leanh::lean_ctor_get(v_x_128_, 0);
        leanh::lean_inc(v_a_131_);
        leanh::lean_dec_ref_known(v_x_128_, 1);
        v___x_132_ = leanh::lean_apply_1(v_h__2_130_, v_a_131_);
        return v___x_132_;
    } else {
        let mut v_a_133_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_134_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_130_);
        v_a_133_ = leanh::lean_ctor_get(v_x_128_, 0);
        leanh::lean_inc(v_a_133_);
        leanh::lean_dec_ref_known(v_x_128_, 1);
        v___x_134_ = leanh::lean_apply_1(v_h__1_129_, v_a_133_);
        return v___x_134_;
    }
}
pub unsafe fn l___private_Std_Do_WP_Adequate_0__Std_Do_instWPAdequateExceptTExceptPureOfLawfulMonad_match__1_splitter___redArg(
    mut v_r_135_: *mut leanh::LeanObject,
    mut v_h__1_136_: *mut leanh::LeanObject,
    mut v_h__2_137_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_r_135_) == 0 {
        let mut v_a_138_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_139_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_136_);
        v_a_138_ = leanh::lean_ctor_get(v_r_135_, 0);
        leanh::lean_inc(v_a_138_);
        leanh::lean_dec_ref_known(v_r_135_, 1);
        v___x_139_ = leanh::lean_apply_1(v_h__2_137_, v_a_138_);
        return v___x_139_;
    } else {
        let mut v_a_140_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_141_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_137_);
        v_a_140_ = leanh::lean_ctor_get(v_r_135_, 0);
        leanh::lean_inc(v_a_140_);
        leanh::lean_dec_ref_known(v_r_135_, 1);
        v___x_141_ = leanh::lean_apply_1(v_h__1_136_, v_a_140_);
        return v___x_141_;
    }
}
pub unsafe fn l___private_Std_Do_WP_Adequate_0__Std_Do_instWPAdequateExceptTExceptPureOfLawfulMonad_match__1_splitter(
    mut v_00_u03b5_142_: *mut leanh::LeanObject,
    mut v_00_u03b1_143_: *mut leanh::LeanObject,
    mut v_motive_144_: *mut leanh::LeanObject,
    mut v_r_145_: *mut leanh::LeanObject,
    mut v_h__1_146_: *mut leanh::LeanObject,
    mut v_h__2_147_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_r_145_) == 0 {
        let mut v_a_148_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_149_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_146_);
        v_a_148_ = leanh::lean_ctor_get(v_r_145_, 0);
        leanh::lean_inc(v_a_148_);
        leanh::lean_dec_ref_known(v_r_145_, 1);
        v___x_149_ = leanh::lean_apply_1(v_h__2_147_, v_a_148_);
        return v___x_149_;
    } else {
        let mut v_a_150_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_151_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_147_);
        v_a_150_ = leanh::lean_ctor_get(v_r_145_, 0);
        leanh::lean_inc(v_a_150_);
        leanh::lean_dec_ref_known(v_r_145_, 1);
        v___x_151_ = leanh::lean_apply_1(v_h__1_146_, v_a_150_);
        return v___x_151_;
    }
}
pub unsafe fn l___private_Std_Do_WP_Adequate_0__Std_Do_instWPAdequateExceptTExceptPureOfLawfulMonad_match__5_splitter___redArg(
    mut v_r_152_: *mut leanh::LeanObject,
    mut v_h__1_153_: *mut leanh::LeanObject,
    mut v_h__2_154_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_r_152_) == 0 {
        let mut v_a_155_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_156_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_153_);
        v_a_155_ = leanh::lean_ctor_get(v_r_152_, 0);
        leanh::lean_inc(v_a_155_);
        leanh::lean_dec_ref_known(v_r_152_, 1);
        v___x_156_ = leanh::lean_apply_2(v_h__2_154_, v_a_155_, leanh::lean_box(0));
        return v___x_156_;
    } else {
        let mut v_a_157_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_158_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_154_);
        v_a_157_ = leanh::lean_ctor_get(v_r_152_, 0);
        leanh::lean_inc(v_a_157_);
        leanh::lean_dec_ref_known(v_r_152_, 1);
        v___x_158_ = leanh::lean_apply_2(v_h__1_153_, v_a_157_, leanh::lean_box(0));
        return v___x_158_;
    }
}
pub unsafe fn l___private_Std_Do_WP_Adequate_0__Std_Do_instWPAdequateExceptTExceptPureOfLawfulMonad_match__5_splitter(
    mut v_00_u03b5_159_: *mut leanh::LeanObject,
    mut v_00_u03b1_160_: *mut leanh::LeanObject,
    mut v_P_161_: *mut leanh::LeanObject,
    mut v_motive_162_: *mut leanh::LeanObject,
    mut v_r_163_: *mut leanh::LeanObject,
    mut v_h_164_: *mut leanh::LeanObject,
    mut v_h__1_165_: *mut leanh::LeanObject,
    mut v_h__2_166_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_r_163_) == 0 {
        let mut v_a_167_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_168_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_165_);
        v_a_167_ = leanh::lean_ctor_get(v_r_163_, 0);
        leanh::lean_inc(v_a_167_);
        leanh::lean_dec_ref_known(v_r_163_, 1);
        v___x_168_ = leanh::lean_apply_2(v_h__2_166_, v_a_167_, leanh::lean_box(0));
        return v___x_168_;
    } else {
        let mut v_a_169_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_170_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_166_);
        v_a_169_ = leanh::lean_ctor_get(v_r_163_, 0);
        leanh::lean_inc(v_a_169_);
        leanh::lean_dec_ref_known(v_r_163_, 1);
        v___x_170_ = leanh::lean_apply_2(v_h__1_165_, v_a_169_, leanh::lean_box(0));
        return v___x_170_;
    }
}
pub unsafe fn l___private_Std_Do_WP_Adequate_0__Std_Do_PredTrans_pushOption_match__1_splitter___redArg(
    mut v_x_171_: *mut leanh::LeanObject,
    mut v_h__1_172_: *mut leanh::LeanObject,
    mut v_h__2_173_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_171_) == 0 {
        let mut v___x_174_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_175_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_172_);
        v___x_174_ = leanh::lean_box(0);
        v___x_175_ = leanh::lean_apply_1(v_h__2_173_, v___x_174_);
        return v___x_175_;
    } else {
        let mut v_val_176_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_177_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_173_);
        v_val_176_ = leanh::lean_ctor_get(v_x_171_, 0);
        leanh::lean_inc(v_val_176_);
        leanh::lean_dec_ref_known(v_x_171_, 1);
        v___x_177_ = leanh::lean_apply_1(v_h__1_172_, v_val_176_);
        return v___x_177_;
    }
}
pub unsafe fn l___private_Std_Do_WP_Adequate_0__Std_Do_PredTrans_pushOption_match__1_splitter(
    mut v_00_u03b1_178_: *mut leanh::LeanObject,
    mut v_motive_179_: *mut leanh::LeanObject,
    mut v_x_180_: *mut leanh::LeanObject,
    mut v_h__1_181_: *mut leanh::LeanObject,
    mut v_h__2_182_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_180_) == 0 {
        let mut v___x_183_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_184_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_181_);
        v___x_183_ = leanh::lean_box(0);
        v___x_184_ = leanh::lean_apply_1(v_h__2_182_, v___x_183_);
        return v___x_184_;
    } else {
        let mut v_val_185_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_186_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_182_);
        v_val_185_ = leanh::lean_ctor_get(v_x_180_, 0);
        leanh::lean_inc(v_val_185_);
        leanh::lean_dec_ref_known(v_x_180_, 1);
        v___x_186_ = leanh::lean_apply_1(v_h__1_181_, v_val_185_);
        return v___x_186_;
    }
}
pub unsafe fn l___private_Std_Do_WP_Adequate_0__Std_Do_instWPAdequateOptionTExceptPUnitPureOfLawfulMonad_match__1_splitter___redArg(
    mut v_r_187_: *mut leanh::LeanObject,
    mut v_h__1_188_: *mut leanh::LeanObject,
    mut v_h__2_189_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_r_187_) == 0 {
        let mut v___x_190_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_191_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_188_);
        v___x_190_ = leanh::lean_box(0);
        v___x_191_ = leanh::lean_apply_1(v_h__2_189_, v___x_190_);
        return v___x_191_;
    } else {
        let mut v_val_192_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_193_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_189_);
        v_val_192_ = leanh::lean_ctor_get(v_r_187_, 0);
        leanh::lean_inc(v_val_192_);
        leanh::lean_dec_ref_known(v_r_187_, 1);
        v___x_193_ = leanh::lean_apply_1(v_h__1_188_, v_val_192_);
        return v___x_193_;
    }
}
pub unsafe fn l___private_Std_Do_WP_Adequate_0__Std_Do_instWPAdequateOptionTExceptPUnitPureOfLawfulMonad_match__1_splitter(
    mut v_00_u03b1_194_: *mut leanh::LeanObject,
    mut v_motive_195_: *mut leanh::LeanObject,
    mut v_r_196_: *mut leanh::LeanObject,
    mut v_h__1_197_: *mut leanh::LeanObject,
    mut v_h__2_198_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_r_196_) == 0 {
        let mut v___x_199_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_200_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_197_);
        v___x_199_ = leanh::lean_box(0);
        v___x_200_ = leanh::lean_apply_1(v_h__2_198_, v___x_199_);
        return v___x_200_;
    } else {
        let mut v_val_201_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_202_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_198_);
        v_val_201_ = leanh::lean_ctor_get(v_r_196_, 0);
        leanh::lean_inc(v_val_201_);
        leanh::lean_dec_ref_known(v_r_196_, 1);
        v___x_202_ = leanh::lean_apply_1(v_h__1_197_, v_val_201_);
        return v___x_202_;
    }
}
pub unsafe fn l___private_Std_Do_WP_Adequate_0__Std_Do_instWPAdequateOptionTExceptPUnitPureOfLawfulMonad_match__5_splitter___redArg(
    mut v_r_203_: *mut leanh::LeanObject,
    mut v_h__1_204_: *mut leanh::LeanObject,
    mut v_h__2_205_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_r_203_) == 0 {
        let mut v___x_206_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_204_);
        v___x_206_ = leanh::lean_apply_1(v_h__2_205_, leanh::lean_box(0));
        return v___x_206_;
    } else {
        let mut v_val_207_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_208_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_205_);
        v_val_207_ = leanh::lean_ctor_get(v_r_203_, 0);
        leanh::lean_inc(v_val_207_);
        leanh::lean_dec_ref_known(v_r_203_, 1);
        v___x_208_ = leanh::lean_apply_2(v_h__1_204_, v_val_207_, leanh::lean_box(0));
        return v___x_208_;
    }
}
pub unsafe fn l___private_Std_Do_WP_Adequate_0__Std_Do_instWPAdequateOptionTExceptPUnitPureOfLawfulMonad_match__5_splitter(
    mut v_00_u03b1_209_: *mut leanh::LeanObject,
    mut v_P_210_: *mut leanh::LeanObject,
    mut v_motive_211_: *mut leanh::LeanObject,
    mut v_r_212_: *mut leanh::LeanObject,
    mut v_h_213_: *mut leanh::LeanObject,
    mut v_h__1_214_: *mut leanh::LeanObject,
    mut v_h__2_215_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_r_212_) == 0 {
        let mut v___x_216_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_214_);
        v___x_216_ = leanh::lean_apply_1(v_h__2_215_, leanh::lean_box(0));
        return v___x_216_;
    } else {
        let mut v_val_217_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_218_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_215_);
        v_val_217_ = leanh::lean_ctor_get(v_r_212_, 0);
        leanh::lean_inc(v_val_217_);
        leanh::lean_dec_ref_known(v_r_212_, 1);
        v___x_218_ = leanh::lean_apply_2(v_h__1_214_, v_val_217_, leanh::lean_box(0));
        return v___x_218_;
    }
}
pub unsafe fn l___private_Std_Do_WP_Adequate_0__OptionT_bind_match__1_splitter___redArg(
    mut v_____do__lift_219_: *mut leanh::LeanObject,
    mut v_h__1_220_: *mut leanh::LeanObject,
    mut v_h__2_221_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_219_) == 0 {
        let mut v___x_222_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_223_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_220_);
        v___x_222_ = leanh::lean_box(0);
        v___x_223_ = leanh::lean_apply_1(v_h__2_221_, v___x_222_);
        return v___x_223_;
    } else {
        let mut v_val_224_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_225_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_221_);
        v_val_224_ = leanh::lean_ctor_get(v_____do__lift_219_, 0);
        leanh::lean_inc(v_val_224_);
        leanh::lean_dec_ref_known(v_____do__lift_219_, 1);
        v___x_225_ = leanh::lean_apply_1(v_h__1_220_, v_val_224_);
        return v___x_225_;
    }
}
pub unsafe fn l___private_Std_Do_WP_Adequate_0__OptionT_bind_match__1_splitter(
    mut v_00_u03b1_226_: *mut leanh::LeanObject,
    mut v_motive_227_: *mut leanh::LeanObject,
    mut v_____do__lift_228_: *mut leanh::LeanObject,
    mut v_h__1_229_: *mut leanh::LeanObject,
    mut v_h__2_230_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_228_) == 0 {
        let mut v___x_231_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_232_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_229_);
        v___x_231_ = leanh::lean_box(0);
        v___x_232_ = leanh::lean_apply_1(v_h__2_230_, v___x_231_);
        return v___x_232_;
    } else {
        let mut v_val_233_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_234_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_230_);
        v_val_233_ = leanh::lean_ctor_get(v_____do__lift_228_, 0);
        leanh::lean_inc(v_val_233_);
        leanh::lean_dec_ref_known(v_____do__lift_228_, 1);
        v___x_234_ = leanh::lean_apply_1(v_h__1_229_, v_val_233_);
        return v___x_234_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Do_WP_Adequate(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Do_WP_Monad(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Do_Internal_Ensures_Def(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Do_WP_Adequate(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Do_WP_Adequate(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Do_WP_Monad(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Do_Internal_Ensures_Def(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Do_WP_Adequate(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Do_WP_Adequate(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Do_WP_Adequate(builtin);
}