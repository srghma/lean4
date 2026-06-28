// Lean compiler output
// Module: Std.Do.WP.Adequate
// Imports: Std.Do.WP.Monad Std.Do.Internal.Ensures.Def
use crate::r#gen::Std::Do::Internal::Ensures::Def::{
    initialize_Std_Do_Internal_Ensures_Def, runtime_initialize_Std_Do_Internal_Ensures_Def,
};
use crate::r#gen::Std::Do::WP::Monad::{
    initialize_Std_Do_WP_Monad, runtime_initialize_Std_Do_WP_Monad,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_apply_1, lean_apply_2, lean_box, lean_ctor_get, lean_dec,
    lean_dec_ref, lean_dec_ref_known, lean_inc, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_obj_tag,
};
pub unsafe fn l___private_Std_Do_WP_Adequate_0__Std_Do_PredTrans_pushExcept_match__1_splitter___redArg(
    mut v_x_118_: *mut LeanObject,
    mut v_h__1_119_: *mut LeanObject,
    mut v_h__2_120_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_118_) == 0 {
        let mut v_a_121_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_122_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_119_);
        v_a_121_ = lean_ctor_get(v_x_118_, 0);
        lean_inc(v_a_121_);
        lean_dec_ref_known(v_x_118_, 1);
        v___x_122_ = lean_apply_1(v_h__2_120_, v_a_121_);
        return v___x_122_;
    } else {
        let mut v_a_123_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_124_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_120_);
        v_a_123_ = lean_ctor_get(v_x_118_, 0);
        lean_inc(v_a_123_);
        lean_dec_ref_known(v_x_118_, 1);
        v___x_124_ = lean_apply_1(v_h__1_119_, v_a_123_);
        return v___x_124_;
    }
}
pub unsafe fn l___private_Std_Do_WP_Adequate_0__Std_Do_PredTrans_pushExcept_match__1_splitter(
    mut v_00_u03b1_125_: *mut LeanObject,
    mut v_00_u03b5_126_: *mut LeanObject,
    mut v_motive_127_: *mut LeanObject,
    mut v_x_128_: *mut LeanObject,
    mut v_h__1_129_: *mut LeanObject,
    mut v_h__2_130_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_128_) == 0 {
        let mut v_a_131_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_132_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_129_);
        v_a_131_ = lean_ctor_get(v_x_128_, 0);
        lean_inc(v_a_131_);
        lean_dec_ref_known(v_x_128_, 1);
        v___x_132_ = lean_apply_1(v_h__2_130_, v_a_131_);
        return v___x_132_;
    } else {
        let mut v_a_133_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_134_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_130_);
        v_a_133_ = lean_ctor_get(v_x_128_, 0);
        lean_inc(v_a_133_);
        lean_dec_ref_known(v_x_128_, 1);
        v___x_134_ = lean_apply_1(v_h__1_129_, v_a_133_);
        return v___x_134_;
    }
}
pub unsafe fn l___private_Std_Do_WP_Adequate_0__Std_Do_instWPAdequateExceptTExceptPureOfLawfulMonad_match__1_splitter___redArg(
    mut v_r_135_: *mut LeanObject,
    mut v_h__1_136_: *mut LeanObject,
    mut v_h__2_137_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_r_135_) == 0 {
        let mut v_a_138_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_139_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_136_);
        v_a_138_ = lean_ctor_get(v_r_135_, 0);
        lean_inc(v_a_138_);
        lean_dec_ref_known(v_r_135_, 1);
        v___x_139_ = lean_apply_1(v_h__2_137_, v_a_138_);
        return v___x_139_;
    } else {
        let mut v_a_140_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_141_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_137_);
        v_a_140_ = lean_ctor_get(v_r_135_, 0);
        lean_inc(v_a_140_);
        lean_dec_ref_known(v_r_135_, 1);
        v___x_141_ = lean_apply_1(v_h__1_136_, v_a_140_);
        return v___x_141_;
    }
}
pub unsafe fn l___private_Std_Do_WP_Adequate_0__Std_Do_instWPAdequateExceptTExceptPureOfLawfulMonad_match__1_splitter(
    mut v_00_u03b5_142_: *mut LeanObject,
    mut v_00_u03b1_143_: *mut LeanObject,
    mut v_motive_144_: *mut LeanObject,
    mut v_r_145_: *mut LeanObject,
    mut v_h__1_146_: *mut LeanObject,
    mut v_h__2_147_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_r_145_) == 0 {
        let mut v_a_148_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_149_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_146_);
        v_a_148_ = lean_ctor_get(v_r_145_, 0);
        lean_inc(v_a_148_);
        lean_dec_ref_known(v_r_145_, 1);
        v___x_149_ = lean_apply_1(v_h__2_147_, v_a_148_);
        return v___x_149_;
    } else {
        let mut v_a_150_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_151_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_147_);
        v_a_150_ = lean_ctor_get(v_r_145_, 0);
        lean_inc(v_a_150_);
        lean_dec_ref_known(v_r_145_, 1);
        v___x_151_ = lean_apply_1(v_h__1_146_, v_a_150_);
        return v___x_151_;
    }
}
pub unsafe fn l___private_Std_Do_WP_Adequate_0__Std_Do_instWPAdequateExceptTExceptPureOfLawfulMonad_match__5_splitter___redArg(
    mut v_r_152_: *mut LeanObject,
    mut v_h__1_153_: *mut LeanObject,
    mut v_h__2_154_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_r_152_) == 0 {
        let mut v_a_155_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_156_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_153_);
        v_a_155_ = lean_ctor_get(v_r_152_, 0);
        lean_inc(v_a_155_);
        lean_dec_ref_known(v_r_152_, 1);
        v___x_156_ = lean_apply_2(v_h__2_154_, v_a_155_, lean_box(0));
        return v___x_156_;
    } else {
        let mut v_a_157_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_158_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_154_);
        v_a_157_ = lean_ctor_get(v_r_152_, 0);
        lean_inc(v_a_157_);
        lean_dec_ref_known(v_r_152_, 1);
        v___x_158_ = lean_apply_2(v_h__1_153_, v_a_157_, lean_box(0));
        return v___x_158_;
    }
}
pub unsafe fn l___private_Std_Do_WP_Adequate_0__Std_Do_instWPAdequateExceptTExceptPureOfLawfulMonad_match__5_splitter(
    mut v_00_u03b5_159_: *mut LeanObject,
    mut v_00_u03b1_160_: *mut LeanObject,
    mut v_P_161_: *mut LeanObject,
    mut v_motive_162_: *mut LeanObject,
    mut v_r_163_: *mut LeanObject,
    mut v_h_164_: *mut LeanObject,
    mut v_h__1_165_: *mut LeanObject,
    mut v_h__2_166_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_r_163_) == 0 {
        let mut v_a_167_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_168_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_165_);
        v_a_167_ = lean_ctor_get(v_r_163_, 0);
        lean_inc(v_a_167_);
        lean_dec_ref_known(v_r_163_, 1);
        v___x_168_ = lean_apply_2(v_h__2_166_, v_a_167_, lean_box(0));
        return v___x_168_;
    } else {
        let mut v_a_169_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_170_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_166_);
        v_a_169_ = lean_ctor_get(v_r_163_, 0);
        lean_inc(v_a_169_);
        lean_dec_ref_known(v_r_163_, 1);
        v___x_170_ = lean_apply_2(v_h__1_165_, v_a_169_, lean_box(0));
        return v___x_170_;
    }
}
pub unsafe fn l___private_Std_Do_WP_Adequate_0__Std_Do_PredTrans_pushOption_match__1_splitter___redArg(
    mut v_x_171_: *mut LeanObject,
    mut v_h__1_172_: *mut LeanObject,
    mut v_h__2_173_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_171_) == 0 {
        let mut v___x_174_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_175_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_172_);
        v___x_174_ = lean_box(0);
        v___x_175_ = lean_apply_1(v_h__2_173_, v___x_174_);
        return v___x_175_;
    } else {
        let mut v_val_176_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_177_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_173_);
        v_val_176_ = lean_ctor_get(v_x_171_, 0);
        lean_inc(v_val_176_);
        lean_dec_ref_known(v_x_171_, 1);
        v___x_177_ = lean_apply_1(v_h__1_172_, v_val_176_);
        return v___x_177_;
    }
}
pub unsafe fn l___private_Std_Do_WP_Adequate_0__Std_Do_PredTrans_pushOption_match__1_splitter(
    mut v_00_u03b1_178_: *mut LeanObject,
    mut v_motive_179_: *mut LeanObject,
    mut v_x_180_: *mut LeanObject,
    mut v_h__1_181_: *mut LeanObject,
    mut v_h__2_182_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_180_) == 0 {
        let mut v___x_183_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_184_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_181_);
        v___x_183_ = lean_box(0);
        v___x_184_ = lean_apply_1(v_h__2_182_, v___x_183_);
        return v___x_184_;
    } else {
        let mut v_val_185_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_186_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_182_);
        v_val_185_ = lean_ctor_get(v_x_180_, 0);
        lean_inc(v_val_185_);
        lean_dec_ref_known(v_x_180_, 1);
        v___x_186_ = lean_apply_1(v_h__1_181_, v_val_185_);
        return v___x_186_;
    }
}
pub unsafe fn l___private_Std_Do_WP_Adequate_0__Std_Do_instWPAdequateOptionTExceptPUnitPureOfLawfulMonad_match__1_splitter___redArg(
    mut v_r_187_: *mut LeanObject,
    mut v_h__1_188_: *mut LeanObject,
    mut v_h__2_189_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_r_187_) == 0 {
        let mut v___x_190_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_191_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_188_);
        v___x_190_ = lean_box(0);
        v___x_191_ = lean_apply_1(v_h__2_189_, v___x_190_);
        return v___x_191_;
    } else {
        let mut v_val_192_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_193_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_189_);
        v_val_192_ = lean_ctor_get(v_r_187_, 0);
        lean_inc(v_val_192_);
        lean_dec_ref_known(v_r_187_, 1);
        v___x_193_ = lean_apply_1(v_h__1_188_, v_val_192_);
        return v___x_193_;
    }
}
pub unsafe fn l___private_Std_Do_WP_Adequate_0__Std_Do_instWPAdequateOptionTExceptPUnitPureOfLawfulMonad_match__1_splitter(
    mut v_00_u03b1_194_: *mut LeanObject,
    mut v_motive_195_: *mut LeanObject,
    mut v_r_196_: *mut LeanObject,
    mut v_h__1_197_: *mut LeanObject,
    mut v_h__2_198_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_r_196_) == 0 {
        let mut v___x_199_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_200_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_197_);
        v___x_199_ = lean_box(0);
        v___x_200_ = lean_apply_1(v_h__2_198_, v___x_199_);
        return v___x_200_;
    } else {
        let mut v_val_201_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_202_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_198_);
        v_val_201_ = lean_ctor_get(v_r_196_, 0);
        lean_inc(v_val_201_);
        lean_dec_ref_known(v_r_196_, 1);
        v___x_202_ = lean_apply_1(v_h__1_197_, v_val_201_);
        return v___x_202_;
    }
}
pub unsafe fn l___private_Std_Do_WP_Adequate_0__Std_Do_instWPAdequateOptionTExceptPUnitPureOfLawfulMonad_match__5_splitter___redArg(
    mut v_r_203_: *mut LeanObject,
    mut v_h__1_204_: *mut LeanObject,
    mut v_h__2_205_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_r_203_) == 0 {
        let mut v___x_206_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_204_);
        v___x_206_ = lean_apply_1(v_h__2_205_, lean_box(0));
        return v___x_206_;
    } else {
        let mut v_val_207_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_208_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_205_);
        v_val_207_ = lean_ctor_get(v_r_203_, 0);
        lean_inc(v_val_207_);
        lean_dec_ref_known(v_r_203_, 1);
        v___x_208_ = lean_apply_2(v_h__1_204_, v_val_207_, lean_box(0));
        return v___x_208_;
    }
}
pub unsafe fn l___private_Std_Do_WP_Adequate_0__Std_Do_instWPAdequateOptionTExceptPUnitPureOfLawfulMonad_match__5_splitter(
    mut v_00_u03b1_209_: *mut LeanObject,
    mut v_P_210_: *mut LeanObject,
    mut v_motive_211_: *mut LeanObject,
    mut v_r_212_: *mut LeanObject,
    mut v_h_213_: *mut LeanObject,
    mut v_h__1_214_: *mut LeanObject,
    mut v_h__2_215_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_r_212_) == 0 {
        let mut v___x_216_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_214_);
        v___x_216_ = lean_apply_1(v_h__2_215_, lean_box(0));
        return v___x_216_;
    } else {
        let mut v_val_217_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_218_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_215_);
        v_val_217_ = lean_ctor_get(v_r_212_, 0);
        lean_inc(v_val_217_);
        lean_dec_ref_known(v_r_212_, 1);
        v___x_218_ = lean_apply_2(v_h__1_214_, v_val_217_, lean_box(0));
        return v___x_218_;
    }
}
pub unsafe fn l___private_Std_Do_WP_Adequate_0__OptionT_bind_match__1_splitter___redArg(
    mut v_____do__lift_219_: *mut LeanObject,
    mut v_h__1_220_: *mut LeanObject,
    mut v_h__2_221_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_219_) == 0 {
        let mut v___x_222_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_223_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_220_);
        v___x_222_ = lean_box(0);
        v___x_223_ = lean_apply_1(v_h__2_221_, v___x_222_);
        return v___x_223_;
    } else {
        let mut v_val_224_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_225_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_221_);
        v_val_224_ = lean_ctor_get(v_____do__lift_219_, 0);
        lean_inc(v_val_224_);
        lean_dec_ref_known(v_____do__lift_219_, 1);
        v___x_225_ = lean_apply_1(v_h__1_220_, v_val_224_);
        return v___x_225_;
    }
}
pub unsafe fn l___private_Std_Do_WP_Adequate_0__OptionT_bind_match__1_splitter(
    mut v_00_u03b1_226_: *mut LeanObject,
    mut v_motive_227_: *mut LeanObject,
    mut v_____do__lift_228_: *mut LeanObject,
    mut v_h__1_229_: *mut LeanObject,
    mut v_h__2_230_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_228_) == 0 {
        let mut v___x_231_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_232_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_229_);
        v___x_231_ = lean_box(0);
        v___x_232_ = lean_apply_1(v_h__2_230_, v___x_231_);
        return v___x_232_;
    } else {
        let mut v_val_233_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_234_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_230_);
        v_val_233_ = lean_ctor_get(v_____do__lift_228_, 0);
        lean_inc(v_val_233_);
        lean_dec_ref_known(v_____do__lift_228_, 1);
        v___x_234_ = lean_apply_1(v_h__1_229_, v_val_233_);
        return v___x_234_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Do_WP_Adequate(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Do_WP_Monad(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Do_Internal_Ensures_Def(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Do_WP_Adequate(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Do_WP_Adequate(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Do_WP_Monad(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Do_Internal_Ensures_Def(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Do_WP_Adequate(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Do_WP_Adequate(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Do_WP_Adequate(builtin);
}
