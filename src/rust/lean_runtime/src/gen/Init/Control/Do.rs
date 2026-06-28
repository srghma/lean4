// Lean compiler output
// Module: Init.Control.Do
// Imports: Init.Control.Except Init.Control.Option
use crate::r#gen::Init::Control::Except::{
    initialize_Init_Control_Except, runtime_initialize_Init_Control_Except,
};
use crate::r#gen::Init::Control::Option::{
    initialize_Init_Control_Option, runtime_initialize_Init_Control_Option,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_apply_1, lean_apply_2, lean_box,
    lean_ctor_get, lean_ctor_set, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc,
    lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok, lean_obj_tag,
};
pub unsafe fn l_EarlyReturnT_return___redArg(
    mut v_inst_89_: *mut LeanObject,
    mut v_r_90_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_91_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_92_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_93_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_94_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_91_ = lean_ctor_get(v_inst_89_, 0);
    lean_inc_ref(v_toApplicative_91_);
    lean_dec_ref(v_inst_89_);
    v_toPure_92_ = lean_ctor_get(v_toApplicative_91_, 1);
    lean_inc(v_toPure_92_);
    lean_dec_ref(v_toApplicative_91_);
    v___x_93_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_93_, 0, v_r_90_);
    v___x_94_ = lean_apply_2(v_toPure_92_, lean_box(0), v___x_93_);
    return v___x_94_;
}
pub unsafe fn l_EarlyReturnT_return(
    mut v_00_u03c1_95_: *mut LeanObject,
    mut v_m_96_: *mut LeanObject,
    mut v_00_u03b1_97_: *mut LeanObject,
    mut v_inst_98_: *mut LeanObject,
    mut v_r_99_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_103_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_100_ = lean_ctor_get(v_inst_98_, 0);
    lean_inc_ref(v_toApplicative_100_);
    lean_dec_ref(v_inst_98_);
    v_toPure_101_ = lean_ctor_get(v_toApplicative_100_, 1);
    lean_inc(v_toPure_101_);
    lean_dec_ref(v_toApplicative_100_);
    v___x_102_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_102_, 0, v_r_99_);
    v___x_103_ = lean_apply_2(v_toPure_101_, lean_box(0), v___x_102_);
    return v___x_103_;
}
pub unsafe fn l_EarlyReturn_runK___redArg(
    mut v_x_104_: *mut LeanObject,
    mut v_ret_105_: *mut LeanObject,
    mut v_pure_106_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_104_) == 0 {
        let mut v_a_107_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_108_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_pure_106_);
        v_a_107_ = lean_ctor_get(v_x_104_, 0);
        lean_inc(v_a_107_);
        lean_dec_ref_known(v_x_104_, 1);
        v___x_108_ = lean_apply_1(v_ret_105_, v_a_107_);
        return v___x_108_;
    } else {
        let mut v_a_109_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_110_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_ret_105_);
        v_a_109_ = lean_ctor_get(v_x_104_, 0);
        lean_inc(v_a_109_);
        lean_dec_ref_known(v_x_104_, 1);
        v___x_110_ = lean_apply_1(v_pure_106_, v_a_109_);
        return v___x_110_;
    }
}
pub unsafe fn l_EarlyReturn_runK(
    mut v_00_u03c1_111_: *mut LeanObject,
    mut v_00_u03b1_112_: *mut LeanObject,
    mut v_00_u03b2_113_: *mut LeanObject,
    mut v_x_114_: *mut LeanObject,
    mut v_ret_115_: *mut LeanObject,
    mut v_pure_116_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_114_) == 0 {
        let mut v_a_117_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_118_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_pure_116_);
        v_a_117_ = lean_ctor_get(v_x_114_, 0);
        lean_inc(v_a_117_);
        lean_dec_ref_known(v_x_114_, 1);
        v___x_118_ = lean_apply_1(v_ret_115_, v_a_117_);
        return v___x_118_;
    } else {
        let mut v_a_119_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_120_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_ret_115_);
        v_a_119_ = lean_ctor_get(v_x_114_, 0);
        lean_inc(v_a_119_);
        lean_dec_ref_known(v_x_114_, 1);
        v___x_120_ = lean_apply_1(v_pure_116_, v_a_119_);
        return v___x_120_;
    }
}
pub unsafe fn l_BreakT_break___redArg(mut v_inst_121_: *mut LeanObject) -> *mut LeanObject {
    let mut v_toApplicative_122_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_125_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_122_ = lean_ctor_get(v_inst_121_, 0);
    lean_inc_ref(v_toApplicative_122_);
    lean_dec_ref(v_inst_121_);
    v_toPure_123_ = lean_ctor_get(v_toApplicative_122_, 1);
    lean_inc(v_toPure_123_);
    lean_dec_ref(v_toApplicative_122_);
    v___x_124_ = lean_box(0);
    v___x_125_ = lean_apply_2(v_toPure_123_, lean_box(0), v___x_124_);
    return v___x_125_;
}
pub unsafe fn l_BreakT_break(
    mut v_00_u03b1_126_: *mut LeanObject,
    mut v_m_127_: *mut LeanObject,
    mut v_inst_128_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_129_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_132_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_129_ = lean_ctor_get(v_inst_128_, 0);
    lean_inc_ref(v_toApplicative_129_);
    lean_dec_ref(v_inst_128_);
    v_toPure_130_ = lean_ctor_get(v_toApplicative_129_, 1);
    lean_inc(v_toPure_130_);
    lean_dec_ref(v_toApplicative_129_);
    v___x_131_ = lean_box(0);
    v___x_132_ = lean_apply_2(v_toPure_130_, lean_box(0), v___x_131_);
    return v___x_132_;
}
pub unsafe fn l_Break_runK___redArg(
    mut v_x_133_: *mut LeanObject,
    mut v_breakK_134_: *mut LeanObject,
    mut v_successK_135_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_133_) == 0 {
        let mut v___x_136_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_137_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_successK_135_);
        v___x_136_ = lean_box(0);
        v___x_137_ = lean_apply_1(v_breakK_134_, v___x_136_);
        return v___x_137_;
    } else {
        let mut v_val_138_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_139_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_breakK_134_);
        v_val_138_ = lean_ctor_get(v_x_133_, 0);
        lean_inc(v_val_138_);
        lean_dec_ref_known(v_x_133_, 1);
        v___x_139_ = lean_apply_1(v_successK_135_, v_val_138_);
        return v___x_139_;
    }
}
pub unsafe fn l_Break_runK(
    mut v_00_u03b1_140_: *mut LeanObject,
    mut v_00_u03b2_141_: *mut LeanObject,
    mut v_x_142_: *mut LeanObject,
    mut v_breakK_143_: *mut LeanObject,
    mut v_successK_144_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_142_) == 0 {
        let mut v___x_145_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_146_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_successK_144_);
        v___x_145_ = lean_box(0);
        v___x_146_ = lean_apply_1(v_breakK_143_, v___x_145_);
        return v___x_146_;
    } else {
        let mut v_val_147_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_148_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_breakK_143_);
        v_val_147_ = lean_ctor_get(v_x_142_, 0);
        lean_inc(v_val_147_);
        lean_dec_ref_known(v_x_142_, 1);
        v___x_148_ = lean_apply_1(v_successK_144_, v_val_147_);
        return v___x_148_;
    }
}
pub unsafe fn l_ContinueT_continue___redArg(mut v_inst_149_: *mut LeanObject) -> *mut LeanObject {
    let mut v_toApplicative_150_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_153_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_150_ = lean_ctor_get(v_inst_149_, 0);
    lean_inc_ref(v_toApplicative_150_);
    lean_dec_ref(v_inst_149_);
    v_toPure_151_ = lean_ctor_get(v_toApplicative_150_, 1);
    lean_inc(v_toPure_151_);
    lean_dec_ref(v_toApplicative_150_);
    v___x_152_ = lean_box(0);
    v___x_153_ = lean_apply_2(v_toPure_151_, lean_box(0), v___x_152_);
    return v___x_153_;
}
pub unsafe fn l_ContinueT_continue(
    mut v_00_u03b1_154_: *mut LeanObject,
    mut v_m_155_: *mut LeanObject,
    mut v_inst_156_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_157_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_160_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_157_ = lean_ctor_get(v_inst_156_, 0);
    lean_inc_ref(v_toApplicative_157_);
    lean_dec_ref(v_inst_156_);
    v_toPure_158_ = lean_ctor_get(v_toApplicative_157_, 1);
    lean_inc(v_toPure_158_);
    lean_dec_ref(v_toApplicative_157_);
    v___x_159_ = lean_box(0);
    v___x_160_ = lean_apply_2(v_toPure_158_, lean_box(0), v___x_159_);
    return v___x_160_;
}
pub unsafe fn l_Continue_runK___redArg(
    mut v_x_161_: *mut LeanObject,
    mut v_continueK_162_: *mut LeanObject,
    mut v_successK_163_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_161_) == 0 {
        let mut v___x_164_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_165_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_successK_163_);
        v___x_164_ = lean_box(0);
        v___x_165_ = lean_apply_1(v_continueK_162_, v___x_164_);
        return v___x_165_;
    } else {
        let mut v_a_166_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_167_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_continueK_162_);
        v_a_166_ = lean_ctor_get(v_x_161_, 0);
        lean_inc(v_a_166_);
        lean_dec_ref_known(v_x_161_, 1);
        v___x_167_ = lean_apply_1(v_successK_163_, v_a_166_);
        return v___x_167_;
    }
}
pub unsafe fn l_Continue_runK(
    mut v_00_u03b1_168_: *mut LeanObject,
    mut v_00_u03b2_169_: *mut LeanObject,
    mut v_x_170_: *mut LeanObject,
    mut v_continueK_171_: *mut LeanObject,
    mut v_successK_172_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_170_) == 0 {
        let mut v___x_173_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_174_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_successK_172_);
        v___x_173_ = lean_box(0);
        v___x_174_ = lean_apply_1(v_continueK_171_, v___x_173_);
        return v___x_174_;
    } else {
        let mut v_a_175_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_176_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_continueK_171_);
        v_a_175_ = lean_ctor_get(v_x_170_, 0);
        lean_inc(v_a_175_);
        lean_dec_ref_known(v_x_170_, 1);
        v___x_176_ = lean_apply_1(v_successK_172_, v_a_175_);
        return v___x_176_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Control_Do(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Control_Except(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Control_Option(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Control_Do(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Control_Do(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Control_Except(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Control_Option(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Control_Do(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Control_Do(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Control_Do(builtin);
}
