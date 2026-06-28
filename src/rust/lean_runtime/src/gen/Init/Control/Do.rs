// Lean compiler output
// Module: Init.Control.Do
// Imports: Init.Control.Except Init.Control.Option
use crate::r#gen::Init::Control::Except::{
    initialize_Init_Control_Except, runtime_initialize_Init_Control_Except,
};
use crate::r#gen::Init::Control::Option::{
    initialize_Init_Control_Option, runtime_initialize_Init_Control_Option,
};
pub unsafe fn l_EarlyReturnT_return___redArg(
    mut v_inst_89_: *mut crate::leanh::LeanObject,
    mut v_r_90_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_91_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_92_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_93_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_94_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_91_ = crate::leanh::lean_ctor_get(v_inst_89_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_91_);
    crate::leanh::lean_dec_ref(v_inst_89_);
    v_toPure_92_ = crate::leanh::lean_ctor_get(v_toApplicative_91_, 1);
    crate::leanh::lean_inc(v_toPure_92_);
    crate::leanh::lean_dec_ref(v_toApplicative_91_);
    v___x_93_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_93_, 0, v_r_90_);
    v___x_94_ = crate::leanh::lean_apply_2(v_toPure_92_, crate::leanh::lean_box(0), v___x_93_);
    return v___x_94_;
}
pub unsafe fn l_EarlyReturnT_return(
    mut v_00_u03c1_95_: *mut crate::leanh::LeanObject,
    mut v_m_96_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_97_: *mut crate::leanh::LeanObject,
    mut v_inst_98_: *mut crate::leanh::LeanObject,
    mut v_r_99_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_100_ = crate::leanh::lean_ctor_get(v_inst_98_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_100_);
    crate::leanh::lean_dec_ref(v_inst_98_);
    v_toPure_101_ = crate::leanh::lean_ctor_get(v_toApplicative_100_, 1);
    crate::leanh::lean_inc(v_toPure_101_);
    crate::leanh::lean_dec_ref(v_toApplicative_100_);
    v___x_102_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_102_, 0, v_r_99_);
    v___x_103_ = crate::leanh::lean_apply_2(v_toPure_101_, crate::leanh::lean_box(0), v___x_102_);
    return v___x_103_;
}
pub unsafe fn l_EarlyReturn_runK___redArg(
    mut v_x_104_: *mut crate::leanh::LeanObject,
    mut v_ret_105_: *mut crate::leanh::LeanObject,
    mut v_pure_106_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_104_) == 0 {
        let mut v_a_107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_pure_106_);
        v_a_107_ = crate::leanh::lean_ctor_get(v_x_104_, 0);
        crate::leanh::lean_inc(v_a_107_);
        crate::leanh::lean_dec_ref_known(v_x_104_, 1);
        v___x_108_ = crate::leanh::lean_apply_1(v_ret_105_, v_a_107_);
        return v___x_108_;
    } else {
        let mut v_a_109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_ret_105_);
        v_a_109_ = crate::leanh::lean_ctor_get(v_x_104_, 0);
        crate::leanh::lean_inc(v_a_109_);
        crate::leanh::lean_dec_ref_known(v_x_104_, 1);
        v___x_110_ = crate::leanh::lean_apply_1(v_pure_106_, v_a_109_);
        return v___x_110_;
    }
}
pub unsafe fn l_EarlyReturn_runK(
    mut v_00_u03c1_111_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_112_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_113_: *mut crate::leanh::LeanObject,
    mut v_x_114_: *mut crate::leanh::LeanObject,
    mut v_ret_115_: *mut crate::leanh::LeanObject,
    mut v_pure_116_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_114_) == 0 {
        let mut v_a_117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_pure_116_);
        v_a_117_ = crate::leanh::lean_ctor_get(v_x_114_, 0);
        crate::leanh::lean_inc(v_a_117_);
        crate::leanh::lean_dec_ref_known(v_x_114_, 1);
        v___x_118_ = crate::leanh::lean_apply_1(v_ret_115_, v_a_117_);
        return v___x_118_;
    } else {
        let mut v_a_119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_ret_115_);
        v_a_119_ = crate::leanh::lean_ctor_get(v_x_114_, 0);
        crate::leanh::lean_inc(v_a_119_);
        crate::leanh::lean_dec_ref_known(v_x_114_, 1);
        v___x_120_ = crate::leanh::lean_apply_1(v_pure_116_, v_a_119_);
        return v___x_120_;
    }
}
pub unsafe fn l_BreakT_break___redArg(
    mut v_inst_121_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_122_ = crate::leanh::lean_ctor_get(v_inst_121_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_122_);
    crate::leanh::lean_dec_ref(v_inst_121_);
    v_toPure_123_ = crate::leanh::lean_ctor_get(v_toApplicative_122_, 1);
    crate::leanh::lean_inc(v_toPure_123_);
    crate::leanh::lean_dec_ref(v_toApplicative_122_);
    v___x_124_ = crate::leanh::lean_box(0);
    v___x_125_ = crate::leanh::lean_apply_2(v_toPure_123_, crate::leanh::lean_box(0), v___x_124_);
    return v___x_125_;
}
pub unsafe fn l_BreakT_break(
    mut v_00_u03b1_126_: *mut crate::leanh::LeanObject,
    mut v_m_127_: *mut crate::leanh::LeanObject,
    mut v_inst_128_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_129_ = crate::leanh::lean_ctor_get(v_inst_128_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_129_);
    crate::leanh::lean_dec_ref(v_inst_128_);
    v_toPure_130_ = crate::leanh::lean_ctor_get(v_toApplicative_129_, 1);
    crate::leanh::lean_inc(v_toPure_130_);
    crate::leanh::lean_dec_ref(v_toApplicative_129_);
    v___x_131_ = crate::leanh::lean_box(0);
    v___x_132_ = crate::leanh::lean_apply_2(v_toPure_130_, crate::leanh::lean_box(0), v___x_131_);
    return v___x_132_;
}
pub unsafe fn l_Break_runK___redArg(
    mut v_x_133_: *mut crate::leanh::LeanObject,
    mut v_breakK_134_: *mut crate::leanh::LeanObject,
    mut v_successK_135_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_133_) == 0 {
        let mut v___x_136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_successK_135_);
        v___x_136_ = crate::leanh::lean_box(0);
        v___x_137_ = crate::leanh::lean_apply_1(v_breakK_134_, v___x_136_);
        return v___x_137_;
    } else {
        let mut v_val_138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_breakK_134_);
        v_val_138_ = crate::leanh::lean_ctor_get(v_x_133_, 0);
        crate::leanh::lean_inc(v_val_138_);
        crate::leanh::lean_dec_ref_known(v_x_133_, 1);
        v___x_139_ = crate::leanh::lean_apply_1(v_successK_135_, v_val_138_);
        return v___x_139_;
    }
}
pub unsafe fn l_Break_runK(
    mut v_00_u03b1_140_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_141_: *mut crate::leanh::LeanObject,
    mut v_x_142_: *mut crate::leanh::LeanObject,
    mut v_breakK_143_: *mut crate::leanh::LeanObject,
    mut v_successK_144_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_142_) == 0 {
        let mut v___x_145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_successK_144_);
        v___x_145_ = crate::leanh::lean_box(0);
        v___x_146_ = crate::leanh::lean_apply_1(v_breakK_143_, v___x_145_);
        return v___x_146_;
    } else {
        let mut v_val_147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_breakK_143_);
        v_val_147_ = crate::leanh::lean_ctor_get(v_x_142_, 0);
        crate::leanh::lean_inc(v_val_147_);
        crate::leanh::lean_dec_ref_known(v_x_142_, 1);
        v___x_148_ = crate::leanh::lean_apply_1(v_successK_144_, v_val_147_);
        return v___x_148_;
    }
}
pub unsafe fn l_ContinueT_continue___redArg(
    mut v_inst_149_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_150_ = crate::leanh::lean_ctor_get(v_inst_149_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_150_);
    crate::leanh::lean_dec_ref(v_inst_149_);
    v_toPure_151_ = crate::leanh::lean_ctor_get(v_toApplicative_150_, 1);
    crate::leanh::lean_inc(v_toPure_151_);
    crate::leanh::lean_dec_ref(v_toApplicative_150_);
    v___x_152_ = crate::leanh::lean_box(0);
    v___x_153_ = crate::leanh::lean_apply_2(v_toPure_151_, crate::leanh::lean_box(0), v___x_152_);
    return v___x_153_;
}
pub unsafe fn l_ContinueT_continue(
    mut v_00_u03b1_154_: *mut crate::leanh::LeanObject,
    mut v_m_155_: *mut crate::leanh::LeanObject,
    mut v_inst_156_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_157_ = crate::leanh::lean_ctor_get(v_inst_156_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_157_);
    crate::leanh::lean_dec_ref(v_inst_156_);
    v_toPure_158_ = crate::leanh::lean_ctor_get(v_toApplicative_157_, 1);
    crate::leanh::lean_inc(v_toPure_158_);
    crate::leanh::lean_dec_ref(v_toApplicative_157_);
    v___x_159_ = crate::leanh::lean_box(0);
    v___x_160_ = crate::leanh::lean_apply_2(v_toPure_158_, crate::leanh::lean_box(0), v___x_159_);
    return v___x_160_;
}
pub unsafe fn l_Continue_runK___redArg(
    mut v_x_161_: *mut crate::leanh::LeanObject,
    mut v_continueK_162_: *mut crate::leanh::LeanObject,
    mut v_successK_163_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_161_) == 0 {
        let mut v___x_164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_successK_163_);
        v___x_164_ = crate::leanh::lean_box(0);
        v___x_165_ = crate::leanh::lean_apply_1(v_continueK_162_, v___x_164_);
        return v___x_165_;
    } else {
        let mut v_a_166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_continueK_162_);
        v_a_166_ = crate::leanh::lean_ctor_get(v_x_161_, 0);
        crate::leanh::lean_inc(v_a_166_);
        crate::leanh::lean_dec_ref_known(v_x_161_, 1);
        v___x_167_ = crate::leanh::lean_apply_1(v_successK_163_, v_a_166_);
        return v___x_167_;
    }
}
pub unsafe fn l_Continue_runK(
    mut v_00_u03b1_168_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_169_: *mut crate::leanh::LeanObject,
    mut v_x_170_: *mut crate::leanh::LeanObject,
    mut v_continueK_171_: *mut crate::leanh::LeanObject,
    mut v_successK_172_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_170_) == 0 {
        let mut v___x_173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_successK_172_);
        v___x_173_ = crate::leanh::lean_box(0);
        v___x_174_ = crate::leanh::lean_apply_1(v_continueK_171_, v___x_173_);
        return v___x_174_;
    } else {
        let mut v_a_175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_continueK_171_);
        v_a_175_ = crate::leanh::lean_ctor_get(v_x_170_, 0);
        crate::leanh::lean_inc(v_a_175_);
        crate::leanh::lean_dec_ref_known(v_x_170_, 1);
        v___x_176_ = crate::leanh::lean_apply_1(v_successK_172_, v_a_175_);
        return v___x_176_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Control_Do(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Control_Except(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Control_Option(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Control_Do(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Control_Do(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Control_Except(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Control_Option(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Control_Do(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Control_Do(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Control_Do(builtin);
}
