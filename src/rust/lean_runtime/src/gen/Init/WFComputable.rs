// Lean compiler output
// Module: Init.WFComputable
// Imports: Init.WF Init.NotationExtra Init.WFTactics
use crate::r#gen::Init::NotationExtra::{
    initialize_Init_NotationExtra, runtime_initialize_Init_NotationExtra,
};
use crate::r#gen::Init::WF::{initialize_Init_WF, runtime_initialize_Init_WF};
use crate::r#gen::Init::WFTactics::{initialize_Init_WFTactics, runtime_initialize_Init_WFTactics};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_apply_2, lean_apply_3, lean_box,
    lean_closure_set, lean_dec_ref, lean_inc, lean_io_result_is_error, lean_io_result_mk_ok,
};
pub unsafe fn l_Acc_wfRel(
    mut v_00_u03b1_71_: *mut LeanObject,
    mut v_r_72_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_73_: *mut LeanObject = core::ptr::null_mut();
    v___x_73_ = lean_box(0);
    return v___x_73_;
}
pub unsafe fn l_Acc_recC___redArg(
    mut v_intro_74_: *mut LeanObject,
    mut v_a_75_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_76_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_77_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_intro_74_);
    v___f_76_ = lean_alloc_closure(l_Acc_recC___redArg___lam__0 as *mut core::ffi::c_void, 3, 1);
    lean_closure_set(v___f_76_, 0, v_intro_74_);
    v___x_77_ = lean_apply_3(v_intro_74_, v_a_75_, lean_box(0), v___f_76_);
    return v___x_77_;
}
pub unsafe fn l_Acc_recC___redArg___lam__0(
    mut v_intro_78_: *mut LeanObject,
    mut v_x_79_: *mut LeanObject,
    mut v_hr_80_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_81_: *mut LeanObject = core::ptr::null_mut();
    v___x_81_ = l_Acc_recC___redArg(v_intro_78_, v_x_79_);
    return v___x_81_;
}
pub unsafe fn l_Acc_recC(
    mut v_00_u03b1_82_: *mut LeanObject,
    mut v_r_83_: *mut LeanObject,
    mut v_motive_84_: *mut LeanObject,
    mut v_intro_85_: *mut LeanObject,
    mut v_a_86_: *mut LeanObject,
    mut v_t_87_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_88_: *mut LeanObject = core::ptr::null_mut();
    v___x_88_ = l_Acc_recC___redArg(v_intro_85_, v_a_86_);
    return v___x_88_;
}
pub unsafe fn l_Acc_ndrecC___redArg(
    mut v_m_89_: *mut LeanObject,
    mut v_a_90_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_91_: *mut LeanObject = core::ptr::null_mut();
    v___x_91_ = l_Acc_recC___redArg(v_m_89_, v_a_90_);
    return v___x_91_;
}
pub unsafe fn l_Acc_ndrecC(
    mut v_00_u03b1_92_: *mut LeanObject,
    mut v_r_93_: *mut LeanObject,
    mut v_C_94_: *mut LeanObject,
    mut v_m_95_: *mut LeanObject,
    mut v_a_96_: *mut LeanObject,
    mut v_n_97_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_98_: *mut LeanObject = core::ptr::null_mut();
    v___x_98_ = l_Acc_recC___redArg(v_m_95_, v_a_96_);
    return v___x_98_;
}
pub unsafe fn l_Acc_ndrecOnC___redArg(
    mut v_a_99_: *mut LeanObject,
    mut v_m_100_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_101_: *mut LeanObject = core::ptr::null_mut();
    v___x_101_ = l_Acc_recC___redArg(v_m_100_, v_a_99_);
    return v___x_101_;
}
pub unsafe fn l_Acc_ndrecOnC(
    mut v_00_u03b1_102_: *mut LeanObject,
    mut v_r_103_: *mut LeanObject,
    mut v_C_104_: *mut LeanObject,
    mut v_a_105_: *mut LeanObject,
    mut v_n_106_: *mut LeanObject,
    mut v_m_107_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_108_: *mut LeanObject = core::ptr::null_mut();
    v___x_108_ = l_Acc_recC___redArg(v_m_107_, v_a_105_);
    return v___x_108_;
}
pub unsafe fn l_WellFounded_fixFC___redArg___lam__0(
    mut v_F_109_: *mut LeanObject,
    mut v_x_u2081_110_: *mut LeanObject,
    mut v_h_111_: *mut LeanObject,
    mut v_ih_112_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_113_: *mut LeanObject = core::ptr::null_mut();
    v___x_113_ = lean_apply_2(v_F_109_, v_x_u2081_110_, v_ih_112_);
    return v___x_113_;
}
pub unsafe fn l_WellFounded_fixFC___redArg(
    mut v_F_114_: *mut LeanObject,
    mut v_x_115_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_117_: *mut LeanObject = core::ptr::null_mut();
    v___f_116_ = lean_alloc_closure(
        l_WellFounded_fixFC___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_116_, 0, v_F_114_);
    v___x_117_ = l_Acc_recC___redArg(v___f_116_, v_x_115_);
    return v___x_117_;
}
pub unsafe fn l_WellFounded_fixFC(
    mut v_00_u03b1_118_: *mut LeanObject,
    mut v_r_119_: *mut LeanObject,
    mut v_C_120_: *mut LeanObject,
    mut v_F_121_: *mut LeanObject,
    mut v_x_122_: *mut LeanObject,
    mut v_a_123_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_125_: *mut LeanObject = core::ptr::null_mut();
    v___f_124_ = lean_alloc_closure(
        l_WellFounded_fixFC___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_124_, 0, v_F_121_);
    v___x_125_ = l_Acc_recC___redArg(v___f_124_, v_x_122_);
    return v___x_125_;
}
pub unsafe fn l_WellFounded_fixC___redArg(
    mut v_F_126_: *mut LeanObject,
    mut v_x_127_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_129_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_F_126_);
    v___f_128_ = lean_alloc_closure(
        l_WellFounded_fixC___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_128_, 0, v_F_126_);
    v___x_129_ = lean_apply_2(v_F_126_, v_x_127_, v___f_128_);
    return v___x_129_;
}
pub unsafe fn l_WellFounded_fixC___redArg___lam__0(
    mut v_F_130_: *mut LeanObject,
    mut v_y_131_: *mut LeanObject,
    mut v_x_132_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_133_: *mut LeanObject = core::ptr::null_mut();
    v___x_133_ = l_WellFounded_fixC___redArg(v_F_130_, v_y_131_);
    return v___x_133_;
}
pub unsafe fn l_WellFounded_fixC(
    mut v_00_u03b1_134_: *mut LeanObject,
    mut v_C_135_: *mut LeanObject,
    mut v_r_136_: *mut LeanObject,
    mut v_hwf_137_: *mut LeanObject,
    mut v_F_138_: *mut LeanObject,
    mut v_x_139_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_140_: *mut LeanObject = core::ptr::null_mut();
    v___x_140_ = l_WellFounded_fixC___redArg(v_F_138_, v_x_139_);
    return v___x_140_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_WFComputable(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_WF(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_NotationExtra(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_WFTactics(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_WFComputable(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_WFComputable(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_WF(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_NotationExtra(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_WFTactics(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_WFComputable(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_WFComputable(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_WFComputable(builtin);
}
