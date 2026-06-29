// Lean compiler output
// Module: Init.Data.Iterators.Lemmas.Monadic.Basic
// Imports: Init.Data.Iterators.Basic
use crate::r#gen::Init::Data::Iterators::Basic::{
    initialize_Init_Data_Iterators_Basic, runtime_initialize_Init_Data_Iterators_Basic,
};
pub unsafe fn l_Std_IterM_inductSteps___redArg___lam__0___boxed(
    mut v_step_64_: *mut crate::leanh::LeanObject,
    mut v_it_x27_65_: *mut crate::leanh::LeanObject,
    mut v_x_66_: *mut crate::leanh::LeanObject,
    mut v_x_67_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_68_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_68_ =
        l_Std_IterM_inductSteps___redArg___lam__0(v_step_64_, v_it_x27_65_, v_x_66_, v_x_67_);
    crate::leanh::lean_dec(v_x_66_);
    return v_res_68_;
}
pub unsafe fn l_Std_IterM_inductSteps___redArg___lam__1(
    mut v_step_69_: *mut crate::leanh::LeanObject,
    mut v_it_x27_70_: *mut crate::leanh::LeanObject,
    mut v_x_71_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_72_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_72_ = l_Std_IterM_inductSteps___redArg(v_step_69_, v_it_x27_70_);
    return v___x_72_;
}
pub unsafe fn l_Std_IterM_inductSteps___redArg(
    mut v_step_73_: *mut crate::leanh::LeanObject,
    mut v_it_74_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_75_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_76_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_77_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_n(v_step_73_, 2);
    v___f_75_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_inductSteps___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_75_, 0, v_step_73_);
    v___f_76_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_inductSteps___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_76_, 0, v_step_73_);
    v___x_77_ = crate::leanh::lean_apply_3(v_step_73_, v_it_74_, v___f_75_, v___f_76_);
    return v___x_77_;
}
pub unsafe fn l_Std_IterM_inductSteps___redArg___lam__0(
    mut v_step_78_: *mut crate::leanh::LeanObject,
    mut v_it_x27_79_: *mut crate::leanh::LeanObject,
    mut v_x_80_: *mut crate::leanh::LeanObject,
    mut v_x_81_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_82_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_82_ = l_Std_IterM_inductSteps___redArg(v_step_78_, v_it_x27_79_);
    return v___x_82_;
}
pub unsafe fn l_Std_IterM_inductSteps(
    mut v_00_u03b1_83_: *mut crate::leanh::LeanObject,
    mut v_m_84_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_85_: *mut crate::leanh::LeanObject,
    mut v_inst_86_: *mut crate::leanh::LeanObject,
    mut v_inst_87_: *mut crate::leanh::LeanObject,
    mut v_motive_88_: *mut crate::leanh::LeanObject,
    mut v_step_89_: *mut crate::leanh::LeanObject,
    mut v_it_90_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_91_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_91_ = l_Std_IterM_inductSteps___redArg(v_step_89_, v_it_90_);
    return v___x_91_;
}
pub unsafe fn l_Std_IterM_inductSteps___boxed(
    mut v_00_u03b1_92_: *mut crate::leanh::LeanObject,
    mut v_m_93_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_94_: *mut crate::leanh::LeanObject,
    mut v_inst_95_: *mut crate::leanh::LeanObject,
    mut v_inst_96_: *mut crate::leanh::LeanObject,
    mut v_motive_97_: *mut crate::leanh::LeanObject,
    mut v_step_98_: *mut crate::leanh::LeanObject,
    mut v_it_99_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_100_ = l_Std_IterM_inductSteps(
        v_00_u03b1_92_,
        v_m_93_,
        v_00_u03b2_94_,
        v_inst_95_,
        v_inst_96_,
        v_motive_97_,
        v_step_98_,
        v_it_99_,
    );
    crate::leanh::lean_dec(v_inst_95_);
    return v_res_100_;
}
pub unsafe fn l_Std_IterM_inductSkips___redArg(
    mut v_step_101_: *mut crate::leanh::LeanObject,
    mut v_it_102_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_step_101_);
    v___f_103_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_inductSkips___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_103_, 0, v_step_101_);
    v___x_104_ = crate::leanh::lean_apply_2(v_step_101_, v_it_102_, v___f_103_);
    return v___x_104_;
}
pub unsafe fn l_Std_IterM_inductSkips___redArg___lam__0(
    mut v_step_105_: *mut crate::leanh::LeanObject,
    mut v_it_x27_106_: *mut crate::leanh::LeanObject,
    mut v_x_107_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_108_ = l_Std_IterM_inductSkips___redArg(v_step_105_, v_it_x27_106_);
    return v___x_108_;
}
pub unsafe fn l_Std_IterM_inductSkips(
    mut v_00_u03b1_109_: *mut crate::leanh::LeanObject,
    mut v_m_110_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_111_: *mut crate::leanh::LeanObject,
    mut v_inst_112_: *mut crate::leanh::LeanObject,
    mut v_inst_113_: *mut crate::leanh::LeanObject,
    mut v_motive_114_: *mut crate::leanh::LeanObject,
    mut v_step_115_: *mut crate::leanh::LeanObject,
    mut v_it_116_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_117_ = l_Std_IterM_inductSkips___redArg(v_step_115_, v_it_116_);
    return v___x_117_;
}
pub unsafe fn l_Std_IterM_inductSkips___boxed(
    mut v_00_u03b1_118_: *mut crate::leanh::LeanObject,
    mut v_m_119_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_120_: *mut crate::leanh::LeanObject,
    mut v_inst_121_: *mut crate::leanh::LeanObject,
    mut v_inst_122_: *mut crate::leanh::LeanObject,
    mut v_motive_123_: *mut crate::leanh::LeanObject,
    mut v_step_124_: *mut crate::leanh::LeanObject,
    mut v_it_125_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_126_ = l_Std_IterM_inductSkips(
        v_00_u03b1_118_,
        v_m_119_,
        v_00_u03b2_120_,
        v_inst_121_,
        v_inst_122_,
        v_motive_123_,
        v_step_124_,
        v_it_125_,
    );
    crate::leanh::lean_dec(v_inst_121_);
    return v_res_126_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Iterators_Lemmas_Monadic_Basic(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Iterators_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Iterators_Lemmas_Monadic_Basic(
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
pub unsafe fn initialize_Init_Data_Iterators_Lemmas_Monadic_Basic(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Iterators_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Monadic_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Iterators_Lemmas_Monadic_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_Iterators_Lemmas_Monadic_Basic(builtin);
}
