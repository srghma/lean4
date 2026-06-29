// Lean compiler output
// Module: Lake.Config.Context
// Imports: Init.Control.Id Lake.Config.Opaque
use crate::r#gen::Init::Control::Id::{
    initialize_Init_Control_Id, runtime_initialize_Init_Control_Id,
};
use crate::r#gen::Lake::Config::Opaque::{
    initialize_Lake_Config_Opaque, runtime_initialize_Lake_Config_Opaque,
};
pub unsafe fn l_Lake_LakeT_run___redArg(
    mut v_ctx_16_: *mut crate::leanh::LeanObject,
    mut v_self_17_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_18_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_18_ = crate::leanh::lean_apply_1(v_self_17_, v_ctx_16_);
    return v___x_18_;
}
pub unsafe fn l_Lake_LakeT_run(
    mut v_m_19_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_20_: *mut crate::leanh::LeanObject,
    mut v_ctx_21_: *mut crate::leanh::LeanObject,
    mut v_self_22_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_23_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_23_ = crate::leanh::lean_apply_1(v_self_22_, v_ctx_21_);
    return v___x_23_;
}
pub unsafe fn l_Lake_LakeM_run___redArg(
    mut v_ctx_24_: *mut crate::leanh::LeanObject,
    mut v_self_25_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_26_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_26_ = crate::leanh::lean_apply_1(v_self_25_, v_ctx_24_);
    return v___x_26_;
}
pub unsafe fn l_Lake_LakeM_run(
    mut v_00_u03b1_27_: *mut crate::leanh::LeanObject,
    mut v_ctx_28_: *mut crate::leanh::LeanObject,
    mut v_self_29_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_30_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_30_ = crate::leanh::lean_apply_1(v_self_29_, v_ctx_28_);
    return v___x_30_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Config_Context(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Control_Id(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_Opaque(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Config_Context(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Config_Context(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Control_Id(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Config_Opaque(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_Context(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_Config_Context(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lake_Config_Context(builtin);
}
