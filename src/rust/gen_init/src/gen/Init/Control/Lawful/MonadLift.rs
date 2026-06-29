// Lean compiler output
// Module: Init.Control.Lawful.MonadLift
// Imports: Init.Control.Lawful.MonadLift.Basic Init.Control.Lawful.MonadLift.Lemmas Init.Control.Lawful.MonadLift.Instances
use crate::r#gen::Init::Control::Lawful::MonadLift::Basic::{
    initialize_Init_Control_Lawful_MonadLift_Basic,
    runtime_initialize_Init_Control_Lawful_MonadLift_Basic,
};
use crate::r#gen::Init::Control::Lawful::MonadLift::Instances::{
    initialize_Init_Control_Lawful_MonadLift_Instances,
    runtime_initialize_Init_Control_Lawful_MonadLift_Instances,
};
use crate::r#gen::Init::Control::Lawful::MonadLift::Lemmas::{
    initialize_Init_Control_Lawful_MonadLift_Lemmas,
    runtime_initialize_Init_Control_Lawful_MonadLift_Lemmas,
};
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Control_Lawful_MonadLift(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Control_Lawful_MonadLift_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Control_Lawful_MonadLift_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Control_Lawful_MonadLift_Instances(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Control_Lawful_MonadLift(
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
pub unsafe fn initialize_Init_Control_Lawful_MonadLift(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Control_Lawful_MonadLift_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Control_Lawful_MonadLift_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Control_Lawful_MonadLift_Instances(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Control_Lawful_MonadLift(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Control_Lawful_MonadLift(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Control_Lawful_MonadLift(builtin);
}
