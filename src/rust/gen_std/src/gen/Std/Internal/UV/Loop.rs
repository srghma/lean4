// Lean compiler output
// Module: Std.Internal.UV.Loop
// Imports: Init.System.Promise
use crate::ffi::{lean_uv_event_loop_alive, lean_uv_event_loop_configure};
use crate::r#gen::Init::System::Promise::{
    initialize_Init_System_Promise, runtime_initialize_Init_System_Promise,
};
pub unsafe fn l_Std_Internal_UV_Loop_configure___boxed(
    mut v_options_12_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_13_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_14_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_14_ = lean_uv_event_loop_configure(v_options_12_);
    return v_res_14_;
}
pub unsafe fn l_Std_Internal_UV_Loop_alive___boxed(
    mut v_a_00___x40___internal___hyg_16_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_17_: u8 = 0;
    let mut v_r_18_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_17_ = lean_uv_event_loop_alive();
    v_r_18_ = leanh::lean_box((v_res_17_) as usize);
    return v_r_18_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Internal_UV_Loop(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_System_Promise(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Internal_UV_Loop(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Internal_UV_Loop(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_System_Promise(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Internal_UV_Loop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Internal_UV_Loop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Internal_UV_Loop(builtin);
}