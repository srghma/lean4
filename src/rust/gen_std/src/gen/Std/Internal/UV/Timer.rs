// Lean compiler output
// Module: Std.Internal.UV.Timer
// Imports: Init.System.Promise
use crate::ffi::{
    lean_uv_timer_cancel, lean_uv_timer_mk, lean_uv_timer_next, lean_uv_timer_reset,
    lean_uv_timer_stop,
};
use crate::r#gen::Init::System::Promise::{
    initialize_Init_System_Promise, runtime_initialize_Init_System_Promise,
};
pub static mut l___private_Std_Internal_UV_Timer_0__Std_Internal_UV_TimerImpl:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l___private_Std_Internal_UV_Timer_0__Std_Internal_UV_TimerImpl()
-> *mut leanh::LeanObject {
    let mut v___x_31_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_31_ = leanh::lean_box(0);
    return v___x_31_;
}
pub unsafe fn l_Std_Internal_UV_Timer_mk___boxed(
    mut v_timeout_35_: *mut leanh::LeanObject,
    mut v_repeating_36_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_37_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_timeout_boxed_38_: u64 = 0;
    let mut v_repeating_boxed_39_: u8 = 0;
    let mut v_res_40_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_timeout_boxed_38_ = leanh::lean_unbox_uint64(v_timeout_35_);
    leanh::lean_dec_ref(v_timeout_35_);
    v_repeating_boxed_39_ = (leanh::lean_unbox(v_repeating_36_) as u8);
    v_res_40_ = lean_uv_timer_mk(v_timeout_boxed_38_, v_repeating_boxed_39_);
    return v_res_40_;
}
pub unsafe fn l_Std_Internal_UV_Timer_next___boxed(
    mut v_timer_43_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_44_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_45_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_45_ = lean_uv_timer_next(v_timer_43_);
    leanh::lean_dec(v_timer_43_);
    return v_res_45_;
}
pub unsafe fn l_Std_Internal_UV_Timer_reset___boxed(
    mut v_timer_48_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_49_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_50_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_50_ = lean_uv_timer_reset(v_timer_48_);
    leanh::lean_dec(v_timer_48_);
    return v_res_50_;
}
pub unsafe fn l_Std_Internal_UV_Timer_stop___boxed(
    mut v_timer_53_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_54_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_55_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_55_ = lean_uv_timer_stop(v_timer_53_);
    leanh::lean_dec(v_timer_53_);
    return v_res_55_;
}
pub unsafe fn l_Std_Internal_UV_Timer_cancel___boxed(
    mut v_timer_58_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_59_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_60_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_60_ = lean_uv_timer_cancel(v_timer_58_);
    leanh::lean_dec(v_timer_58_);
    return v_res_60_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Internal_UV_Timer(
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
    l___private_Std_Internal_UV_Timer_0__Std_Internal_UV_TimerImpl =
        _init_l___private_Std_Internal_UV_Timer_0__Std_Internal_UV_TimerImpl();
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Internal_UV_Timer(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Internal_UV_Timer(builtin: u8) -> *mut leanh::LeanObject {
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
    res = runtime_initialize_Std_Internal_UV_Timer(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Internal_UV_Timer(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Internal_UV_Timer(builtin);
}