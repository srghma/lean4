// Lean compiler output
// Module: Std.Internal.UV.Signal
// Imports: Init.System.Promise Init.Data.SInt Std.Net
use crate::ffi::{
    lean_uv_signal_cancel, lean_uv_signal_mk, lean_uv_signal_next, lean_uv_signal_stop,
};
use crate::r#gen::Init::Data::SInt::{
    initialize_Init_Data_SInt, runtime_initialize_Init_Data_SInt,
};
use crate::r#gen::Init::System::Promise::{
    initialize_Init_System_Promise, runtime_initialize_Init_System_Promise,
};
use crate::r#gen::Std::Net::{initialize_Std_Net, runtime_initialize_Std_Net};
pub static mut l___private_Std_Internal_UV_Signal_0__Std_Internal_UV_SignalImpl:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l___private_Std_Internal_UV_Signal_0__Std_Internal_UV_SignalImpl()
-> *mut leanh::LeanObject {
    let mut v___x_26_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_26_ = leanh::lean_box(0);
    return v___x_26_;
}
pub unsafe fn l_Std_Internal_UV_Signal_mk___boxed(
    mut v_signum_30_: *mut leanh::LeanObject,
    mut v_repeating_31_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_32_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_signum_boxed_33_: u32 = 0;
    let mut v_repeating_boxed_34_: u8 = 0;
    let mut v_res_35_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_signum_boxed_33_ = leanh::lean_unbox_uint32(v_signum_30_);
    leanh::lean_dec(v_signum_30_);
    v_repeating_boxed_34_ = (leanh::lean_unbox(v_repeating_31_) as u8);
    v_res_35_ = lean_uv_signal_mk(v_signum_boxed_33_, v_repeating_boxed_34_);
    return v_res_35_;
}
pub unsafe fn l_Std_Internal_UV_Signal_next___boxed(
    mut v_signal_38_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_39_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_40_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_40_ = lean_uv_signal_next(v_signal_38_);
    leanh::lean_dec(v_signal_38_);
    return v_res_40_;
}
pub unsafe fn l_Std_Internal_UV_Signal_stop___boxed(
    mut v_signal_43_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_44_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_45_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_45_ = lean_uv_signal_stop(v_signal_43_);
    leanh::lean_dec(v_signal_43_);
    return v_res_45_;
}
pub unsafe fn l_Std_Internal_UV_Signal_cancel___boxed(
    mut v_signal_48_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_49_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_50_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_50_ = lean_uv_signal_cancel(v_signal_48_);
    leanh::lean_dec(v_signal_48_);
    return v_res_50_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Internal_UV_Signal(
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
    res = runtime_initialize_Init_Data_SInt(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Net(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l___private_Std_Internal_UV_Signal_0__Std_Internal_UV_SignalImpl =
        _init_l___private_Std_Internal_UV_Signal_0__Std_Internal_UV_SignalImpl();
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Internal_UV_Signal(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Internal_UV_Signal(builtin: u8) -> *mut leanh::LeanObject {
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
    res = initialize_Init_Data_SInt(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Net(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Internal_UV_Signal(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Internal_UV_Signal(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Internal_UV_Signal(builtin);
}