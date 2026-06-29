// Lean compiler output
// Module: Std.Internal.UV.DNS
// Imports: Init.System.Promise Init.Data.SInt Std.Net
use crate::r#gen::Init::Data::SInt::{
    initialize_Init_Data_SInt, runtime_initialize_Init_Data_SInt,
};
use crate::r#gen::Init::System::Promise::{
    initialize_Init_System_Promise, runtime_initialize_Init_System_Promise,
};
use crate::r#gen::Std::Net::{initialize_Std_Net, runtime_initialize_Std_Net};
use crate::ffi::{lean_uv_dns_get_info, lean_uv_dns_get_name};
pub unsafe fn l_Std_Internal_UV_DNS_getAddrInfo___boxed(
    mut v_host_20_: *mut crate::leanh::LeanObject,
    mut v_service_21_: *mut crate::leanh::LeanObject,
    mut v_family_22_: *mut crate::leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_23_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_family_boxed_24_: u8 = 0;
    let mut v_res_25_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_family_boxed_24_ = (crate::leanh::lean_unbox(v_family_22_) as u8);
    v_res_25_ = lean_uv_dns_get_info(v_host_20_, v_service_21_, v_family_boxed_24_);
    crate::leanh::lean_dec_ref(v_service_21_);
    crate::leanh::lean_dec_ref(v_host_20_);
    return v_res_25_;
}
pub unsafe fn l_Std_Internal_UV_DNS_getNameInfo___boxed(
    mut v_host_28_: *mut crate::leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_29_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_30_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_30_ = lean_uv_dns_get_name(v_host_28_);
    crate::leanh::lean_dec_ref(v_host_28_);
    return v_res_30_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Internal_UV_DNS(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_System_Promise(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_SInt(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Net(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Internal_UV_DNS(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Internal_UV_DNS(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_System_Promise(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_SInt(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Net(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Internal_UV_DNS(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Internal_UV_DNS(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Internal_UV_DNS(builtin);
}
