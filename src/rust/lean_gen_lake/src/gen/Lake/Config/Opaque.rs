// Lean compiler output
// Module: Lake.Config.Opaque
// Imports: Init.Prelude Lake.Util.OpaqueType Lake.Util.OpaqueType
use crate::r#gen::Init::Prelude::{initialize_Init_Prelude, runtime_initialize_Init_Prelude};
use crate::r#gen::Lake::Util::OpaqueType::{
    initialize_Lake_Util_OpaqueType, runtime_initialize_Lake_Util_OpaqueType,
};
pub static mut l___private_Lake_Config_Opaque_0__Lake_OpaqueWorkspace_nonemptyType:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l___private_Lake_Config_Opaque_0__Lake_OpaqueWorkspace_nonemptyType()
-> *mut crate::leanh::LeanObject {
    let mut v___x_8_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8_ = crate::leanh::lean_box(0);
    return v___x_8_;
}
pub unsafe fn l___private_Lake_Config_Opaque_0__Lake_OpaqueTargetConfig_nonemptyType(
    mut v_pkgName_9_: *mut crate::leanh::LeanObject,
    mut v_name_10_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_11_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_11_ = crate::leanh::lean_box(0);
    return v___x_11_;
}
pub unsafe fn l___private_Lake_Config_Opaque_0__Lake_OpaqueTargetConfig_nonemptyType___boxed(
    mut v_pkgName_12_: *mut crate::leanh::LeanObject,
    mut v_name_13_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_14_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_14_ = l___private_Lake_Config_Opaque_0__Lake_OpaqueTargetConfig_nonemptyType(
        v_pkgName_12_,
        v_name_13_,
    );
    crate::leanh::lean_dec(v_name_13_);
    crate::leanh::lean_dec(v_pkgName_12_);
    return v_res_14_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Config_Opaque(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Prelude(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_OpaqueType(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l___private_Lake_Config_Opaque_0__Lake_OpaqueWorkspace_nonemptyType =
        _init_l___private_Lake_Config_Opaque_0__Lake_OpaqueWorkspace_nonemptyType();
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Config_Opaque(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    res = runtime_initialize_Lake_Util_OpaqueType(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Config_Opaque(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Prelude(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Util_OpaqueType(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Util_OpaqueType(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_Opaque(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_Config_Opaque(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lake_Config_Opaque(builtin);
}
