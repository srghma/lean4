// Lean compiler output
// Module: Lake.Config.Opaque
// Imports: Init.Prelude Lake.Util.OpaqueType Lake.Util.OpaqueType
use crate::r#gen::Init::Prelude::{initialize_Init_Prelude, runtime_initialize_Init_Prelude};
use crate::r#gen::Lake::Util::OpaqueType::{
    initialize_Lake_Util_OpaqueType, meta_initialize_Lake_Util_OpaqueType,
    runtime_initialize_Lake_Util_OpaqueType,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_box, lean_dec, lean_dec_ref, lean_io_result_is_error,
    lean_io_result_mk_ok,
};
pub static mut l___private_Lake_Config_Opaque_0__Lake_OpaqueWorkspace_nonemptyType:
    *mut LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l___private_Lake_Config_Opaque_0__Lake_OpaqueWorkspace_nonemptyType()
-> *mut LeanObject {
    let mut v___x_8_: *mut LeanObject = core::ptr::null_mut();
    v___x_8_ = lean_box(0);
    return v___x_8_;
}
pub unsafe fn l___private_Lake_Config_Opaque_0__Lake_OpaqueTargetConfig_nonemptyType(
    mut v_pkgName_9_: *mut LeanObject,
    mut v_name_10_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_11_: *mut LeanObject = core::ptr::null_mut();
    v___x_11_ = lean_box(0);
    return v___x_11_;
}
pub unsafe fn l___private_Lake_Config_Opaque_0__Lake_OpaqueTargetConfig_nonemptyType___boxed(
    mut v_pkgName_12_: *mut LeanObject,
    mut v_name_13_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_14_: *mut LeanObject = core::ptr::null_mut();
    v_res_14_ = l___private_Lake_Config_Opaque_0__Lake_OpaqueTargetConfig_nonemptyType(
        v_pkgName_12_,
        v_name_13_,
    );
    lean_dec(v_name_13_);
    lean_dec(v_pkgName_12_);
    return v_res_14_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Config_Opaque(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Prelude(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_OpaqueType(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l___private_Lake_Config_Opaque_0__Lake_OpaqueWorkspace_nonemptyType =
        _init_l___private_Lake_Config_Opaque_0__Lake_OpaqueWorkspace_nonemptyType();
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Config_Opaque(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    res = runtime_initialize_Lake_Util_OpaqueType(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Config_Opaque(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Prelude(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Util_OpaqueType(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_Opaque(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lake_Config_Opaque(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lake_Config_Opaque(builtin);
}
