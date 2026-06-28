// Lean compiler output
// Module: Lean.ToLevel
// Imports: Lean.Expr
use crate::r#gen::Lean::Expr::{initialize_Lean_Expr, runtime_initialize_Lean_Expr};
use crate::r#gen::Lean::Level::{
    l_Lean_Level_imax___override, l_Lean_Level_max___override, l_Lean_Level_succ___override,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_box, lean_dec_ref, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_mark_persistent,
};
pub static mut l_Lean_instToLevel: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l_Lean_instToLevel() -> *mut LeanObject {
    let mut v___x_10_: *mut LeanObject = core::ptr::null_mut();
    v___x_10_ = lean_box(0);
    return v___x_10_;
}
pub unsafe fn l_Lean_instToLevel__1(mut v_inst_11_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_12_: *mut LeanObject = core::ptr::null_mut();
    v___x_12_ = l_Lean_Level_succ___override(v_inst_11_);
    return v___x_12_;
}
pub unsafe fn l_Lean_ToLevel_max(
    mut v_inst_13_: *mut LeanObject,
    mut v_inst_14_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_15_: *mut LeanObject = core::ptr::null_mut();
    v___x_15_ = l_Lean_Level_max___override(v_inst_13_, v_inst_14_);
    return v___x_15_;
}
pub unsafe fn l_Lean_ToLevel_imax(
    mut v_inst_16_: *mut LeanObject,
    mut v_inst_17_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_18_: *mut LeanObject = core::ptr::null_mut();
    v___x_18_ = l_Lean_Level_imax___override(v_inst_16_, v_inst_17_);
    return v___x_18_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_ToLevel(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Expr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_instToLevel = _init_l_Lean_instToLevel();
    lean_mark_persistent(l_Lean_instToLevel);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_ToLevel(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_ToLevel(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Expr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_ToLevel(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_ToLevel(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_ToLevel(builtin);
}
