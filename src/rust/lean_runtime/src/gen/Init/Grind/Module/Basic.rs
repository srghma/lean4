// Lean compiler output
// Module: Init.Grind.Module.Basic
// Imports: Init.Grind.ToInt Init.Grind.ToInt
use crate::r#gen::Init::Grind::ToInt::{
    initialize_Init_Grind_ToInt, runtime_initialize_Init_Grind_ToInt,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_get, lean_ctor_set,
    lean_dec_ref, lean_inc, lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok,
};
pub unsafe fn l_Lean_Grind_IntModule_toNatModule___redArg(
    mut v_I_14_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toAddCommGroup_15_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nsmul_16_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toAddCommMonoid_17_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_18_: *mut LeanObject = core::ptr::null_mut();
    v_toAddCommGroup_15_ = lean_ctor_get(v_I_14_, 0);
    v_nsmul_16_ = lean_ctor_get(v_I_14_, 1);
    v_toAddCommMonoid_17_ = lean_ctor_get(v_toAddCommGroup_15_, 0);
    lean_inc(v_nsmul_16_);
    lean_inc_ref(v_toAddCommMonoid_17_);
    v___x_18_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_18_, 0, v_toAddCommMonoid_17_);
    lean_ctor_set(v___x_18_, 1, v_nsmul_16_);
    return v___x_18_;
}
pub unsafe fn l_Lean_Grind_IntModule_toNatModule___redArg___boxed(
    mut v_I_19_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_20_: *mut LeanObject = core::ptr::null_mut();
    v_res_20_ = l_Lean_Grind_IntModule_toNatModule___redArg(v_I_19_);
    lean_dec_ref(v_I_19_);
    return v_res_20_;
}
pub unsafe fn l_Lean_Grind_IntModule_toNatModule(
    mut v_M_21_: *mut LeanObject,
    mut v_I_22_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_23_: *mut LeanObject = core::ptr::null_mut();
    v___x_23_ = l_Lean_Grind_IntModule_toNatModule___redArg(v_I_22_);
    return v___x_23_;
}
pub unsafe fn l_Lean_Grind_IntModule_toNatModule___boxed(
    mut v_M_24_: *mut LeanObject,
    mut v_I_25_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_26_: *mut LeanObject = core::ptr::null_mut();
    v_res_26_ = l_Lean_Grind_IntModule_toNatModule(v_M_24_, v_I_25_);
    lean_dec_ref(v_I_25_);
    return v_res_26_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Grind_Module_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Grind_ToInt(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Grind_Module_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Grind_Module_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Grind_ToInt(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_Module_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Grind_Module_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Grind_Module_Basic(builtin);
}
