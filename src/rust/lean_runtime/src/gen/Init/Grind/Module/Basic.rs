// Lean compiler output
// Module: Init.Grind.Module.Basic
// Imports: Init.Grind.ToInt Init.Grind.ToInt
use crate::r#gen::Init::Grind::ToInt::{
    initialize_Init_Grind_ToInt, runtime_initialize_Init_Grind_ToInt,
};
pub unsafe fn l_Lean_Grind_IntModule_toNatModule___redArg(
    mut v_I_14_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toAddCommGroup_15_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nsmul_16_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toAddCommMonoid_17_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_18_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toAddCommGroup_15_ = crate::leanh::lean_ctor_get(v_I_14_, 0);
    v_nsmul_16_ = crate::leanh::lean_ctor_get(v_I_14_, 1);
    v_toAddCommMonoid_17_ = crate::leanh::lean_ctor_get(v_toAddCommGroup_15_, 0);
    crate::leanh::lean_inc(v_nsmul_16_);
    crate::leanh::lean_inc_ref(v_toAddCommMonoid_17_);
    v___x_18_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_18_, 0, v_toAddCommMonoid_17_);
    crate::leanh::lean_ctor_set(v___x_18_, 1, v_nsmul_16_);
    return v___x_18_;
}
pub unsafe fn l_Lean_Grind_IntModule_toNatModule___redArg___boxed(
    mut v_I_19_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_20_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_20_ = l_Lean_Grind_IntModule_toNatModule___redArg(v_I_19_);
    crate::leanh::lean_dec_ref(v_I_19_);
    return v_res_20_;
}
pub unsafe fn l_Lean_Grind_IntModule_toNatModule(
    mut v_M_21_: *mut crate::leanh::LeanObject,
    mut v_I_22_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_23_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_23_ = l_Lean_Grind_IntModule_toNatModule___redArg(v_I_22_);
    return v___x_23_;
}
pub unsafe fn l_Lean_Grind_IntModule_toNatModule___boxed(
    mut v_M_24_: *mut crate::leanh::LeanObject,
    mut v_I_25_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_26_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_26_ = l_Lean_Grind_IntModule_toNatModule(v_M_24_, v_I_25_);
    crate::leanh::lean_dec_ref(v_I_25_);
    return v_res_26_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Grind_Module_Basic(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Grind_ToInt(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_ToInt(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Grind_Module_Basic(
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
pub unsafe fn initialize_Init_Grind_Module_Basic(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Grind_ToInt(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Grind_ToInt(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_Module_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Grind_Module_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Grind_Module_Basic(builtin);
}
