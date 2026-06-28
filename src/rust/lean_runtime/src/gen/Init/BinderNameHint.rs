// Lean compiler output
// Module: Init.BinderNameHint
// Imports: Init.Prelude Init.Tactics
use crate::r#gen::Init::Prelude::{initialize_Init_Prelude, runtime_initialize_Init_Prelude};
use crate::r#gen::Init::Tactics::{initialize_Init_Tactics, runtime_initialize_Init_Tactics};
pub unsafe fn l_binderNameHint___redArg(
    mut v_e_17_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_e_17_);
    return v_e_17_;
}
pub unsafe fn l_binderNameHint___redArg___boxed(
    mut v_e_18_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_19_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_19_ = l_binderNameHint___redArg(v_e_18_);
    crate::leanh::lean_dec(v_e_18_);
    return v_res_19_;
}
pub unsafe fn l_binderNameHint(
    mut v_00_u03b1_20_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_21_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_22_: *mut crate::leanh::LeanObject,
    mut v_v_23_: *mut crate::leanh::LeanObject,
    mut v_binder_24_: *mut crate::leanh::LeanObject,
    mut v_e_25_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_e_25_);
    return v_e_25_;
}
pub unsafe fn l_binderNameHint___boxed(
    mut v_00_u03b1_26_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_27_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_28_: *mut crate::leanh::LeanObject,
    mut v_v_29_: *mut crate::leanh::LeanObject,
    mut v_binder_30_: *mut crate::leanh::LeanObject,
    mut v_e_31_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_32_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_32_ = l_binderNameHint(
        v_00_u03b1_26_,
        v_00_u03b2_27_,
        v_00_u03b3_28_,
        v_v_29_,
        v_binder_30_,
        v_e_31_,
    );
    crate::leanh::lean_dec(v_e_31_);
    crate::leanh::lean_dec(v_binder_30_);
    crate::leanh::lean_dec(v_v_29_);
    return v_res_32_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_BinderNameHint(builtin: u8) -> *mut crate::leanh::LeanObject {
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
    res = runtime_initialize_Init_Tactics(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_BinderNameHint(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_BinderNameHint(builtin: u8) -> *mut crate::leanh::LeanObject {
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
    res = initialize_Init_Tactics(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_BinderNameHint(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_BinderNameHint(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_BinderNameHint(builtin);
}
