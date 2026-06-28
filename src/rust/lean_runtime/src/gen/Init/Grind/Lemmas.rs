// Lean compiler output
// Module: Init.Grind.Lemmas
// Imports: Init.Grind.Ring.Basic Init.NotationExtra Init.ByCases Init.Classical Init.Data.Bool
use crate::r#gen::Init::ByCases::{initialize_Init_ByCases, runtime_initialize_Init_ByCases};
use crate::r#gen::Init::Classical::{initialize_Init_Classical, runtime_initialize_Init_Classical};
use crate::r#gen::Init::Data::Bool::{
    initialize_Init_Data_Bool, runtime_initialize_Init_Data_Bool,
};
use crate::r#gen::Init::Grind::Ring::Basic::{
    initialize_Init_Grind_Ring_Basic, runtime_initialize_Init_Grind_Ring_Basic,
};
use crate::r#gen::Init::NotationExtra::{
    initialize_Init_NotationExtra, runtime_initialize_Init_NotationExtra,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_apply_1, lean_box, lean_dec_ref, lean_io_result_is_error,
    lean_io_result_mk_ok,
};
pub unsafe fn l_Lean_Grind_intro__with__eq___redArg(
    mut v_h_19_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_20_: *mut LeanObject = core::ptr::null_mut();
    v___x_20_ = lean_apply_1(v_h_19_, lean_box(0));
    return v___x_20_;
}
pub unsafe fn l_Lean_Grind_intro__with__eq(
    mut v_p_21_: *mut LeanObject,
    mut v_p_x27_22_: *mut LeanObject,
    mut v_q_23_: *mut LeanObject,
    mut v_he_24_: *mut LeanObject,
    mut v_h_25_: *mut LeanObject,
    mut v_hp_26_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_27_: *mut LeanObject = core::ptr::null_mut();
    v___x_27_ = lean_apply_1(v_h_25_, lean_box(0));
    return v___x_27_;
}
pub unsafe fn l_Lean_Grind_intro__with__eq_x27___redArg(
    mut v_h_28_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_29_: *mut LeanObject = core::ptr::null_mut();
    v___x_29_ = lean_apply_1(v_h_28_, lean_box(0));
    return v___x_29_;
}
pub unsafe fn l_Lean_Grind_intro__with__eq_x27(
    mut v_p_30_: *mut LeanObject,
    mut v_p_x27_31_: *mut LeanObject,
    mut v_q_32_: *mut LeanObject,
    mut v_he_33_: *mut LeanObject,
    mut v_h_34_: *mut LeanObject,
    mut v_hp_35_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_36_: *mut LeanObject = core::ptr::null_mut();
    v___x_36_ = lean_apply_1(v_h_34_, lean_box(0));
    return v___x_36_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Grind_Lemmas(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Grind_Ring_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_NotationExtra(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_ByCases(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Classical(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Bool(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Grind_Lemmas(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Grind_Lemmas(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Grind_Ring_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_NotationExtra(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_ByCases(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Classical(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Bool(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Grind_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Grind_Lemmas(builtin);
}
