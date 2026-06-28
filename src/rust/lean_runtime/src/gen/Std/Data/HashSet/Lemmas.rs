// Lean compiler output
// Module: Std.Data.HashSet.Lemmas
// Imports: Std.Data.HashMap.Lemmas Std.Data.HashSet.Basic
use crate::r#gen::Std::Data::HashMap::Lemmas::{
    initialize_Std_Data_HashMap_Lemmas, runtime_initialize_Std_Data_HashMap_Lemmas,
};
use crate::r#gen::Std::Data::HashSet::Basic::{
    initialize_Std_Data_HashSet_Basic, runtime_initialize_Std_Data_HashSet_Basic,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_box, lean_dec_ref, lean_io_result_is_error,
    lean_io_result_mk_ok,
};
pub unsafe fn l_Std_HashSet_Equiv_instTrans(
    mut v_00_u03b1_9_: *mut LeanObject,
    mut v_x_10_: *mut LeanObject,
    mut v_x_11_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_12_: *mut LeanObject = core::ptr::null_mut();
    v___x_12_ = lean_box(0);
    return v___x_12_;
}
pub unsafe fn l_Std_HashSet_Equiv_instTrans___boxed(
    mut v_00_u03b1_13_: *mut LeanObject,
    mut v_x_14_: *mut LeanObject,
    mut v_x_15_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_16_: *mut LeanObject = core::ptr::null_mut();
    v_res_16_ = l_Std_HashSet_Equiv_instTrans(v_00_u03b1_13_, v_x_14_, v_x_15_);
    lean_dec_ref(v_x_15_);
    lean_dec_ref(v_x_14_);
    return v_res_16_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_HashSet_Lemmas(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_HashMap_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_HashSet_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_HashSet_Lemmas(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Data_HashSet_Lemmas(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_HashMap_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Data_HashSet_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_HashSet_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Data_HashSet_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Data_HashSet_Lemmas(builtin);
}
