// Lean compiler output
// Module: Std.Data.ExtTreeMap.Lemmas
// Imports: Std.Data.ExtDTreeMap.Lemmas Std.Data.ExtTreeMap.Basic Init.Data.List.Pairwise
use crate::r#gen::Init::Data::List::Pairwise::{
    initialize_Init_Data_List_Pairwise, runtime_initialize_Init_Data_List_Pairwise,
};
use crate::r#gen::Std::Data::ExtDTreeMap::Lemmas::{
    initialize_Std_Data_ExtDTreeMap_Lemmas, runtime_initialize_Std_Data_ExtDTreeMap_Lemmas,
};
use crate::r#gen::Std::Data::ExtTreeMap::Basic::{
    initialize_Std_Data_ExtTreeMap_Basic, runtime_initialize_Std_Data_ExtTreeMap_Basic,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_apply_1, lean_box, lean_ctor_get, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_inc, lean_io_result_is_error, lean_io_result_mk_ok, lean_obj_tag,
};
pub unsafe fn l___private_Std_Data_ExtTreeMap_Lemmas_0__GetElem_x3f_match__1_splitter___redArg(
    mut v_x_17_: *mut LeanObject,
    mut v_h__1_18_: *mut LeanObject,
    mut v_h__2_19_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_17_) == 0 {
        let mut v___x_20_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_21_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_18_);
        v___x_20_ = lean_box(0);
        v___x_21_ = lean_apply_1(v_h__2_19_, v___x_20_);
        return v___x_21_;
    } else {
        let mut v_val_22_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_23_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_19_);
        v_val_22_ = lean_ctor_get(v_x_17_, 0);
        lean_inc(v_val_22_);
        lean_dec_ref_known(v_x_17_, 1);
        v___x_23_ = lean_apply_1(v_h__1_18_, v_val_22_);
        return v___x_23_;
    }
}
pub unsafe fn l___private_Std_Data_ExtTreeMap_Lemmas_0__GetElem_x3f_match__1_splitter(
    mut v_elem_24_: *mut LeanObject,
    mut v_motive_25_: *mut LeanObject,
    mut v_x_26_: *mut LeanObject,
    mut v_h__1_27_: *mut LeanObject,
    mut v_h__2_28_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_26_) == 0 {
        let mut v___x_29_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_30_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_27_);
        v___x_29_ = lean_box(0);
        v___x_30_ = lean_apply_1(v_h__2_28_, v___x_29_);
        return v___x_30_;
    } else {
        let mut v_val_31_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_32_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_28_);
        v_val_31_ = lean_ctor_get(v_x_26_, 0);
        lean_inc(v_val_31_);
        lean_dec_ref_known(v_x_26_, 1);
        v___x_32_ = lean_apply_1(v_h__1_27_, v_val_31_);
        return v___x_32_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_ExtTreeMap_Lemmas(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_ExtDTreeMap_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_ExtTreeMap_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Pairwise(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_ExtTreeMap_Lemmas(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Data_ExtTreeMap_Lemmas(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_ExtDTreeMap_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Data_ExtTreeMap_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_Pairwise(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_ExtTreeMap_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Data_ExtTreeMap_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Data_ExtTreeMap_Lemmas(builtin);
}
