// Lean compiler output
// Module: Std.Data.HashMap.Lemmas
// Imports: Std.Data.DHashMap.Lemmas Std.Data.HashMap.AdditionalOperations Std.Data.DHashMap.Basic Init.Data.List.Pairwise
use crate::r#gen::Init::Data::List::Pairwise::{
    initialize_Init_Data_List_Pairwise, runtime_initialize_Init_Data_List_Pairwise,
};
use crate::r#gen::Std::Data::DHashMap::Basic::{
    initialize_Std_Data_DHashMap_Basic, runtime_initialize_Std_Data_DHashMap_Basic,
};
use crate::r#gen::Std::Data::DHashMap::Lemmas::{
    initialize_Std_Data_DHashMap_Lemmas, runtime_initialize_Std_Data_DHashMap_Lemmas,
};
use crate::r#gen::Std::Data::HashMap::AdditionalOperations::{
    initialize_Std_Data_HashMap_AdditionalOperations,
    runtime_initialize_Std_Data_HashMap_AdditionalOperations,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_apply_1, lean_box, lean_ctor_get, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_inc, lean_io_result_is_error, lean_io_result_mk_ok, lean_obj_tag,
};
pub unsafe fn l___private_Std_Data_HashMap_Lemmas_0__GetElem_x3f_match__1_splitter___redArg(
    mut v_x_27_: *mut LeanObject,
    mut v_h__1_28_: *mut LeanObject,
    mut v_h__2_29_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_27_) == 0 {
        let mut v___x_30_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_31_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_28_);
        v___x_30_ = lean_box(0);
        v___x_31_ = lean_apply_1(v_h__2_29_, v___x_30_);
        return v___x_31_;
    } else {
        let mut v_val_32_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_33_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_29_);
        v_val_32_ = lean_ctor_get(v_x_27_, 0);
        lean_inc(v_val_32_);
        lean_dec_ref_known(v_x_27_, 1);
        v___x_33_ = lean_apply_1(v_h__1_28_, v_val_32_);
        return v___x_33_;
    }
}
pub unsafe fn l___private_Std_Data_HashMap_Lemmas_0__GetElem_x3f_match__1_splitter(
    mut v_elem_34_: *mut LeanObject,
    mut v_motive_35_: *mut LeanObject,
    mut v_x_36_: *mut LeanObject,
    mut v_h__1_37_: *mut LeanObject,
    mut v_h__2_38_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_36_) == 0 {
        let mut v___x_39_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_40_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_37_);
        v___x_39_ = lean_box(0);
        v___x_40_ = lean_apply_1(v_h__2_38_, v___x_39_);
        return v___x_40_;
    } else {
        let mut v_val_41_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_42_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_38_);
        v_val_41_ = lean_ctor_get(v_x_36_, 0);
        lean_inc(v_val_41_);
        lean_dec_ref_known(v_x_36_, 1);
        v___x_42_ = lean_apply_1(v_h__1_37_, v_val_41_);
        return v___x_42_;
    }
}
pub unsafe fn l_Std_HashMap_Equiv_instTrans(
    mut v_00_u03b1_43_: *mut LeanObject,
    mut v_00_u03b2_44_: *mut LeanObject,
    mut v_x_45_: *mut LeanObject,
    mut v_x_46_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_47_: *mut LeanObject = core::ptr::null_mut();
    v___x_47_ = lean_box(0);
    return v___x_47_;
}
pub unsafe fn l_Std_HashMap_Equiv_instTrans___boxed(
    mut v_00_u03b1_48_: *mut LeanObject,
    mut v_00_u03b2_49_: *mut LeanObject,
    mut v_x_50_: *mut LeanObject,
    mut v_x_51_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_52_: *mut LeanObject = core::ptr::null_mut();
    v_res_52_ = l_Std_HashMap_Equiv_instTrans(v_00_u03b1_48_, v_00_u03b2_49_, v_x_50_, v_x_51_);
    lean_dec_ref(v_x_51_);
    lean_dec_ref(v_x_50_);
    return v_res_52_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_HashMap_Lemmas(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_DHashMap_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_HashMap_AdditionalOperations(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_DHashMap_Basic(builtin);
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
pub unsafe fn meta_initialize_Std_Data_HashMap_Lemmas(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Data_HashMap_Lemmas(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_DHashMap_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Data_HashMap_AdditionalOperations(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Data_DHashMap_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_Pairwise(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_HashMap_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Data_HashMap_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Data_HashMap_Lemmas(builtin);
}
