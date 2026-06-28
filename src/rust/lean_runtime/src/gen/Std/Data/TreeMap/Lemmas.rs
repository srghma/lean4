// Lean compiler output
// Module: Std.Data.TreeMap.Lemmas
// Imports: Std.Data.DTreeMap.Lemmas Std.Data.TreeMap.AdditionalOperations Init.Data.Array.Perm Init.Data.List.Pairwise
use crate::r#gen::Init::Data::Array::Perm::{
    initialize_Init_Data_Array_Perm, runtime_initialize_Init_Data_Array_Perm,
};
use crate::r#gen::Init::Data::List::Pairwise::{
    initialize_Init_Data_List_Pairwise, runtime_initialize_Init_Data_List_Pairwise,
};
use crate::r#gen::Std::Data::DTreeMap::Lemmas::{
    initialize_Std_Data_DTreeMap_Lemmas, runtime_initialize_Std_Data_DTreeMap_Lemmas,
};
use crate::r#gen::Std::Data::TreeMap::AdditionalOperations::{
    initialize_Std_Data_TreeMap_AdditionalOperations,
    runtime_initialize_Std_Data_TreeMap_AdditionalOperations,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_apply_1, lean_box, lean_ctor_get, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_inc, lean_io_result_is_error, lean_io_result_mk_ok, lean_obj_tag,
};
pub unsafe fn l___private_Std_Data_TreeMap_Lemmas_0__GetElem_x3f_match__1_splitter___redArg(
    mut v_x_25_: *mut LeanObject,
    mut v_h__1_26_: *mut LeanObject,
    mut v_h__2_27_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_25_) == 0 {
        let mut v___x_28_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_29_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_26_);
        v___x_28_ = lean_box(0);
        v___x_29_ = lean_apply_1(v_h__2_27_, v___x_28_);
        return v___x_29_;
    } else {
        let mut v_val_30_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_31_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_27_);
        v_val_30_ = lean_ctor_get(v_x_25_, 0);
        lean_inc(v_val_30_);
        lean_dec_ref_known(v_x_25_, 1);
        v___x_31_ = lean_apply_1(v_h__1_26_, v_val_30_);
        return v___x_31_;
    }
}
pub unsafe fn l___private_Std_Data_TreeMap_Lemmas_0__GetElem_x3f_match__1_splitter(
    mut v_elem_32_: *mut LeanObject,
    mut v_motive_33_: *mut LeanObject,
    mut v_x_34_: *mut LeanObject,
    mut v_h__1_35_: *mut LeanObject,
    mut v_h__2_36_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_34_) == 0 {
        let mut v___x_37_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_38_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_35_);
        v___x_37_ = lean_box(0);
        v___x_38_ = lean_apply_1(v_h__2_36_, v___x_37_);
        return v___x_38_;
    } else {
        let mut v_val_39_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_40_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_36_);
        v_val_39_ = lean_ctor_get(v_x_34_, 0);
        lean_inc(v_val_39_);
        lean_dec_ref_known(v_x_34_, 1);
        v___x_40_ = lean_apply_1(v_h__1_35_, v_val_39_);
        return v___x_40_;
    }
}
pub unsafe fn l_Std_TreeMap_Equiv_instTrans(
    mut v_00_u03b1_41_: *mut LeanObject,
    mut v_00_u03b2_42_: *mut LeanObject,
    mut v_cmp_43_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_44_: *mut LeanObject = core::ptr::null_mut();
    v___x_44_ = lean_box(0);
    return v___x_44_;
}
pub unsafe fn l_Std_TreeMap_Equiv_instTrans___boxed(
    mut v_00_u03b1_45_: *mut LeanObject,
    mut v_00_u03b2_46_: *mut LeanObject,
    mut v_cmp_47_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_48_: *mut LeanObject = core::ptr::null_mut();
    v_res_48_ = l_Std_TreeMap_Equiv_instTrans(v_00_u03b1_45_, v_00_u03b2_46_, v_cmp_47_);
    lean_dec_ref(v_cmp_47_);
    return v_res_48_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_TreeMap_Lemmas(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_DTreeMap_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_TreeMap_AdditionalOperations(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Perm(builtin);
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
pub unsafe fn meta_initialize_Std_Data_TreeMap_Lemmas(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Data_TreeMap_Lemmas(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_DTreeMap_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Data_TreeMap_AdditionalOperations(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Array_Perm(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_Pairwise(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_TreeMap_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Data_TreeMap_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Data_TreeMap_Lemmas(builtin);
}
