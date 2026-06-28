// Lean compiler output
// Module: Init.Data.List.Scan.Lemmas
// Imports: Init.Data.List.Scan.Basic Init.Data.List.Lemmas Init.Data.List.Scan.Basic Init.Data.List.TakeDrop Init.Data.Option.Lemmas Init.Data.Nat.Lemmas
use crate::r#gen::Init::Data::List::Lemmas::{
    initialize_Init_Data_List_Lemmas, runtime_initialize_Init_Data_List_Lemmas,
};
use crate::r#gen::Init::Data::List::Scan::Basic::{
    initialize_Init_Data_List_Scan_Basic, runtime_initialize_Init_Data_List_Scan_Basic,
};
use crate::r#gen::Init::Data::List::TakeDrop::{
    initialize_Init_Data_List_TakeDrop, runtime_initialize_Init_Data_List_TakeDrop,
};
use crate::r#gen::Init::Data::Nat::Lemmas::{
    initialize_Init_Data_Nat_Lemmas, runtime_initialize_Init_Data_Nat_Lemmas,
};
use crate::r#gen::Init::Data::Option::Lemmas::{
    initialize_Init_Data_Option_Lemmas, runtime_initialize_Init_Data_Option_Lemmas,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_apply_2, lean_apply_4, lean_box, lean_ctor_get, lean_dec,
    lean_dec_ref, lean_dec_ref_known, lean_inc, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_obj_tag,
};
pub unsafe fn l___private_Init_Data_List_Scan_Lemmas_0__List_scanAuxM_go_match__1_splitter___redArg(
    mut v_x_22_: *mut LeanObject,
    mut v_x_23_: *mut LeanObject,
    mut v_x_24_: *mut LeanObject,
    mut v_h__1_25_: *mut LeanObject,
    mut v_h__2_26_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_22_) == 0 {
        let mut v___x_27_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_26_);
        v___x_27_ = lean_apply_2(v_h__1_25_, v_x_23_, v_x_24_);
        return v___x_27_;
    } else {
        let mut v_head_28_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_29_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_30_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_25_);
        v_head_28_ = lean_ctor_get(v_x_22_, 0);
        lean_inc(v_head_28_);
        v_tail_29_ = lean_ctor_get(v_x_22_, 1);
        lean_inc(v_tail_29_);
        lean_dec_ref_known(v_x_22_, 2);
        v___x_30_ = lean_apply_4(v_h__2_26_, v_head_28_, v_tail_29_, v_x_23_, v_x_24_);
        return v___x_30_;
    }
}
pub unsafe fn l___private_Init_Data_List_Scan_Lemmas_0__List_scanAuxM_go_match__1_splitter(
    mut v_00_u03b2_31_: *mut LeanObject,
    mut v_00_u03b1_32_: *mut LeanObject,
    mut v_motive_33_: *mut LeanObject,
    mut v_x_34_: *mut LeanObject,
    mut v_x_35_: *mut LeanObject,
    mut v_x_36_: *mut LeanObject,
    mut v_h__1_37_: *mut LeanObject,
    mut v_h__2_38_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_34_) == 0 {
        let mut v___x_39_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_38_);
        v___x_39_ = lean_apply_2(v_h__1_37_, v_x_35_, v_x_36_);
        return v___x_39_;
    } else {
        let mut v_head_40_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_41_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_42_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_37_);
        v_head_40_ = lean_ctor_get(v_x_34_, 0);
        lean_inc(v_head_40_);
        v_tail_41_ = lean_ctor_get(v_x_34_, 1);
        lean_inc(v_tail_41_);
        lean_dec_ref_known(v_x_34_, 2);
        v___x_42_ = lean_apply_4(v_h__2_38_, v_head_40_, v_tail_41_, v_x_35_, v_x_36_);
        return v___x_42_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_List_Scan_Lemmas(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_List_Scan_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_TakeDrop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_List_Scan_Lemmas(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_List_Scan_Lemmas(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_List_Scan_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_TakeDrop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Option_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Scan_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_List_Scan_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_List_Scan_Lemmas(builtin);
}
