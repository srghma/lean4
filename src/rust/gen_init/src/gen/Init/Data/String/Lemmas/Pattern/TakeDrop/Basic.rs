// Lean compiler output
// Module: Init.Data.String.Lemmas.Pattern.TakeDrop.Basic
// Imports: Init.Data.String.Slice Init.Data.String.TakeDrop Init.Data.String.Lemmas.Pattern.Basic Init.Data.String.Slice Init.Data.String.TakeDrop Init.Data.String.Lemmas.Intercalate Init.Data.String.Lemmas.Order Init.Data.String.Lemmas.Basic Init.Data.String.OrderInstances Init.ByCases
use crate::r#gen::Init::ByCases::{initialize_Init_ByCases, runtime_initialize_Init_ByCases};
use crate::r#gen::Init::Data::String::Lemmas::Basic::{
    initialize_Init_Data_String_Lemmas_Basic, runtime_initialize_Init_Data_String_Lemmas_Basic,
};
use crate::r#gen::Init::Data::String::Lemmas::Intercalate::{
    initialize_Init_Data_String_Lemmas_Intercalate,
    runtime_initialize_Init_Data_String_Lemmas_Intercalate,
};
use crate::r#gen::Init::Data::String::Lemmas::Order::{
    initialize_Init_Data_String_Lemmas_Order, runtime_initialize_Init_Data_String_Lemmas_Order,
};
use crate::r#gen::Init::Data::String::Lemmas::Pattern::Basic::{
    initialize_Init_Data_String_Lemmas_Pattern_Basic,
    runtime_initialize_Init_Data_String_Lemmas_Pattern_Basic,
};
use crate::r#gen::Init::Data::String::OrderInstances::{
    initialize_Init_Data_String_OrderInstances, runtime_initialize_Init_Data_String_OrderInstances,
};
use crate::r#gen::Init::Data::String::Slice::{
    initialize_Init_Data_String_Slice, runtime_initialize_Init_Data_String_Slice,
};
use crate::r#gen::Init::Data::String::TakeDrop::{
    initialize_Init_Data_String_TakeDrop, runtime_initialize_Init_Data_String_TakeDrop,
};
pub unsafe fn l___private_Init_Data_String_Lemmas_Pattern_TakeDrop_Basic_0__String_Slice_Pos_skipWhile_match__1_splitter___redArg(
    mut v_x_23_: *mut leanh::LeanObject,
    mut v_h__1_24_: *mut leanh::LeanObject,
    mut v_h__2_25_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_23_) == 0 {
        let mut v___x_26_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_27_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_24_);
        v___x_26_ = leanh::lean_box(0);
        v___x_27_ = leanh::lean_apply_1(v_h__2_25_, v___x_26_);
        return v___x_27_;
    } else {
        let mut v_val_28_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_29_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_25_);
        v_val_28_ = leanh::lean_ctor_get(v_x_23_, 0);
        leanh::lean_inc(v_val_28_);
        leanh::lean_dec_ref_known(v_x_23_, 1);
        v___x_29_ = leanh::lean_apply_1(v_h__1_24_, v_val_28_);
        return v___x_29_;
    }
}
pub unsafe fn l___private_Init_Data_String_Lemmas_Pattern_TakeDrop_Basic_0__String_Slice_Pos_skipWhile_match__1_splitter(
    mut v_s_30_: *mut leanh::LeanObject,
    mut v_motive_31_: *mut leanh::LeanObject,
    mut v_x_32_: *mut leanh::LeanObject,
    mut v_h__1_33_: *mut leanh::LeanObject,
    mut v_h__2_34_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_32_) == 0 {
        let mut v___x_35_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_36_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_33_);
        v___x_35_ = leanh::lean_box(0);
        v___x_36_ = leanh::lean_apply_1(v_h__2_34_, v___x_35_);
        return v___x_36_;
    } else {
        let mut v_val_37_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_38_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_34_);
        v_val_37_ = leanh::lean_ctor_get(v_x_32_, 0);
        leanh::lean_inc(v_val_37_);
        leanh::lean_dec_ref_known(v_x_32_, 1);
        v___x_38_ = leanh::lean_apply_1(v_h__1_33_, v_val_37_);
        return v___x_38_;
    }
}
pub unsafe fn l___private_Init_Data_String_Lemmas_Pattern_TakeDrop_Basic_0__String_Slice_Pos_skipWhile_match__1_splitter___boxed(
    mut v_s_39_: *mut leanh::LeanObject,
    mut v_motive_40_: *mut leanh::LeanObject,
    mut v_x_41_: *mut leanh::LeanObject,
    mut v_h__1_42_: *mut leanh::LeanObject,
    mut v_h__2_43_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_44_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_44_ = l___private_Init_Data_String_Lemmas_Pattern_TakeDrop_Basic_0__String_Slice_Pos_skipWhile_match__1_splitter(v_s_39_, v_motive_40_, v_x_41_, v_h__1_42_, v_h__2_43_);
    leanh::lean_dec_ref(v_s_39_);
    return v_res_44_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_String_Lemmas_Pattern_TakeDrop_Basic(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_String_Slice(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_TakeDrop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_Pattern_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Slice(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_TakeDrop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_Intercalate(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_Order(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_OrderInstances(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_ByCases(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_String_Lemmas_Pattern_TakeDrop_Basic(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_String_Lemmas_Pattern_TakeDrop_Basic(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_String_Slice(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_TakeDrop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Lemmas_Pattern_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Slice(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_TakeDrop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Lemmas_Intercalate(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Lemmas_Order(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Lemmas_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_OrderInstances(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_ByCases(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_Pattern_TakeDrop_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_String_Lemmas_Pattern_TakeDrop_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_String_Lemmas_Pattern_TakeDrop_Basic(builtin);
}