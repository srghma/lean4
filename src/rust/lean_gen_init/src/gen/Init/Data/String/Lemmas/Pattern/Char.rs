// Lean compiler output
// Module: Init.Data.String.Lemmas.Pattern.Char
// Imports: Init.Data.String.Pattern.Char Init.Data.String.Lemmas.Pattern.Basic Init.Data.String.Slice Init.Data.String.Lemmas.Pattern.Pred Init.Data.String.Search Init.Data.String.Slice Init.Data.String.Pattern.Char Init.Data.String.Search Init.Data.Option.Lemmas Init.Data.String.Lemmas.Basic Init.Data.String.Lemmas.Order Init.Data.Order.Lemmas Init.Data.String.OrderInstances Init.Omega Init.Data.String.Lemmas.FindPos
use crate::r#gen::Init::Data::Option::Lemmas::{
    initialize_Init_Data_Option_Lemmas, runtime_initialize_Init_Data_Option_Lemmas,
};
use crate::r#gen::Init::Data::Order::Lemmas::{
    initialize_Init_Data_Order_Lemmas, runtime_initialize_Init_Data_Order_Lemmas,
};
use crate::r#gen::Init::Data::String::Lemmas::Basic::{
    initialize_Init_Data_String_Lemmas_Basic, runtime_initialize_Init_Data_String_Lemmas_Basic,
};
use crate::r#gen::Init::Data::String::Lemmas::FindPos::{
    initialize_Init_Data_String_Lemmas_FindPos, runtime_initialize_Init_Data_String_Lemmas_FindPos,
};
use crate::r#gen::Init::Data::String::Lemmas::Order::{
    initialize_Init_Data_String_Lemmas_Order, runtime_initialize_Init_Data_String_Lemmas_Order,
};
use crate::r#gen::Init::Data::String::Lemmas::Pattern::Basic::{
    initialize_Init_Data_String_Lemmas_Pattern_Basic,
    runtime_initialize_Init_Data_String_Lemmas_Pattern_Basic,
};
use crate::r#gen::Init::Data::String::Lemmas::Pattern::Pred::{
    initialize_Init_Data_String_Lemmas_Pattern_Pred,
    runtime_initialize_Init_Data_String_Lemmas_Pattern_Pred,
};
use crate::r#gen::Init::Data::String::OrderInstances::{
    initialize_Init_Data_String_OrderInstances, runtime_initialize_Init_Data_String_OrderInstances,
};
use crate::r#gen::Init::Data::String::Pattern::Char::{
    initialize_Init_Data_String_Pattern_Char, runtime_initialize_Init_Data_String_Pattern_Char,
};
use crate::r#gen::Init::Data::String::Search::{
    initialize_Init_Data_String_Search, runtime_initialize_Init_Data_String_Search,
};
use crate::r#gen::Init::Data::String::Slice::{
    initialize_Init_Data_String_Slice, runtime_initialize_Init_Data_String_Slice,
};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
pub unsafe fn l_String_Slice_Pattern_Model_Char_instPatternModelChar(
    mut v_c_28_: u32,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_29_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_29_ = crate::leanh::lean_box(0);
    return v___x_29_;
}
pub unsafe fn l_String_Slice_Pattern_Model_Char_instPatternModelChar___boxed(
    mut v_c_30_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_c_boxed_31_: u32 = 0;
    let mut v_res_32_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_31_ = crate::leanh::lean_unbox_uint32(v_c_30_);
    crate::leanh::lean_dec(v_c_30_);
    v_res_32_ = l_String_Slice_Pattern_Model_Char_instPatternModelChar(v_c_boxed_31_);
    return v_res_32_;
}
pub unsafe fn l___private_Init_Data_String_Lemmas_Pattern_Char_0__String_Slice_Pos_skipWhile_match__1_splitter___redArg(
    mut v_x_33_: *mut crate::leanh::LeanObject,
    mut v_h__1_34_: *mut crate::leanh::LeanObject,
    mut v_h__2_35_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_33_) == 0 {
        let mut v___x_36_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_37_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_34_);
        v___x_36_ = crate::leanh::lean_box(0);
        v___x_37_ = crate::leanh::lean_apply_1(v_h__2_35_, v___x_36_);
        return v___x_37_;
    } else {
        let mut v_val_38_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_39_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_35_);
        v_val_38_ = crate::leanh::lean_ctor_get(v_x_33_, 0);
        crate::leanh::lean_inc(v_val_38_);
        crate::leanh::lean_dec_ref_known(v_x_33_, 1);
        v___x_39_ = crate::leanh::lean_apply_1(v_h__1_34_, v_val_38_);
        return v___x_39_;
    }
}
pub unsafe fn l___private_Init_Data_String_Lemmas_Pattern_Char_0__String_Slice_Pos_skipWhile_match__1_splitter(
    mut v_s_40_: *mut crate::leanh::LeanObject,
    mut v_motive_41_: *mut crate::leanh::LeanObject,
    mut v_x_42_: *mut crate::leanh::LeanObject,
    mut v_h__1_43_: *mut crate::leanh::LeanObject,
    mut v_h__2_44_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_42_) == 0 {
        let mut v___x_45_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_46_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_43_);
        v___x_45_ = crate::leanh::lean_box(0);
        v___x_46_ = crate::leanh::lean_apply_1(v_h__2_44_, v___x_45_);
        return v___x_46_;
    } else {
        let mut v_val_47_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_48_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_44_);
        v_val_47_ = crate::leanh::lean_ctor_get(v_x_42_, 0);
        crate::leanh::lean_inc(v_val_47_);
        crate::leanh::lean_dec_ref_known(v_x_42_, 1);
        v___x_48_ = crate::leanh::lean_apply_1(v_h__1_43_, v_val_47_);
        return v___x_48_;
    }
}
pub unsafe fn l___private_Init_Data_String_Lemmas_Pattern_Char_0__String_Slice_Pos_skipWhile_match__1_splitter___boxed(
    mut v_s_49_: *mut crate::leanh::LeanObject,
    mut v_motive_50_: *mut crate::leanh::LeanObject,
    mut v_x_51_: *mut crate::leanh::LeanObject,
    mut v_h__1_52_: *mut crate::leanh::LeanObject,
    mut v_h__2_53_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_54_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_54_ = l___private_Init_Data_String_Lemmas_Pattern_Char_0__String_Slice_Pos_skipWhile_match__1_splitter(v_s_49_, v_motive_50_, v_x_51_, v_h__1_52_, v_h__2_53_);
    crate::leanh::lean_dec_ref(v_s_49_);
    return v_res_54_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_String_Lemmas_Pattern_Char(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_String_Pattern_Char(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_Pattern_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Slice(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_Pattern_Pred(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Search(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Slice(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Pattern_Char(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Search(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_Order(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Order_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_OrderInstances(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_FindPos(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_String_Lemmas_Pattern_Char(
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
pub unsafe fn initialize_Init_Data_String_Lemmas_Pattern_Char(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_String_Pattern_Char(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Lemmas_Pattern_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Slice(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Lemmas_Pattern_Pred(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Search(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Slice(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Pattern_Char(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Search(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Option_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Lemmas_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Lemmas_Order(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Order_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_OrderInstances(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Lemmas_FindPos(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_Pattern_Char(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_String_Lemmas_Pattern_Char(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_String_Lemmas_Pattern_Char(builtin);
}
