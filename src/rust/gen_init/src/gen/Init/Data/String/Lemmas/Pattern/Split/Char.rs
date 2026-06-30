// Lean compiler output
// Module: Init.Data.String.Lemmas.Pattern.Split.Char
// Imports: Init.Data.String.Slice Init.Data.String.Search Init.Data.List.SplitOn.Basic Init.Data.String.Lemmas.Pattern.Split.Basic Init.Data.String.Lemmas.Pattern.Char Init.Data.String.Lemmas.Pattern.Split.Basic Init.Data.String.Termination Init.Data.Order.Lemmas Init.Data.Iterators.Lemmas.Combinators.FilterMap Init.Data.String.Lemmas.Pattern.Split.Basic Init.Data.String.Lemmas.Pattern.Split.Pred Init.Data.String.Lemmas.Pattern.Char Init.ByCases Init.Data.String.OrderInstances Init.Data.String.Lemmas.Order Init.Data.String.Lemmas.Intercalate Init.Data.List.SplitOn.Lemmas Init.Data.String.Lemmas.Slice
use crate::r#gen::Init::ByCases::{initialize_Init_ByCases, runtime_initialize_Init_ByCases};
use crate::r#gen::Init::Data::Iterators::Lemmas::Combinators::FilterMap::{
    initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap,
    runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap,
};
use crate::r#gen::Init::Data::List::SplitOn::Basic::{
    initialize_Init_Data_List_SplitOn_Basic, runtime_initialize_Init_Data_List_SplitOn_Basic,
};
use crate::r#gen::Init::Data::List::SplitOn::Lemmas::{
    initialize_Init_Data_List_SplitOn_Lemmas, runtime_initialize_Init_Data_List_SplitOn_Lemmas,
};
use crate::r#gen::Init::Data::Order::Lemmas::{
    initialize_Init_Data_Order_Lemmas, runtime_initialize_Init_Data_Order_Lemmas,
};
use crate::r#gen::Init::Data::String::Lemmas::Intercalate::{
    initialize_Init_Data_String_Lemmas_Intercalate,
    runtime_initialize_Init_Data_String_Lemmas_Intercalate,
};
use crate::r#gen::Init::Data::String::Lemmas::Order::{
    initialize_Init_Data_String_Lemmas_Order, runtime_initialize_Init_Data_String_Lemmas_Order,
};
use crate::r#gen::Init::Data::String::Lemmas::Pattern::Char::{
    initialize_Init_Data_String_Lemmas_Pattern_Char,
    runtime_initialize_Init_Data_String_Lemmas_Pattern_Char,
};
use crate::r#gen::Init::Data::String::Lemmas::Pattern::Split::Basic::{
    initialize_Init_Data_String_Lemmas_Pattern_Split_Basic,
    runtime_initialize_Init_Data_String_Lemmas_Pattern_Split_Basic,
};
use crate::r#gen::Init::Data::String::Lemmas::Pattern::Split::Pred::{
    initialize_Init_Data_String_Lemmas_Pattern_Split_Pred,
    runtime_initialize_Init_Data_String_Lemmas_Pattern_Split_Pred,
};
use crate::r#gen::Init::Data::String::Lemmas::Slice::{
    initialize_Init_Data_String_Lemmas_Slice, runtime_initialize_Init_Data_String_Lemmas_Slice,
};
use crate::r#gen::Init::Data::String::OrderInstances::{
    initialize_Init_Data_String_OrderInstances, runtime_initialize_Init_Data_String_OrderInstances,
};
use crate::r#gen::Init::Data::String::Search::{
    initialize_Init_Data_String_Search, runtime_initialize_Init_Data_String_Search,
};
use crate::r#gen::Init::Data::String::Slice::{
    initialize_Init_Data_String_Slice, runtime_initialize_Init_Data_String_Slice,
};
use crate::r#gen::Init::Data::String::Termination::{
    initialize_Init_Data_String_Termination, runtime_initialize_Init_Data_String_Termination,
};
pub unsafe fn l___private_Init_Data_String_Lemmas_Pattern_Split_Char_0__String_Slice_Pattern_Model_split_match__1_splitter___redArg(
    mut v_x_21_: *mut leanh::LeanObject,
    mut v_h__1_22_: *mut leanh::LeanObject,
    mut v_h__2_23_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_21_) == 0 {
        let mut v___x_24_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_22_);
        v___x_24_ = leanh::lean_apply_1(v_h__2_23_, leanh::lean_box(0));
        return v___x_24_;
    } else {
        let mut v_val_25_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_26_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_23_);
        v_val_25_ = leanh::lean_ctor_get(v_x_21_, 0);
        leanh::lean_inc(v_val_25_);
        leanh::lean_dec_ref_known(v_x_21_, 1);
        v___x_26_ = leanh::lean_apply_2(v_h__1_22_, v_val_25_, leanh::lean_box(0));
        return v___x_26_;
    }
}
pub unsafe fn l___private_Init_Data_String_Lemmas_Pattern_Split_Char_0__String_Slice_Pattern_Model_split_match__1_splitter(
    mut v_s_27_: *mut leanh::LeanObject,
    mut v_motive_28_: *mut leanh::LeanObject,
    mut v_x_29_: *mut leanh::LeanObject,
    mut v_h__1_30_: *mut leanh::LeanObject,
    mut v_h__2_31_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_29_) == 0 {
        let mut v___x_32_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_30_);
        v___x_32_ = leanh::lean_apply_1(v_h__2_31_, leanh::lean_box(0));
        return v___x_32_;
    } else {
        let mut v_val_33_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_34_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_31_);
        v_val_33_ = leanh::lean_ctor_get(v_x_29_, 0);
        leanh::lean_inc(v_val_33_);
        leanh::lean_dec_ref_known(v_x_29_, 1);
        v___x_34_ = leanh::lean_apply_2(v_h__1_30_, v_val_33_, leanh::lean_box(0));
        return v___x_34_;
    }
}
pub unsafe fn l___private_Init_Data_String_Lemmas_Pattern_Split_Char_0__String_Slice_Pattern_Model_split_match__1_splitter___boxed(
    mut v_s_35_: *mut leanh::LeanObject,
    mut v_motive_36_: *mut leanh::LeanObject,
    mut v_x_37_: *mut leanh::LeanObject,
    mut v_h__1_38_: *mut leanh::LeanObject,
    mut v_h__2_39_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_40_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_40_ = l___private_Init_Data_String_Lemmas_Pattern_Split_Char_0__String_Slice_Pattern_Model_split_match__1_splitter(v_s_35_, v_motive_36_, v_x_37_, v_h__1_38_, v_h__2_39_);
    leanh::lean_dec_ref(v_s_35_);
    return v_res_40_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_String_Lemmas_Pattern_Split_Char(
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
    res = runtime_initialize_Init_Data_String_Search(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_SplitOn_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_Pattern_Split_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_Pattern_Char(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_Pattern_Split_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Termination(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Order_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_Pattern_Split_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_Pattern_Split_Pred(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_Pattern_Char(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_ByCases(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_OrderInstances(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_Order(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_Intercalate(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_SplitOn_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_Slice(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_String_Lemmas_Pattern_Split_Char(
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
pub unsafe fn initialize_Init_Data_String_Lemmas_Pattern_Split_Char(
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
    res = initialize_Init_Data_String_Search(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_SplitOn_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Lemmas_Pattern_Split_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Lemmas_Pattern_Char(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Lemmas_Pattern_Split_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Termination(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Order_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Lemmas_Pattern_Split_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Lemmas_Pattern_Split_Pred(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Lemmas_Pattern_Char(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_ByCases(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_OrderInstances(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Lemmas_Order(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Lemmas_Intercalate(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_SplitOn_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Lemmas_Slice(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_Pattern_Split_Char(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_String_Lemmas_Pattern_Split_Char(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_String_Lemmas_Pattern_Split_Char(builtin);
}