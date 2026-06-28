// Lean compiler output
// Module: Init.Data.String.Lemmas.Pattern.Split.Pred
// Imports: Init.Data.String.Slice Init.Data.String.Search Init.Data.List.SplitOn.Basic Init.Data.String.Lemmas.Pattern.Split.Basic Init.Data.String.Lemmas.Pattern.Pred Init.Data.String.Termination Init.Data.String.Lemmas.Pattern.Split.Basic Init.Data.Order.Lemmas Init.Data.Iterators.Lemmas.Combinators.FilterMap Init.Data.String.Lemmas.Pattern.Split.Basic Init.Data.String.Lemmas.Pattern.Pred Init.ByCases Init.Data.String.OrderInstances Init.Data.List.SplitOn.Lemmas Init.Data.String.Lemmas.Order
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
use crate::r#gen::Init::Data::String::Lemmas::Order::{
    initialize_Init_Data_String_Lemmas_Order, runtime_initialize_Init_Data_String_Lemmas_Order,
};
use crate::r#gen::Init::Data::String::Lemmas::Pattern::Pred::{
    initialize_Init_Data_String_Lemmas_Pattern_Pred,
    runtime_initialize_Init_Data_String_Lemmas_Pattern_Pred,
};
use crate::r#gen::Init::Data::String::Lemmas::Pattern::Split::Basic::{
    initialize_Init_Data_String_Lemmas_Pattern_Split_Basic,
    runtime_initialize_Init_Data_String_Lemmas_Pattern_Split_Basic,
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
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_apply_1, lean_apply_2, lean_box, lean_ctor_get, lean_dec,
    lean_dec_ref, lean_dec_ref_known, lean_inc, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_obj_tag,
};
pub unsafe fn l___private_Init_Data_String_Lemmas_Pattern_Split_Pred_0__String_Slice_Pattern_Model_split_match__1_splitter___redArg(
    mut v_x_21_: *mut LeanObject,
    mut v_h__1_22_: *mut LeanObject,
    mut v_h__2_23_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_21_) == 0 {
        let mut v___x_24_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_22_);
        v___x_24_ = lean_apply_1(v_h__2_23_, lean_box(0));
        return v___x_24_;
    } else {
        let mut v_val_25_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_26_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_23_);
        v_val_25_ = lean_ctor_get(v_x_21_, 0);
        lean_inc(v_val_25_);
        lean_dec_ref_known(v_x_21_, 1);
        v___x_26_ = lean_apply_2(v_h__1_22_, v_val_25_, lean_box(0));
        return v___x_26_;
    }
}
pub unsafe fn l___private_Init_Data_String_Lemmas_Pattern_Split_Pred_0__String_Slice_Pattern_Model_split_match__1_splitter(
    mut v_s_27_: *mut LeanObject,
    mut v_motive_28_: *mut LeanObject,
    mut v_x_29_: *mut LeanObject,
    mut v_h__1_30_: *mut LeanObject,
    mut v_h__2_31_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_29_) == 0 {
        let mut v___x_32_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_30_);
        v___x_32_ = lean_apply_1(v_h__2_31_, lean_box(0));
        return v___x_32_;
    } else {
        let mut v_val_33_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_34_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_31_);
        v_val_33_ = lean_ctor_get(v_x_29_, 0);
        lean_inc(v_val_33_);
        lean_dec_ref_known(v_x_29_, 1);
        v___x_34_ = lean_apply_2(v_h__1_30_, v_val_33_, lean_box(0));
        return v___x_34_;
    }
}
pub unsafe fn l___private_Init_Data_String_Lemmas_Pattern_Split_Pred_0__String_Slice_Pattern_Model_split_match__1_splitter___boxed(
    mut v_s_35_: *mut LeanObject,
    mut v_motive_36_: *mut LeanObject,
    mut v_x_37_: *mut LeanObject,
    mut v_h__1_38_: *mut LeanObject,
    mut v_h__2_39_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_40_: *mut LeanObject = core::ptr::null_mut();
    v_res_40_ = l___private_Init_Data_String_Lemmas_Pattern_Split_Pred_0__String_Slice_Pattern_Model_split_match__1_splitter(v_s_35_, v_motive_36_, v_x_37_, v_h__1_38_, v_h__2_39_);
    lean_dec_ref(v_s_35_);
    return v_res_40_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_String_Lemmas_Pattern_Split_Pred(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_String_Slice(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Search(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_SplitOn_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_Pattern_Split_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_Pattern_Pred(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Termination(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Order_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_ByCases(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_OrderInstances(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_SplitOn_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_Order(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_String_Lemmas_Pattern_Split_Pred(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_String_Lemmas_Pattern_Split_Pred(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_String_Slice(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_String_Search(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_SplitOn_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_String_Lemmas_Pattern_Split_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_String_Lemmas_Pattern_Pred(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_String_Termination(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Order_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_ByCases(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_String_OrderInstances(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_SplitOn_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_String_Lemmas_Order(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_Pattern_Split_Pred(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_String_Lemmas_Pattern_Split_Pred(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_String_Lemmas_Pattern_Split_Pred(builtin);
}
