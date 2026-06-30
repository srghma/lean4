// Lean compiler output
// Module: Init.Data.String.Lemmas.Pattern.Find.String
// Imports: Init.Data.String.Search Init.Data.String.Slice Init.Data.String.Pattern.String Init.ByCases Init.Data.String.Lemmas.Pattern.Find.Basic Init.Data.String.Lemmas.Pattern.String.ForwardSearcher Init.Data.Iterators.Lemmas.Consumers.Loop Init.Data.List.Sublist
use crate::r#gen::Init::ByCases::{initialize_Init_ByCases, runtime_initialize_Init_ByCases};
use crate::r#gen::Init::Data::Iterators::Lemmas::Consumers::Loop::{
    initialize_Init_Data_Iterators_Lemmas_Consumers_Loop,
    runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Loop,
};
use crate::r#gen::Init::Data::List::Sublist::{
    initialize_Init_Data_List_Sublist, runtime_initialize_Init_Data_List_Sublist,
};
use crate::r#gen::Init::Data::String::Lemmas::Pattern::Find::Basic::{
    initialize_Init_Data_String_Lemmas_Pattern_Find_Basic,
    runtime_initialize_Init_Data_String_Lemmas_Pattern_Find_Basic,
};
use crate::r#gen::Init::Data::String::Lemmas::Pattern::String::ForwardSearcher::{
    initialize_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher,
    runtime_initialize_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher,
};
use crate::r#gen::Init::Data::String::Pattern::String::{
    initialize_Init_Data_String_Pattern_String, runtime_initialize_Init_Data_String_Pattern_String,
};
use crate::r#gen::Init::Data::String::Search::{
    initialize_Init_Data_String_Search, runtime_initialize_Init_Data_String_Search,
};
use crate::r#gen::Init::Data::String::Slice::{
    initialize_Init_Data_String_Slice, runtime_initialize_Init_Data_String_Slice,
};
pub unsafe fn l___private_Init_Data_String_Lemmas_Pattern_Find_String_0__String_Slice_contains_match__1_splitter___redArg(
    mut v_x_23_: *mut leanh::LeanObject,
    mut v_h__1_24_: *mut leanh::LeanObject,
    mut v_h__2_25_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_23_) == 1 {
        let mut v_startPos_26_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_endPos_27_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_28_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_25_);
        v_startPos_26_ = leanh::lean_ctor_get(v_x_23_, 0);
        leanh::lean_inc(v_startPos_26_);
        v_endPos_27_ = leanh::lean_ctor_get(v_x_23_, 1);
        leanh::lean_inc(v_endPos_27_);
        leanh::lean_dec_ref_known(v_x_23_, 2);
        v___x_28_ = leanh::lean_apply_2(v_h__1_24_, v_startPos_26_, v_endPos_27_);
        return v___x_28_;
    } else {
        let mut v___x_29_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_24_);
        v___x_29_ = leanh::lean_apply_2(v_h__2_25_, v_x_23_, leanh::lean_box(0));
        return v___x_29_;
    }
}
pub unsafe fn l___private_Init_Data_String_Lemmas_Pattern_Find_String_0__String_Slice_contains_match__1_splitter(
    mut v_s_30_: *mut leanh::LeanObject,
    mut v_motive_31_: *mut leanh::LeanObject,
    mut v_x_32_: *mut leanh::LeanObject,
    mut v_h__1_33_: *mut leanh::LeanObject,
    mut v_h__2_34_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_32_) == 1 {
        let mut v_startPos_35_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_endPos_36_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_37_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_34_);
        v_startPos_35_ = leanh::lean_ctor_get(v_x_32_, 0);
        leanh::lean_inc(v_startPos_35_);
        v_endPos_36_ = leanh::lean_ctor_get(v_x_32_, 1);
        leanh::lean_inc(v_endPos_36_);
        leanh::lean_dec_ref_known(v_x_32_, 2);
        v___x_37_ = leanh::lean_apply_2(v_h__1_33_, v_startPos_35_, v_endPos_36_);
        return v___x_37_;
    } else {
        let mut v___x_38_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_33_);
        v___x_38_ = leanh::lean_apply_2(v_h__2_34_, v_x_32_, leanh::lean_box(0));
        return v___x_38_;
    }
}
pub unsafe fn l___private_Init_Data_String_Lemmas_Pattern_Find_String_0__String_Slice_contains_match__1_splitter___boxed(
    mut v_s_39_: *mut leanh::LeanObject,
    mut v_motive_40_: *mut leanh::LeanObject,
    mut v_x_41_: *mut leanh::LeanObject,
    mut v_h__1_42_: *mut leanh::LeanObject,
    mut v_h__2_43_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_44_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_44_ = l___private_Init_Data_String_Lemmas_Pattern_Find_String_0__String_Slice_contains_match__1_splitter(v_s_39_, v_motive_40_, v_x_41_, v_h__1_42_, v_h__2_43_);
    leanh::lean_dec_ref(v_s_39_);
    return v_res_44_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_String_Lemmas_Pattern_Find_String(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_String_Search(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Slice(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Pattern_String(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_ByCases(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_Pattern_Find_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Loop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Sublist(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_String_Lemmas_Pattern_Find_String(
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
pub unsafe fn initialize_Init_Data_String_Lemmas_Pattern_Find_String(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_String_Search(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Slice(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Pattern_String(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_ByCases(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Lemmas_Pattern_Find_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Consumers_Loop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Sublist(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_Pattern_Find_String(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_String_Lemmas_Pattern_Find_String(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_String_Lemmas_Pattern_Find_String(builtin);
}