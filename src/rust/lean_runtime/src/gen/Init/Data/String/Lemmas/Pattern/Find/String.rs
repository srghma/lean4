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
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_apply_2, lean_box, lean_ctor_get, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_inc, lean_io_result_is_error, lean_io_result_mk_ok, lean_obj_tag,
};
pub unsafe fn l___private_Init_Data_String_Lemmas_Pattern_Find_String_0__String_Slice_contains_match__1_splitter___redArg(
    mut v_x_23_: *mut LeanObject,
    mut v_h__1_24_: *mut LeanObject,
    mut v_h__2_25_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_23_) == 1 {
        let mut v_startPos_26_: *mut LeanObject = core::ptr::null_mut();
        let mut v_endPos_27_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_28_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_25_);
        v_startPos_26_ = lean_ctor_get(v_x_23_, 0);
        lean_inc(v_startPos_26_);
        v_endPos_27_ = lean_ctor_get(v_x_23_, 1);
        lean_inc(v_endPos_27_);
        lean_dec_ref_known(v_x_23_, 2);
        v___x_28_ = lean_apply_2(v_h__1_24_, v_startPos_26_, v_endPos_27_);
        return v___x_28_;
    } else {
        let mut v___x_29_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_24_);
        v___x_29_ = lean_apply_2(v_h__2_25_, v_x_23_, lean_box(0));
        return v___x_29_;
    }
}
pub unsafe fn l___private_Init_Data_String_Lemmas_Pattern_Find_String_0__String_Slice_contains_match__1_splitter(
    mut v_s_30_: *mut LeanObject,
    mut v_motive_31_: *mut LeanObject,
    mut v_x_32_: *mut LeanObject,
    mut v_h__1_33_: *mut LeanObject,
    mut v_h__2_34_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_32_) == 1 {
        let mut v_startPos_35_: *mut LeanObject = core::ptr::null_mut();
        let mut v_endPos_36_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_37_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_34_);
        v_startPos_35_ = lean_ctor_get(v_x_32_, 0);
        lean_inc(v_startPos_35_);
        v_endPos_36_ = lean_ctor_get(v_x_32_, 1);
        lean_inc(v_endPos_36_);
        lean_dec_ref_known(v_x_32_, 2);
        v___x_37_ = lean_apply_2(v_h__1_33_, v_startPos_35_, v_endPos_36_);
        return v___x_37_;
    } else {
        let mut v___x_38_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_33_);
        v___x_38_ = lean_apply_2(v_h__2_34_, v_x_32_, lean_box(0));
        return v___x_38_;
    }
}
pub unsafe fn l___private_Init_Data_String_Lemmas_Pattern_Find_String_0__String_Slice_contains_match__1_splitter___boxed(
    mut v_s_39_: *mut LeanObject,
    mut v_motive_40_: *mut LeanObject,
    mut v_x_41_: *mut LeanObject,
    mut v_h__1_42_: *mut LeanObject,
    mut v_h__2_43_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_44_: *mut LeanObject = core::ptr::null_mut();
    v_res_44_ = l___private_Init_Data_String_Lemmas_Pattern_Find_String_0__String_Slice_contains_match__1_splitter(v_s_39_, v_motive_40_, v_x_41_, v_h__1_42_, v_h__2_43_);
    lean_dec_ref(v_s_39_);
    return v_res_44_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_String_Lemmas_Pattern_Find_String(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_String_Search(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Slice(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Pattern_String(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_ByCases(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_Pattern_Find_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Loop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Sublist(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_String_Lemmas_Pattern_Find_String(
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
pub unsafe fn initialize_Init_Data_String_Lemmas_Pattern_Find_String(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_String_Search(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_String_Slice(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_String_Pattern_String(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_ByCases(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_String_Lemmas_Pattern_Find_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Consumers_Loop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_Sublist(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_Pattern_Find_String(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_String_Lemmas_Pattern_Find_String(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_String_Lemmas_Pattern_Find_String(builtin);
}
