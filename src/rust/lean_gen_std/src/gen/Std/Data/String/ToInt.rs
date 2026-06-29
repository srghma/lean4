// Lean compiler output
// Module: Std.Data.String.ToInt
// Imports: Init.Data.String.Slice Init.Data.String.Search Init.Data.ToString.Extra Init.Data.String.TakeDrop Init.Data.String.Slice Init.Data.String.Search Std.Data.String.ToNat Init.Data.String.Lemmas.Pattern.TakeDrop.Basic Init.Data.String.Lemmas.Pattern.TakeDrop.Char Init.Data.Int.ToString
use crate::r#gen::Init::Data::Int::ToString::{
    initialize_Init_Data_Int_ToString, runtime_initialize_Init_Data_Int_ToString,
};
use crate::r#gen::Init::Data::String::Lemmas::Pattern::TakeDrop::Basic::{
    initialize_Init_Data_String_Lemmas_Pattern_TakeDrop_Basic,
    runtime_initialize_Init_Data_String_Lemmas_Pattern_TakeDrop_Basic,
};
use crate::r#gen::Init::Data::String::Lemmas::Pattern::TakeDrop::Char::{
    initialize_Init_Data_String_Lemmas_Pattern_TakeDrop_Char,
    runtime_initialize_Init_Data_String_Lemmas_Pattern_TakeDrop_Char,
};
use crate::r#gen::Init::Data::String::Search::{
    initialize_Init_Data_String_Search, runtime_initialize_Init_Data_String_Search,
};
use crate::r#gen::Init::Data::String::Slice::{
    initialize_Init_Data_String_Slice, runtime_initialize_Init_Data_String_Slice,
};
use crate::r#gen::Init::Data::String::TakeDrop::{
    initialize_Init_Data_String_TakeDrop, runtime_initialize_Init_Data_String_TakeDrop,
};
use crate::r#gen::Init::Data::ToString::Extra::{
    initialize_Init_Data_ToString_Extra, runtime_initialize_Init_Data_ToString_Extra,
};
use crate::r#gen::Std::Data::String::ToNat::{
    initialize_Std_Data_String_ToNat, runtime_initialize_Std_Data_String_ToNat,
};
pub unsafe fn l___private_Std_Data_String_ToInt_0__String_Slice_isInt_match__1_splitter___redArg(
    mut v_x_16_: *mut crate::leanh::LeanObject,
    mut v_h__1_17_: *mut crate::leanh::LeanObject,
    mut v_h__2_18_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_16_) == 0 {
        let mut v___x_19_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_20_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_17_);
        v___x_19_ = crate::leanh::lean_box(0);
        v___x_20_ = crate::leanh::lean_apply_1(v_h__2_18_, v___x_19_);
        return v___x_20_;
    } else {
        let mut v_val_21_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_22_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_18_);
        v_val_21_ = crate::leanh::lean_ctor_get(v_x_16_, 0);
        crate::leanh::lean_inc(v_val_21_);
        crate::leanh::lean_dec_ref_known(v_x_16_, 1);
        v___x_22_ = crate::leanh::lean_apply_1(v_h__1_17_, v_val_21_);
        return v___x_22_;
    }
}
pub unsafe fn l___private_Std_Data_String_ToInt_0__String_Slice_isInt_match__1_splitter(
    mut v_motive_23_: *mut crate::leanh::LeanObject,
    mut v_x_24_: *mut crate::leanh::LeanObject,
    mut v_h__1_25_: *mut crate::leanh::LeanObject,
    mut v_h__2_26_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_24_) == 0 {
        let mut v___x_27_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_28_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_25_);
        v___x_27_ = crate::leanh::lean_box(0);
        v___x_28_ = crate::leanh::lean_apply_1(v_h__2_26_, v___x_27_);
        return v___x_28_;
    } else {
        let mut v_val_29_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_30_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_26_);
        v_val_29_ = crate::leanh::lean_ctor_get(v_x_24_, 0);
        crate::leanh::lean_inc(v_val_29_);
        crate::leanh::lean_dec_ref_known(v_x_24_, 1);
        v___x_30_ = crate::leanh::lean_apply_1(v_h__1_25_, v_val_29_);
        return v___x_30_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_String_ToInt(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_String_Slice(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Search(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_ToString_Extra(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_TakeDrop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Slice(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Search(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_String_ToNat(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_Pattern_TakeDrop_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_Pattern_TakeDrop_Char(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Int_ToString(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_String_ToInt(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Data_String_ToInt(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_String_Slice(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Search(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_ToString_Extra(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_TakeDrop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Slice(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Search(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Data_String_ToNat(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Lemmas_Pattern_TakeDrop_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Lemmas_Pattern_TakeDrop_Char(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Int_ToString(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_String_ToInt(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Data_String_ToInt(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Data_String_ToInt(builtin);
}
