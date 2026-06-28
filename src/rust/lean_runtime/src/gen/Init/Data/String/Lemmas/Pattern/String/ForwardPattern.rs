// Lean compiler output
// Module: Init.Data.String.Lemmas.Pattern.String.ForwardPattern
// Imports: Init.Data.String.Lemmas.Pattern.String.Basic Init.Data.String.Pattern.String Init.Data.String.Slice Init.Data.String.Pattern.String Init.Data.String.Slice Init.Data.String.Lemmas.Pattern.Pred Init.Data.String.Lemmas.Pattern.Memcmp Init.Data.String.Lemmas.Basic Init.Data.ByteArray.Lemmas
use crate::r#gen::Init::Data::ByteArray::Lemmas::{
    initialize_Init_Data_ByteArray_Lemmas, runtime_initialize_Init_Data_ByteArray_Lemmas,
};
use crate::r#gen::Init::Data::String::Lemmas::Basic::{
    initialize_Init_Data_String_Lemmas_Basic, runtime_initialize_Init_Data_String_Lemmas_Basic,
};
use crate::r#gen::Init::Data::String::Lemmas::Pattern::Memcmp::{
    initialize_Init_Data_String_Lemmas_Pattern_Memcmp,
    runtime_initialize_Init_Data_String_Lemmas_Pattern_Memcmp,
};
use crate::r#gen::Init::Data::String::Lemmas::Pattern::Pred::{
    initialize_Init_Data_String_Lemmas_Pattern_Pred,
    runtime_initialize_Init_Data_String_Lemmas_Pattern_Pred,
};
use crate::r#gen::Init::Data::String::Lemmas::Pattern::String::Basic::{
    initialize_Init_Data_String_Lemmas_Pattern_String_Basic,
    runtime_initialize_Init_Data_String_Lemmas_Pattern_String_Basic,
};
use crate::r#gen::Init::Data::String::Pattern::String::{
    initialize_Init_Data_String_Pattern_String, runtime_initialize_Init_Data_String_Pattern_String,
};
use crate::r#gen::Init::Data::String::Slice::{
    initialize_Init_Data_String_Slice, runtime_initialize_Init_Data_String_Slice,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_apply_1, lean_box, lean_ctor_get, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_inc, lean_io_result_is_error, lean_io_result_mk_ok, lean_obj_tag,
};
pub unsafe fn l___private_Init_Data_String_Lemmas_Pattern_String_ForwardPattern_0__String_Slice_Pos_skipWhile_match__1_splitter___redArg(
    mut v_x_23_: *mut LeanObject,
    mut v_h__1_24_: *mut LeanObject,
    mut v_h__2_25_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_23_) == 0 {
        let mut v___x_26_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_27_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_24_);
        v___x_26_ = lean_box(0);
        v___x_27_ = lean_apply_1(v_h__2_25_, v___x_26_);
        return v___x_27_;
    } else {
        let mut v_val_28_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_29_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_25_);
        v_val_28_ = lean_ctor_get(v_x_23_, 0);
        lean_inc(v_val_28_);
        lean_dec_ref_known(v_x_23_, 1);
        v___x_29_ = lean_apply_1(v_h__1_24_, v_val_28_);
        return v___x_29_;
    }
}
pub unsafe fn l___private_Init_Data_String_Lemmas_Pattern_String_ForwardPattern_0__String_Slice_Pos_skipWhile_match__1_splitter(
    mut v_s_30_: *mut LeanObject,
    mut v_motive_31_: *mut LeanObject,
    mut v_x_32_: *mut LeanObject,
    mut v_h__1_33_: *mut LeanObject,
    mut v_h__2_34_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_32_) == 0 {
        let mut v___x_35_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_36_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_33_);
        v___x_35_ = lean_box(0);
        v___x_36_ = lean_apply_1(v_h__2_34_, v___x_35_);
        return v___x_36_;
    } else {
        let mut v_val_37_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_38_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_34_);
        v_val_37_ = lean_ctor_get(v_x_32_, 0);
        lean_inc(v_val_37_);
        lean_dec_ref_known(v_x_32_, 1);
        v___x_38_ = lean_apply_1(v_h__1_33_, v_val_37_);
        return v___x_38_;
    }
}
pub unsafe fn l___private_Init_Data_String_Lemmas_Pattern_String_ForwardPattern_0__String_Slice_Pos_skipWhile_match__1_splitter___boxed(
    mut v_s_39_: *mut LeanObject,
    mut v_motive_40_: *mut LeanObject,
    mut v_x_41_: *mut LeanObject,
    mut v_h__1_42_: *mut LeanObject,
    mut v_h__2_43_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_44_: *mut LeanObject = core::ptr::null_mut();
    v_res_44_ = l___private_Init_Data_String_Lemmas_Pattern_String_ForwardPattern_0__String_Slice_Pos_skipWhile_match__1_splitter(v_s_39_, v_motive_40_, v_x_41_, v_h__1_42_, v_h__2_43_);
    lean_dec_ref(v_s_39_);
    return v_res_44_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_String_Lemmas_Pattern_String_ForwardPattern(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_String_Lemmas_Pattern_String_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Pattern_String(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Slice(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_Pattern_Pred(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_Pattern_Memcmp(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_ByteArray_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_String_Lemmas_Pattern_String_ForwardPattern(
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
pub unsafe fn initialize_Init_Data_String_Lemmas_Pattern_String_ForwardPattern(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_String_Lemmas_Pattern_String_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_String_Pattern_String(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_String_Slice(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_String_Lemmas_Pattern_Pred(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_String_Lemmas_Pattern_Memcmp(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_String_Lemmas_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_ByteArray_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_Pattern_String_ForwardPattern(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_String_Lemmas_Pattern_String_ForwardPattern(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_String_Lemmas_Pattern_String_ForwardPattern(builtin);
}
