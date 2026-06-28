// Lean compiler output
// Module: Init.Data.ByteArray.Bootstrap
// Imports: Init.Data.List.Basic
use crate::r#gen::Init::Data::List::Basic::{
    initialize_Init_Data_List_Basic, l_List_appendTR___redArg,
    runtime_initialize_Init_Data_List_Basic,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_mk, lean_array_to_list, lean_byte_array_data, lean_byte_array_mk,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_apply_1, lean_apply_3, lean_box, lean_ctor_get, lean_dec,
    lean_dec_ref, lean_dec_ref_known, lean_inc, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_obj_tag,
};
pub unsafe fn l_ByteArray_append(
    mut v_a_27_: *mut LeanObject,
    mut v_b_28_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_29_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_30_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_31_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_32_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_33_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_34_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_35_: *mut LeanObject = core::ptr::null_mut();
    v___x_29_ = lean_byte_array_data(v_a_27_);
    v___x_30_ = lean_array_to_list(v___x_29_);
    v___x_31_ = lean_byte_array_data(v_b_28_);
    v___x_32_ = lean_array_to_list(v___x_31_);
    v___x_33_ = l_List_appendTR___redArg(v___x_30_, v___x_32_);
    v___x_34_ = lean_array_mk(v___x_33_);
    v___x_35_ = lean_byte_array_mk(v___x_34_);
    return v___x_35_;
}
pub unsafe fn l___private_Init_Data_ByteArray_Bootstrap_0__List_toByteArray_match__1_splitter___redArg(
    mut v_x_36_: *mut LeanObject,
    mut v_x_37_: *mut LeanObject,
    mut v_h__1_38_: *mut LeanObject,
    mut v_h__2_39_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_36_) == 0 {
        let mut v___x_40_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_39_);
        v___x_40_ = lean_apply_1(v_h__1_38_, v_x_37_);
        return v___x_40_;
    } else {
        let mut v_head_41_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_42_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_43_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_38_);
        v_head_41_ = lean_ctor_get(v_x_36_, 0);
        lean_inc(v_head_41_);
        v_tail_42_ = lean_ctor_get(v_x_36_, 1);
        lean_inc(v_tail_42_);
        lean_dec_ref_known(v_x_36_, 2);
        v___x_43_ = lean_apply_3(v_h__2_39_, v_head_41_, v_tail_42_, v_x_37_);
        return v___x_43_;
    }
}
pub unsafe fn l___private_Init_Data_ByteArray_Bootstrap_0__List_toByteArray_match__1_splitter(
    mut v_motive_44_: *mut LeanObject,
    mut v_x_45_: *mut LeanObject,
    mut v_x_46_: *mut LeanObject,
    mut v_h__1_47_: *mut LeanObject,
    mut v_h__2_48_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_45_) == 0 {
        let mut v___x_49_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_48_);
        v___x_49_ = lean_apply_1(v_h__1_47_, v_x_46_);
        return v___x_49_;
    } else {
        let mut v_head_50_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_51_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_52_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_47_);
        v_head_50_ = lean_ctor_get(v_x_45_, 0);
        lean_inc(v_head_50_);
        v_tail_51_ = lean_ctor_get(v_x_45_, 1);
        lean_inc(v_tail_51_);
        lean_dec_ref_known(v_x_45_, 2);
        v___x_52_ = lean_apply_3(v_h__2_48_, v_head_50_, v_tail_51_, v_x_46_);
        return v___x_52_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_ByteArray_Bootstrap(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_List_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_ByteArray_Bootstrap(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_ByteArray_Bootstrap(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_List_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_ByteArray_Bootstrap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_ByteArray_Bootstrap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_ByteArray_Bootstrap(builtin);
}
