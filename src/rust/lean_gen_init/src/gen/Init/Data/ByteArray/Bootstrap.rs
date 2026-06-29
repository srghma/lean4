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
pub unsafe fn l_ByteArray_append(
    mut v_a_27_: *mut crate::leanh::LeanObject,
    mut v_b_28_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_29_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_30_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_31_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_32_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_33_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_34_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_35_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_x_36_: *mut crate::leanh::LeanObject,
    mut v_x_37_: *mut crate::leanh::LeanObject,
    mut v_h__1_38_: *mut crate::leanh::LeanObject,
    mut v_h__2_39_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_36_) == 0 {
        let mut v___x_40_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_39_);
        v___x_40_ = crate::leanh::lean_apply_1(v_h__1_38_, v_x_37_);
        return v___x_40_;
    } else {
        let mut v_head_41_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_42_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_43_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_38_);
        v_head_41_ = crate::leanh::lean_ctor_get(v_x_36_, 0);
        crate::leanh::lean_inc(v_head_41_);
        v_tail_42_ = crate::leanh::lean_ctor_get(v_x_36_, 1);
        crate::leanh::lean_inc(v_tail_42_);
        crate::leanh::lean_dec_ref_known(v_x_36_, 2);
        v___x_43_ = crate::leanh::lean_apply_3(v_h__2_39_, v_head_41_, v_tail_42_, v_x_37_);
        return v___x_43_;
    }
}
pub unsafe fn l___private_Init_Data_ByteArray_Bootstrap_0__List_toByteArray_match__1_splitter(
    mut v_motive_44_: *mut crate::leanh::LeanObject,
    mut v_x_45_: *mut crate::leanh::LeanObject,
    mut v_x_46_: *mut crate::leanh::LeanObject,
    mut v_h__1_47_: *mut crate::leanh::LeanObject,
    mut v_h__2_48_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_45_) == 0 {
        let mut v___x_49_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_48_);
        v___x_49_ = crate::leanh::lean_apply_1(v_h__1_47_, v_x_46_);
        return v___x_49_;
    } else {
        let mut v_head_50_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_51_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_52_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_47_);
        v_head_50_ = crate::leanh::lean_ctor_get(v_x_45_, 0);
        crate::leanh::lean_inc(v_head_50_);
        v_tail_51_ = crate::leanh::lean_ctor_get(v_x_45_, 1);
        crate::leanh::lean_inc(v_tail_51_);
        crate::leanh::lean_dec_ref_known(v_x_45_, 2);
        v___x_52_ = crate::leanh::lean_apply_3(v_h__2_48_, v_head_50_, v_tail_51_, v_x_46_);
        return v___x_52_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_ByteArray_Bootstrap(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_List_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_ByteArray_Bootstrap(
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
pub unsafe fn initialize_Init_Data_ByteArray_Bootstrap(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_List_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_ByteArray_Bootstrap(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_ByteArray_Bootstrap(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_ByteArray_Bootstrap(builtin);
}
