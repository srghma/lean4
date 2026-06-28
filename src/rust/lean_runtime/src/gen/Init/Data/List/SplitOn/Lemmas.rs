// Lean compiler output
// Module: Init.Data.List.SplitOn.Lemmas
// Imports: Init.Data.List.SplitOn.Basic Init.Data.List.SplitOn.Basic Init.Data.List.Nat.Modify Init.ByCases
use crate::r#gen::Init::ByCases::{initialize_Init_ByCases, runtime_initialize_Init_ByCases};
use crate::r#gen::Init::Data::List::Nat::Modify::{
    initialize_Init_Data_List_Nat_Modify, runtime_initialize_Init_Data_List_Nat_Modify,
};
use crate::r#gen::Init::Data::List::SplitOn::Basic::{
    initialize_Init_Data_List_SplitOn_Basic, runtime_initialize_Init_Data_List_SplitOn_Basic,
};
pub unsafe fn l___private_Init_Data_List_SplitOn_Lemmas_0__List_splitOnPPrepend_match__1_splitter___redArg(
    mut v_x_19_: *mut crate::leanh::LeanObject,
    mut v_x_20_: *mut crate::leanh::LeanObject,
    mut v_h__1_21_: *mut crate::leanh::LeanObject,
    mut v_h__2_22_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_19_) == 0 {
        let mut v___x_23_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_22_);
        v___x_23_ = crate::leanh::lean_apply_1(v_h__1_21_, v_x_20_);
        return v___x_23_;
    } else {
        let mut v_head_24_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_25_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_26_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_21_);
        v_head_24_ = crate::leanh::lean_ctor_get(v_x_19_, 0);
        crate::leanh::lean_inc(v_head_24_);
        v_tail_25_ = crate::leanh::lean_ctor_get(v_x_19_, 1);
        crate::leanh::lean_inc(v_tail_25_);
        crate::leanh::lean_dec_ref_known(v_x_19_, 2);
        v___x_26_ = crate::leanh::lean_apply_3(v_h__2_22_, v_head_24_, v_tail_25_, v_x_20_);
        return v___x_26_;
    }
}
pub unsafe fn l___private_Init_Data_List_SplitOn_Lemmas_0__List_splitOnPPrepend_match__1_splitter(
    mut v_00_u03b1_27_: *mut crate::leanh::LeanObject,
    mut v_motive_28_: *mut crate::leanh::LeanObject,
    mut v_x_29_: *mut crate::leanh::LeanObject,
    mut v_x_30_: *mut crate::leanh::LeanObject,
    mut v_h__1_31_: *mut crate::leanh::LeanObject,
    mut v_h__2_32_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_29_) == 0 {
        let mut v___x_33_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_32_);
        v___x_33_ = crate::leanh::lean_apply_1(v_h__1_31_, v_x_30_);
        return v___x_33_;
    } else {
        let mut v_head_34_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_35_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_36_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_31_);
        v_head_34_ = crate::leanh::lean_ctor_get(v_x_29_, 0);
        crate::leanh::lean_inc(v_head_34_);
        v_tail_35_ = crate::leanh::lean_ctor_get(v_x_29_, 1);
        crate::leanh::lean_inc(v_tail_35_);
        crate::leanh::lean_dec_ref_known(v_x_29_, 2);
        v___x_36_ = crate::leanh::lean_apply_3(v_h__2_32_, v_head_34_, v_tail_35_, v_x_30_);
        return v___x_36_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_List_SplitOn_Lemmas(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_List_SplitOn_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_SplitOn_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Nat_Modify(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_ByCases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_List_SplitOn_Lemmas(
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
pub unsafe fn initialize_Init_Data_List_SplitOn_Lemmas(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_List_SplitOn_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_SplitOn_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Nat_Modify(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_ByCases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_SplitOn_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_List_SplitOn_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_List_SplitOn_Lemmas(builtin);
}
