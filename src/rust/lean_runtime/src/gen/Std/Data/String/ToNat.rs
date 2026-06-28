// Lean compiler output
// Module: Std.Data.String.ToNat
// Imports: Init.Data.String.Slice Init.Data.String.Search Init.Data.Nat.ToString Init.Data.String.Slice Init.Data.String.Search Init.Data.String.Lemmas.Iterate Std.Tactic.Do Init.Data.List.Sublist
use crate::r#gen::Init::Data::List::Sublist::{
    initialize_Init_Data_List_Sublist, runtime_initialize_Init_Data_List_Sublist,
};
use crate::r#gen::Init::Data::Nat::ToString::{
    initialize_Init_Data_Nat_ToString, runtime_initialize_Init_Data_Nat_ToString,
};
use crate::r#gen::Init::Data::String::Lemmas::Iterate::{
    initialize_Init_Data_String_Lemmas_Iterate, runtime_initialize_Init_Data_String_Lemmas_Iterate,
};
use crate::r#gen::Init::Data::String::Search::{
    initialize_Init_Data_String_Search, runtime_initialize_Init_Data_String_Search,
};
use crate::r#gen::Init::Data::String::Slice::{
    initialize_Init_Data_String_Slice, runtime_initialize_Init_Data_String_Slice,
};
use crate::r#gen::Std::Tactic::Do::{initialize_Std_Tactic_Do, runtime_initialize_Std_Tactic_Do};
pub unsafe fn l___private_Std_Data_String_ToNat_0__Break_runK_match__1_splitter___redArg(
    mut v_x_17_: *mut crate::leanh::LeanObject,
    mut v_h__1_18_: *mut crate::leanh::LeanObject,
    mut v_h__2_19_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_17_) == 0 {
        let mut v___x_20_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_21_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_18_);
        v___x_20_ = crate::leanh::lean_box(0);
        v___x_21_ = crate::leanh::lean_apply_1(v_h__2_19_, v___x_20_);
        return v___x_21_;
    } else {
        let mut v_val_22_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_23_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_19_);
        v_val_22_ = crate::leanh::lean_ctor_get(v_x_17_, 0);
        crate::leanh::lean_inc(v_val_22_);
        crate::leanh::lean_dec_ref_known(v_x_17_, 1);
        v___x_23_ = crate::leanh::lean_apply_1(v_h__1_18_, v_val_22_);
        return v___x_23_;
    }
}
pub unsafe fn l___private_Std_Data_String_ToNat_0__Break_runK_match__1_splitter(
    mut v_00_u03b1_24_: *mut crate::leanh::LeanObject,
    mut v_motive_25_: *mut crate::leanh::LeanObject,
    mut v_x_26_: *mut crate::leanh::LeanObject,
    mut v_h__1_27_: *mut crate::leanh::LeanObject,
    mut v_h__2_28_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_26_) == 0 {
        let mut v___x_29_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_30_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_27_);
        v___x_29_ = crate::leanh::lean_box(0);
        v___x_30_ = crate::leanh::lean_apply_1(v_h__2_28_, v___x_29_);
        return v___x_30_;
    } else {
        let mut v_val_31_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_32_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_28_);
        v_val_31_ = crate::leanh::lean_ctor_get(v_x_26_, 0);
        crate::leanh::lean_inc(v_val_31_);
        crate::leanh::lean_dec_ref_known(v_x_26_, 1);
        v___x_32_ = crate::leanh::lean_apply_1(v_h__1_27_, v_val_31_);
        return v___x_32_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_String_ToNat(
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
    res = runtime_initialize_Init_Data_Nat_ToString(builtin);
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
    res = runtime_initialize_Init_Data_String_Lemmas_Iterate(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_Do(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Sublist(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_String_ToNat(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Data_String_ToNat(builtin: u8) -> *mut crate::leanh::LeanObject {
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
    res = initialize_Init_Data_Nat_ToString(builtin);
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
    res = initialize_Init_Data_String_Lemmas_Iterate(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Tactic_Do(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Sublist(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_String_ToNat(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Data_String_ToNat(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Data_String_ToNat(builtin);
}
