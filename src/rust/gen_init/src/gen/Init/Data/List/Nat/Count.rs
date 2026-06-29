// Lean compiler output
// Module: Init.Data.List.Nat.Count
// Imports: Init.GetElem Init.ByCases Init.Data.Bool Init.Data.List.Count Init.Data.List.Lemmas Init.Data.List.Sublist Init.Data.Nat.Lemmas Init.Data.Nat.MinMax Init.Omega
use crate::r#gen::Init::ByCases::{initialize_Init_ByCases, runtime_initialize_Init_ByCases};
use crate::r#gen::Init::Data::Bool::{
    initialize_Init_Data_Bool, runtime_initialize_Init_Data_Bool,
};
use crate::r#gen::Init::Data::List::Count::{
    initialize_Init_Data_List_Count, runtime_initialize_Init_Data_List_Count,
};
use crate::r#gen::Init::Data::List::Lemmas::{
    initialize_Init_Data_List_Lemmas, runtime_initialize_Init_Data_List_Lemmas,
};
use crate::r#gen::Init::Data::List::Sublist::{
    initialize_Init_Data_List_Sublist, runtime_initialize_Init_Data_List_Sublist,
};
use crate::r#gen::Init::Data::Nat::Lemmas::{
    initialize_Init_Data_Nat_Lemmas, runtime_initialize_Init_Data_Nat_Lemmas,
};
use crate::r#gen::Init::Data::Nat::MinMax::{
    initialize_Init_Data_Nat_MinMax, runtime_initialize_Init_Data_Nat_MinMax,
};
use crate::r#gen::Init::GetElem::{initialize_Init_GetElem, runtime_initialize_Init_GetElem};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
pub unsafe fn l___private_Init_Data_List_Nat_Count_0__List_filter_match__1_splitter___redArg(
    mut v_x_27_: u8,
    mut v_h__1_28_: *mut crate::leanh::LeanObject,
    mut v_h__2_29_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if v_x_27_ == 0 {
        let mut v___x_30_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_31_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_28_);
        v___x_30_ = crate::leanh::lean_box(0);
        v___x_31_ = crate::leanh::lean_apply_1(v_h__2_29_, v___x_30_);
        return v___x_31_;
    } else {
        let mut v___x_32_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_33_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_29_);
        v___x_32_ = crate::leanh::lean_box(0);
        v___x_33_ = crate::leanh::lean_apply_1(v_h__1_28_, v___x_32_);
        return v___x_33_;
    }
}
pub unsafe fn l___private_Init_Data_List_Nat_Count_0__List_filter_match__1_splitter___redArg___boxed(
    mut v_x_34_: *mut crate::leanh::LeanObject,
    mut v_h__1_35_: *mut crate::leanh::LeanObject,
    mut v_h__2_36_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_26__boxed_37_: u8 = 0;
    let mut v_res_38_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_26__boxed_37_ = (crate::leanh::lean_unbox(v_x_34_) as u8);
    v_res_38_ = l___private_Init_Data_List_Nat_Count_0__List_filter_match__1_splitter___redArg(
        v_x_26__boxed_37_,
        v_h__1_35_,
        v_h__2_36_,
    );
    return v_res_38_;
}
pub unsafe fn l___private_Init_Data_List_Nat_Count_0__List_filter_match__1_splitter(
    mut v_motive_39_: *mut crate::leanh::LeanObject,
    mut v_x_40_: u8,
    mut v_h__1_41_: *mut crate::leanh::LeanObject,
    mut v_h__2_42_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if v_x_40_ == 0 {
        let mut v___x_43_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_44_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_41_);
        v___x_43_ = crate::leanh::lean_box(0);
        v___x_44_ = crate::leanh::lean_apply_1(v_h__2_42_, v___x_43_);
        return v___x_44_;
    } else {
        let mut v___x_45_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_46_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_42_);
        v___x_45_ = crate::leanh::lean_box(0);
        v___x_46_ = crate::leanh::lean_apply_1(v_h__1_41_, v___x_45_);
        return v___x_46_;
    }
}
pub unsafe fn l___private_Init_Data_List_Nat_Count_0__List_filter_match__1_splitter___boxed(
    mut v_motive_47_: *mut crate::leanh::LeanObject,
    mut v_x_48_: *mut crate::leanh::LeanObject,
    mut v_h__1_49_: *mut crate::leanh::LeanObject,
    mut v_h__2_50_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_37__boxed_51_: u8 = 0;
    let mut v_res_52_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_37__boxed_51_ = (crate::leanh::lean_unbox(v_x_48_) as u8);
    v_res_52_ = l___private_Init_Data_List_Nat_Count_0__List_filter_match__1_splitter(
        v_motive_47_,
        v_x_37__boxed_51_,
        v_h__1_49_,
        v_h__2_50_,
    );
    return v_res_52_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_List_Nat_Count(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_GetElem(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_ByCases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Bool(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Count(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Sublist(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_MinMax(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_List_Nat_Count(
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
pub unsafe fn initialize_Init_Data_List_Nat_Count(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_GetElem(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_ByCases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Bool(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Count(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Sublist(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_MinMax(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Nat_Count(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_List_Nat_Count(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_List_Nat_Count(builtin);
}
