// Lean compiler output
// Module: Init.Data.String.Lemmas.FindPos
// Imports: Init.Data.String.FindPos Init.Data.String.FindPos Init.Data.String.OrderInstances Init.Data.String.Lemmas.Order Init.Data.Order.Lemmas Init.Data.Option.Lemmas Init.ByCases
use crate::r#gen::Init::ByCases::{initialize_Init_ByCases, runtime_initialize_Init_ByCases};
use crate::r#gen::Init::Data::Option::Lemmas::{
    initialize_Init_Data_Option_Lemmas, runtime_initialize_Init_Data_Option_Lemmas,
};
use crate::r#gen::Init::Data::Order::Lemmas::{
    initialize_Init_Data_Order_Lemmas, runtime_initialize_Init_Data_Order_Lemmas,
};
use crate::r#gen::Init::Data::String::FindPos::{
    initialize_Init_Data_String_FindPos, runtime_initialize_Init_Data_String_FindPos,
};
use crate::r#gen::Init::Data::String::Lemmas::Order::{
    initialize_Init_Data_String_Lemmas_Order, runtime_initialize_Init_Data_String_Lemmas_Order,
};
use crate::r#gen::Init::Data::String::OrderInstances::{
    initialize_Init_Data_String_OrderInstances, runtime_initialize_Init_Data_String_OrderInstances,
};
use crate::lean_imports_rs::Init::Prelude::{lean_nat_dec_eq, lean_nat_sub};
pub unsafe fn l___private_Init_Data_String_Lemmas_FindPos_0__String_Slice_Pos_prevn_match__1_splitter___redArg(
    mut v_n_31_: *mut crate::leanh::LeanObject,
    mut v_h__1_32_: *mut crate::leanh::LeanObject,
    mut v_h__2_33_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_34_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_35_: u8 = 0;
    v_zero_34_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_35_ = lean_nat_dec_eq(v_n_31_, v_zero_34_);
    if v_isZero_35_ == 1 {
        let mut v___x_36_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_37_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_33_);
        v___x_36_ = crate::leanh::lean_box(0);
        v___x_37_ = crate::leanh::lean_apply_1(v_h__1_32_, v___x_36_);
        return v___x_37_;
    } else {
        let mut v_one_38_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_39_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_40_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_32_);
        v_one_38_ = crate::leanh::lean_unsigned_to_nat(1);
        v_n_39_ = lean_nat_sub(v_n_31_, v_one_38_);
        v___x_40_ = crate::leanh::lean_apply_1(v_h__2_33_, v_n_39_);
        return v___x_40_;
    }
}
pub unsafe fn l___private_Init_Data_String_Lemmas_FindPos_0__String_Slice_Pos_prevn_match__1_splitter___redArg___boxed(
    mut v_n_41_: *mut crate::leanh::LeanObject,
    mut v_h__1_42_: *mut crate::leanh::LeanObject,
    mut v_h__2_43_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_44_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_44_ = l___private_Init_Data_String_Lemmas_FindPos_0__String_Slice_Pos_prevn_match__1_splitter___redArg(v_n_41_, v_h__1_42_, v_h__2_43_);
    crate::leanh::lean_dec(v_n_41_);
    return v_res_44_;
}
pub unsafe fn l___private_Init_Data_String_Lemmas_FindPos_0__String_Slice_Pos_prevn_match__1_splitter(
    mut v_motive_45_: *mut crate::leanh::LeanObject,
    mut v_n_46_: *mut crate::leanh::LeanObject,
    mut v_h__1_47_: *mut crate::leanh::LeanObject,
    mut v_h__2_48_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_49_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_50_: u8 = 0;
    v_zero_49_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_50_ = lean_nat_dec_eq(v_n_46_, v_zero_49_);
    if v_isZero_50_ == 1 {
        let mut v___x_51_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_52_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_48_);
        v___x_51_ = crate::leanh::lean_box(0);
        v___x_52_ = crate::leanh::lean_apply_1(v_h__1_47_, v___x_51_);
        return v___x_52_;
    } else {
        let mut v_one_53_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_54_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_55_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_47_);
        v_one_53_ = crate::leanh::lean_unsigned_to_nat(1);
        v_n_54_ = lean_nat_sub(v_n_46_, v_one_53_);
        v___x_55_ = crate::leanh::lean_apply_1(v_h__2_48_, v_n_54_);
        return v___x_55_;
    }
}
pub unsafe fn l___private_Init_Data_String_Lemmas_FindPos_0__String_Slice_Pos_prevn_match__1_splitter___boxed(
    mut v_motive_56_: *mut crate::leanh::LeanObject,
    mut v_n_57_: *mut crate::leanh::LeanObject,
    mut v_h__1_58_: *mut crate::leanh::LeanObject,
    mut v_h__2_59_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_60_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_60_ =
        l___private_Init_Data_String_Lemmas_FindPos_0__String_Slice_Pos_prevn_match__1_splitter(
            v_motive_56_,
            v_n_57_,
            v_h__1_58_,
            v_h__2_59_,
        );
    crate::leanh::lean_dec(v_n_57_);
    return v_res_60_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_String_Lemmas_FindPos(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_String_FindPos(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_FindPos(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_OrderInstances(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_Order(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Order_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
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
pub unsafe fn meta_initialize_Init_Data_String_Lemmas_FindPos(
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
pub unsafe fn initialize_Init_Data_String_Lemmas_FindPos(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_String_FindPos(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_FindPos(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_OrderInstances(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Lemmas_Order(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Order_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Option_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_ByCases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_FindPos(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_String_Lemmas_FindPos(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_String_Lemmas_FindPos(builtin);
}
