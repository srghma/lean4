// Lean compiler output
// Module: Init.Data.String.Lemmas.Basic
// Imports: Init.Data.String.Basic Init.Data.String.Basic Init.Data.ByteArray.Lemmas Init.Data.Nat.MinMax
use crate::ffi::{lean_nat_dec_eq, lean_nat_sub};
use crate::r#gen::Init::Data::ByteArray::Lemmas::{
    initialize_Init_Data_ByteArray_Lemmas, runtime_initialize_Init_Data_ByteArray_Lemmas,
};
use crate::r#gen::Init::Data::Nat::MinMax::{
    initialize_Init_Data_Nat_MinMax, runtime_initialize_Init_Data_Nat_MinMax,
};
use crate::r#gen::Init::Data::String::Basic::{
    initialize_Init_Data_String_Basic, runtime_initialize_Init_Data_String_Basic,
};
pub unsafe fn l___private_Init_Data_String_Lemmas_Basic_0__String_Slice_Pos_nextn_match__1_splitter___redArg(
    mut v_n_31_: *mut leanh::LeanObject,
    mut v_h__1_32_: *mut leanh::LeanObject,
    mut v_h__2_33_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_34_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_35_: u8 = 0;
    v_zero_34_ = leanh::lean_unsigned_to_nat(0);
    v_isZero_35_ = lean_nat_dec_eq(v_n_31_, v_zero_34_);
    if v_isZero_35_ == 1 {
        let mut v___x_36_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_37_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_33_);
        v___x_36_ = leanh::lean_box(0);
        v___x_37_ = leanh::lean_apply_1(v_h__1_32_, v___x_36_);
        return v___x_37_;
    } else {
        let mut v_one_38_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_39_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_40_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_32_);
        v_one_38_ = leanh::lean_unsigned_to_nat(1);
        v_n_39_ = lean_nat_sub(v_n_31_, v_one_38_);
        v___x_40_ = leanh::lean_apply_1(v_h__2_33_, v_n_39_);
        return v___x_40_;
    }
}
pub unsafe fn l___private_Init_Data_String_Lemmas_Basic_0__String_Slice_Pos_nextn_match__1_splitter___redArg___boxed(
    mut v_n_41_: *mut leanh::LeanObject,
    mut v_h__1_42_: *mut leanh::LeanObject,
    mut v_h__2_43_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_44_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_44_ = l___private_Init_Data_String_Lemmas_Basic_0__String_Slice_Pos_nextn_match__1_splitter___redArg(v_n_41_, v_h__1_42_, v_h__2_43_);
    leanh::lean_dec(v_n_41_);
    return v_res_44_;
}
pub unsafe fn l___private_Init_Data_String_Lemmas_Basic_0__String_Slice_Pos_nextn_match__1_splitter(
    mut v_motive_45_: *mut leanh::LeanObject,
    mut v_n_46_: *mut leanh::LeanObject,
    mut v_h__1_47_: *mut leanh::LeanObject,
    mut v_h__2_48_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_49_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_50_: u8 = 0;
    v_zero_49_ = leanh::lean_unsigned_to_nat(0);
    v_isZero_50_ = lean_nat_dec_eq(v_n_46_, v_zero_49_);
    if v_isZero_50_ == 1 {
        let mut v___x_51_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_52_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_48_);
        v___x_51_ = leanh::lean_box(0);
        v___x_52_ = leanh::lean_apply_1(v_h__1_47_, v___x_51_);
        return v___x_52_;
    } else {
        let mut v_one_53_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_54_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_55_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_47_);
        v_one_53_ = leanh::lean_unsigned_to_nat(1);
        v_n_54_ = lean_nat_sub(v_n_46_, v_one_53_);
        v___x_55_ = leanh::lean_apply_1(v_h__2_48_, v_n_54_);
        return v___x_55_;
    }
}
pub unsafe fn l___private_Init_Data_String_Lemmas_Basic_0__String_Slice_Pos_nextn_match__1_splitter___boxed(
    mut v_motive_56_: *mut leanh::LeanObject,
    mut v_n_57_: *mut leanh::LeanObject,
    mut v_h__1_58_: *mut leanh::LeanObject,
    mut v_h__2_59_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_60_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_60_ =
        l___private_Init_Data_String_Lemmas_Basic_0__String_Slice_Pos_nextn_match__1_splitter(
            v_motive_56_,
            v_n_57_,
            v_h__1_58_,
            v_h__2_59_,
        );
    leanh::lean_dec(v_n_57_);
    return v_res_60_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_String_Lemmas_Basic(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_String_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_ByteArray_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_MinMax(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_String_Lemmas_Basic(
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
pub unsafe fn initialize_Init_Data_String_Lemmas_Basic(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_String_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_ByteArray_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_MinMax(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_String_Lemmas_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_String_Lemmas_Basic(builtin);
}