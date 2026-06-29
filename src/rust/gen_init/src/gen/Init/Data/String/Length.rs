// Lean compiler output
// Module: Init.Data.String.Length
// Imports: Init.Data.String.Basic Init.Data.Char.Lemmas
use crate::r#gen::Init::Data::Char::Lemmas::{
    initialize_Init_Data_Char_Lemmas, runtime_initialize_Init_Data_Char_Lemmas,
};
use crate::r#gen::Init::Data::String::Basic::{
    initialize_Init_Data_String_Basic, runtime_initialize_Init_Data_String_Basic,
};
use crate::ffi::lean_string_length;
use crate::ffi::{lean_nat_dec_eq, lean_nat_sub};
pub unsafe fn l_String_length___boxed(
    mut v_b_39_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_40_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_40_ = lean_string_length(v_b_39_);
    crate::leanh::lean_dec_ref(v_b_39_);
    return v_res_40_;
}
pub unsafe fn l___private_Init_Data_String_Length_0__Nat_repeat_match__1_splitter___redArg(
    mut v_x_41_: *mut crate::leanh::LeanObject,
    mut v_x_42_: *mut crate::leanh::LeanObject,
    mut v_h__1_43_: *mut crate::leanh::LeanObject,
    mut v_h__2_44_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_45_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_46_: u8 = 0;
    v_zero_45_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_46_ = lean_nat_dec_eq(v_x_41_, v_zero_45_);
    if v_isZero_46_ == 1 {
        let mut v___x_47_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_44_);
        v___x_47_ = crate::leanh::lean_apply_1(v_h__1_43_, v_x_42_);
        return v___x_47_;
    } else {
        let mut v_one_48_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_49_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_50_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_43_);
        v_one_48_ = crate::leanh::lean_unsigned_to_nat(1);
        v_n_49_ = lean_nat_sub(v_x_41_, v_one_48_);
        v___x_50_ = crate::leanh::lean_apply_2(v_h__2_44_, v_n_49_, v_x_42_);
        return v___x_50_;
    }
}
pub unsafe fn l___private_Init_Data_String_Length_0__Nat_repeat_match__1_splitter___redArg___boxed(
    mut v_x_51_: *mut crate::leanh::LeanObject,
    mut v_x_52_: *mut crate::leanh::LeanObject,
    mut v_h__1_53_: *mut crate::leanh::LeanObject,
    mut v_h__2_54_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_55_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_55_ = l___private_Init_Data_String_Length_0__Nat_repeat_match__1_splitter___redArg(
        v_x_51_, v_x_52_, v_h__1_53_, v_h__2_54_,
    );
    crate::leanh::lean_dec(v_x_51_);
    return v_res_55_;
}
pub unsafe fn l___private_Init_Data_String_Length_0__Nat_repeat_match__1_splitter(
    mut v_00_u03b1_56_: *mut crate::leanh::LeanObject,
    mut v_motive_57_: *mut crate::leanh::LeanObject,
    mut v_x_58_: *mut crate::leanh::LeanObject,
    mut v_x_59_: *mut crate::leanh::LeanObject,
    mut v_h__1_60_: *mut crate::leanh::LeanObject,
    mut v_h__2_61_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_62_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_63_: u8 = 0;
    v_zero_62_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_63_ = lean_nat_dec_eq(v_x_58_, v_zero_62_);
    if v_isZero_63_ == 1 {
        let mut v___x_64_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_61_);
        v___x_64_ = crate::leanh::lean_apply_1(v_h__1_60_, v_x_59_);
        return v___x_64_;
    } else {
        let mut v_one_65_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_66_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_67_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_60_);
        v_one_65_ = crate::leanh::lean_unsigned_to_nat(1);
        v_n_66_ = lean_nat_sub(v_x_58_, v_one_65_);
        v___x_67_ = crate::leanh::lean_apply_2(v_h__2_61_, v_n_66_, v_x_59_);
        return v___x_67_;
    }
}
pub unsafe fn l___private_Init_Data_String_Length_0__Nat_repeat_match__1_splitter___boxed(
    mut v_00_u03b1_68_: *mut crate::leanh::LeanObject,
    mut v_motive_69_: *mut crate::leanh::LeanObject,
    mut v_x_70_: *mut crate::leanh::LeanObject,
    mut v_x_71_: *mut crate::leanh::LeanObject,
    mut v_h__1_72_: *mut crate::leanh::LeanObject,
    mut v_h__2_73_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_74_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_74_ = l___private_Init_Data_String_Length_0__Nat_repeat_match__1_splitter(
        v_00_u03b1_68_,
        v_motive_69_,
        v_x_70_,
        v_x_71_,
        v_h__1_72_,
        v_h__2_73_,
    );
    crate::leanh::lean_dec(v_x_70_);
    return v_res_74_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_String_Length(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_String_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Char_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_String_Length(
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
pub unsafe fn initialize_Init_Data_String_Length(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_String_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Char_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Length(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_String_Length(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_String_Length(builtin);
}
