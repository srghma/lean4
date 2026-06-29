// Lean compiler output
// Module: Init.Data.ByteArray.Lemmas
// Imports: Init.Data.ByteArray.Basic Init.ByCases Init.Data.Array.Bootstrap Init.Data.Array.Extract Init.Data.Array.Lemmas Init.Omega
use crate::ffi::lean_byte_array_data;
use crate::r#gen::Init::ByCases::{initialize_Init_ByCases, runtime_initialize_Init_ByCases};
use crate::r#gen::Init::Data::Array::Bootstrap::{
    initialize_Init_Data_Array_Bootstrap, runtime_initialize_Init_Data_Array_Bootstrap,
};
use crate::r#gen::Init::Data::Array::Extract::{
    initialize_Init_Data_Array_Extract, runtime_initialize_Init_Data_Array_Extract,
};
use crate::r#gen::Init::Data::Array::Lemmas::{
    initialize_Init_Data_Array_Lemmas, runtime_initialize_Init_Data_Array_Lemmas,
};
use crate::r#gen::Init::Data::ByteArray::Basic::{
    initialize_Init_Data_ByteArray_Basic, runtime_initialize_Init_Data_ByteArray_Basic,
};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
pub unsafe fn l___private_Init_Data_ByteArray_Lemmas_0__ByteArray_set_match__1_splitter___redArg(
    mut v_x_40_: *mut crate::leanh::LeanObject,
    mut v_x_41_: *mut crate::leanh::LeanObject,
    mut v_x_42_: u8,
    mut v_h__1_43_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_data_44_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_45_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_46_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_data_44_ = lean_byte_array_data(v_x_40_);
    v___x_45_ = crate::leanh::lean_box((v_x_42_) as usize);
    v___x_46_ = crate::leanh::lean_apply_4(
        v_h__1_43_,
        v_data_44_,
        v_x_41_,
        v___x_45_,
        crate::leanh::lean_box(0),
    );
    return v___x_46_;
}
pub unsafe fn l___private_Init_Data_ByteArray_Lemmas_0__ByteArray_set_match__1_splitter___redArg___boxed(
    mut v_x_47_: *mut crate::leanh::LeanObject,
    mut v_x_48_: *mut crate::leanh::LeanObject,
    mut v_x_49_: *mut crate::leanh::LeanObject,
    mut v_h__1_50_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_33__boxed_51_: u8 = 0;
    let mut v_res_52_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_33__boxed_51_ = (crate::leanh::lean_unbox(v_x_49_) as u8);
    v_res_52_ = l___private_Init_Data_ByteArray_Lemmas_0__ByteArray_set_match__1_splitter___redArg(
        v_x_47_,
        v_x_48_,
        v_x_33__boxed_51_,
        v_h__1_50_,
    );
    return v_res_52_;
}
pub unsafe fn l___private_Init_Data_ByteArray_Lemmas_0__ByteArray_set_match__1_splitter(
    mut v_motive_53_: *mut crate::leanh::LeanObject,
    mut v_x_54_: *mut crate::leanh::LeanObject,
    mut v_x_55_: *mut crate::leanh::LeanObject,
    mut v_x_56_: u8,
    mut v_x_57_: *mut crate::leanh::LeanObject,
    mut v_h__1_58_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_data_59_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_60_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_61_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_data_59_ = lean_byte_array_data(v_x_54_);
    v___x_60_ = crate::leanh::lean_box((v_x_56_) as usize);
    v___x_61_ = crate::leanh::lean_apply_4(
        v_h__1_58_,
        v_data_59_,
        v_x_55_,
        v___x_60_,
        crate::leanh::lean_box(0),
    );
    return v___x_61_;
}
pub unsafe fn l___private_Init_Data_ByteArray_Lemmas_0__ByteArray_set_match__1_splitter___boxed(
    mut v_motive_62_: *mut crate::leanh::LeanObject,
    mut v_x_63_: *mut crate::leanh::LeanObject,
    mut v_x_64_: *mut crate::leanh::LeanObject,
    mut v_x_65_: *mut crate::leanh::LeanObject,
    mut v_x_66_: *mut crate::leanh::LeanObject,
    mut v_h__1_67_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_48__boxed_68_: u8 = 0;
    let mut v_res_69_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_48__boxed_68_ = (crate::leanh::lean_unbox(v_x_65_) as u8);
    v_res_69_ = l___private_Init_Data_ByteArray_Lemmas_0__ByteArray_set_match__1_splitter(
        v_motive_62_,
        v_x_63_,
        v_x_64_,
        v_x_48__boxed_68_,
        v_x_66_,
        v_h__1_67_,
    );
    return v_res_69_;
}
pub unsafe fn l___private_Init_Data_ByteArray_Lemmas_0__ByteArray_size_match__1_splitter___redArg(
    mut v_x_70_: *mut crate::leanh::LeanObject,
    mut v_h__1_71_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_data_72_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_73_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_data_72_ = lean_byte_array_data(v_x_70_);
    v___x_73_ = crate::leanh::lean_apply_1(v_h__1_71_, v_data_72_);
    return v___x_73_;
}
pub unsafe fn l___private_Init_Data_ByteArray_Lemmas_0__ByteArray_size_match__1_splitter(
    mut v_motive_74_: *mut crate::leanh::LeanObject,
    mut v_x_75_: *mut crate::leanh::LeanObject,
    mut v_h__1_76_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_data_77_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_78_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_data_77_ = lean_byte_array_data(v_x_75_);
    v___x_78_ = crate::leanh::lean_apply_1(v_h__1_76_, v_data_77_);
    return v___x_78_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_ByteArray_Lemmas(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_ByteArray_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_ByCases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Bootstrap(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Extract(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Lemmas(builtin);
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
pub unsafe fn meta_initialize_Init_Data_ByteArray_Lemmas(
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
pub unsafe fn initialize_Init_Data_ByteArray_Lemmas(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_ByteArray_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_ByCases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_Bootstrap(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_Extract(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_ByteArray_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_ByteArray_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_ByteArray_Lemmas(builtin);
}
