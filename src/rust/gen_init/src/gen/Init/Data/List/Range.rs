// Lean compiler output
// Module: Init.Data.List.Range
// Imports: Init.BinderPredicates Init.Ext Init.NotationExtra Init.Data.List.Lemmas Init.Data.List.Sublist Init.Data.List.Zip Init.Data.Option.Lemmas
use crate::r#gen::Init::BinderPredicates::{
    initialize_Init_BinderPredicates, runtime_initialize_Init_BinderPredicates,
};
use crate::r#gen::Init::Data::List::Lemmas::{
    initialize_Init_Data_List_Lemmas, runtime_initialize_Init_Data_List_Lemmas,
};
use crate::r#gen::Init::Data::List::Sublist::{
    initialize_Init_Data_List_Sublist, runtime_initialize_Init_Data_List_Sublist,
};
use crate::r#gen::Init::Data::List::Zip::{
    initialize_Init_Data_List_Zip, runtime_initialize_Init_Data_List_Zip,
};
use crate::r#gen::Init::Data::Option::Lemmas::{
    initialize_Init_Data_Option_Lemmas, runtime_initialize_Init_Data_Option_Lemmas,
};
use crate::r#gen::Init::Ext::{initialize_Init_Ext, runtime_initialize_Init_Ext};
use crate::r#gen::Init::NotationExtra::{
    initialize_Init_NotationExtra, runtime_initialize_Init_NotationExtra,
};
use crate::ffi::{lean_nat_dec_eq, lean_nat_sub};
pub unsafe fn l___private_Init_Data_List_Range_0__List_range_x27_match__1_splitter___redArg(
    mut v_x_37_: *mut crate::leanh::LeanObject,
    mut v_x_38_: *mut crate::leanh::LeanObject,
    mut v_x_39_: *mut crate::leanh::LeanObject,
    mut v_h__1_40_: *mut crate::leanh::LeanObject,
    mut v_h__2_41_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_42_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_43_: u8 = 0;
    v_zero_42_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_43_ = lean_nat_dec_eq(v_x_38_, v_zero_42_);
    if v_isZero_43_ == 1 {
        let mut v___x_44_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_41_);
        v___x_44_ = crate::leanh::lean_apply_2(v_h__1_40_, v_x_37_, v_x_39_);
        return v___x_44_;
    } else {
        let mut v_one_45_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_46_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_47_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_40_);
        v_one_45_ = crate::leanh::lean_unsigned_to_nat(1);
        v_n_46_ = lean_nat_sub(v_x_38_, v_one_45_);
        v___x_47_ = crate::leanh::lean_apply_3(v_h__2_41_, v_x_37_, v_n_46_, v_x_39_);
        return v___x_47_;
    }
}
pub unsafe fn l___private_Init_Data_List_Range_0__List_range_x27_match__1_splitter___redArg___boxed(
    mut v_x_48_: *mut crate::leanh::LeanObject,
    mut v_x_49_: *mut crate::leanh::LeanObject,
    mut v_x_50_: *mut crate::leanh::LeanObject,
    mut v_h__1_51_: *mut crate::leanh::LeanObject,
    mut v_h__2_52_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_53_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_53_ = l___private_Init_Data_List_Range_0__List_range_x27_match__1_splitter___redArg(
        v_x_48_, v_x_49_, v_x_50_, v_h__1_51_, v_h__2_52_,
    );
    crate::leanh::lean_dec(v_x_49_);
    return v_res_53_;
}
pub unsafe fn l___private_Init_Data_List_Range_0__List_range_x27_match__1_splitter(
    mut v_motive_54_: *mut crate::leanh::LeanObject,
    mut v_x_55_: *mut crate::leanh::LeanObject,
    mut v_x_56_: *mut crate::leanh::LeanObject,
    mut v_x_57_: *mut crate::leanh::LeanObject,
    mut v_h__1_58_: *mut crate::leanh::LeanObject,
    mut v_h__2_59_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_60_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_61_: u8 = 0;
    v_zero_60_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_61_ = lean_nat_dec_eq(v_x_56_, v_zero_60_);
    if v_isZero_61_ == 1 {
        let mut v___x_62_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_59_);
        v___x_62_ = crate::leanh::lean_apply_2(v_h__1_58_, v_x_55_, v_x_57_);
        return v___x_62_;
    } else {
        let mut v_one_63_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_64_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_65_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_58_);
        v_one_63_ = crate::leanh::lean_unsigned_to_nat(1);
        v_n_64_ = lean_nat_sub(v_x_56_, v_one_63_);
        v___x_65_ = crate::leanh::lean_apply_3(v_h__2_59_, v_x_55_, v_n_64_, v_x_57_);
        return v___x_65_;
    }
}
pub unsafe fn l___private_Init_Data_List_Range_0__List_range_x27_match__1_splitter___boxed(
    mut v_motive_66_: *mut crate::leanh::LeanObject,
    mut v_x_67_: *mut crate::leanh::LeanObject,
    mut v_x_68_: *mut crate::leanh::LeanObject,
    mut v_x_69_: *mut crate::leanh::LeanObject,
    mut v_h__1_70_: *mut crate::leanh::LeanObject,
    mut v_h__2_71_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_72_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_72_ = l___private_Init_Data_List_Range_0__List_range_x27_match__1_splitter(
        v_motive_66_,
        v_x_67_,
        v_x_68_,
        v_x_69_,
        v_h__1_70_,
        v_h__2_71_,
    );
    crate::leanh::lean_dec(v_x_68_);
    return v_res_72_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_List_Range(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_BinderPredicates(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Ext(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_NotationExtra(builtin);
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
    res = runtime_initialize_Init_Data_List_Zip(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_List_Range(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_List_Range(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_BinderPredicates(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Ext(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_NotationExtra(builtin);
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
    res = initialize_Init_Data_List_Zip(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Option_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Range(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_List_Range(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_List_Range(builtin);
}
