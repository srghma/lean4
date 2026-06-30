// Lean compiler output
// Module: Init.Data.Array.Erase
// Imports: Init.Data.Array.Basic Init.Data.Array.Lemmas Init.Data.Array.Bootstrap Init.Data.Bool Init.Data.List.Erase Init.Data.List.Nat.Basic Init.Data.List.Nat.Erase Init.Data.List.TakeDrop Init.Omega
use crate::r#gen::Init::Data::Array::Basic::{
    initialize_Init_Data_Array_Basic, runtime_initialize_Init_Data_Array_Basic,
};
use crate::r#gen::Init::Data::Array::Bootstrap::{
    initialize_Init_Data_Array_Bootstrap, runtime_initialize_Init_Data_Array_Bootstrap,
};
use crate::r#gen::Init::Data::Array::Lemmas::{
    initialize_Init_Data_Array_Lemmas, runtime_initialize_Init_Data_Array_Lemmas,
};
use crate::r#gen::Init::Data::Bool::{
    initialize_Init_Data_Bool, runtime_initialize_Init_Data_Bool,
};
use crate::r#gen::Init::Data::List::Erase::{
    initialize_Init_Data_List_Erase, runtime_initialize_Init_Data_List_Erase,
};
use crate::r#gen::Init::Data::List::Nat::Basic::{
    initialize_Init_Data_List_Nat_Basic, runtime_initialize_Init_Data_List_Nat_Basic,
};
use crate::r#gen::Init::Data::List::Nat::Erase::{
    initialize_Init_Data_List_Nat_Erase, runtime_initialize_Init_Data_List_Nat_Erase,
};
use crate::r#gen::Init::Data::List::TakeDrop::{
    initialize_Init_Data_List_TakeDrop, runtime_initialize_Init_Data_List_TakeDrop,
};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
pub unsafe fn l___private_Init_Data_Array_Erase_0__Array_eraseP__filterMap_match__1_splitter___redArg(
    mut v_x_33_: *mut leanh::LeanObject,
    mut v_h__1_34_: *mut leanh::LeanObject,
    mut v_h__2_35_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_33_) == 0 {
        let mut v___x_36_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_37_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_34_);
        v___x_36_ = leanh::lean_box(0);
        v___x_37_ = leanh::lean_apply_1(v_h__2_35_, v___x_36_);
        return v___x_37_;
    } else {
        let mut v_val_38_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_39_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_35_);
        v_val_38_ = leanh::lean_ctor_get(v_x_33_, 0);
        leanh::lean_inc(v_val_38_);
        leanh::lean_dec_ref_known(v_x_33_, 1);
        v___x_39_ = leanh::lean_apply_1(v_h__1_34_, v_val_38_);
        return v___x_39_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Erase_0__Array_eraseP__filterMap_match__1_splitter(
    mut v_00_u03b2_40_: *mut leanh::LeanObject,
    mut v_motive_41_: *mut leanh::LeanObject,
    mut v_x_42_: *mut leanh::LeanObject,
    mut v_h__1_43_: *mut leanh::LeanObject,
    mut v_h__2_44_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_42_) == 0 {
        let mut v___x_45_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_46_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_43_);
        v___x_45_ = leanh::lean_box(0);
        v___x_46_ = leanh::lean_apply_1(v_h__2_44_, v___x_45_);
        return v___x_46_;
    } else {
        let mut v_val_47_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_48_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_44_);
        v_val_47_ = leanh::lean_ctor_get(v_x_42_, 0);
        leanh::lean_inc(v_val_47_);
        leanh::lean_dec_ref_known(v_x_42_, 1);
        v___x_48_ = leanh::lean_apply_1(v_h__1_43_, v_val_47_);
        return v___x_48_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Erase_0__List_eraseP__filterMap_match__1_splitter___redArg(
    mut v_x_49_: *mut leanh::LeanObject,
    mut v_h__1_50_: *mut leanh::LeanObject,
    mut v_h__2_51_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_49_) == 0 {
        let mut v___x_52_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_53_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_50_);
        v___x_52_ = leanh::lean_box(0);
        v___x_53_ = leanh::lean_apply_1(v_h__2_51_, v___x_52_);
        return v___x_53_;
    } else {
        let mut v_val_54_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_55_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_51_);
        v_val_54_ = leanh::lean_ctor_get(v_x_49_, 0);
        leanh::lean_inc(v_val_54_);
        leanh::lean_dec_ref_known(v_x_49_, 1);
        v___x_55_ = leanh::lean_apply_1(v_h__1_50_, v_val_54_);
        return v___x_55_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Erase_0__List_eraseP__filterMap_match__1_splitter(
    mut v_00_u03b2_56_: *mut leanh::LeanObject,
    mut v_motive_57_: *mut leanh::LeanObject,
    mut v_x_58_: *mut leanh::LeanObject,
    mut v_h__1_59_: *mut leanh::LeanObject,
    mut v_h__2_60_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_58_) == 0 {
        let mut v___x_61_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_62_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_59_);
        v___x_61_ = leanh::lean_box(0);
        v___x_62_ = leanh::lean_apply_1(v_h__2_60_, v___x_61_);
        return v___x_62_;
    } else {
        let mut v_val_63_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_64_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_60_);
        v_val_63_ = leanh::lean_ctor_get(v_x_58_, 0);
        leanh::lean_inc(v_val_63_);
        leanh::lean_dec_ref_known(v_x_58_, 1);
        v___x_64_ = leanh::lean_apply_1(v_h__1_59_, v_val_63_);
        return v___x_64_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Array_Erase(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Array_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Bootstrap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Bool(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Erase(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Nat_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Nat_Erase(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_TakeDrop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Array_Erase(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Array_Erase(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Array_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_Bootstrap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Bool(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Erase(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Nat_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Nat_Erase(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_TakeDrop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Erase(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Array_Erase(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_Array_Erase(builtin);
}