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
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_apply_1, lean_box, lean_ctor_get, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_inc, lean_io_result_is_error, lean_io_result_mk_ok, lean_obj_tag,
};
pub unsafe fn l___private_Init_Data_Array_Erase_0__Array_eraseP__filterMap_match__1_splitter___redArg(
    mut v_x_33_: *mut LeanObject,
    mut v_h__1_34_: *mut LeanObject,
    mut v_h__2_35_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_33_) == 0 {
        let mut v___x_36_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_37_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_34_);
        v___x_36_ = lean_box(0);
        v___x_37_ = lean_apply_1(v_h__2_35_, v___x_36_);
        return v___x_37_;
    } else {
        let mut v_val_38_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_39_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_35_);
        v_val_38_ = lean_ctor_get(v_x_33_, 0);
        lean_inc(v_val_38_);
        lean_dec_ref_known(v_x_33_, 1);
        v___x_39_ = lean_apply_1(v_h__1_34_, v_val_38_);
        return v___x_39_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Erase_0__Array_eraseP__filterMap_match__1_splitter(
    mut v_00_u03b2_40_: *mut LeanObject,
    mut v_motive_41_: *mut LeanObject,
    mut v_x_42_: *mut LeanObject,
    mut v_h__1_43_: *mut LeanObject,
    mut v_h__2_44_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_42_) == 0 {
        let mut v___x_45_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_46_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_43_);
        v___x_45_ = lean_box(0);
        v___x_46_ = lean_apply_1(v_h__2_44_, v___x_45_);
        return v___x_46_;
    } else {
        let mut v_val_47_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_48_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_44_);
        v_val_47_ = lean_ctor_get(v_x_42_, 0);
        lean_inc(v_val_47_);
        lean_dec_ref_known(v_x_42_, 1);
        v___x_48_ = lean_apply_1(v_h__1_43_, v_val_47_);
        return v___x_48_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Erase_0__List_eraseP__filterMap_match__1_splitter___redArg(
    mut v_x_49_: *mut LeanObject,
    mut v_h__1_50_: *mut LeanObject,
    mut v_h__2_51_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_49_) == 0 {
        let mut v___x_52_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_53_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_50_);
        v___x_52_ = lean_box(0);
        v___x_53_ = lean_apply_1(v_h__2_51_, v___x_52_);
        return v___x_53_;
    } else {
        let mut v_val_54_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_55_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_51_);
        v_val_54_ = lean_ctor_get(v_x_49_, 0);
        lean_inc(v_val_54_);
        lean_dec_ref_known(v_x_49_, 1);
        v___x_55_ = lean_apply_1(v_h__1_50_, v_val_54_);
        return v___x_55_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Erase_0__List_eraseP__filterMap_match__1_splitter(
    mut v_00_u03b2_56_: *mut LeanObject,
    mut v_motive_57_: *mut LeanObject,
    mut v_x_58_: *mut LeanObject,
    mut v_h__1_59_: *mut LeanObject,
    mut v_h__2_60_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_58_) == 0 {
        let mut v___x_61_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_62_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_59_);
        v___x_61_ = lean_box(0);
        v___x_62_ = lean_apply_1(v_h__2_60_, v___x_61_);
        return v___x_62_;
    } else {
        let mut v_val_63_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_64_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_60_);
        v_val_63_ = lean_ctor_get(v_x_58_, 0);
        lean_inc(v_val_63_);
        lean_dec_ref_known(v_x_58_, 1);
        v___x_64_ = lean_apply_1(v_h__1_59_, v_val_63_);
        return v___x_64_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Array_Erase(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Array_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Bootstrap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Bool(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Erase(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Nat_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Nat_Erase(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_TakeDrop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Array_Erase(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Array_Erase(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Array_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Array_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Array_Bootstrap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Bool(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_Erase(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_Nat_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_Nat_Erase(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_TakeDrop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Erase(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_Array_Erase(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_Array_Erase(builtin);
}
