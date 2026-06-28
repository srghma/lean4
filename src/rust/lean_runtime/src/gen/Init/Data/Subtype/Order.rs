// Lean compiler output
// Module: Init.Data.Subtype.Order
// Imports: Init.Data.Order.Classes Init.Data.Order.Lemmas Init.Ext
use crate::r#gen::Init::Data::Order::Classes::{
    initialize_Init_Data_Order_Classes, runtime_initialize_Init_Data_Order_Classes,
};
use crate::r#gen::Init::Data::Order::Lemmas::{
    initialize_Init_Data_Order_Lemmas, runtime_initialize_Init_Data_Order_Lemmas,
};
use crate::r#gen::Init::Ext::{initialize_Init_Ext, runtime_initialize_Init_Ext};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_apply_2, lean_box, lean_closure_set,
    lean_dec_ref, lean_io_result_is_error, lean_io_result_mk_ok,
};
pub unsafe fn l_Subtype_instLE(
    mut v_00_u03b1_32_: *mut LeanObject,
    mut v_inst_33_: *mut LeanObject,
    mut v_P_34_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_35_: *mut LeanObject = core::ptr::null_mut();
    v___x_35_ = lean_box(0);
    return v___x_35_;
}
pub unsafe fn l_Subtype_instLT(
    mut v_00_u03b1_36_: *mut LeanObject,
    mut v_inst_37_: *mut LeanObject,
    mut v_P_38_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_39_: *mut LeanObject = core::ptr::null_mut();
    v___x_39_ = lean_box(0);
    return v___x_39_;
}
pub unsafe fn l_Subtype_instMin___redArg___lam__0(
    mut v_inst_40_: *mut LeanObject,
    mut v_a_41_: *mut LeanObject,
    mut v_b_42_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_43_: *mut LeanObject = core::ptr::null_mut();
    v___x_43_ = lean_apply_2(v_inst_40_, v_a_41_, v_b_42_);
    return v___x_43_;
}
pub unsafe fn l_Subtype_instMin___redArg(mut v_inst_44_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_45_: *mut LeanObject = core::ptr::null_mut();
    v___f_45_ = lean_alloc_closure(
        l_Subtype_instMin___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_45_, 0, v_inst_44_);
    return v___f_45_;
}
pub unsafe fn l_Subtype_instMin(
    mut v_00_u03b1_46_: *mut LeanObject,
    mut v_inst_47_: *mut LeanObject,
    mut v_inst_48_: *mut LeanObject,
    mut v_P_49_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_50_: *mut LeanObject = core::ptr::null_mut();
    v___f_50_ = lean_alloc_closure(
        l_Subtype_instMin___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_50_, 0, v_inst_47_);
    return v___f_50_;
}
pub unsafe fn l_Subtype_instMax___redArg(mut v_inst_51_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_52_: *mut LeanObject = core::ptr::null_mut();
    v___f_52_ = lean_alloc_closure(
        l_Subtype_instMin___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_52_, 0, v_inst_51_);
    return v___f_52_;
}
pub unsafe fn l_Subtype_instMax(
    mut v_00_u03b1_53_: *mut LeanObject,
    mut v_inst_54_: *mut LeanObject,
    mut v_inst_55_: *mut LeanObject,
    mut v_P_56_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_57_: *mut LeanObject = core::ptr::null_mut();
    v___f_57_ = lean_alloc_closure(
        l_Subtype_instMin___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_57_, 0, v_inst_54_);
    return v___f_57_;
}
pub unsafe fn l_Subtype_instTransLE(
    mut v_00_u03b1_58_: *mut LeanObject,
    mut v_inst_59_: *mut LeanObject,
    mut v_i_60_: *mut LeanObject,
    mut v_P_61_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_62_: *mut LeanObject = core::ptr::null_mut();
    v___x_62_ = lean_box(0);
    return v___x_62_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Subtype_Order(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Order_Classes(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Order_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Ext(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Subtype_Order(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Subtype_Order(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Order_Classes(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Order_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Ext(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Subtype_Order(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_Subtype_Order(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_Subtype_Order(builtin);
}
