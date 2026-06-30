// Lean compiler output
// Module: Init.Data.Option.Array
// Imports: Init.Data.Option.Instances Init.Control.Lawful Init.Data.Option.Lemmas Init.Data.Array.Bootstrap Init.Data.Array.Lemmas Init.Data.Bool Init.Data.List.Zip Init.Data.Option.List
use crate::r#gen::Init::Control::Lawful::{
    initialize_Init_Control_Lawful, runtime_initialize_Init_Control_Lawful,
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
use crate::r#gen::Init::Data::List::Zip::{
    initialize_Init_Data_List_Zip, runtime_initialize_Init_Data_List_Zip,
};
use crate::r#gen::Init::Data::Option::Instances::{
    initialize_Init_Data_Option_Instances, runtime_initialize_Init_Data_Option_Instances,
};
use crate::r#gen::Init::Data::Option::Lemmas::{
    initialize_Init_Data_Option_Lemmas, runtime_initialize_Init_Data_Option_Lemmas,
};
use crate::r#gen::Init::Data::Option::List::{
    initialize_Init_Data_Option_List, runtime_initialize_Init_Data_Option_List,
};
pub unsafe fn l___private_Init_Data_Option_Array_0__List_forIn_x27__cons_match__1_splitter___redArg(
    mut v_x_17_: *mut leanh::LeanObject,
    mut v_h__1_18_: *mut leanh::LeanObject,
    mut v_h__2_19_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_17_) == 0 {
        let mut v_a_20_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_21_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_19_);
        v_a_20_ = leanh::lean_ctor_get(v_x_17_, 0);
        leanh::lean_inc(v_a_20_);
        leanh::lean_dec_ref_known(v_x_17_, 1);
        v___x_21_ = leanh::lean_apply_1(v_h__1_18_, v_a_20_);
        return v___x_21_;
    } else {
        let mut v_a_22_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_23_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_18_);
        v_a_22_ = leanh::lean_ctor_get(v_x_17_, 0);
        leanh::lean_inc(v_a_22_);
        leanh::lean_dec_ref_known(v_x_17_, 1);
        v___x_23_ = leanh::lean_apply_1(v_h__2_19_, v_a_22_);
        return v___x_23_;
    }
}
pub unsafe fn l___private_Init_Data_Option_Array_0__List_forIn_x27__cons_match__1_splitter(
    mut v_00_u03b2_24_: *mut leanh::LeanObject,
    mut v_motive_25_: *mut leanh::LeanObject,
    mut v_x_26_: *mut leanh::LeanObject,
    mut v_h__1_27_: *mut leanh::LeanObject,
    mut v_h__2_28_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_26_) == 0 {
        let mut v_a_29_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_30_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_28_);
        v_a_29_ = leanh::lean_ctor_get(v_x_26_, 0);
        leanh::lean_inc(v_a_29_);
        leanh::lean_dec_ref_known(v_x_26_, 1);
        v___x_30_ = leanh::lean_apply_1(v_h__1_27_, v_a_29_);
        return v___x_30_;
    } else {
        let mut v_a_31_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_32_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_27_);
        v_a_31_ = leanh::lean_ctor_get(v_x_26_, 0);
        leanh::lean_inc(v_a_31_);
        leanh::lean_dec_ref_known(v_x_26_, 1);
        v___x_32_ = leanh::lean_apply_1(v_h__2_28_, v_a_31_);
        return v___x_32_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Option_Array(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Option_Instances(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Control_Lawful(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Bootstrap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Bool(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Zip(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_List(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Option_Array(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Option_Array(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Option_Instances(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Control_Lawful(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Option_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_Bootstrap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Bool(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Zip(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Option_List(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Array(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Option_Array(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_Option_Array(builtin);
}