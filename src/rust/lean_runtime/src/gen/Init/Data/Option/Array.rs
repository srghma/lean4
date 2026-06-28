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
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_apply_1, lean_box, lean_ctor_get, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_inc, lean_io_result_is_error, lean_io_result_mk_ok, lean_obj_tag,
};
pub unsafe fn l___private_Init_Data_Option_Array_0__List_forIn_x27__cons_match__1_splitter___redArg(
    mut v_x_17_: *mut LeanObject,
    mut v_h__1_18_: *mut LeanObject,
    mut v_h__2_19_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_17_) == 0 {
        let mut v_a_20_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_21_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_19_);
        v_a_20_ = lean_ctor_get(v_x_17_, 0);
        lean_inc(v_a_20_);
        lean_dec_ref_known(v_x_17_, 1);
        v___x_21_ = lean_apply_1(v_h__1_18_, v_a_20_);
        return v___x_21_;
    } else {
        let mut v_a_22_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_23_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_18_);
        v_a_22_ = lean_ctor_get(v_x_17_, 0);
        lean_inc(v_a_22_);
        lean_dec_ref_known(v_x_17_, 1);
        v___x_23_ = lean_apply_1(v_h__2_19_, v_a_22_);
        return v___x_23_;
    }
}
pub unsafe fn l___private_Init_Data_Option_Array_0__List_forIn_x27__cons_match__1_splitter(
    mut v_00_u03b2_24_: *mut LeanObject,
    mut v_motive_25_: *mut LeanObject,
    mut v_x_26_: *mut LeanObject,
    mut v_h__1_27_: *mut LeanObject,
    mut v_h__2_28_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_26_) == 0 {
        let mut v_a_29_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_30_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_28_);
        v_a_29_ = lean_ctor_get(v_x_26_, 0);
        lean_inc(v_a_29_);
        lean_dec_ref_known(v_x_26_, 1);
        v___x_30_ = lean_apply_1(v_h__1_27_, v_a_29_);
        return v___x_30_;
    } else {
        let mut v_a_31_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_32_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_27_);
        v_a_31_ = lean_ctor_get(v_x_26_, 0);
        lean_inc(v_a_31_);
        lean_dec_ref_known(v_x_26_, 1);
        v___x_32_ = lean_apply_1(v_h__2_28_, v_a_31_);
        return v___x_32_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Option_Array(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Option_Instances(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Control_Lawful(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Bootstrap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Bool(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Zip(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_List(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Option_Array(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Option_Array(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Option_Instances(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Control_Lawful(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Option_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Array_Bootstrap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Array_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Bool(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_Zip(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Option_List(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Array(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_Option_Array(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_Option_Array(builtin);
}
