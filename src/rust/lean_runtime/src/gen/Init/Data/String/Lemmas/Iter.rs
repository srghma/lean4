// Lean compiler output
// Module: Init.Data.String.Lemmas.Iter
// Imports: Init.Data.String.Iter.Intercalate Init.Data.String.Slice Init.Data.String.Iter.Intercalate Init.Data.String.Defs Init.Data.String.Lemmas.Intercalate Init.Data.Iterators.Lemmas.Consumers.Loop Init.Data.Iterators.Lemmas.Combinators.FilterMap
use crate::r#gen::Init::Data::Iterators::Lemmas::Combinators::FilterMap::{
    initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap,
    runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap,
};
use crate::r#gen::Init::Data::Iterators::Lemmas::Consumers::Loop::{
    initialize_Init_Data_Iterators_Lemmas_Consumers_Loop,
    runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Loop,
};
use crate::r#gen::Init::Data::String::Defs::{
    initialize_Init_Data_String_Defs, runtime_initialize_Init_Data_String_Defs,
};
use crate::r#gen::Init::Data::String::Iter::Intercalate::{
    initialize_Init_Data_String_Iter_Intercalate,
    runtime_initialize_Init_Data_String_Iter_Intercalate,
};
use crate::r#gen::Init::Data::String::Lemmas::Intercalate::{
    initialize_Init_Data_String_Lemmas_Intercalate,
    runtime_initialize_Init_Data_String_Lemmas_Intercalate,
};
use crate::r#gen::Init::Data::String::Slice::{
    initialize_Init_Data_String_Slice, runtime_initialize_Init_Data_String_Slice,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_apply_1, lean_apply_2, lean_box, lean_ctor_get, lean_dec,
    lean_dec_ref, lean_dec_ref_known, lean_inc, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_obj_tag,
};
pub unsafe fn l___private_Init_Data_String_Lemmas_Iter_0__Std_Iter_intercalateString_match__1_splitter___redArg(
    mut v_x_31_: *mut LeanObject,
    mut v_x_32_: *mut LeanObject,
    mut v_h__1_33_: *mut LeanObject,
    mut v_h__2_34_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_31_) == 0 {
        let mut v___x_35_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_34_);
        v___x_35_ = lean_apply_1(v_h__1_33_, v_x_32_);
        return v___x_35_;
    } else {
        let mut v_val_36_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_37_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_33_);
        v_val_36_ = lean_ctor_get(v_x_31_, 0);
        lean_inc(v_val_36_);
        lean_dec_ref_known(v_x_31_, 1);
        v___x_37_ = lean_apply_2(v_h__2_34_, v_val_36_, v_x_32_);
        return v___x_37_;
    }
}
pub unsafe fn l___private_Init_Data_String_Lemmas_Iter_0__Std_Iter_intercalateString_match__1_splitter(
    mut v_motive_38_: *mut LeanObject,
    mut v_x_39_: *mut LeanObject,
    mut v_x_40_: *mut LeanObject,
    mut v_h__1_41_: *mut LeanObject,
    mut v_h__2_42_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_39_) == 0 {
        let mut v___x_43_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_42_);
        v___x_43_ = lean_apply_1(v_h__1_41_, v_x_40_);
        return v___x_43_;
    } else {
        let mut v_val_44_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_45_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_41_);
        v_val_44_ = lean_ctor_get(v_x_39_, 0);
        lean_inc(v_val_44_);
        lean_dec_ref_known(v_x_39_, 1);
        v___x_45_ = lean_apply_2(v_h__2_42_, v_val_44_, v_x_40_);
        return v___x_45_;
    }
}
pub unsafe fn l___private_Init_Data_String_Lemmas_Iter_0__Std_Iter_intercalateString__eq_match__1__4_splitter___redArg(
    mut v_x_46_: *mut LeanObject,
    mut v_x_47_: *mut LeanObject,
    mut v_h__1_48_: *mut LeanObject,
    mut v_h__2_49_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_46_) == 0 {
        let mut v___x_50_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_49_);
        v___x_50_ = lean_apply_1(v_h__1_48_, v_x_47_);
        return v___x_50_;
    } else {
        let mut v_val_51_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_52_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_48_);
        v_val_51_ = lean_ctor_get(v_x_46_, 0);
        lean_inc(v_val_51_);
        lean_dec_ref_known(v_x_46_, 1);
        v___x_52_ = lean_apply_2(v_h__2_49_, v_val_51_, v_x_47_);
        return v___x_52_;
    }
}
pub unsafe fn l___private_Init_Data_String_Lemmas_Iter_0__Std_Iter_intercalateString__eq_match__1__4_splitter(
    mut v_motive_53_: *mut LeanObject,
    mut v_x_54_: *mut LeanObject,
    mut v_x_55_: *mut LeanObject,
    mut v_h__1_56_: *mut LeanObject,
    mut v_h__2_57_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_54_) == 0 {
        let mut v___x_58_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_57_);
        v___x_58_ = lean_apply_1(v_h__1_56_, v_x_55_);
        return v___x_58_;
    } else {
        let mut v_val_59_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_60_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_56_);
        v_val_59_ = lean_ctor_get(v_x_54_, 0);
        lean_inc(v_val_59_);
        lean_dec_ref_known(v_x_54_, 1);
        v___x_60_ = lean_apply_2(v_h__2_57_, v_val_59_, v_x_55_);
        return v___x_60_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_String_Lemmas_Iter(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_String_Iter_Intercalate(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Slice(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Defs(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_Intercalate(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Loop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_String_Lemmas_Iter(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_String_Lemmas_Iter(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_String_Iter_Intercalate(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_String_Slice(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_String_Defs(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_String_Lemmas_Intercalate(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Consumers_Loop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_Iter(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_String_Lemmas_Iter(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_String_Lemmas_Iter(builtin);
}
