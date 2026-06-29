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
pub unsafe fn l___private_Init_Data_String_Lemmas_Iter_0__Std_Iter_intercalateString_match__1_splitter___redArg(
    mut v_x_31_: *mut crate::leanh::LeanObject,
    mut v_x_32_: *mut crate::leanh::LeanObject,
    mut v_h__1_33_: *mut crate::leanh::LeanObject,
    mut v_h__2_34_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_31_) == 0 {
        let mut v___x_35_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_34_);
        v___x_35_ = crate::leanh::lean_apply_1(v_h__1_33_, v_x_32_);
        return v___x_35_;
    } else {
        let mut v_val_36_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_37_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_33_);
        v_val_36_ = crate::leanh::lean_ctor_get(v_x_31_, 0);
        crate::leanh::lean_inc(v_val_36_);
        crate::leanh::lean_dec_ref_known(v_x_31_, 1);
        v___x_37_ = crate::leanh::lean_apply_2(v_h__2_34_, v_val_36_, v_x_32_);
        return v___x_37_;
    }
}
pub unsafe fn l___private_Init_Data_String_Lemmas_Iter_0__Std_Iter_intercalateString_match__1_splitter(
    mut v_motive_38_: *mut crate::leanh::LeanObject,
    mut v_x_39_: *mut crate::leanh::LeanObject,
    mut v_x_40_: *mut crate::leanh::LeanObject,
    mut v_h__1_41_: *mut crate::leanh::LeanObject,
    mut v_h__2_42_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_39_) == 0 {
        let mut v___x_43_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_42_);
        v___x_43_ = crate::leanh::lean_apply_1(v_h__1_41_, v_x_40_);
        return v___x_43_;
    } else {
        let mut v_val_44_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_45_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_41_);
        v_val_44_ = crate::leanh::lean_ctor_get(v_x_39_, 0);
        crate::leanh::lean_inc(v_val_44_);
        crate::leanh::lean_dec_ref_known(v_x_39_, 1);
        v___x_45_ = crate::leanh::lean_apply_2(v_h__2_42_, v_val_44_, v_x_40_);
        return v___x_45_;
    }
}
pub unsafe fn l___private_Init_Data_String_Lemmas_Iter_0__Std_Iter_intercalateString__eq_match__1__4_splitter___redArg(
    mut v_x_46_: *mut crate::leanh::LeanObject,
    mut v_x_47_: *mut crate::leanh::LeanObject,
    mut v_h__1_48_: *mut crate::leanh::LeanObject,
    mut v_h__2_49_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_46_) == 0 {
        let mut v___x_50_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_49_);
        v___x_50_ = crate::leanh::lean_apply_1(v_h__1_48_, v_x_47_);
        return v___x_50_;
    } else {
        let mut v_val_51_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_52_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_48_);
        v_val_51_ = crate::leanh::lean_ctor_get(v_x_46_, 0);
        crate::leanh::lean_inc(v_val_51_);
        crate::leanh::lean_dec_ref_known(v_x_46_, 1);
        v___x_52_ = crate::leanh::lean_apply_2(v_h__2_49_, v_val_51_, v_x_47_);
        return v___x_52_;
    }
}
pub unsafe fn l___private_Init_Data_String_Lemmas_Iter_0__Std_Iter_intercalateString__eq_match__1__4_splitter(
    mut v_motive_53_: *mut crate::leanh::LeanObject,
    mut v_x_54_: *mut crate::leanh::LeanObject,
    mut v_x_55_: *mut crate::leanh::LeanObject,
    mut v_h__1_56_: *mut crate::leanh::LeanObject,
    mut v_h__2_57_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_54_) == 0 {
        let mut v___x_58_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_57_);
        v___x_58_ = crate::leanh::lean_apply_1(v_h__1_56_, v_x_55_);
        return v___x_58_;
    } else {
        let mut v_val_59_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_60_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_56_);
        v_val_59_ = crate::leanh::lean_ctor_get(v_x_54_, 0);
        crate::leanh::lean_inc(v_val_59_);
        crate::leanh::lean_dec_ref_known(v_x_54_, 1);
        v___x_60_ = crate::leanh::lean_apply_2(v_h__2_57_, v_val_59_, v_x_55_);
        return v___x_60_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_String_Lemmas_Iter(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_String_Iter_Intercalate(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Slice(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Iter_Intercalate(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Defs(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_Intercalate(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Loop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_String_Lemmas_Iter(
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
pub unsafe fn initialize_Init_Data_String_Lemmas_Iter(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_String_Iter_Intercalate(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Slice(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Iter_Intercalate(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Defs(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Lemmas_Intercalate(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Consumers_Loop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_Iter(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_String_Lemmas_Iter(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_String_Lemmas_Iter(builtin);
}
