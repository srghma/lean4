// Lean compiler output
// Module: Init.Data.Slice.Array.Lemmas
// Imports: Init.Data.Slice.Array.Iterator Init.Data.Array.Subarray Init.Data.Slice.Array.Basic Init.Data.Slice.Lemmas Init.Data.Slice.Array.Iterator Init.Data.Slice.Operations Init.Data.Range.Polymorphic.Iterators Init.Data.Range.Polymorphic.Lemmas Init.Data.Slice.List.Lemmas Init.Data.List.Control Init.Data.Nat.MinMax Init.Data.Slice.Array.Basic Init.Data.List.Nat.TakeDrop Init.Data.List.TakeDrop Init.Data.Array.Subarray.Split Init.Data.Array.Subarray.Split Init.Data.Slice.InternalLemmas
use crate::r#gen::Init::Data::Array::Subarray::Split::{
    initialize_Init_Data_Array_Subarray_Split, runtime_initialize_Init_Data_Array_Subarray_Split,
};
use crate::r#gen::Init::Data::Array::Subarray::{
    initialize_Init_Data_Array_Subarray, runtime_initialize_Init_Data_Array_Subarray,
};
use crate::r#gen::Init::Data::List::Control::{
    initialize_Init_Data_List_Control, runtime_initialize_Init_Data_List_Control,
};
use crate::r#gen::Init::Data::List::Nat::TakeDrop::{
    initialize_Init_Data_List_Nat_TakeDrop, runtime_initialize_Init_Data_List_Nat_TakeDrop,
};
use crate::r#gen::Init::Data::List::TakeDrop::{
    initialize_Init_Data_List_TakeDrop, runtime_initialize_Init_Data_List_TakeDrop,
};
use crate::r#gen::Init::Data::Nat::MinMax::{
    initialize_Init_Data_Nat_MinMax, runtime_initialize_Init_Data_Nat_MinMax,
};
use crate::r#gen::Init::Data::Range::Polymorphic::Iterators::{
    initialize_Init_Data_Range_Polymorphic_Iterators,
    runtime_initialize_Init_Data_Range_Polymorphic_Iterators,
};
use crate::r#gen::Init::Data::Range::Polymorphic::Lemmas::{
    initialize_Init_Data_Range_Polymorphic_Lemmas,
    runtime_initialize_Init_Data_Range_Polymorphic_Lemmas,
};
use crate::r#gen::Init::Data::Slice::Array::Basic::{
    initialize_Init_Data_Slice_Array_Basic, runtime_initialize_Init_Data_Slice_Array_Basic,
};
use crate::r#gen::Init::Data::Slice::Array::Iterator::{
    initialize_Init_Data_Slice_Array_Iterator, runtime_initialize_Init_Data_Slice_Array_Iterator,
};
use crate::r#gen::Init::Data::Slice::InternalLemmas::{
    initialize_Init_Data_Slice_InternalLemmas, runtime_initialize_Init_Data_Slice_InternalLemmas,
};
use crate::r#gen::Init::Data::Slice::Lemmas::{
    initialize_Init_Data_Slice_Lemmas, runtime_initialize_Init_Data_Slice_Lemmas,
};
use crate::r#gen::Init::Data::Slice::List::Lemmas::{
    initialize_Init_Data_Slice_List_Lemmas, runtime_initialize_Init_Data_Slice_List_Lemmas,
};
use crate::r#gen::Init::Data::Slice::Operations::{
    initialize_Init_Data_Slice_Operations, runtime_initialize_Init_Data_Slice_Operations,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_apply_1, lean_apply_2, lean_box, lean_ctor_get, lean_dec,
    lean_dec_ref, lean_dec_ref_known, lean_inc, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_obj_tag,
};
pub unsafe fn l___private_Init_Data_Slice_Array_Lemmas_0__Std_IterStep_successor_match__1_splitter___redArg(
    mut v_x_26_: *mut LeanObject,
    mut v_h__1_27_: *mut LeanObject,
    mut v_h__2_28_: *mut LeanObject,
    mut v_h__3_29_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_26_) {
        0 => {
            let mut v_it_30_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_31_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_32_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_29_);
            lean_dec(v_h__2_28_);
            v_it_30_ = lean_ctor_get(v_x_26_, 0);
            lean_inc(v_it_30_);
            v_out_31_ = lean_ctor_get(v_x_26_, 1);
            lean_inc(v_out_31_);
            lean_dec_ref_known(v_x_26_, 2);
            v___x_32_ = lean_apply_2(v_h__1_27_, v_it_30_, v_out_31_);
            return v___x_32_;
        }
        1 => {
            let mut v_it_33_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_34_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_29_);
            lean_dec(v_h__1_27_);
            v_it_33_ = lean_ctor_get(v_x_26_, 0);
            lean_inc(v_it_33_);
            lean_dec_ref_known(v_x_26_, 1);
            v___x_34_ = lean_apply_1(v_h__2_28_, v_it_33_);
            return v___x_34_;
        }
        _ => {
            let mut v___x_35_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_36_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_28_);
            lean_dec(v_h__1_27_);
            v___x_35_ = lean_box(0);
            v___x_36_ = lean_apply_1(v_h__3_29_, v___x_35_);
            return v___x_36_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Slice_Array_Lemmas_0__Std_IterStep_successor_match__1_splitter(
    mut v_00_u03b1_37_: *mut LeanObject,
    mut v_00_u03b2_38_: *mut LeanObject,
    mut v_motive_39_: *mut LeanObject,
    mut v_x_40_: *mut LeanObject,
    mut v_h__1_41_: *mut LeanObject,
    mut v_h__2_42_: *mut LeanObject,
    mut v_h__3_43_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_40_) {
        0 => {
            let mut v_it_44_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_45_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_46_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_43_);
            lean_dec(v_h__2_42_);
            v_it_44_ = lean_ctor_get(v_x_40_, 0);
            lean_inc(v_it_44_);
            v_out_45_ = lean_ctor_get(v_x_40_, 1);
            lean_inc(v_out_45_);
            lean_dec_ref_known(v_x_40_, 2);
            v___x_46_ = lean_apply_2(v_h__1_41_, v_it_44_, v_out_45_);
            return v___x_46_;
        }
        1 => {
            let mut v_it_47_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_48_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_43_);
            lean_dec(v_h__1_41_);
            v_it_47_ = lean_ctor_get(v_x_40_, 0);
            lean_inc(v_it_47_);
            lean_dec_ref_known(v_x_40_, 1);
            v___x_48_ = lean_apply_1(v_h__2_42_, v_it_47_);
            return v___x_48_;
        }
        _ => {
            let mut v___x_49_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_50_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_42_);
            lean_dec(v_h__1_41_);
            v___x_49_ = lean_box(0);
            v___x_50_ = lean_apply_1(v_h__3_43_, v___x_49_);
            return v___x_50_;
        }
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Slice_Array_Lemmas(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Slice_Array_Iterator(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Subarray(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Slice_Array_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Slice_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Slice_Operations(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Slice_List_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Control(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_MinMax(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Nat_TakeDrop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_TakeDrop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Subarray_Split(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Slice_InternalLemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Slice_Array_Lemmas(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Slice_Array_Lemmas(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Slice_Array_Iterator(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Array_Subarray(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Slice_Array_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Slice_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Slice_Operations(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Range_Polymorphic_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Slice_List_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_Control(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Nat_MinMax(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_Nat_TakeDrop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_TakeDrop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Array_Subarray_Split(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Slice_InternalLemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Slice_Array_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_Slice_Array_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_Slice_Array_Lemmas(builtin);
}
