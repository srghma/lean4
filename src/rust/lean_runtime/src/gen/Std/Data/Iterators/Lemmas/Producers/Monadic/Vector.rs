// Lean compiler output
// Module: Std.Data.Iterators.Lemmas.Producers.Monadic.Vector
// Imports: Std.Data.Iterators.Lemmas.Producers.Monadic.Array Std.Data.Iterators.Producers.Monadic.Vector Std.Data.Iterators.Lemmas.Consumers.Monadic Std.Data.Iterators.Lemmas.Producers.Monadic.List Init.Data.Array.Lemmas Init.Data.List.Nat.TakeDrop Init.Data.List.TakeDrop Init.Omega Init.Data.Vector.Lemmas
use crate::r#gen::Init::Data::Array::Lemmas::{
    initialize_Init_Data_Array_Lemmas, runtime_initialize_Init_Data_Array_Lemmas,
};
use crate::r#gen::Init::Data::List::Nat::TakeDrop::{
    initialize_Init_Data_List_Nat_TakeDrop, runtime_initialize_Init_Data_List_Nat_TakeDrop,
};
use crate::r#gen::Init::Data::List::TakeDrop::{
    initialize_Init_Data_List_TakeDrop, runtime_initialize_Init_Data_List_TakeDrop,
};
use crate::r#gen::Init::Data::Vector::Lemmas::{
    initialize_Init_Data_Vector_Lemmas, runtime_initialize_Init_Data_Vector_Lemmas,
};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Std::Data::Iterators::Lemmas::Consumers::Monadic::{
    initialize_Std_Data_Iterators_Lemmas_Consumers_Monadic,
    runtime_initialize_Std_Data_Iterators_Lemmas_Consumers_Monadic,
};
use crate::r#gen::Std::Data::Iterators::Lemmas::Producers::Monadic::Array::{
    initialize_Std_Data_Iterators_Lemmas_Producers_Monadic_Array,
    runtime_initialize_Std_Data_Iterators_Lemmas_Producers_Monadic_Array,
};
use crate::r#gen::Std::Data::Iterators::Lemmas::Producers::Monadic::List::{
    initialize_Std_Data_Iterators_Lemmas_Producers_Monadic_List,
    runtime_initialize_Std_Data_Iterators_Lemmas_Producers_Monadic_List,
};
use crate::r#gen::Std::Data::Iterators::Producers::Monadic::Vector::{
    initialize_Std_Data_Iterators_Producers_Monadic_Vector,
    runtime_initialize_Std_Data_Iterators_Producers_Monadic_Vector,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_apply_1, lean_apply_2, lean_box, lean_ctor_get, lean_dec,
    lean_dec_ref, lean_dec_ref_known, lean_inc, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_obj_tag,
};
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Producers_Monadic_Vector_0__Std_Iterators_Types_ArrayIterator_instIterator_match__1_splitter___redArg(
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
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Producers_Monadic_Vector_0__Std_Iterators_Types_ArrayIterator_instIterator_match__1_splitter(
    mut v_m_37_: *mut LeanObject,
    mut v_00_u03b1_38_: *mut LeanObject,
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
pub unsafe fn runtime_initialize_Std_Data_Iterators_Lemmas_Producers_Monadic_Vector(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_Iterators_Lemmas_Producers_Monadic_Array(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Producers_Monadic_Vector(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Lemmas_Consumers_Monadic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Lemmas_Producers_Monadic_List(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Lemmas(builtin);
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
    res = runtime_initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Vector_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_Iterators_Lemmas_Producers_Monadic_Vector(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Data_Iterators_Lemmas_Producers_Monadic_Vector(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_Iterators_Lemmas_Producers_Monadic_Array(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Data_Iterators_Producers_Monadic_Vector(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Data_Iterators_Lemmas_Consumers_Monadic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Data_Iterators_Lemmas_Producers_Monadic_List(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Array_Lemmas(builtin);
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
    res = initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Vector_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Lemmas_Producers_Monadic_Vector(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Data_Iterators_Lemmas_Producers_Monadic_Vector(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Data_Iterators_Lemmas_Producers_Monadic_Vector(builtin);
}
