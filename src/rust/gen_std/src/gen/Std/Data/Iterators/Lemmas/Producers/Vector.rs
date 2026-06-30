// Lean compiler output
// Module: Std.Data.Iterators.Lemmas.Producers.Vector
// Imports: Std.Data.Iterators.Lemmas.Producers.Array Std.Data.Iterators.Producers.Vector Std.Data.Iterators.Producers.Monadic.Vector Init.Data.Vector.Lemmas Std.Data.Iterators.Lemmas.Consumers.Collect Std.Data.Iterators.Lemmas.Consumers.Loop Init.Data.List.TakeDrop Std.Data.Iterators.Lemmas.Producers.Monadic.Vector
use crate::r#gen::Init::Data::List::TakeDrop::{
    initialize_Init_Data_List_TakeDrop, runtime_initialize_Init_Data_List_TakeDrop,
};
use crate::r#gen::Init::Data::Vector::Lemmas::{
    initialize_Init_Data_Vector_Lemmas, runtime_initialize_Init_Data_Vector_Lemmas,
};
use crate::r#gen::Std::Data::Iterators::Lemmas::Consumers::Collect::{
    initialize_Std_Data_Iterators_Lemmas_Consumers_Collect,
    runtime_initialize_Std_Data_Iterators_Lemmas_Consumers_Collect,
};
use crate::r#gen::Std::Data::Iterators::Lemmas::Consumers::Loop::{
    initialize_Std_Data_Iterators_Lemmas_Consumers_Loop,
    runtime_initialize_Std_Data_Iterators_Lemmas_Consumers_Loop,
};
use crate::r#gen::Std::Data::Iterators::Lemmas::Producers::Array::{
    initialize_Std_Data_Iterators_Lemmas_Producers_Array,
    runtime_initialize_Std_Data_Iterators_Lemmas_Producers_Array,
};
use crate::r#gen::Std::Data::Iterators::Lemmas::Producers::Monadic::Vector::{
    initialize_Std_Data_Iterators_Lemmas_Producers_Monadic_Vector,
    runtime_initialize_Std_Data_Iterators_Lemmas_Producers_Monadic_Vector,
};
use crate::r#gen::Std::Data::Iterators::Producers::Monadic::Vector::{
    initialize_Std_Data_Iterators_Producers_Monadic_Vector,
    runtime_initialize_Std_Data_Iterators_Producers_Monadic_Vector,
};
use crate::r#gen::Std::Data::Iterators::Producers::Vector::{
    initialize_Std_Data_Iterators_Producers_Vector,
    runtime_initialize_Std_Data_Iterators_Producers_Vector,
};
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Producers_Vector_0__Std_Iterators_Types_ArrayIterator_instIterator_match__1_splitter___redArg(
    mut v_x_26_: *mut leanh::LeanObject,
    mut v_h__1_27_: *mut leanh::LeanObject,
    mut v_h__2_28_: *mut leanh::LeanObject,
    mut v_h__3_29_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_26_) {
        0 => {
            let mut v_it_30_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_31_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_32_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_29_);
            leanh::lean_dec(v_h__2_28_);
            v_it_30_ = leanh::lean_ctor_get(v_x_26_, 0);
            leanh::lean_inc(v_it_30_);
            v_out_31_ = leanh::lean_ctor_get(v_x_26_, 1);
            leanh::lean_inc(v_out_31_);
            leanh::lean_dec_ref_known(v_x_26_, 2);
            v___x_32_ = leanh::lean_apply_2(v_h__1_27_, v_it_30_, v_out_31_);
            return v___x_32_;
        }
        1 => {
            let mut v_it_33_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_34_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_29_);
            leanh::lean_dec(v_h__1_27_);
            v_it_33_ = leanh::lean_ctor_get(v_x_26_, 0);
            leanh::lean_inc(v_it_33_);
            leanh::lean_dec_ref_known(v_x_26_, 1);
            v___x_34_ = leanh::lean_apply_1(v_h__2_28_, v_it_33_);
            return v___x_34_;
        }
        _ => {
            let mut v___x_35_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_36_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_28_);
            leanh::lean_dec(v_h__1_27_);
            v___x_35_ = leanh::lean_box(0);
            v___x_36_ = leanh::lean_apply_1(v_h__3_29_, v___x_35_);
            return v___x_36_;
        }
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Producers_Vector_0__Std_Iterators_Types_ArrayIterator_instIterator_match__1_splitter(
    mut v_m_37_: *mut leanh::LeanObject,
    mut v_00_u03b1_38_: *mut leanh::LeanObject,
    mut v_motive_39_: *mut leanh::LeanObject,
    mut v_x_40_: *mut leanh::LeanObject,
    mut v_h__1_41_: *mut leanh::LeanObject,
    mut v_h__2_42_: *mut leanh::LeanObject,
    mut v_h__3_43_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_40_) {
        0 => {
            let mut v_it_44_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_45_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_46_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_43_);
            leanh::lean_dec(v_h__2_42_);
            v_it_44_ = leanh::lean_ctor_get(v_x_40_, 0);
            leanh::lean_inc(v_it_44_);
            v_out_45_ = leanh::lean_ctor_get(v_x_40_, 1);
            leanh::lean_inc(v_out_45_);
            leanh::lean_dec_ref_known(v_x_40_, 2);
            v___x_46_ = leanh::lean_apply_2(v_h__1_41_, v_it_44_, v_out_45_);
            return v___x_46_;
        }
        1 => {
            let mut v_it_47_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_48_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_43_);
            leanh::lean_dec(v_h__1_41_);
            v_it_47_ = leanh::lean_ctor_get(v_x_40_, 0);
            leanh::lean_inc(v_it_47_);
            leanh::lean_dec_ref_known(v_x_40_, 1);
            v___x_48_ = leanh::lean_apply_1(v_h__2_42_, v_it_47_);
            return v___x_48_;
        }
        _ => {
            let mut v___x_49_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_50_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_42_);
            leanh::lean_dec(v_h__1_41_);
            v___x_49_ = leanh::lean_box(0);
            v___x_50_ = leanh::lean_apply_1(v_h__3_43_, v___x_49_);
            return v___x_50_;
        }
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_Iterators_Lemmas_Producers_Vector(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_Iterators_Lemmas_Producers_Array(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Producers_Vector(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Producers_Monadic_Vector(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Vector_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Lemmas_Consumers_Collect(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Lemmas_Consumers_Loop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_TakeDrop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Lemmas_Producers_Monadic_Vector(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_Iterators_Lemmas_Producers_Vector(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Data_Iterators_Lemmas_Producers_Vector(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_Iterators_Lemmas_Producers_Array(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Data_Iterators_Producers_Vector(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Data_Iterators_Producers_Monadic_Vector(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Vector_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Data_Iterators_Lemmas_Consumers_Collect(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Data_Iterators_Lemmas_Consumers_Loop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_TakeDrop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Data_Iterators_Lemmas_Producers_Monadic_Vector(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Lemmas_Producers_Vector(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Data_Iterators_Lemmas_Producers_Vector(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Data_Iterators_Lemmas_Producers_Vector(builtin);
}