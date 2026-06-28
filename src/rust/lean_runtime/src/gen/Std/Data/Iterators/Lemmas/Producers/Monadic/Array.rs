// Lean compiler output
// Module: Std.Data.Iterators.Lemmas.Producers.Monadic.Array
// Imports: Std.Data.Iterators.Producers.Monadic.Array Std.Data.Iterators.Lemmas.Consumers.Monadic Std.Data.Iterators.Lemmas.Producers.Monadic.List Init.Data.Array.Lemmas Init.Data.List.Nat.TakeDrop Init.Data.List.TakeDrop Init.Omega
use crate::r#gen::Init::Data::Array::Lemmas::{
    initialize_Init_Data_Array_Lemmas, runtime_initialize_Init_Data_Array_Lemmas,
};
use crate::r#gen::Init::Data::List::Nat::TakeDrop::{
    initialize_Init_Data_List_Nat_TakeDrop, runtime_initialize_Init_Data_List_Nat_TakeDrop,
};
use crate::r#gen::Init::Data::List::TakeDrop::{
    initialize_Init_Data_List_TakeDrop, runtime_initialize_Init_Data_List_TakeDrop,
};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Std::Data::Iterators::Lemmas::Consumers::Monadic::{
    initialize_Std_Data_Iterators_Lemmas_Consumers_Monadic,
    runtime_initialize_Std_Data_Iterators_Lemmas_Consumers_Monadic,
};
use crate::r#gen::Std::Data::Iterators::Lemmas::Producers::Monadic::List::{
    initialize_Std_Data_Iterators_Lemmas_Producers_Monadic_List,
    runtime_initialize_Std_Data_Iterators_Lemmas_Producers_Monadic_List,
};
use crate::r#gen::Std::Data::Iterators::Producers::Monadic::Array::{
    initialize_Std_Data_Iterators_Producers_Monadic_Array,
    runtime_initialize_Std_Data_Iterators_Producers_Monadic_Array,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_apply_1, lean_apply_2, lean_box, lean_ctor_get, lean_dec,
    lean_dec_ref, lean_dec_ref_known, lean_inc, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_obj_tag,
};
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Producers_Monadic_Array_0__Std_Iterators_Types_ArrayIterator_instIterator_match__1_splitter___redArg(
    mut v_x_44_: *mut LeanObject,
    mut v_h__1_45_: *mut LeanObject,
    mut v_h__2_46_: *mut LeanObject,
    mut v_h__3_47_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_44_) {
        0 => {
            let mut v_it_48_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_49_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_50_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_47_);
            lean_dec(v_h__2_46_);
            v_it_48_ = lean_ctor_get(v_x_44_, 0);
            lean_inc(v_it_48_);
            v_out_49_ = lean_ctor_get(v_x_44_, 1);
            lean_inc(v_out_49_);
            lean_dec_ref_known(v_x_44_, 2);
            v___x_50_ = lean_apply_2(v_h__1_45_, v_it_48_, v_out_49_);
            return v___x_50_;
        }
        1 => {
            let mut v_it_51_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_52_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_47_);
            lean_dec(v_h__1_45_);
            v_it_51_ = lean_ctor_get(v_x_44_, 0);
            lean_inc(v_it_51_);
            lean_dec_ref_known(v_x_44_, 1);
            v___x_52_ = lean_apply_1(v_h__2_46_, v_it_51_);
            return v___x_52_;
        }
        _ => {
            let mut v___x_53_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_54_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_46_);
            lean_dec(v_h__1_45_);
            v___x_53_ = lean_box(0);
            v___x_54_ = lean_apply_1(v_h__3_47_, v___x_53_);
            return v___x_54_;
        }
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Producers_Monadic_Array_0__Std_Iterators_Types_ArrayIterator_instIterator_match__1_splitter(
    mut v_m_55_: *mut LeanObject,
    mut v_00_u03b1_56_: *mut LeanObject,
    mut v_motive_57_: *mut LeanObject,
    mut v_x_58_: *mut LeanObject,
    mut v_h__1_59_: *mut LeanObject,
    mut v_h__2_60_: *mut LeanObject,
    mut v_h__3_61_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_58_) {
        0 => {
            let mut v_it_62_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_63_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_64_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_61_);
            lean_dec(v_h__2_60_);
            v_it_62_ = lean_ctor_get(v_x_58_, 0);
            lean_inc(v_it_62_);
            v_out_63_ = lean_ctor_get(v_x_58_, 1);
            lean_inc(v_out_63_);
            lean_dec_ref_known(v_x_58_, 2);
            v___x_64_ = lean_apply_2(v_h__1_59_, v_it_62_, v_out_63_);
            return v___x_64_;
        }
        1 => {
            let mut v_it_65_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_66_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_61_);
            lean_dec(v_h__1_59_);
            v_it_65_ = lean_ctor_get(v_x_58_, 0);
            lean_inc(v_it_65_);
            lean_dec_ref_known(v_x_58_, 1);
            v___x_66_ = lean_apply_1(v_h__2_60_, v_it_65_);
            return v___x_66_;
        }
        _ => {
            let mut v___x_67_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_68_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_60_);
            lean_dec(v_h__1_59_);
            v___x_67_ = lean_box(0);
            v___x_68_ = lean_apply_1(v_h__3_61_, v___x_67_);
            return v___x_68_;
        }
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Producers_Monadic_Array_0__Std_Types_ListIterator_stepAsHetT__iterM_match__1_splitter___redArg(
    mut v_l_69_: *mut LeanObject,
    mut v_h__1_70_: *mut LeanObject,
    mut v_h__2_71_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_l_69_) == 0 {
        let mut v___x_72_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_73_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_71_);
        v___x_72_ = lean_box(0);
        v___x_73_ = lean_apply_1(v_h__1_70_, v___x_72_);
        return v___x_73_;
    } else {
        let mut v_head_74_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_75_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_76_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_70_);
        v_head_74_ = lean_ctor_get(v_l_69_, 0);
        lean_inc(v_head_74_);
        v_tail_75_ = lean_ctor_get(v_l_69_, 1);
        lean_inc(v_tail_75_);
        lean_dec_ref_known(v_l_69_, 2);
        v___x_76_ = lean_apply_2(v_h__2_71_, v_head_74_, v_tail_75_);
        return v___x_76_;
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Producers_Monadic_Array_0__Std_Types_ListIterator_stepAsHetT__iterM_match__1_splitter(
    mut v_00_u03b2_77_: *mut LeanObject,
    mut v_motive_78_: *mut LeanObject,
    mut v_l_79_: *mut LeanObject,
    mut v_h__1_80_: *mut LeanObject,
    mut v_h__2_81_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_l_79_) == 0 {
        let mut v___x_82_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_83_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_81_);
        v___x_82_ = lean_box(0);
        v___x_83_ = lean_apply_1(v_h__1_80_, v___x_82_);
        return v___x_83_;
    } else {
        let mut v_head_84_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_85_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_86_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_80_);
        v_head_84_ = lean_ctor_get(v_l_79_, 0);
        lean_inc(v_head_84_);
        v_tail_85_ = lean_ctor_get(v_l_79_, 1);
        lean_inc(v_tail_85_);
        lean_dec_ref_known(v_l_79_, 2);
        v___x_86_ = lean_apply_2(v_h__2_81_, v_head_84_, v_tail_85_);
        return v___x_86_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_Iterators_Lemmas_Producers_Monadic_Array(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_Iterators_Producers_Monadic_Array(builtin);
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
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_Iterators_Lemmas_Producers_Monadic_Array(
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
pub unsafe fn initialize_Std_Data_Iterators_Lemmas_Producers_Monadic_Array(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_Iterators_Producers_Monadic_Array(builtin);
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
    res = runtime_initialize_Std_Data_Iterators_Lemmas_Producers_Monadic_Array(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Data_Iterators_Lemmas_Producers_Monadic_Array(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Data_Iterators_Lemmas_Producers_Monadic_Array(builtin);
}
