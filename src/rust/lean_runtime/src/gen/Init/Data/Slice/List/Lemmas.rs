// Lean compiler output
// Module: Init.Data.Slice.List.Lemmas
// Imports: Init.Data.Slice.List.Basic Init.Data.Slice.List.Iterator Init.Data.Slice.List.Iterator Init.Data.Slice.Operations Init.Data.Range.Polymorphic.Iterators Init.Data.Range.Polymorphic.Lemmas Init.Data.Iterators.Lemmas.Combinators.Take Init.Data.Iterators.Lemmas.Producers.List Init.Data.List.Nat.TakeDrop Init.Data.List.TakeDrop Init.Data.Nat.Simproc Init.Data.Slice.Lemmas
use crate::r#gen::Init::Data::Iterators::Lemmas::Combinators::Take::{
    initialize_Init_Data_Iterators_Lemmas_Combinators_Take,
    runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_Take,
};
use crate::r#gen::Init::Data::Iterators::Lemmas::Producers::List::{
    initialize_Init_Data_Iterators_Lemmas_Producers_List,
    runtime_initialize_Init_Data_Iterators_Lemmas_Producers_List,
};
use crate::r#gen::Init::Data::List::Nat::TakeDrop::{
    initialize_Init_Data_List_Nat_TakeDrop, runtime_initialize_Init_Data_List_Nat_TakeDrop,
};
use crate::r#gen::Init::Data::List::TakeDrop::{
    initialize_Init_Data_List_TakeDrop, runtime_initialize_Init_Data_List_TakeDrop,
};
use crate::r#gen::Init::Data::Nat::Simproc::{
    initialize_Init_Data_Nat_Simproc, runtime_initialize_Init_Data_Nat_Simproc,
};
use crate::r#gen::Init::Data::Range::Polymorphic::Iterators::{
    initialize_Init_Data_Range_Polymorphic_Iterators,
    runtime_initialize_Init_Data_Range_Polymorphic_Iterators,
};
use crate::r#gen::Init::Data::Range::Polymorphic::Lemmas::{
    initialize_Init_Data_Range_Polymorphic_Lemmas,
    runtime_initialize_Init_Data_Range_Polymorphic_Lemmas,
};
use crate::r#gen::Init::Data::Slice::Lemmas::{
    initialize_Init_Data_Slice_Lemmas, runtime_initialize_Init_Data_Slice_Lemmas,
};
use crate::r#gen::Init::Data::Slice::List::Basic::{
    initialize_Init_Data_Slice_List_Basic, runtime_initialize_Init_Data_Slice_List_Basic,
};
use crate::r#gen::Init::Data::Slice::List::Iterator::{
    initialize_Init_Data_Slice_List_Iterator, runtime_initialize_Init_Data_Slice_List_Iterator,
};
use crate::r#gen::Init::Data::Slice::Operations::{
    initialize_Init_Data_Slice_Operations, runtime_initialize_Init_Data_Slice_Operations,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_apply_1, lean_box, lean_ctor_get, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_inc, lean_io_result_is_error, lean_io_result_mk_ok, lean_obj_tag,
};
pub unsafe fn l___private_Init_Data_Slice_List_Lemmas_0__ListSlice_internalIter__eq_match__1_splitter___redArg(
    mut v_x_46_: *mut LeanObject,
    mut v_h__1_47_: *mut LeanObject,
    mut v_h__2_48_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_46_) == 0 {
        let mut v___x_49_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_50_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_47_);
        v___x_49_ = lean_box(0);
        v___x_50_ = lean_apply_1(v_h__2_48_, v___x_49_);
        return v___x_50_;
    } else {
        let mut v_val_51_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_52_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_48_);
        v_val_51_ = lean_ctor_get(v_x_46_, 0);
        lean_inc(v_val_51_);
        lean_dec_ref_known(v_x_46_, 1);
        v___x_52_ = lean_apply_1(v_h__1_47_, v_val_51_);
        return v___x_52_;
    }
}
pub unsafe fn l___private_Init_Data_Slice_List_Lemmas_0__ListSlice_internalIter__eq_match__1_splitter(
    mut v_motive_53_: *mut LeanObject,
    mut v_x_54_: *mut LeanObject,
    mut v_h__1_55_: *mut LeanObject,
    mut v_h__2_56_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_54_) == 0 {
        let mut v___x_57_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_58_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_55_);
        v___x_57_ = lean_box(0);
        v___x_58_ = lean_apply_1(v_h__2_56_, v___x_57_);
        return v___x_58_;
    } else {
        let mut v_val_59_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_60_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_56_);
        v_val_59_ = lean_ctor_get(v_x_54_, 0);
        lean_inc(v_val_59_);
        lean_dec_ref_known(v_x_54_, 1);
        v___x_60_ = lean_apply_1(v_h__1_55_, v_val_59_);
        return v___x_60_;
    }
}
pub unsafe fn l___private_Init_Data_Slice_List_Lemmas_0__ListSlice_toList__eq_match__1_splitter___redArg(
    mut v_x_61_: *mut LeanObject,
    mut v_h__1_62_: *mut LeanObject,
    mut v_h__2_63_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_61_) == 0 {
        let mut v___x_64_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_65_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_62_);
        v___x_64_ = lean_box(0);
        v___x_65_ = lean_apply_1(v_h__2_63_, v___x_64_);
        return v___x_65_;
    } else {
        let mut v_val_66_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_67_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_63_);
        v_val_66_ = lean_ctor_get(v_x_61_, 0);
        lean_inc(v_val_66_);
        lean_dec_ref_known(v_x_61_, 1);
        v___x_67_ = lean_apply_1(v_h__1_62_, v_val_66_);
        return v___x_67_;
    }
}
pub unsafe fn l___private_Init_Data_Slice_List_Lemmas_0__ListSlice_toList__eq_match__1_splitter(
    mut v_motive_68_: *mut LeanObject,
    mut v_x_69_: *mut LeanObject,
    mut v_h__1_70_: *mut LeanObject,
    mut v_h__2_71_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_69_) == 0 {
        let mut v___x_72_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_73_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_70_);
        v___x_72_ = lean_box(0);
        v___x_73_ = lean_apply_1(v_h__2_71_, v___x_72_);
        return v___x_73_;
    } else {
        let mut v_val_74_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_75_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_71_);
        v_val_74_ = lean_ctor_get(v_x_69_, 0);
        lean_inc(v_val_74_);
        lean_dec_ref_known(v_x_69_, 1);
        v___x_75_ = lean_apply_1(v_h__1_70_, v_val_74_);
        return v___x_75_;
    }
}
pub unsafe fn l___private_Init_Data_Slice_List_Lemmas_0__instSliceableListSliceNat_match__1_splitter___redArg(
    mut v_x_76_: *mut LeanObject,
    mut v_h__1_77_: *mut LeanObject,
    mut v_h__2_78_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_76_) == 0 {
        let mut v___x_79_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_80_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_78_);
        v___x_79_ = lean_box(0);
        v___x_80_ = lean_apply_1(v_h__1_77_, v___x_79_);
        return v___x_80_;
    } else {
        let mut v_val_81_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_82_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_77_);
        v_val_81_ = lean_ctor_get(v_x_76_, 0);
        lean_inc(v_val_81_);
        lean_dec_ref_known(v_x_76_, 1);
        v___x_82_ = lean_apply_1(v_h__2_78_, v_val_81_);
        return v___x_82_;
    }
}
pub unsafe fn l___private_Init_Data_Slice_List_Lemmas_0__instSliceableListSliceNat_match__1_splitter(
    mut v_motive_83_: *mut LeanObject,
    mut v_x_84_: *mut LeanObject,
    mut v_h__1_85_: *mut LeanObject,
    mut v_h__2_86_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_84_) == 0 {
        let mut v___x_87_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_88_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_86_);
        v___x_87_ = lean_box(0);
        v___x_88_ = lean_apply_1(v_h__1_85_, v___x_87_);
        return v___x_88_;
    } else {
        let mut v_val_89_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_90_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_85_);
        v_val_89_ = lean_ctor_get(v_x_84_, 0);
        lean_inc(v_val_89_);
        lean_dec_ref_known(v_x_84_, 1);
        v___x_90_ = lean_apply_1(v_h__2_86_, v_val_89_);
        return v___x_90_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Slice_List_Lemmas(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Slice_List_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Slice_List_Iterator(builtin);
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
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_Take(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Producers_List(builtin);
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
    res = runtime_initialize_Init_Data_Nat_Simproc(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Slice_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Slice_List_Lemmas(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Slice_List_Lemmas(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Slice_List_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Slice_List_Iterator(builtin);
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
    res = initialize_Init_Data_Iterators_Lemmas_Combinators_Take(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Producers_List(builtin);
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
    res = initialize_Init_Data_Nat_Simproc(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Slice_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Slice_List_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_Slice_List_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_Slice_List_Lemmas(builtin);
}
