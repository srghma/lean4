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
pub unsafe fn l___private_Init_Data_Slice_List_Lemmas_0__ListSlice_internalIter__eq_match__1_splitter___redArg(
    mut v_x_46_: *mut crate::leanh::LeanObject,
    mut v_h__1_47_: *mut crate::leanh::LeanObject,
    mut v_h__2_48_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_46_) == 0 {
        let mut v___x_49_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_50_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_47_);
        v___x_49_ = crate::leanh::lean_box(0);
        v___x_50_ = crate::leanh::lean_apply_1(v_h__2_48_, v___x_49_);
        return v___x_50_;
    } else {
        let mut v_val_51_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_52_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_48_);
        v_val_51_ = crate::leanh::lean_ctor_get(v_x_46_, 0);
        crate::leanh::lean_inc(v_val_51_);
        crate::leanh::lean_dec_ref_known(v_x_46_, 1);
        v___x_52_ = crate::leanh::lean_apply_1(v_h__1_47_, v_val_51_);
        return v___x_52_;
    }
}
pub unsafe fn l___private_Init_Data_Slice_List_Lemmas_0__ListSlice_internalIter__eq_match__1_splitter(
    mut v_motive_53_: *mut crate::leanh::LeanObject,
    mut v_x_54_: *mut crate::leanh::LeanObject,
    mut v_h__1_55_: *mut crate::leanh::LeanObject,
    mut v_h__2_56_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_54_) == 0 {
        let mut v___x_57_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_58_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_55_);
        v___x_57_ = crate::leanh::lean_box(0);
        v___x_58_ = crate::leanh::lean_apply_1(v_h__2_56_, v___x_57_);
        return v___x_58_;
    } else {
        let mut v_val_59_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_60_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_56_);
        v_val_59_ = crate::leanh::lean_ctor_get(v_x_54_, 0);
        crate::leanh::lean_inc(v_val_59_);
        crate::leanh::lean_dec_ref_known(v_x_54_, 1);
        v___x_60_ = crate::leanh::lean_apply_1(v_h__1_55_, v_val_59_);
        return v___x_60_;
    }
}
pub unsafe fn l___private_Init_Data_Slice_List_Lemmas_0__ListSlice_toList__eq_match__1_splitter___redArg(
    mut v_x_61_: *mut crate::leanh::LeanObject,
    mut v_h__1_62_: *mut crate::leanh::LeanObject,
    mut v_h__2_63_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_61_) == 0 {
        let mut v___x_64_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_65_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_62_);
        v___x_64_ = crate::leanh::lean_box(0);
        v___x_65_ = crate::leanh::lean_apply_1(v_h__2_63_, v___x_64_);
        return v___x_65_;
    } else {
        let mut v_val_66_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_67_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_63_);
        v_val_66_ = crate::leanh::lean_ctor_get(v_x_61_, 0);
        crate::leanh::lean_inc(v_val_66_);
        crate::leanh::lean_dec_ref_known(v_x_61_, 1);
        v___x_67_ = crate::leanh::lean_apply_1(v_h__1_62_, v_val_66_);
        return v___x_67_;
    }
}
pub unsafe fn l___private_Init_Data_Slice_List_Lemmas_0__ListSlice_toList__eq_match__1_splitter(
    mut v_motive_68_: *mut crate::leanh::LeanObject,
    mut v_x_69_: *mut crate::leanh::LeanObject,
    mut v_h__1_70_: *mut crate::leanh::LeanObject,
    mut v_h__2_71_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_69_) == 0 {
        let mut v___x_72_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_73_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_70_);
        v___x_72_ = crate::leanh::lean_box(0);
        v___x_73_ = crate::leanh::lean_apply_1(v_h__2_71_, v___x_72_);
        return v___x_73_;
    } else {
        let mut v_val_74_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_75_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_71_);
        v_val_74_ = crate::leanh::lean_ctor_get(v_x_69_, 0);
        crate::leanh::lean_inc(v_val_74_);
        crate::leanh::lean_dec_ref_known(v_x_69_, 1);
        v___x_75_ = crate::leanh::lean_apply_1(v_h__1_70_, v_val_74_);
        return v___x_75_;
    }
}
pub unsafe fn l___private_Init_Data_Slice_List_Lemmas_0__instSliceableListSliceNat_match__1_splitter___redArg(
    mut v_x_76_: *mut crate::leanh::LeanObject,
    mut v_h__1_77_: *mut crate::leanh::LeanObject,
    mut v_h__2_78_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_76_) == 0 {
        let mut v___x_79_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_80_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_78_);
        v___x_79_ = crate::leanh::lean_box(0);
        v___x_80_ = crate::leanh::lean_apply_1(v_h__1_77_, v___x_79_);
        return v___x_80_;
    } else {
        let mut v_val_81_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_82_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_77_);
        v_val_81_ = crate::leanh::lean_ctor_get(v_x_76_, 0);
        crate::leanh::lean_inc(v_val_81_);
        crate::leanh::lean_dec_ref_known(v_x_76_, 1);
        v___x_82_ = crate::leanh::lean_apply_1(v_h__2_78_, v_val_81_);
        return v___x_82_;
    }
}
pub unsafe fn l___private_Init_Data_Slice_List_Lemmas_0__instSliceableListSliceNat_match__1_splitter(
    mut v_motive_83_: *mut crate::leanh::LeanObject,
    mut v_x_84_: *mut crate::leanh::LeanObject,
    mut v_h__1_85_: *mut crate::leanh::LeanObject,
    mut v_h__2_86_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_84_) == 0 {
        let mut v___x_87_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_88_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_86_);
        v___x_87_ = crate::leanh::lean_box(0);
        v___x_88_ = crate::leanh::lean_apply_1(v_h__1_85_, v___x_87_);
        return v___x_88_;
    } else {
        let mut v_val_89_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_90_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_85_);
        v_val_89_ = crate::leanh::lean_ctor_get(v_x_84_, 0);
        crate::leanh::lean_inc(v_val_89_);
        crate::leanh::lean_dec_ref_known(v_x_84_, 1);
        v___x_90_ = crate::leanh::lean_apply_1(v_h__2_86_, v_val_89_);
        return v___x_90_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Slice_List_Lemmas(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Slice_List_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Slice_List_Iterator(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Slice_List_Iterator(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Slice_Operations(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_Take(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Producers_List(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Nat_TakeDrop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_TakeDrop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Simproc(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Slice_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Slice_List_Lemmas(
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
pub unsafe fn initialize_Init_Data_Slice_List_Lemmas(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Slice_List_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Slice_List_Iterator(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Slice_List_Iterator(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Slice_Operations(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Range_Polymorphic_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Combinators_Take(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Producers_List(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Nat_TakeDrop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_TakeDrop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Simproc(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Slice_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Slice_List_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Slice_List_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_Slice_List_Lemmas(builtin);
}
