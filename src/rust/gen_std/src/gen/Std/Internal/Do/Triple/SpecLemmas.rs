// Lean compiler output
// Module: Std.Internal.Do.Triple.SpecLemmas
// Imports: Std.Internal.Do.Triple.Basic Std.Do.Triple.SpecLemmas Init.Data.Range.Polymorphic.Iterators Init.Data.Range.Polymorphic Init.Data.Slice.Array Init.Data.Iterators.Lemmas.Combinators.FilterMap Init.Data.Range Init.Data.Iterators.Lemmas Init.Data.List.Nat.Range Init.Data.List.Nat.TakeDrop Init.Data.List.Range Init.Data.List.TakeDrop Init.Data.Nat.Mod Init.Data.Slice.Lemmas Init.Omega Init.Data.String.Defs Init.Data.String.Iterate Init.Data.String.Lemmas.Splits Init.Data.String.Termination Init.Data.String.Lemmas.Iterate
use crate::r#gen::Init::Data::Iterators::Lemmas::Combinators::FilterMap::{
    initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap,
    runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap,
};
use crate::r#gen::Init::Data::Iterators::Lemmas::{
    initialize_Init_Data_Iterators_Lemmas, runtime_initialize_Init_Data_Iterators_Lemmas,
};
use crate::r#gen::Init::Data::List::Nat::Range::{
    initialize_Init_Data_List_Nat_Range, runtime_initialize_Init_Data_List_Nat_Range,
};
use crate::r#gen::Init::Data::List::Nat::TakeDrop::{
    initialize_Init_Data_List_Nat_TakeDrop, runtime_initialize_Init_Data_List_Nat_TakeDrop,
};
use crate::r#gen::Init::Data::List::Range::{
    initialize_Init_Data_List_Range, runtime_initialize_Init_Data_List_Range,
};
use crate::r#gen::Init::Data::List::TakeDrop::{
    initialize_Init_Data_List_TakeDrop, runtime_initialize_Init_Data_List_TakeDrop,
};
use crate::r#gen::Init::Data::Nat::Mod::{
    initialize_Init_Data_Nat_Mod, runtime_initialize_Init_Data_Nat_Mod,
};
use crate::r#gen::Init::Data::Range::Polymorphic::Iterators::{
    initialize_Init_Data_Range_Polymorphic_Iterators,
    runtime_initialize_Init_Data_Range_Polymorphic_Iterators,
};
use crate::r#gen::Init::Data::Range::Polymorphic::{
    initialize_Init_Data_Range_Polymorphic, runtime_initialize_Init_Data_Range_Polymorphic,
};
use crate::r#gen::Init::Data::Range::{
    initialize_Init_Data_Range, runtime_initialize_Init_Data_Range,
};
use crate::r#gen::Init::Data::Slice::Array::{
    initialize_Init_Data_Slice_Array, runtime_initialize_Init_Data_Slice_Array,
};
use crate::r#gen::Init::Data::Slice::Lemmas::{
    initialize_Init_Data_Slice_Lemmas, runtime_initialize_Init_Data_Slice_Lemmas,
};
use crate::r#gen::Init::Data::String::Defs::{
    initialize_Init_Data_String_Defs, runtime_initialize_Init_Data_String_Defs,
};
use crate::r#gen::Init::Data::String::Iterate::{
    initialize_Init_Data_String_Iterate, runtime_initialize_Init_Data_String_Iterate,
};
use crate::r#gen::Init::Data::String::Lemmas::Iterate::{
    initialize_Init_Data_String_Lemmas_Iterate, runtime_initialize_Init_Data_String_Lemmas_Iterate,
};
use crate::r#gen::Init::Data::String::Lemmas::Splits::{
    initialize_Init_Data_String_Lemmas_Splits, runtime_initialize_Init_Data_String_Lemmas_Splits,
};
use crate::r#gen::Init::Data::String::Termination::{
    initialize_Init_Data_String_Termination, runtime_initialize_Init_Data_String_Termination,
};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Std::Do::Triple::SpecLemmas::{
    initialize_Std_Do_Triple_SpecLemmas, runtime_initialize_Std_Do_Triple_SpecLemmas,
};
use crate::r#gen::Std::Internal::Do::Triple::Basic::{
    initialize_Std_Internal_Do_Triple_Basic, runtime_initialize_Std_Internal_Do_Triple_Basic,
};
pub unsafe fn l___private_Std_Internal_Do_Triple_SpecLemmas_0__Std_Internal_Do_Except_instWPMonad_match__1_splitter___redArg(
    mut v_x_50_: *mut leanh::LeanObject,
    mut v_h__1_51_: *mut leanh::LeanObject,
    mut v_h__2_52_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_50_) == 0 {
        let mut v_a_53_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_54_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_51_);
        v_a_53_ = leanh::lean_ctor_get(v_x_50_, 0);
        leanh::lean_inc(v_a_53_);
        leanh::lean_dec_ref_known(v_x_50_, 1);
        v___x_54_ = leanh::lean_apply_1(v_h__2_52_, v_a_53_);
        return v___x_54_;
    } else {
        let mut v_a_55_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_56_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_52_);
        v_a_55_ = leanh::lean_ctor_get(v_x_50_, 0);
        leanh::lean_inc(v_a_55_);
        leanh::lean_dec_ref_known(v_x_50_, 1);
        v___x_56_ = leanh::lean_apply_1(v_h__1_51_, v_a_55_);
        return v___x_56_;
    }
}
pub unsafe fn l___private_Std_Internal_Do_Triple_SpecLemmas_0__Std_Internal_Do_Except_instWPMonad_match__1_splitter(
    mut v_00_u03b5_57_: *mut leanh::LeanObject,
    mut v_00_u03b1_58_: *mut leanh::LeanObject,
    mut v_motive_59_: *mut leanh::LeanObject,
    mut v_x_60_: *mut leanh::LeanObject,
    mut v_h__1_61_: *mut leanh::LeanObject,
    mut v_h__2_62_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_60_) == 0 {
        let mut v_a_63_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_64_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_61_);
        v_a_63_ = leanh::lean_ctor_get(v_x_60_, 0);
        leanh::lean_inc(v_a_63_);
        leanh::lean_dec_ref_known(v_x_60_, 1);
        v___x_64_ = leanh::lean_apply_1(v_h__2_62_, v_a_63_);
        return v___x_64_;
    } else {
        let mut v_a_65_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_66_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_62_);
        v_a_65_ = leanh::lean_ctor_get(v_x_60_, 0);
        leanh::lean_inc(v_a_65_);
        leanh::lean_dec_ref_known(v_x_60_, 1);
        v___x_66_ = leanh::lean_apply_1(v_h__1_61_, v_a_65_);
        return v___x_66_;
    }
}
pub unsafe fn l___private_Std_Internal_Do_Triple_SpecLemmas_0__List_forIn_x27__cons_match__1_splitter___redArg(
    mut v_x_67_: *mut leanh::LeanObject,
    mut v_h__1_68_: *mut leanh::LeanObject,
    mut v_h__2_69_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_67_) == 0 {
        let mut v_a_70_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_71_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_69_);
        v_a_70_ = leanh::lean_ctor_get(v_x_67_, 0);
        leanh::lean_inc(v_a_70_);
        leanh::lean_dec_ref_known(v_x_67_, 1);
        v___x_71_ = leanh::lean_apply_1(v_h__1_68_, v_a_70_);
        return v___x_71_;
    } else {
        let mut v_a_72_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_73_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_68_);
        v_a_72_ = leanh::lean_ctor_get(v_x_67_, 0);
        leanh::lean_inc(v_a_72_);
        leanh::lean_dec_ref_known(v_x_67_, 1);
        v___x_73_ = leanh::lean_apply_1(v_h__2_69_, v_a_72_);
        return v___x_73_;
    }
}
pub unsafe fn l___private_Std_Internal_Do_Triple_SpecLemmas_0__List_forIn_x27__cons_match__1_splitter(
    mut v_00_u03b2_74_: *mut leanh::LeanObject,
    mut v_motive_75_: *mut leanh::LeanObject,
    mut v_x_76_: *mut leanh::LeanObject,
    mut v_h__1_77_: *mut leanh::LeanObject,
    mut v_h__2_78_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_76_) == 0 {
        let mut v_a_79_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_80_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_78_);
        v_a_79_ = leanh::lean_ctor_get(v_x_76_, 0);
        leanh::lean_inc(v_a_79_);
        leanh::lean_dec_ref_known(v_x_76_, 1);
        v___x_80_ = leanh::lean_apply_1(v_h__1_77_, v_a_79_);
        return v___x_80_;
    } else {
        let mut v_a_81_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_82_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_77_);
        v_a_81_ = leanh::lean_ctor_get(v_x_76_, 0);
        leanh::lean_inc(v_a_81_);
        leanh::lean_dec_ref_known(v_x_76_, 1);
        v___x_82_ = leanh::lean_apply_1(v_h__2_78_, v_a_81_);
        return v___x_82_;
    }
}
pub unsafe fn l___private_Std_Internal_Do_Triple_SpecLemmas_0__Std_Internal_Do_Spec_forIn_x27__list_match__1_splitter___redArg(
    mut v_r_83_: *mut leanh::LeanObject,
    mut v_h__1_84_: *mut leanh::LeanObject,
    mut v_h__2_85_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_r_83_) == 0 {
        let mut v_a_86_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_87_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_84_);
        v_a_86_ = leanh::lean_ctor_get(v_r_83_, 0);
        leanh::lean_inc(v_a_86_);
        leanh::lean_dec_ref_known(v_r_83_, 1);
        v___x_87_ = leanh::lean_apply_1(v_h__2_85_, v_a_86_);
        return v___x_87_;
    } else {
        let mut v_a_88_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_89_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_85_);
        v_a_88_ = leanh::lean_ctor_get(v_r_83_, 0);
        leanh::lean_inc(v_a_88_);
        leanh::lean_dec_ref_known(v_r_83_, 1);
        v___x_89_ = leanh::lean_apply_1(v_h__1_84_, v_a_88_);
        return v___x_89_;
    }
}
pub unsafe fn l___private_Std_Internal_Do_Triple_SpecLemmas_0__Std_Internal_Do_Spec_forIn_x27__list_match__1_splitter(
    mut v_00_u03b2_90_: *mut leanh::LeanObject,
    mut v_motive_91_: *mut leanh::LeanObject,
    mut v_r_92_: *mut leanh::LeanObject,
    mut v_h__1_93_: *mut leanh::LeanObject,
    mut v_h__2_94_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_r_92_) == 0 {
        let mut v_a_95_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_96_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_93_);
        v_a_95_ = leanh::lean_ctor_get(v_r_92_, 0);
        leanh::lean_inc(v_a_95_);
        leanh::lean_dec_ref_known(v_r_92_, 1);
        v___x_96_ = leanh::lean_apply_1(v_h__2_94_, v_a_95_);
        return v___x_96_;
    } else {
        let mut v_a_97_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_98_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_94_);
        v_a_97_ = leanh::lean_ctor_get(v_r_92_, 0);
        leanh::lean_inc(v_a_97_);
        leanh::lean_dec_ref_known(v_r_92_, 1);
        v___x_98_ = leanh::lean_apply_1(v_h__1_93_, v_a_97_);
        return v___x_98_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Internal_Do_Triple_SpecLemmas(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Internal_Do_Triple_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Do_Triple_SpecLemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Slice_Array(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Nat_Range(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Nat_TakeDrop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Range(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_TakeDrop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Mod(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Slice_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Defs(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Iterate(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_Splits(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Termination(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_Iterate(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Internal_Do_Triple_SpecLemmas(
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
pub unsafe fn initialize_Std_Internal_Do_Triple_SpecLemmas(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Internal_Do_Triple_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Do_Triple_SpecLemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Range_Polymorphic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Slice_Array(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Range(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Nat_Range(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Nat_TakeDrop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Range(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_TakeDrop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Mod(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Slice_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Defs(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Iterate(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Lemmas_Splits(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Termination(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Lemmas_Iterate(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Internal_Do_Triple_SpecLemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Internal_Do_Triple_SpecLemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Internal_Do_Triple_SpecLemmas(builtin);
}