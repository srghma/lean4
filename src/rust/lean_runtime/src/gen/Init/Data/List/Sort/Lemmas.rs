// Lean compiler output
// Module: Init.Data.List.Sort.Lemmas
// Imports: Init.Data.List.Sort.Basic Init.Data.List.Sort.Basic Init.BinderPredicates Init.Data.Bool Init.Data.List.Nat.Range Init.Data.List.Pairwise Init.Data.List.Perm Init.Data.List.Range Init.Data.List.Sublist Init.Data.Nat.Linear Init.Data.Prod
use crate::r#gen::Init::BinderPredicates::{
    initialize_Init_BinderPredicates, runtime_initialize_Init_BinderPredicates,
};
use crate::r#gen::Init::Data::Bool::{
    initialize_Init_Data_Bool, runtime_initialize_Init_Data_Bool,
};
use crate::r#gen::Init::Data::List::Nat::Range::{
    initialize_Init_Data_List_Nat_Range, runtime_initialize_Init_Data_List_Nat_Range,
};
use crate::r#gen::Init::Data::List::Pairwise::{
    initialize_Init_Data_List_Pairwise, runtime_initialize_Init_Data_List_Pairwise,
};
use crate::r#gen::Init::Data::List::Perm::{
    initialize_Init_Data_List_Perm, runtime_initialize_Init_Data_List_Perm,
};
use crate::r#gen::Init::Data::List::Range::{
    initialize_Init_Data_List_Range, runtime_initialize_Init_Data_List_Range,
};
use crate::r#gen::Init::Data::List::Sort::Basic::{
    initialize_Init_Data_List_Sort_Basic, runtime_initialize_Init_Data_List_Sort_Basic,
};
use crate::r#gen::Init::Data::List::Sublist::{
    initialize_Init_Data_List_Sublist, runtime_initialize_Init_Data_List_Sublist,
};
use crate::r#gen::Init::Data::Nat::Linear::{
    initialize_Init_Data_Nat_Linear, runtime_initialize_Init_Data_Nat_Linear,
};
use crate::r#gen::Init::Data::Prod::{
    initialize_Init_Data_Prod, runtime_initialize_Init_Data_Prod,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_apply_1, lean_apply_2, lean_apply_3, lean_apply_4,
    lean_box, lean_ctor_get, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_obj_tag,
};
pub unsafe fn l___private_Init_Data_List_Sort_Lemmas_0__List_merge_match__1_splitter___redArg(
    mut v_xs_73_: *mut LeanObject,
    mut v_ys_74_: *mut LeanObject,
    mut v_h__1_75_: *mut LeanObject,
    mut v_h__2_76_: *mut LeanObject,
    mut v_h__3_77_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_xs_73_) == 0 {
        let mut v___x_78_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__3_77_);
        lean_dec(v_h__2_76_);
        v___x_78_ = lean_apply_1(v_h__1_75_, v_ys_74_);
        return v___x_78_;
    } else {
        lean_dec(v_h__1_75_);
        if lean_obj_tag(v_ys_74_) == 0 {
            let mut v___x_79_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_77_);
            v___x_79_ = lean_apply_2(v_h__2_76_, v_xs_73_, lean_box(0));
            return v___x_79_;
        } else {
            let mut v_head_80_: *mut LeanObject = core::ptr::null_mut();
            let mut v_tail_81_: *mut LeanObject = core::ptr::null_mut();
            let mut v_head_82_: *mut LeanObject = core::ptr::null_mut();
            let mut v_tail_83_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_84_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_76_);
            v_head_80_ = lean_ctor_get(v_xs_73_, 0);
            lean_inc(v_head_80_);
            v_tail_81_ = lean_ctor_get(v_xs_73_, 1);
            lean_inc(v_tail_81_);
            lean_dec_ref_known(v_xs_73_, 2);
            v_head_82_ = lean_ctor_get(v_ys_74_, 0);
            lean_inc(v_head_82_);
            v_tail_83_ = lean_ctor_get(v_ys_74_, 1);
            lean_inc(v_tail_83_);
            lean_dec_ref_known(v_ys_74_, 2);
            v___x_84_ = lean_apply_4(v_h__3_77_, v_head_80_, v_tail_81_, v_head_82_, v_tail_83_);
            return v___x_84_;
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Sort_Lemmas_0__List_merge_match__1_splitter(
    mut v_00_u03b1_85_: *mut LeanObject,
    mut v_motive_86_: *mut LeanObject,
    mut v_xs_87_: *mut LeanObject,
    mut v_ys_88_: *mut LeanObject,
    mut v_h__1_89_: *mut LeanObject,
    mut v_h__2_90_: *mut LeanObject,
    mut v_h__3_91_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_xs_87_) == 0 {
        let mut v___x_92_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__3_91_);
        lean_dec(v_h__2_90_);
        v___x_92_ = lean_apply_1(v_h__1_89_, v_ys_88_);
        return v___x_92_;
    } else {
        lean_dec(v_h__1_89_);
        if lean_obj_tag(v_ys_88_) == 0 {
            let mut v___x_93_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_91_);
            v___x_93_ = lean_apply_2(v_h__2_90_, v_xs_87_, lean_box(0));
            return v___x_93_;
        } else {
            let mut v_head_94_: *mut LeanObject = core::ptr::null_mut();
            let mut v_tail_95_: *mut LeanObject = core::ptr::null_mut();
            let mut v_head_96_: *mut LeanObject = core::ptr::null_mut();
            let mut v_tail_97_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_98_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_90_);
            v_head_94_ = lean_ctor_get(v_xs_87_, 0);
            lean_inc(v_head_94_);
            v_tail_95_ = lean_ctor_get(v_xs_87_, 1);
            lean_inc(v_tail_95_);
            lean_dec_ref_known(v_xs_87_, 2);
            v_head_96_ = lean_ctor_get(v_ys_88_, 0);
            lean_inc(v_head_96_);
            v_tail_97_ = lean_ctor_get(v_ys_88_, 1);
            lean_inc(v_tail_97_);
            lean_dec_ref_known(v_ys_88_, 2);
            v___x_98_ = lean_apply_4(v_h__3_91_, v_head_94_, v_tail_95_, v_head_96_, v_tail_97_);
            return v___x_98_;
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Sort_Lemmas_0__List_mergeSort_match__1_splitter___redArg(
    mut v_x_99_: *mut LeanObject,
    mut v_x_100_: *mut LeanObject,
    mut v_h__1_101_: *mut LeanObject,
    mut v_h__2_102_: *mut LeanObject,
    mut v_h__3_103_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_99_) == 0 {
        let mut v___x_104_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__3_103_);
        lean_dec(v_h__2_102_);
        v___x_104_ = lean_apply_1(v_h__1_101_, v_x_100_);
        return v___x_104_;
    } else {
        let mut v_tail_105_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_101_);
        v_tail_105_ = lean_ctor_get(v_x_99_, 1);
        if lean_obj_tag(v_tail_105_) == 0 {
            let mut v_head_106_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_107_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_103_);
            v_head_106_ = lean_ctor_get(v_x_99_, 0);
            lean_inc(v_head_106_);
            lean_dec_ref_known(v_x_99_, 2);
            v___x_107_ = lean_apply_2(v_h__2_102_, v_head_106_, v_x_100_);
            return v___x_107_;
        } else {
            let mut v_head_108_: *mut LeanObject = core::ptr::null_mut();
            let mut v_head_109_: *mut LeanObject = core::ptr::null_mut();
            let mut v_tail_110_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_111_: *mut LeanObject = core::ptr::null_mut();
            lean_inc_ref(v_tail_105_);
            lean_dec(v_h__2_102_);
            v_head_108_ = lean_ctor_get(v_x_99_, 0);
            lean_inc(v_head_108_);
            lean_dec_ref_known(v_x_99_, 2);
            v_head_109_ = lean_ctor_get(v_tail_105_, 0);
            lean_inc(v_head_109_);
            v_tail_110_ = lean_ctor_get(v_tail_105_, 1);
            lean_inc(v_tail_110_);
            lean_dec_ref_known(v_tail_105_, 2);
            v___x_111_ = lean_apply_4(v_h__3_103_, v_head_108_, v_head_109_, v_tail_110_, v_x_100_);
            return v___x_111_;
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Sort_Lemmas_0__List_mergeSort_match__1_splitter(
    mut v_00_u03b1_112_: *mut LeanObject,
    mut v_motive_113_: *mut LeanObject,
    mut v_x_114_: *mut LeanObject,
    mut v_x_115_: *mut LeanObject,
    mut v_h__1_116_: *mut LeanObject,
    mut v_h__2_117_: *mut LeanObject,
    mut v_h__3_118_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_114_) == 0 {
        let mut v___x_119_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__3_118_);
        lean_dec(v_h__2_117_);
        v___x_119_ = lean_apply_1(v_h__1_116_, v_x_115_);
        return v___x_119_;
    } else {
        let mut v_tail_120_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_116_);
        v_tail_120_ = lean_ctor_get(v_x_114_, 1);
        if lean_obj_tag(v_tail_120_) == 0 {
            let mut v_head_121_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_122_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_118_);
            v_head_121_ = lean_ctor_get(v_x_114_, 0);
            lean_inc(v_head_121_);
            lean_dec_ref_known(v_x_114_, 2);
            v___x_122_ = lean_apply_2(v_h__2_117_, v_head_121_, v_x_115_);
            return v___x_122_;
        } else {
            let mut v_head_123_: *mut LeanObject = core::ptr::null_mut();
            let mut v_head_124_: *mut LeanObject = core::ptr::null_mut();
            let mut v_tail_125_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_126_: *mut LeanObject = core::ptr::null_mut();
            lean_inc_ref(v_tail_120_);
            lean_dec(v_h__2_117_);
            v_head_123_ = lean_ctor_get(v_x_114_, 0);
            lean_inc(v_head_123_);
            lean_dec_ref_known(v_x_114_, 2);
            v_head_124_ = lean_ctor_get(v_tail_120_, 0);
            lean_inc(v_head_124_);
            v_tail_125_ = lean_ctor_get(v_tail_120_, 1);
            lean_inc(v_tail_125_);
            lean_dec_ref_known(v_tail_120_, 2);
            v___x_126_ = lean_apply_4(v_h__3_118_, v_head_123_, v_head_124_, v_tail_125_, v_x_115_);
            return v___x_126_;
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Sort_Lemmas_0__List_findIdx_go_match__1_splitter___redArg(
    mut v_x_127_: *mut LeanObject,
    mut v_x_128_: *mut LeanObject,
    mut v_h__1_129_: *mut LeanObject,
    mut v_h__2_130_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_127_) == 0 {
        let mut v___x_131_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_130_);
        v___x_131_ = lean_apply_1(v_h__1_129_, v_x_128_);
        return v___x_131_;
    } else {
        let mut v_head_132_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_133_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_134_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_129_);
        v_head_132_ = lean_ctor_get(v_x_127_, 0);
        lean_inc(v_head_132_);
        v_tail_133_ = lean_ctor_get(v_x_127_, 1);
        lean_inc(v_tail_133_);
        lean_dec_ref_known(v_x_127_, 2);
        v___x_134_ = lean_apply_3(v_h__2_130_, v_head_132_, v_tail_133_, v_x_128_);
        return v___x_134_;
    }
}
pub unsafe fn l___private_Init_Data_List_Sort_Lemmas_0__List_findIdx_go_match__1_splitter(
    mut v_00_u03b1_135_: *mut LeanObject,
    mut v_motive_136_: *mut LeanObject,
    mut v_x_137_: *mut LeanObject,
    mut v_x_138_: *mut LeanObject,
    mut v_h__1_139_: *mut LeanObject,
    mut v_h__2_140_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_137_) == 0 {
        let mut v___x_141_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_140_);
        v___x_141_ = lean_apply_1(v_h__1_139_, v_x_138_);
        return v___x_141_;
    } else {
        let mut v_head_142_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_143_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_144_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_139_);
        v_head_142_ = lean_ctor_get(v_x_137_, 0);
        lean_inc(v_head_142_);
        v_tail_143_ = lean_ctor_get(v_x_137_, 1);
        lean_inc(v_tail_143_);
        lean_dec_ref_known(v_x_137_, 2);
        v___x_144_ = lean_apply_3(v_h__2_140_, v_head_142_, v_tail_143_, v_x_138_);
        return v___x_144_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_List_Sort_Lemmas(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_List_Sort_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_BinderPredicates(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Bool(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Nat_Range(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Pairwise(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Perm(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Range(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Sublist(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Linear(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Prod(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_List_Sort_Lemmas(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_List_Sort_Lemmas(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_List_Sort_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_BinderPredicates(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Bool(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_Nat_Range(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_Pairwise(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_Perm(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_Range(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_Sublist(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Linear(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Prod(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Sort_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_List_Sort_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_List_Sort_Lemmas(builtin);
}
