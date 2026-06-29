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
pub unsafe fn l___private_Init_Data_List_Sort_Lemmas_0__List_merge_match__1_splitter___redArg(
    mut v_xs_73_: *mut crate::leanh::LeanObject,
    mut v_ys_74_: *mut crate::leanh::LeanObject,
    mut v_h__1_75_: *mut crate::leanh::LeanObject,
    mut v_h__2_76_: *mut crate::leanh::LeanObject,
    mut v_h__3_77_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_xs_73_) == 0 {
        let mut v___x_78_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__3_77_);
        crate::leanh::lean_dec(v_h__2_76_);
        v___x_78_ = crate::leanh::lean_apply_1(v_h__1_75_, v_ys_74_);
        return v___x_78_;
    } else {
        crate::leanh::lean_dec(v_h__1_75_);
        if crate::leanh::lean_obj_tag(v_ys_74_) == 0 {
            let mut v___x_79_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_77_);
            v___x_79_ = crate::leanh::lean_apply_2(v_h__2_76_, v_xs_73_, crate::leanh::lean_box(0));
            return v___x_79_;
        } else {
            let mut v_head_80_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_tail_81_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_head_82_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_tail_83_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_84_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_76_);
            v_head_80_ = crate::leanh::lean_ctor_get(v_xs_73_, 0);
            crate::leanh::lean_inc(v_head_80_);
            v_tail_81_ = crate::leanh::lean_ctor_get(v_xs_73_, 1);
            crate::leanh::lean_inc(v_tail_81_);
            crate::leanh::lean_dec_ref_known(v_xs_73_, 2);
            v_head_82_ = crate::leanh::lean_ctor_get(v_ys_74_, 0);
            crate::leanh::lean_inc(v_head_82_);
            v_tail_83_ = crate::leanh::lean_ctor_get(v_ys_74_, 1);
            crate::leanh::lean_inc(v_tail_83_);
            crate::leanh::lean_dec_ref_known(v_ys_74_, 2);
            v___x_84_ = crate::leanh::lean_apply_4(
                v_h__3_77_, v_head_80_, v_tail_81_, v_head_82_, v_tail_83_,
            );
            return v___x_84_;
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Sort_Lemmas_0__List_merge_match__1_splitter(
    mut v_00_u03b1_85_: *mut crate::leanh::LeanObject,
    mut v_motive_86_: *mut crate::leanh::LeanObject,
    mut v_xs_87_: *mut crate::leanh::LeanObject,
    mut v_ys_88_: *mut crate::leanh::LeanObject,
    mut v_h__1_89_: *mut crate::leanh::LeanObject,
    mut v_h__2_90_: *mut crate::leanh::LeanObject,
    mut v_h__3_91_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_xs_87_) == 0 {
        let mut v___x_92_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__3_91_);
        crate::leanh::lean_dec(v_h__2_90_);
        v___x_92_ = crate::leanh::lean_apply_1(v_h__1_89_, v_ys_88_);
        return v___x_92_;
    } else {
        crate::leanh::lean_dec(v_h__1_89_);
        if crate::leanh::lean_obj_tag(v_ys_88_) == 0 {
            let mut v___x_93_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_91_);
            v___x_93_ = crate::leanh::lean_apply_2(v_h__2_90_, v_xs_87_, crate::leanh::lean_box(0));
            return v___x_93_;
        } else {
            let mut v_head_94_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_tail_95_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_head_96_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_tail_97_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_98_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_90_);
            v_head_94_ = crate::leanh::lean_ctor_get(v_xs_87_, 0);
            crate::leanh::lean_inc(v_head_94_);
            v_tail_95_ = crate::leanh::lean_ctor_get(v_xs_87_, 1);
            crate::leanh::lean_inc(v_tail_95_);
            crate::leanh::lean_dec_ref_known(v_xs_87_, 2);
            v_head_96_ = crate::leanh::lean_ctor_get(v_ys_88_, 0);
            crate::leanh::lean_inc(v_head_96_);
            v_tail_97_ = crate::leanh::lean_ctor_get(v_ys_88_, 1);
            crate::leanh::lean_inc(v_tail_97_);
            crate::leanh::lean_dec_ref_known(v_ys_88_, 2);
            v___x_98_ = crate::leanh::lean_apply_4(
                v_h__3_91_, v_head_94_, v_tail_95_, v_head_96_, v_tail_97_,
            );
            return v___x_98_;
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Sort_Lemmas_0__List_mergeSort_match__1_splitter___redArg(
    mut v_x_99_: *mut crate::leanh::LeanObject,
    mut v_x_100_: *mut crate::leanh::LeanObject,
    mut v_h__1_101_: *mut crate::leanh::LeanObject,
    mut v_h__2_102_: *mut crate::leanh::LeanObject,
    mut v_h__3_103_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_99_) == 0 {
        let mut v___x_104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__3_103_);
        crate::leanh::lean_dec(v_h__2_102_);
        v___x_104_ = crate::leanh::lean_apply_1(v_h__1_101_, v_x_100_);
        return v___x_104_;
    } else {
        let mut v_tail_105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_101_);
        v_tail_105_ = crate::leanh::lean_ctor_get(v_x_99_, 1);
        if crate::leanh::lean_obj_tag(v_tail_105_) == 0 {
            let mut v_head_106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_103_);
            v_head_106_ = crate::leanh::lean_ctor_get(v_x_99_, 0);
            crate::leanh::lean_inc(v_head_106_);
            crate::leanh::lean_dec_ref_known(v_x_99_, 2);
            v___x_107_ = crate::leanh::lean_apply_2(v_h__2_102_, v_head_106_, v_x_100_);
            return v___x_107_;
        } else {
            let mut v_head_108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_head_109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_tail_110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc_ref(v_tail_105_);
            crate::leanh::lean_dec(v_h__2_102_);
            v_head_108_ = crate::leanh::lean_ctor_get(v_x_99_, 0);
            crate::leanh::lean_inc(v_head_108_);
            crate::leanh::lean_dec_ref_known(v_x_99_, 2);
            v_head_109_ = crate::leanh::lean_ctor_get(v_tail_105_, 0);
            crate::leanh::lean_inc(v_head_109_);
            v_tail_110_ = crate::leanh::lean_ctor_get(v_tail_105_, 1);
            crate::leanh::lean_inc(v_tail_110_);
            crate::leanh::lean_dec_ref_known(v_tail_105_, 2);
            v___x_111_ = crate::leanh::lean_apply_4(
                v_h__3_103_,
                v_head_108_,
                v_head_109_,
                v_tail_110_,
                v_x_100_,
            );
            return v___x_111_;
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Sort_Lemmas_0__List_mergeSort_match__1_splitter(
    mut v_00_u03b1_112_: *mut crate::leanh::LeanObject,
    mut v_motive_113_: *mut crate::leanh::LeanObject,
    mut v_x_114_: *mut crate::leanh::LeanObject,
    mut v_x_115_: *mut crate::leanh::LeanObject,
    mut v_h__1_116_: *mut crate::leanh::LeanObject,
    mut v_h__2_117_: *mut crate::leanh::LeanObject,
    mut v_h__3_118_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_114_) == 0 {
        let mut v___x_119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__3_118_);
        crate::leanh::lean_dec(v_h__2_117_);
        v___x_119_ = crate::leanh::lean_apply_1(v_h__1_116_, v_x_115_);
        return v___x_119_;
    } else {
        let mut v_tail_120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_116_);
        v_tail_120_ = crate::leanh::lean_ctor_get(v_x_114_, 1);
        if crate::leanh::lean_obj_tag(v_tail_120_) == 0 {
            let mut v_head_121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_118_);
            v_head_121_ = crate::leanh::lean_ctor_get(v_x_114_, 0);
            crate::leanh::lean_inc(v_head_121_);
            crate::leanh::lean_dec_ref_known(v_x_114_, 2);
            v___x_122_ = crate::leanh::lean_apply_2(v_h__2_117_, v_head_121_, v_x_115_);
            return v___x_122_;
        } else {
            let mut v_head_123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_head_124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_tail_125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc_ref(v_tail_120_);
            crate::leanh::lean_dec(v_h__2_117_);
            v_head_123_ = crate::leanh::lean_ctor_get(v_x_114_, 0);
            crate::leanh::lean_inc(v_head_123_);
            crate::leanh::lean_dec_ref_known(v_x_114_, 2);
            v_head_124_ = crate::leanh::lean_ctor_get(v_tail_120_, 0);
            crate::leanh::lean_inc(v_head_124_);
            v_tail_125_ = crate::leanh::lean_ctor_get(v_tail_120_, 1);
            crate::leanh::lean_inc(v_tail_125_);
            crate::leanh::lean_dec_ref_known(v_tail_120_, 2);
            v___x_126_ = crate::leanh::lean_apply_4(
                v_h__3_118_,
                v_head_123_,
                v_head_124_,
                v_tail_125_,
                v_x_115_,
            );
            return v___x_126_;
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Sort_Lemmas_0__List_findIdx_go_match__1_splitter___redArg(
    mut v_x_127_: *mut crate::leanh::LeanObject,
    mut v_x_128_: *mut crate::leanh::LeanObject,
    mut v_h__1_129_: *mut crate::leanh::LeanObject,
    mut v_h__2_130_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_127_) == 0 {
        let mut v___x_131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_130_);
        v___x_131_ = crate::leanh::lean_apply_1(v_h__1_129_, v_x_128_);
        return v___x_131_;
    } else {
        let mut v_head_132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_129_);
        v_head_132_ = crate::leanh::lean_ctor_get(v_x_127_, 0);
        crate::leanh::lean_inc(v_head_132_);
        v_tail_133_ = crate::leanh::lean_ctor_get(v_x_127_, 1);
        crate::leanh::lean_inc(v_tail_133_);
        crate::leanh::lean_dec_ref_known(v_x_127_, 2);
        v___x_134_ = crate::leanh::lean_apply_3(v_h__2_130_, v_head_132_, v_tail_133_, v_x_128_);
        return v___x_134_;
    }
}
pub unsafe fn l___private_Init_Data_List_Sort_Lemmas_0__List_findIdx_go_match__1_splitter(
    mut v_00_u03b1_135_: *mut crate::leanh::LeanObject,
    mut v_motive_136_: *mut crate::leanh::LeanObject,
    mut v_x_137_: *mut crate::leanh::LeanObject,
    mut v_x_138_: *mut crate::leanh::LeanObject,
    mut v_h__1_139_: *mut crate::leanh::LeanObject,
    mut v_h__2_140_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_137_) == 0 {
        let mut v___x_141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_140_);
        v___x_141_ = crate::leanh::lean_apply_1(v_h__1_139_, v_x_138_);
        return v___x_141_;
    } else {
        let mut v_head_142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_139_);
        v_head_142_ = crate::leanh::lean_ctor_get(v_x_137_, 0);
        crate::leanh::lean_inc(v_head_142_);
        v_tail_143_ = crate::leanh::lean_ctor_get(v_x_137_, 1);
        crate::leanh::lean_inc(v_tail_143_);
        crate::leanh::lean_dec_ref_known(v_x_137_, 2);
        v___x_144_ = crate::leanh::lean_apply_3(v_h__2_140_, v_head_142_, v_tail_143_, v_x_138_);
        return v___x_144_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_List_Sort_Lemmas(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_List_Sort_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Sort_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_BinderPredicates(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Bool(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Nat_Range(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Pairwise(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Perm(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Range(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Sublist(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Linear(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Prod(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_List_Sort_Lemmas(
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
pub unsafe fn initialize_Init_Data_List_Sort_Lemmas(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_List_Sort_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Sort_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_BinderPredicates(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Bool(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Nat_Range(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Pairwise(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Perm(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Range(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Sublist(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Linear(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Prod(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Sort_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_List_Sort_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_List_Sort_Lemmas(builtin);
}
