// Lean compiler output
// Module: Init.Data.String.Lemmas.Pattern.Find.Basic
// Imports: Init.Data.String.Slice Init.Data.String.Search Init.Data.String.Lemmas.Pattern.Basic Init.Data.String.Slice Init.Data.String.Search Init.Data.Iterators.Lemmas.Consumers.Loop Init.Data.String.Lemmas.Order Init.Data.String.Lemmas.Basic Init.Data.String.OrderInstances Init.Grind
use crate::r#gen::Init::Data::Iterators::Lemmas::Consumers::Loop::{
    initialize_Init_Data_Iterators_Lemmas_Consumers_Loop,
    runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Loop,
};
use crate::r#gen::Init::Data::String::Lemmas::Basic::{
    initialize_Init_Data_String_Lemmas_Basic, runtime_initialize_Init_Data_String_Lemmas_Basic,
};
use crate::r#gen::Init::Data::String::Lemmas::Order::{
    initialize_Init_Data_String_Lemmas_Order, runtime_initialize_Init_Data_String_Lemmas_Order,
};
use crate::r#gen::Init::Data::String::Lemmas::Pattern::Basic::{
    initialize_Init_Data_String_Lemmas_Pattern_Basic,
    runtime_initialize_Init_Data_String_Lemmas_Pattern_Basic,
};
use crate::r#gen::Init::Data::String::OrderInstances::{
    initialize_Init_Data_String_OrderInstances, runtime_initialize_Init_Data_String_OrderInstances,
};
use crate::r#gen::Init::Data::String::Search::{
    initialize_Init_Data_String_Search, runtime_initialize_Init_Data_String_Search,
};
use crate::r#gen::Init::Data::String::Slice::{
    initialize_Init_Data_String_Slice, runtime_initialize_Init_Data_String_Slice,
};
use crate::r#gen::Init::Grind::{initialize_Init_Grind, runtime_initialize_Init_Grind};
pub unsafe fn l___private_Init_Data_String_Lemmas_Pattern_Find_Basic_0__String_Slice_find_x3f_match__1_splitter___redArg(
    mut v_x_91_: *mut crate::leanh::LeanObject,
    mut v_h__1_92_: *mut crate::leanh::LeanObject,
    mut v_h__2_93_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_91_) == 0 {
        let mut v_startPos_94_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_endPos_95_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_96_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_92_);
        v_startPos_94_ = crate::leanh::lean_ctor_get(v_x_91_, 0);
        crate::leanh::lean_inc(v_startPos_94_);
        v_endPos_95_ = crate::leanh::lean_ctor_get(v_x_91_, 1);
        crate::leanh::lean_inc(v_endPos_95_);
        crate::leanh::lean_dec_ref_known(v_x_91_, 2);
        v___x_96_ = crate::leanh::lean_apply_2(v_h__2_93_, v_startPos_94_, v_endPos_95_);
        return v___x_96_;
    } else {
        let mut v_startPos_97_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_endPos_98_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_99_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_93_);
        v_startPos_97_ = crate::leanh::lean_ctor_get(v_x_91_, 0);
        crate::leanh::lean_inc(v_startPos_97_);
        v_endPos_98_ = crate::leanh::lean_ctor_get(v_x_91_, 1);
        crate::leanh::lean_inc(v_endPos_98_);
        crate::leanh::lean_dec_ref_known(v_x_91_, 2);
        v___x_99_ = crate::leanh::lean_apply_2(v_h__1_92_, v_startPos_97_, v_endPos_98_);
        return v___x_99_;
    }
}
pub unsafe fn l___private_Init_Data_String_Lemmas_Pattern_Find_Basic_0__String_Slice_find_x3f_match__1_splitter(
    mut v_s_100_: *mut crate::leanh::LeanObject,
    mut v_motive_101_: *mut crate::leanh::LeanObject,
    mut v_x_102_: *mut crate::leanh::LeanObject,
    mut v_h__1_103_: *mut crate::leanh::LeanObject,
    mut v_h__2_104_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_102_) == 0 {
        let mut v_startPos_105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_endPos_106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_103_);
        v_startPos_105_ = crate::leanh::lean_ctor_get(v_x_102_, 0);
        crate::leanh::lean_inc(v_startPos_105_);
        v_endPos_106_ = crate::leanh::lean_ctor_get(v_x_102_, 1);
        crate::leanh::lean_inc(v_endPos_106_);
        crate::leanh::lean_dec_ref_known(v_x_102_, 2);
        v___x_107_ = crate::leanh::lean_apply_2(v_h__2_104_, v_startPos_105_, v_endPos_106_);
        return v___x_107_;
    } else {
        let mut v_startPos_108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_endPos_109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_104_);
        v_startPos_108_ = crate::leanh::lean_ctor_get(v_x_102_, 0);
        crate::leanh::lean_inc(v_startPos_108_);
        v_endPos_109_ = crate::leanh::lean_ctor_get(v_x_102_, 1);
        crate::leanh::lean_inc(v_endPos_109_);
        crate::leanh::lean_dec_ref_known(v_x_102_, 2);
        v___x_110_ = crate::leanh::lean_apply_2(v_h__1_103_, v_startPos_108_, v_endPos_109_);
        return v___x_110_;
    }
}
pub unsafe fn l___private_Init_Data_String_Lemmas_Pattern_Find_Basic_0__String_Slice_find_x3f_match__1_splitter___boxed(
    mut v_s_111_: *mut crate::leanh::LeanObject,
    mut v_motive_112_: *mut crate::leanh::LeanObject,
    mut v_x_113_: *mut crate::leanh::LeanObject,
    mut v_h__1_114_: *mut crate::leanh::LeanObject,
    mut v_h__2_115_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_116_ = l___private_Init_Data_String_Lemmas_Pattern_Find_Basic_0__String_Slice_find_x3f_match__1_splitter(v_s_111_, v_motive_112_, v_x_113_, v_h__1_114_, v_h__2_115_);
    crate::leanh::lean_dec_ref(v_s_111_);
    return v_res_116_;
}
pub unsafe fn l___private_Init_Data_String_Lemmas_Pattern_Find_Basic_0__String_Slice_Pattern_Model_find_x3f__eq__some__iff_match__1__2_splitter___redArg(
    mut v_x_117_: *mut crate::leanh::LeanObject,
    mut v_h__1_118_: *mut crate::leanh::LeanObject,
    mut v_h__2_119_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_117_) == 0 {
        let mut v_startPos_120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_endPos_121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_118_);
        v_startPos_120_ = crate::leanh::lean_ctor_get(v_x_117_, 0);
        crate::leanh::lean_inc(v_startPos_120_);
        v_endPos_121_ = crate::leanh::lean_ctor_get(v_x_117_, 1);
        crate::leanh::lean_inc(v_endPos_121_);
        crate::leanh::lean_dec_ref_known(v_x_117_, 2);
        v___x_122_ = crate::leanh::lean_apply_2(v_h__2_119_, v_startPos_120_, v_endPos_121_);
        return v___x_122_;
    } else {
        let mut v_startPos_123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_endPos_124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_119_);
        v_startPos_123_ = crate::leanh::lean_ctor_get(v_x_117_, 0);
        crate::leanh::lean_inc(v_startPos_123_);
        v_endPos_124_ = crate::leanh::lean_ctor_get(v_x_117_, 1);
        crate::leanh::lean_inc(v_endPos_124_);
        crate::leanh::lean_dec_ref_known(v_x_117_, 2);
        v___x_125_ = crate::leanh::lean_apply_2(v_h__1_118_, v_startPos_123_, v_endPos_124_);
        return v___x_125_;
    }
}
pub unsafe fn l___private_Init_Data_String_Lemmas_Pattern_Find_Basic_0__String_Slice_Pattern_Model_find_x3f__eq__some__iff_match__1__2_splitter(
    mut v_s_126_: *mut crate::leanh::LeanObject,
    mut v_motive_127_: *mut crate::leanh::LeanObject,
    mut v_x_128_: *mut crate::leanh::LeanObject,
    mut v_h__1_129_: *mut crate::leanh::LeanObject,
    mut v_h__2_130_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_128_) == 0 {
        let mut v_startPos_131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_endPos_132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_129_);
        v_startPos_131_ = crate::leanh::lean_ctor_get(v_x_128_, 0);
        crate::leanh::lean_inc(v_startPos_131_);
        v_endPos_132_ = crate::leanh::lean_ctor_get(v_x_128_, 1);
        crate::leanh::lean_inc(v_endPos_132_);
        crate::leanh::lean_dec_ref_known(v_x_128_, 2);
        v___x_133_ = crate::leanh::lean_apply_2(v_h__2_130_, v_startPos_131_, v_endPos_132_);
        return v___x_133_;
    } else {
        let mut v_startPos_134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_endPos_135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_130_);
        v_startPos_134_ = crate::leanh::lean_ctor_get(v_x_128_, 0);
        crate::leanh::lean_inc(v_startPos_134_);
        v_endPos_135_ = crate::leanh::lean_ctor_get(v_x_128_, 1);
        crate::leanh::lean_inc(v_endPos_135_);
        crate::leanh::lean_dec_ref_known(v_x_128_, 2);
        v___x_136_ = crate::leanh::lean_apply_2(v_h__1_129_, v_startPos_134_, v_endPos_135_);
        return v___x_136_;
    }
}
pub unsafe fn l___private_Init_Data_String_Lemmas_Pattern_Find_Basic_0__String_Slice_Pattern_Model_find_x3f__eq__some__iff_match__1__2_splitter___boxed(
    mut v_s_137_: *mut crate::leanh::LeanObject,
    mut v_motive_138_: *mut crate::leanh::LeanObject,
    mut v_x_139_: *mut crate::leanh::LeanObject,
    mut v_h__1_140_: *mut crate::leanh::LeanObject,
    mut v_h__2_141_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_142_ = l___private_Init_Data_String_Lemmas_Pattern_Find_Basic_0__String_Slice_Pattern_Model_find_x3f__eq__some__iff_match__1__2_splitter(v_s_137_, v_motive_138_, v_x_139_, v_h__1_140_, v_h__2_141_);
    crate::leanh::lean_dec_ref(v_s_137_);
    return v_res_142_;
}
pub unsafe fn l___private_Init_Data_String_Lemmas_Pattern_Find_Basic_0__String_Slice_contains_match__1_splitter___redArg(
    mut v_x_143_: *mut crate::leanh::LeanObject,
    mut v_h__1_144_: *mut crate::leanh::LeanObject,
    mut v_h__2_145_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_143_) == 1 {
        let mut v_startPos_146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_endPos_147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_145_);
        v_startPos_146_ = crate::leanh::lean_ctor_get(v_x_143_, 0);
        crate::leanh::lean_inc(v_startPos_146_);
        v_endPos_147_ = crate::leanh::lean_ctor_get(v_x_143_, 1);
        crate::leanh::lean_inc(v_endPos_147_);
        crate::leanh::lean_dec_ref_known(v_x_143_, 2);
        v___x_148_ = crate::leanh::lean_apply_2(v_h__1_144_, v_startPos_146_, v_endPos_147_);
        return v___x_148_;
    } else {
        let mut v___x_149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_144_);
        v___x_149_ = crate::leanh::lean_apply_2(v_h__2_145_, v_x_143_, crate::leanh::lean_box(0));
        return v___x_149_;
    }
}
pub unsafe fn l___private_Init_Data_String_Lemmas_Pattern_Find_Basic_0__String_Slice_contains_match__1_splitter(
    mut v_s_150_: *mut crate::leanh::LeanObject,
    mut v_motive_151_: *mut crate::leanh::LeanObject,
    mut v_x_152_: *mut crate::leanh::LeanObject,
    mut v_h__1_153_: *mut crate::leanh::LeanObject,
    mut v_h__2_154_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_152_) == 1 {
        let mut v_startPos_155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_endPos_156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_154_);
        v_startPos_155_ = crate::leanh::lean_ctor_get(v_x_152_, 0);
        crate::leanh::lean_inc(v_startPos_155_);
        v_endPos_156_ = crate::leanh::lean_ctor_get(v_x_152_, 1);
        crate::leanh::lean_inc(v_endPos_156_);
        crate::leanh::lean_dec_ref_known(v_x_152_, 2);
        v___x_157_ = crate::leanh::lean_apply_2(v_h__1_153_, v_startPos_155_, v_endPos_156_);
        return v___x_157_;
    } else {
        let mut v___x_158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_153_);
        v___x_158_ = crate::leanh::lean_apply_2(v_h__2_154_, v_x_152_, crate::leanh::lean_box(0));
        return v___x_158_;
    }
}
pub unsafe fn l___private_Init_Data_String_Lemmas_Pattern_Find_Basic_0__String_Slice_contains_match__1_splitter___boxed(
    mut v_s_159_: *mut crate::leanh::LeanObject,
    mut v_motive_160_: *mut crate::leanh::LeanObject,
    mut v_x_161_: *mut crate::leanh::LeanObject,
    mut v_h__1_162_: *mut crate::leanh::LeanObject,
    mut v_h__2_163_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_164_ = l___private_Init_Data_String_Lemmas_Pattern_Find_Basic_0__String_Slice_contains_match__1_splitter(v_s_159_, v_motive_160_, v_x_161_, v_h__1_162_, v_h__2_163_);
    crate::leanh::lean_dec_ref(v_s_159_);
    return v_res_164_;
}
pub unsafe fn l___private_Init_Data_String_Lemmas_Pattern_Find_Basic_0__List_findSome_x3f_match__1_splitter___redArg(
    mut v_x_165_: *mut crate::leanh::LeanObject,
    mut v_h__1_166_: *mut crate::leanh::LeanObject,
    mut v_h__2_167_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_165_) == 0 {
        let mut v___x_168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_166_);
        v___x_168_ = crate::leanh::lean_box(0);
        v___x_169_ = crate::leanh::lean_apply_1(v_h__2_167_, v___x_168_);
        return v___x_169_;
    } else {
        let mut v_val_170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_167_);
        v_val_170_ = crate::leanh::lean_ctor_get(v_x_165_, 0);
        crate::leanh::lean_inc(v_val_170_);
        crate::leanh::lean_dec_ref_known(v_x_165_, 1);
        v___x_171_ = crate::leanh::lean_apply_1(v_h__1_166_, v_val_170_);
        return v___x_171_;
    }
}
pub unsafe fn l___private_Init_Data_String_Lemmas_Pattern_Find_Basic_0__List_findSome_x3f_match__1_splitter(
    mut v_00_u03b2_172_: *mut crate::leanh::LeanObject,
    mut v_motive_173_: *mut crate::leanh::LeanObject,
    mut v_x_174_: *mut crate::leanh::LeanObject,
    mut v_h__1_175_: *mut crate::leanh::LeanObject,
    mut v_h__2_176_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_174_) == 0 {
        let mut v___x_177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_175_);
        v___x_177_ = crate::leanh::lean_box(0);
        v___x_178_ = crate::leanh::lean_apply_1(v_h__2_176_, v___x_177_);
        return v___x_178_;
    } else {
        let mut v_val_179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_176_);
        v_val_179_ = crate::leanh::lean_ctor_get(v_x_174_, 0);
        crate::leanh::lean_inc(v_val_179_);
        crate::leanh::lean_dec_ref_known(v_x_174_, 1);
        v___x_180_ = crate::leanh::lean_apply_1(v_h__1_175_, v_val_179_);
        return v___x_180_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_String_Lemmas_Pattern_Find_Basic(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_String_Slice(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Search(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_Pattern_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Slice(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Search(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Loop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_Order(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_OrderInstances(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Grind(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_String_Lemmas_Pattern_Find_Basic(
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
pub unsafe fn initialize_Init_Data_String_Lemmas_Pattern_Find_Basic(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_String_Slice(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Search(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Lemmas_Pattern_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Slice(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Search(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Consumers_Loop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Lemmas_Order(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Lemmas_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_OrderInstances(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Grind(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_Pattern_Find_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_String_Lemmas_Pattern_Find_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_String_Lemmas_Pattern_Find_Basic(builtin);
}
