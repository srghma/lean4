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
    mut v_x_91_: *mut leanh::LeanObject,
    mut v_h__1_92_: *mut leanh::LeanObject,
    mut v_h__2_93_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_91_) == 0 {
        let mut v_startPos_94_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_endPos_95_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_96_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_92_);
        v_startPos_94_ = leanh::lean_ctor_get(v_x_91_, 0);
        leanh::lean_inc(v_startPos_94_);
        v_endPos_95_ = leanh::lean_ctor_get(v_x_91_, 1);
        leanh::lean_inc(v_endPos_95_);
        leanh::lean_dec_ref_known(v_x_91_, 2);
        v___x_96_ = leanh::lean_apply_2(v_h__2_93_, v_startPos_94_, v_endPos_95_);
        return v___x_96_;
    } else {
        let mut v_startPos_97_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_endPos_98_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_99_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_93_);
        v_startPos_97_ = leanh::lean_ctor_get(v_x_91_, 0);
        leanh::lean_inc(v_startPos_97_);
        v_endPos_98_ = leanh::lean_ctor_get(v_x_91_, 1);
        leanh::lean_inc(v_endPos_98_);
        leanh::lean_dec_ref_known(v_x_91_, 2);
        v___x_99_ = leanh::lean_apply_2(v_h__1_92_, v_startPos_97_, v_endPos_98_);
        return v___x_99_;
    }
}
pub unsafe fn l___private_Init_Data_String_Lemmas_Pattern_Find_Basic_0__String_Slice_find_x3f_match__1_splitter(
    mut v_s_100_: *mut leanh::LeanObject,
    mut v_motive_101_: *mut leanh::LeanObject,
    mut v_x_102_: *mut leanh::LeanObject,
    mut v_h__1_103_: *mut leanh::LeanObject,
    mut v_h__2_104_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_102_) == 0 {
        let mut v_startPos_105_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_endPos_106_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_107_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_103_);
        v_startPos_105_ = leanh::lean_ctor_get(v_x_102_, 0);
        leanh::lean_inc(v_startPos_105_);
        v_endPos_106_ = leanh::lean_ctor_get(v_x_102_, 1);
        leanh::lean_inc(v_endPos_106_);
        leanh::lean_dec_ref_known(v_x_102_, 2);
        v___x_107_ = leanh::lean_apply_2(v_h__2_104_, v_startPos_105_, v_endPos_106_);
        return v___x_107_;
    } else {
        let mut v_startPos_108_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_endPos_109_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_110_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_104_);
        v_startPos_108_ = leanh::lean_ctor_get(v_x_102_, 0);
        leanh::lean_inc(v_startPos_108_);
        v_endPos_109_ = leanh::lean_ctor_get(v_x_102_, 1);
        leanh::lean_inc(v_endPos_109_);
        leanh::lean_dec_ref_known(v_x_102_, 2);
        v___x_110_ = leanh::lean_apply_2(v_h__1_103_, v_startPos_108_, v_endPos_109_);
        return v___x_110_;
    }
}
pub unsafe fn l___private_Init_Data_String_Lemmas_Pattern_Find_Basic_0__String_Slice_find_x3f_match__1_splitter___boxed(
    mut v_s_111_: *mut leanh::LeanObject,
    mut v_motive_112_: *mut leanh::LeanObject,
    mut v_x_113_: *mut leanh::LeanObject,
    mut v_h__1_114_: *mut leanh::LeanObject,
    mut v_h__2_115_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_116_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_116_ = l___private_Init_Data_String_Lemmas_Pattern_Find_Basic_0__String_Slice_find_x3f_match__1_splitter(v_s_111_, v_motive_112_, v_x_113_, v_h__1_114_, v_h__2_115_);
    leanh::lean_dec_ref(v_s_111_);
    return v_res_116_;
}
pub unsafe fn l___private_Init_Data_String_Lemmas_Pattern_Find_Basic_0__String_Slice_Pattern_Model_find_x3f__eq__some__iff_match__1__2_splitter___redArg(
    mut v_x_117_: *mut leanh::LeanObject,
    mut v_h__1_118_: *mut leanh::LeanObject,
    mut v_h__2_119_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_117_) == 0 {
        let mut v_startPos_120_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_endPos_121_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_122_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_118_);
        v_startPos_120_ = leanh::lean_ctor_get(v_x_117_, 0);
        leanh::lean_inc(v_startPos_120_);
        v_endPos_121_ = leanh::lean_ctor_get(v_x_117_, 1);
        leanh::lean_inc(v_endPos_121_);
        leanh::lean_dec_ref_known(v_x_117_, 2);
        v___x_122_ = leanh::lean_apply_2(v_h__2_119_, v_startPos_120_, v_endPos_121_);
        return v___x_122_;
    } else {
        let mut v_startPos_123_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_endPos_124_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_125_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_119_);
        v_startPos_123_ = leanh::lean_ctor_get(v_x_117_, 0);
        leanh::lean_inc(v_startPos_123_);
        v_endPos_124_ = leanh::lean_ctor_get(v_x_117_, 1);
        leanh::lean_inc(v_endPos_124_);
        leanh::lean_dec_ref_known(v_x_117_, 2);
        v___x_125_ = leanh::lean_apply_2(v_h__1_118_, v_startPos_123_, v_endPos_124_);
        return v___x_125_;
    }
}
pub unsafe fn l___private_Init_Data_String_Lemmas_Pattern_Find_Basic_0__String_Slice_Pattern_Model_find_x3f__eq__some__iff_match__1__2_splitter(
    mut v_s_126_: *mut leanh::LeanObject,
    mut v_motive_127_: *mut leanh::LeanObject,
    mut v_x_128_: *mut leanh::LeanObject,
    mut v_h__1_129_: *mut leanh::LeanObject,
    mut v_h__2_130_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_128_) == 0 {
        let mut v_startPos_131_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_endPos_132_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_133_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_129_);
        v_startPos_131_ = leanh::lean_ctor_get(v_x_128_, 0);
        leanh::lean_inc(v_startPos_131_);
        v_endPos_132_ = leanh::lean_ctor_get(v_x_128_, 1);
        leanh::lean_inc(v_endPos_132_);
        leanh::lean_dec_ref_known(v_x_128_, 2);
        v___x_133_ = leanh::lean_apply_2(v_h__2_130_, v_startPos_131_, v_endPos_132_);
        return v___x_133_;
    } else {
        let mut v_startPos_134_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_endPos_135_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_136_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_130_);
        v_startPos_134_ = leanh::lean_ctor_get(v_x_128_, 0);
        leanh::lean_inc(v_startPos_134_);
        v_endPos_135_ = leanh::lean_ctor_get(v_x_128_, 1);
        leanh::lean_inc(v_endPos_135_);
        leanh::lean_dec_ref_known(v_x_128_, 2);
        v___x_136_ = leanh::lean_apply_2(v_h__1_129_, v_startPos_134_, v_endPos_135_);
        return v___x_136_;
    }
}
pub unsafe fn l___private_Init_Data_String_Lemmas_Pattern_Find_Basic_0__String_Slice_Pattern_Model_find_x3f__eq__some__iff_match__1__2_splitter___boxed(
    mut v_s_137_: *mut leanh::LeanObject,
    mut v_motive_138_: *mut leanh::LeanObject,
    mut v_x_139_: *mut leanh::LeanObject,
    mut v_h__1_140_: *mut leanh::LeanObject,
    mut v_h__2_141_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_142_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_142_ = l___private_Init_Data_String_Lemmas_Pattern_Find_Basic_0__String_Slice_Pattern_Model_find_x3f__eq__some__iff_match__1__2_splitter(v_s_137_, v_motive_138_, v_x_139_, v_h__1_140_, v_h__2_141_);
    leanh::lean_dec_ref(v_s_137_);
    return v_res_142_;
}
pub unsafe fn l___private_Init_Data_String_Lemmas_Pattern_Find_Basic_0__String_Slice_contains_match__1_splitter___redArg(
    mut v_x_143_: *mut leanh::LeanObject,
    mut v_h__1_144_: *mut leanh::LeanObject,
    mut v_h__2_145_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_143_) == 1 {
        let mut v_startPos_146_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_endPos_147_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_148_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_145_);
        v_startPos_146_ = leanh::lean_ctor_get(v_x_143_, 0);
        leanh::lean_inc(v_startPos_146_);
        v_endPos_147_ = leanh::lean_ctor_get(v_x_143_, 1);
        leanh::lean_inc(v_endPos_147_);
        leanh::lean_dec_ref_known(v_x_143_, 2);
        v___x_148_ = leanh::lean_apply_2(v_h__1_144_, v_startPos_146_, v_endPos_147_);
        return v___x_148_;
    } else {
        let mut v___x_149_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_144_);
        v___x_149_ = leanh::lean_apply_2(v_h__2_145_, v_x_143_, leanh::lean_box(0));
        return v___x_149_;
    }
}
pub unsafe fn l___private_Init_Data_String_Lemmas_Pattern_Find_Basic_0__String_Slice_contains_match__1_splitter(
    mut v_s_150_: *mut leanh::LeanObject,
    mut v_motive_151_: *mut leanh::LeanObject,
    mut v_x_152_: *mut leanh::LeanObject,
    mut v_h__1_153_: *mut leanh::LeanObject,
    mut v_h__2_154_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_152_) == 1 {
        let mut v_startPos_155_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_endPos_156_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_157_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_154_);
        v_startPos_155_ = leanh::lean_ctor_get(v_x_152_, 0);
        leanh::lean_inc(v_startPos_155_);
        v_endPos_156_ = leanh::lean_ctor_get(v_x_152_, 1);
        leanh::lean_inc(v_endPos_156_);
        leanh::lean_dec_ref_known(v_x_152_, 2);
        v___x_157_ = leanh::lean_apply_2(v_h__1_153_, v_startPos_155_, v_endPos_156_);
        return v___x_157_;
    } else {
        let mut v___x_158_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_153_);
        v___x_158_ = leanh::lean_apply_2(v_h__2_154_, v_x_152_, leanh::lean_box(0));
        return v___x_158_;
    }
}
pub unsafe fn l___private_Init_Data_String_Lemmas_Pattern_Find_Basic_0__String_Slice_contains_match__1_splitter___boxed(
    mut v_s_159_: *mut leanh::LeanObject,
    mut v_motive_160_: *mut leanh::LeanObject,
    mut v_x_161_: *mut leanh::LeanObject,
    mut v_h__1_162_: *mut leanh::LeanObject,
    mut v_h__2_163_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_164_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_164_ = l___private_Init_Data_String_Lemmas_Pattern_Find_Basic_0__String_Slice_contains_match__1_splitter(v_s_159_, v_motive_160_, v_x_161_, v_h__1_162_, v_h__2_163_);
    leanh::lean_dec_ref(v_s_159_);
    return v_res_164_;
}
pub unsafe fn l___private_Init_Data_String_Lemmas_Pattern_Find_Basic_0__List_findSome_x3f_match__1_splitter___redArg(
    mut v_x_165_: *mut leanh::LeanObject,
    mut v_h__1_166_: *mut leanh::LeanObject,
    mut v_h__2_167_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_165_) == 0 {
        let mut v___x_168_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_169_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_166_);
        v___x_168_ = leanh::lean_box(0);
        v___x_169_ = leanh::lean_apply_1(v_h__2_167_, v___x_168_);
        return v___x_169_;
    } else {
        let mut v_val_170_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_171_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_167_);
        v_val_170_ = leanh::lean_ctor_get(v_x_165_, 0);
        leanh::lean_inc(v_val_170_);
        leanh::lean_dec_ref_known(v_x_165_, 1);
        v___x_171_ = leanh::lean_apply_1(v_h__1_166_, v_val_170_);
        return v___x_171_;
    }
}
pub unsafe fn l___private_Init_Data_String_Lemmas_Pattern_Find_Basic_0__List_findSome_x3f_match__1_splitter(
    mut v_00_u03b2_172_: *mut leanh::LeanObject,
    mut v_motive_173_: *mut leanh::LeanObject,
    mut v_x_174_: *mut leanh::LeanObject,
    mut v_h__1_175_: *mut leanh::LeanObject,
    mut v_h__2_176_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_174_) == 0 {
        let mut v___x_177_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_178_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_175_);
        v___x_177_ = leanh::lean_box(0);
        v___x_178_ = leanh::lean_apply_1(v_h__2_176_, v___x_177_);
        return v___x_178_;
    } else {
        let mut v_val_179_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_180_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_176_);
        v_val_179_ = leanh::lean_ctor_get(v_x_174_, 0);
        leanh::lean_inc(v_val_179_);
        leanh::lean_dec_ref_known(v_x_174_, 1);
        v___x_180_ = leanh::lean_apply_1(v_h__1_175_, v_val_179_);
        return v___x_180_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_String_Lemmas_Pattern_Find_Basic(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_String_Slice(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Search(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_Pattern_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Slice(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Search(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Loop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_Order(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_OrderInstances(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Grind(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_String_Lemmas_Pattern_Find_Basic(
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
pub unsafe fn initialize_Init_Data_String_Lemmas_Pattern_Find_Basic(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_String_Slice(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Search(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Lemmas_Pattern_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Slice(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Search(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Consumers_Loop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Lemmas_Order(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Lemmas_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_OrderInstances(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Grind(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_Pattern_Find_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_String_Lemmas_Pattern_Find_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_String_Lemmas_Pattern_Find_Basic(builtin);
}