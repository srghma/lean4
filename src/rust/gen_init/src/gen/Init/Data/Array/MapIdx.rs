// Lean compiler output
// Module: Init.Data.Array.MapIdx
// Imports: Init.Data.Array.Basic Init.Data.List.MapIdx Init.Data.List.MapIdx Init.Data.Array.OfFn
use crate::ffi::{lean_nat_dec_eq, lean_nat_sub};
use crate::r#gen::Init::Data::Array::Basic::{
    initialize_Init_Data_Array_Basic, runtime_initialize_Init_Data_Array_Basic,
};
use crate::r#gen::Init::Data::Array::OfFn::{
    initialize_Init_Data_Array_OfFn, runtime_initialize_Init_Data_Array_OfFn,
};
use crate::r#gen::Init::Data::List::MapIdx::{
    initialize_Init_Data_List_MapIdx, runtime_initialize_Init_Data_List_MapIdx,
};
pub unsafe fn l___private_Init_Data_Array_MapIdx_0__Array_mapFinIdxM_map_match__1_splitter___redArg(
    mut v_i_87_: *mut crate::leanh::LeanObject,
    mut v_h__1_88_: *mut crate::leanh::LeanObject,
    mut v_h__2_89_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_90_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_91_: u8 = 0;
    v_zero_90_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_91_ = lean_nat_dec_eq(v_i_87_, v_zero_90_);
    if v_isZero_91_ == 1 {
        let mut v___x_92_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_89_);
        v___x_92_ = crate::leanh::lean_apply_1(v_h__1_88_, crate::leanh::lean_box(0));
        return v___x_92_;
    } else {
        let mut v_one_93_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_94_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_95_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_88_);
        v_one_93_ = crate::leanh::lean_unsigned_to_nat(1);
        v_n_94_ = lean_nat_sub(v_i_87_, v_one_93_);
        v___x_95_ = crate::leanh::lean_apply_2(v_h__2_89_, v_n_94_, crate::leanh::lean_box(0));
        return v___x_95_;
    }
}
pub unsafe fn l___private_Init_Data_Array_MapIdx_0__Array_mapFinIdxM_map_match__1_splitter___redArg___boxed(
    mut v_i_96_: *mut crate::leanh::LeanObject,
    mut v_h__1_97_: *mut crate::leanh::LeanObject,
    mut v_h__2_98_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_99_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_99_ =
        l___private_Init_Data_Array_MapIdx_0__Array_mapFinIdxM_map_match__1_splitter___redArg(
            v_i_96_, v_h__1_97_, v_h__2_98_,
        );
    crate::leanh::lean_dec(v_i_96_);
    return v_res_99_;
}
pub unsafe fn l___private_Init_Data_Array_MapIdx_0__Array_mapFinIdxM_map_match__1_splitter(
    mut v_00_u03b1_100_: *mut crate::leanh::LeanObject,
    mut v_as_101_: *mut crate::leanh::LeanObject,
    mut v_j_102_: *mut crate::leanh::LeanObject,
    mut v_motive_103_: *mut crate::leanh::LeanObject,
    mut v_i_104_: *mut crate::leanh::LeanObject,
    mut v_inv_105_: *mut crate::leanh::LeanObject,
    mut v_h__1_106_: *mut crate::leanh::LeanObject,
    mut v_h__2_107_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_109_: u8 = 0;
    v_zero_108_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_109_ = lean_nat_dec_eq(v_i_104_, v_zero_108_);
    if v_isZero_109_ == 1 {
        let mut v___x_110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_107_);
        v___x_110_ = crate::leanh::lean_apply_1(v_h__1_106_, crate::leanh::lean_box(0));
        return v___x_110_;
    } else {
        let mut v_one_111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_106_);
        v_one_111_ = crate::leanh::lean_unsigned_to_nat(1);
        v_n_112_ = lean_nat_sub(v_i_104_, v_one_111_);
        v___x_113_ = crate::leanh::lean_apply_2(v_h__2_107_, v_n_112_, crate::leanh::lean_box(0));
        return v___x_113_;
    }
}
pub unsafe fn l___private_Init_Data_Array_MapIdx_0__Array_mapFinIdxM_map_match__1_splitter___boxed(
    mut v_00_u03b1_114_: *mut crate::leanh::LeanObject,
    mut v_as_115_: *mut crate::leanh::LeanObject,
    mut v_j_116_: *mut crate::leanh::LeanObject,
    mut v_motive_117_: *mut crate::leanh::LeanObject,
    mut v_i_118_: *mut crate::leanh::LeanObject,
    mut v_inv_119_: *mut crate::leanh::LeanObject,
    mut v_h__1_120_: *mut crate::leanh::LeanObject,
    mut v_h__2_121_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_122_ = l___private_Init_Data_Array_MapIdx_0__Array_mapFinIdxM_map_match__1_splitter(
        v_00_u03b1_114_,
        v_as_115_,
        v_j_116_,
        v_motive_117_,
        v_i_118_,
        v_inv_119_,
        v_h__1_120_,
        v_h__2_121_,
    );
    crate::leanh::lean_dec(v_i_118_);
    crate::leanh::lean_dec(v_j_116_);
    crate::leanh::lean_dec_ref(v_as_115_);
    return v_res_122_;
}
pub unsafe fn l___private_Init_Data_Array_MapIdx_0__List_mapFinIdx_go_match__1_splitter___redArg(
    mut v_x_123_: *mut crate::leanh::LeanObject,
    mut v_x_124_: *mut crate::leanh::LeanObject,
    mut v_h__1_125_: *mut crate::leanh::LeanObject,
    mut v_h__2_126_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_123_) == 0 {
        let mut v___x_127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_126_);
        v___x_127_ = crate::leanh::lean_apply_2(v_h__1_125_, v_x_124_, crate::leanh::lean_box(0));
        return v___x_127_;
    } else {
        let mut v_head_128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_125_);
        v_head_128_ = crate::leanh::lean_ctor_get(v_x_123_, 0);
        crate::leanh::lean_inc(v_head_128_);
        v_tail_129_ = crate::leanh::lean_ctor_get(v_x_123_, 1);
        crate::leanh::lean_inc(v_tail_129_);
        crate::leanh::lean_dec_ref_known(v_x_123_, 2);
        v___x_130_ = crate::leanh::lean_apply_4(
            v_h__2_126_,
            v_head_128_,
            v_tail_129_,
            v_x_124_,
            crate::leanh::lean_box(0),
        );
        return v___x_130_;
    }
}
pub unsafe fn l___private_Init_Data_Array_MapIdx_0__List_mapFinIdx_go_match__1_splitter(
    mut v_00_u03b1_131_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_132_: *mut crate::leanh::LeanObject,
    mut v_as_133_: *mut crate::leanh::LeanObject,
    mut v_motive_134_: *mut crate::leanh::LeanObject,
    mut v_x_135_: *mut crate::leanh::LeanObject,
    mut v_x_136_: *mut crate::leanh::LeanObject,
    mut v_x_137_: *mut crate::leanh::LeanObject,
    mut v_h__1_138_: *mut crate::leanh::LeanObject,
    mut v_h__2_139_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_135_) == 0 {
        let mut v___x_140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_139_);
        v___x_140_ = crate::leanh::lean_apply_2(v_h__1_138_, v_x_136_, crate::leanh::lean_box(0));
        return v___x_140_;
    } else {
        let mut v_head_141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_138_);
        v_head_141_ = crate::leanh::lean_ctor_get(v_x_135_, 0);
        crate::leanh::lean_inc(v_head_141_);
        v_tail_142_ = crate::leanh::lean_ctor_get(v_x_135_, 1);
        crate::leanh::lean_inc(v_tail_142_);
        crate::leanh::lean_dec_ref_known(v_x_135_, 2);
        v___x_143_ = crate::leanh::lean_apply_4(
            v_h__2_139_,
            v_head_141_,
            v_tail_142_,
            v_x_136_,
            crate::leanh::lean_box(0),
        );
        return v___x_143_;
    }
}
pub unsafe fn l___private_Init_Data_Array_MapIdx_0__List_mapFinIdx_go_match__1_splitter___boxed(
    mut v_00_u03b1_144_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_145_: *mut crate::leanh::LeanObject,
    mut v_as_146_: *mut crate::leanh::LeanObject,
    mut v_motive_147_: *mut crate::leanh::LeanObject,
    mut v_x_148_: *mut crate::leanh::LeanObject,
    mut v_x_149_: *mut crate::leanh::LeanObject,
    mut v_x_150_: *mut crate::leanh::LeanObject,
    mut v_h__1_151_: *mut crate::leanh::LeanObject,
    mut v_h__2_152_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_153_ = l___private_Init_Data_Array_MapIdx_0__List_mapFinIdx_go_match__1_splitter(
        v_00_u03b1_144_,
        v_00_u03b2_145_,
        v_as_146_,
        v_motive_147_,
        v_x_148_,
        v_x_149_,
        v_x_150_,
        v_h__1_151_,
        v_h__2_152_,
    );
    crate::leanh::lean_dec(v_as_146_);
    return v_res_153_;
}
pub unsafe fn l___private_Init_Data_Array_MapIdx_0__List_mapIdx_go_match__1_splitter___redArg(
    mut v_x_154_: *mut crate::leanh::LeanObject,
    mut v_x_155_: *mut crate::leanh::LeanObject,
    mut v_h__1_156_: *mut crate::leanh::LeanObject,
    mut v_h__2_157_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_154_) == 0 {
        let mut v___x_158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_157_);
        v___x_158_ = crate::leanh::lean_apply_1(v_h__1_156_, v_x_155_);
        return v___x_158_;
    } else {
        let mut v_head_159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_156_);
        v_head_159_ = crate::leanh::lean_ctor_get(v_x_154_, 0);
        crate::leanh::lean_inc(v_head_159_);
        v_tail_160_ = crate::leanh::lean_ctor_get(v_x_154_, 1);
        crate::leanh::lean_inc(v_tail_160_);
        crate::leanh::lean_dec_ref_known(v_x_154_, 2);
        v___x_161_ = crate::leanh::lean_apply_3(v_h__2_157_, v_head_159_, v_tail_160_, v_x_155_);
        return v___x_161_;
    }
}
pub unsafe fn l___private_Init_Data_Array_MapIdx_0__List_mapIdx_go_match__1_splitter(
    mut v_00_u03b1_162_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_163_: *mut crate::leanh::LeanObject,
    mut v_motive_164_: *mut crate::leanh::LeanObject,
    mut v_x_165_: *mut crate::leanh::LeanObject,
    mut v_x_166_: *mut crate::leanh::LeanObject,
    mut v_h__1_167_: *mut crate::leanh::LeanObject,
    mut v_h__2_168_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_165_) == 0 {
        let mut v___x_169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_168_);
        v___x_169_ = crate::leanh::lean_apply_1(v_h__1_167_, v_x_166_);
        return v___x_169_;
    } else {
        let mut v_head_170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_167_);
        v_head_170_ = crate::leanh::lean_ctor_get(v_x_165_, 0);
        crate::leanh::lean_inc(v_head_170_);
        v_tail_171_ = crate::leanh::lean_ctor_get(v_x_165_, 1);
        crate::leanh::lean_inc(v_tail_171_);
        crate::leanh::lean_dec_ref_known(v_x_165_, 2);
        v___x_172_ = crate::leanh::lean_apply_3(v_h__2_168_, v_head_170_, v_tail_171_, v_x_166_);
        return v___x_172_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Array_MapIdx(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Array_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_MapIdx(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_MapIdx(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_OfFn(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Array_MapIdx(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Array_MapIdx(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Array_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_MapIdx(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_MapIdx(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_OfFn(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_MapIdx(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Array_MapIdx(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_Array_MapIdx(builtin);
}
