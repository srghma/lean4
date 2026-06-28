// Lean compiler output
// Module: Init.Data.Array.MapIdx
// Imports: Init.Data.Array.Basic Init.Data.List.MapIdx Init.Data.List.MapIdx Init.Data.Array.OfFn
use crate::r#gen::Init::Data::Array::Basic::{
    initialize_Init_Data_Array_Basic, runtime_initialize_Init_Data_Array_Basic,
};
use crate::r#gen::Init::Data::Array::OfFn::{
    initialize_Init_Data_Array_OfFn, runtime_initialize_Init_Data_Array_OfFn,
};
use crate::r#gen::Init::Data::List::MapIdx::{
    initialize_Init_Data_List_MapIdx, runtime_initialize_Init_Data_List_MapIdx,
};
use crate::lean_imports_rs::Init::Prelude::{lean_nat_dec_eq, lean_nat_sub};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_apply_1, lean_apply_2, lean_apply_3, lean_apply_4,
    lean_box, lean_ctor_get, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_obj_tag, lean_unsigned_to_nat,
};
pub unsafe fn l___private_Init_Data_Array_MapIdx_0__Array_mapFinIdxM_map_match__1_splitter___redArg(
    mut v_i_87_: *mut LeanObject,
    mut v_h__1_88_: *mut LeanObject,
    mut v_h__2_89_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_90_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_91_: u8 = 0;
    v_zero_90_ = lean_unsigned_to_nat(0);
    v_isZero_91_ = lean_nat_dec_eq(v_i_87_, v_zero_90_);
    if v_isZero_91_ == 1 {
        let mut v___x_92_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_89_);
        v___x_92_ = lean_apply_1(v_h__1_88_, lean_box(0));
        return v___x_92_;
    } else {
        let mut v_one_93_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_94_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_95_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_88_);
        v_one_93_ = lean_unsigned_to_nat(1);
        v_n_94_ = lean_nat_sub(v_i_87_, v_one_93_);
        v___x_95_ = lean_apply_2(v_h__2_89_, v_n_94_, lean_box(0));
        return v___x_95_;
    }
}
pub unsafe fn l___private_Init_Data_Array_MapIdx_0__Array_mapFinIdxM_map_match__1_splitter___redArg___boxed(
    mut v_i_96_: *mut LeanObject,
    mut v_h__1_97_: *mut LeanObject,
    mut v_h__2_98_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_99_: *mut LeanObject = core::ptr::null_mut();
    v_res_99_ =
        l___private_Init_Data_Array_MapIdx_0__Array_mapFinIdxM_map_match__1_splitter___redArg(
            v_i_96_, v_h__1_97_, v_h__2_98_,
        );
    lean_dec(v_i_96_);
    return v_res_99_;
}
pub unsafe fn l___private_Init_Data_Array_MapIdx_0__Array_mapFinIdxM_map_match__1_splitter(
    mut v_00_u03b1_100_: *mut LeanObject,
    mut v_as_101_: *mut LeanObject,
    mut v_j_102_: *mut LeanObject,
    mut v_motive_103_: *mut LeanObject,
    mut v_i_104_: *mut LeanObject,
    mut v_inv_105_: *mut LeanObject,
    mut v_h__1_106_: *mut LeanObject,
    mut v_h__2_107_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_108_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_109_: u8 = 0;
    v_zero_108_ = lean_unsigned_to_nat(0);
    v_isZero_109_ = lean_nat_dec_eq(v_i_104_, v_zero_108_);
    if v_isZero_109_ == 1 {
        let mut v___x_110_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_107_);
        v___x_110_ = lean_apply_1(v_h__1_106_, lean_box(0));
        return v___x_110_;
    } else {
        let mut v_one_111_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_112_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_113_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_106_);
        v_one_111_ = lean_unsigned_to_nat(1);
        v_n_112_ = lean_nat_sub(v_i_104_, v_one_111_);
        v___x_113_ = lean_apply_2(v_h__2_107_, v_n_112_, lean_box(0));
        return v___x_113_;
    }
}
pub unsafe fn l___private_Init_Data_Array_MapIdx_0__Array_mapFinIdxM_map_match__1_splitter___boxed(
    mut v_00_u03b1_114_: *mut LeanObject,
    mut v_as_115_: *mut LeanObject,
    mut v_j_116_: *mut LeanObject,
    mut v_motive_117_: *mut LeanObject,
    mut v_i_118_: *mut LeanObject,
    mut v_inv_119_: *mut LeanObject,
    mut v_h__1_120_: *mut LeanObject,
    mut v_h__2_121_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_122_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_i_118_);
    lean_dec(v_j_116_);
    lean_dec_ref(v_as_115_);
    return v_res_122_;
}
pub unsafe fn l___private_Init_Data_Array_MapIdx_0__List_mapFinIdx_go_match__1_splitter___redArg(
    mut v_x_123_: *mut LeanObject,
    mut v_x_124_: *mut LeanObject,
    mut v_h__1_125_: *mut LeanObject,
    mut v_h__2_126_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_123_) == 0 {
        let mut v___x_127_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_126_);
        v___x_127_ = lean_apply_2(v_h__1_125_, v_x_124_, lean_box(0));
        return v___x_127_;
    } else {
        let mut v_head_128_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_129_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_130_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_125_);
        v_head_128_ = lean_ctor_get(v_x_123_, 0);
        lean_inc(v_head_128_);
        v_tail_129_ = lean_ctor_get(v_x_123_, 1);
        lean_inc(v_tail_129_);
        lean_dec_ref_known(v_x_123_, 2);
        v___x_130_ = lean_apply_4(v_h__2_126_, v_head_128_, v_tail_129_, v_x_124_, lean_box(0));
        return v___x_130_;
    }
}
pub unsafe fn l___private_Init_Data_Array_MapIdx_0__List_mapFinIdx_go_match__1_splitter(
    mut v_00_u03b1_131_: *mut LeanObject,
    mut v_00_u03b2_132_: *mut LeanObject,
    mut v_as_133_: *mut LeanObject,
    mut v_motive_134_: *mut LeanObject,
    mut v_x_135_: *mut LeanObject,
    mut v_x_136_: *mut LeanObject,
    mut v_x_137_: *mut LeanObject,
    mut v_h__1_138_: *mut LeanObject,
    mut v_h__2_139_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_135_) == 0 {
        let mut v___x_140_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_139_);
        v___x_140_ = lean_apply_2(v_h__1_138_, v_x_136_, lean_box(0));
        return v___x_140_;
    } else {
        let mut v_head_141_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_142_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_143_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_138_);
        v_head_141_ = lean_ctor_get(v_x_135_, 0);
        lean_inc(v_head_141_);
        v_tail_142_ = lean_ctor_get(v_x_135_, 1);
        lean_inc(v_tail_142_);
        lean_dec_ref_known(v_x_135_, 2);
        v___x_143_ = lean_apply_4(v_h__2_139_, v_head_141_, v_tail_142_, v_x_136_, lean_box(0));
        return v___x_143_;
    }
}
pub unsafe fn l___private_Init_Data_Array_MapIdx_0__List_mapFinIdx_go_match__1_splitter___boxed(
    mut v_00_u03b1_144_: *mut LeanObject,
    mut v_00_u03b2_145_: *mut LeanObject,
    mut v_as_146_: *mut LeanObject,
    mut v_motive_147_: *mut LeanObject,
    mut v_x_148_: *mut LeanObject,
    mut v_x_149_: *mut LeanObject,
    mut v_x_150_: *mut LeanObject,
    mut v_h__1_151_: *mut LeanObject,
    mut v_h__2_152_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_153_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_as_146_);
    return v_res_153_;
}
pub unsafe fn l___private_Init_Data_Array_MapIdx_0__List_mapIdx_go_match__1_splitter___redArg(
    mut v_x_154_: *mut LeanObject,
    mut v_x_155_: *mut LeanObject,
    mut v_h__1_156_: *mut LeanObject,
    mut v_h__2_157_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_154_) == 0 {
        let mut v___x_158_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_157_);
        v___x_158_ = lean_apply_1(v_h__1_156_, v_x_155_);
        return v___x_158_;
    } else {
        let mut v_head_159_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_160_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_161_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_156_);
        v_head_159_ = lean_ctor_get(v_x_154_, 0);
        lean_inc(v_head_159_);
        v_tail_160_ = lean_ctor_get(v_x_154_, 1);
        lean_inc(v_tail_160_);
        lean_dec_ref_known(v_x_154_, 2);
        v___x_161_ = lean_apply_3(v_h__2_157_, v_head_159_, v_tail_160_, v_x_155_);
        return v___x_161_;
    }
}
pub unsafe fn l___private_Init_Data_Array_MapIdx_0__List_mapIdx_go_match__1_splitter(
    mut v_00_u03b1_162_: *mut LeanObject,
    mut v_00_u03b2_163_: *mut LeanObject,
    mut v_motive_164_: *mut LeanObject,
    mut v_x_165_: *mut LeanObject,
    mut v_x_166_: *mut LeanObject,
    mut v_h__1_167_: *mut LeanObject,
    mut v_h__2_168_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_165_) == 0 {
        let mut v___x_169_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_168_);
        v___x_169_ = lean_apply_1(v_h__1_167_, v_x_166_);
        return v___x_169_;
    } else {
        let mut v_head_170_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_171_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_172_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_167_);
        v_head_170_ = lean_ctor_get(v_x_165_, 0);
        lean_inc(v_head_170_);
        v_tail_171_ = lean_ctor_get(v_x_165_, 1);
        lean_inc(v_tail_171_);
        lean_dec_ref_known(v_x_165_, 2);
        v___x_172_ = lean_apply_3(v_h__2_168_, v_head_170_, v_tail_171_, v_x_166_);
        return v___x_172_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Array_MapIdx(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Array_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_MapIdx(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_OfFn(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Array_MapIdx(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Array_MapIdx(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Array_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_MapIdx(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Array_OfFn(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_MapIdx(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_Array_MapIdx(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_Array_MapIdx(builtin);
}
