// Lean compiler output
// Module: Init.Data.String.Lemmas.Iterate
// Imports: Init.Data.String.Iterate Init.Data.Iterators.Consumers.Collect Init.Data.String.Lemmas.Splits Init.Data.String.Iterate Init.Data.String.Termination Init.Data.Iterators.Lemmas.Consumers.Collect Init.ByCases Init.Data.Iterators.Lemmas.Combinators.FilterMap Init.Data.String.Lemmas.Basic Init.Data.Iterators.Lemmas.Consumers.Loop Init.Data.String.Lemmas.Order Init.Data.String.OrderInstances Init.Data.Subtype.Basic
use crate::ffi::{
    lean_nat_add, lean_nat_dec_eq, lean_nat_sub, lean_string_utf8_byte_size,
    lean_string_utf8_next_fast,
};
use crate::r#gen::Init::ByCases::{initialize_Init_ByCases, runtime_initialize_Init_ByCases};
use crate::r#gen::Init::Data::Iterators::Consumers::Collect::{
    initialize_Init_Data_Iterators_Consumers_Collect,
    runtime_initialize_Init_Data_Iterators_Consumers_Collect,
};
use crate::r#gen::Init::Data::Iterators::Lemmas::Combinators::FilterMap::{
    initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap,
    runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap,
};
use crate::r#gen::Init::Data::Iterators::Lemmas::Consumers::Collect::{
    initialize_Init_Data_Iterators_Lemmas_Consumers_Collect,
    runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Collect,
};
use crate::r#gen::Init::Data::Iterators::Lemmas::Consumers::Loop::{
    initialize_Init_Data_Iterators_Lemmas_Consumers_Loop,
    runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Loop,
};
use crate::r#gen::Init::Data::String::FindPos::l_String_Slice_posLE;
use crate::r#gen::Init::Data::String::Iterate::{
    initialize_Init_Data_String_Iterate, runtime_initialize_Init_Data_String_Iterate,
};
use crate::r#gen::Init::Data::String::Lemmas::Basic::{
    initialize_Init_Data_String_Lemmas_Basic, runtime_initialize_Init_Data_String_Lemmas_Basic,
};
use crate::r#gen::Init::Data::String::Lemmas::Order::{
    initialize_Init_Data_String_Lemmas_Order, runtime_initialize_Init_Data_String_Lemmas_Order,
};
use crate::r#gen::Init::Data::String::Lemmas::Splits::{
    initialize_Init_Data_String_Lemmas_Splits, runtime_initialize_Init_Data_String_Lemmas_Splits,
};
use crate::r#gen::Init::Data::String::OrderInstances::{
    initialize_Init_Data_String_OrderInstances, runtime_initialize_Init_Data_String_OrderInstances,
};
use crate::r#gen::Init::Data::String::Termination::{
    initialize_Init_Data_String_Termination, runtime_initialize_Init_Data_String_Termination,
};
use crate::r#gen::Init::Data::Subtype::Basic::{
    initialize_Init_Data_Subtype_Basic, runtime_initialize_Init_Data_Subtype_Basic,
};
pub unsafe fn l_String_Slice_Model_positionsFrom(
    mut v_s_94_: *mut leanh::LeanObject,
    mut v_p_95_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_str_96_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_97_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_98_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_99_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_100_: u8 = 0;
    v_str_96_ = leanh::lean_ctor_get(v_s_94_, 0);
    v_startInclusive_97_ = leanh::lean_ctor_get(v_s_94_, 1);
    v_endExclusive_98_ = leanh::lean_ctor_get(v_s_94_, 2);
    v___x_99_ = lean_nat_sub(v_endExclusive_98_, v_startInclusive_97_);
    v___x_100_ = lean_nat_dec_eq(v_p_95_, v___x_99_);
    leanh::lean_dec(v___x_99_);
    if v___x_100_ == 0 {
        let mut v___x_101_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_102_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_103_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_104_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_105_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_101_ = lean_nat_add(v_startInclusive_97_, v_p_95_);
        v___x_102_ = lean_string_utf8_next_fast(v_str_96_, v___x_101_);
        leanh::lean_dec(v___x_101_);
        v___x_103_ = lean_nat_sub(v___x_102_, v_startInclusive_97_);
        v___x_104_ = l_String_Slice_Model_positionsFrom(v_s_94_, v___x_103_);
        v___x_105_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_105_, 0, v_p_95_);
        leanh::lean_ctor_set(v___x_105_, 1, v___x_104_);
        return v___x_105_;
    } else {
        let mut v___x_106_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_p_95_);
        v___x_106_ = leanh::lean_box(0);
        return v___x_106_;
    }
}
pub unsafe fn l_String_Slice_Model_positionsFrom___boxed(
    mut v_s_107_: *mut leanh::LeanObject,
    mut v_p_108_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_109_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_109_ = l_String_Slice_Model_positionsFrom(v_s_107_, v_p_108_);
    leanh::lean_dec_ref(v_s_107_);
    return v_res_109_;
}
pub unsafe fn l___private_Init_Data_String_Lemmas_Iterate_0__Std_Iter_toArray__eq__match__step_match__1_splitter___redArg(
    mut v_x_110_: *mut leanh::LeanObject,
    mut v_h__1_111_: *mut leanh::LeanObject,
    mut v_h__2_112_: *mut leanh::LeanObject,
    mut v_h__3_113_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_110_) {
        0 => {
            let mut v_it_114_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_115_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_116_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_113_);
            leanh::lean_dec(v_h__2_112_);
            v_it_114_ = leanh::lean_ctor_get(v_x_110_, 0);
            leanh::lean_inc(v_it_114_);
            v_out_115_ = leanh::lean_ctor_get(v_x_110_, 1);
            leanh::lean_inc(v_out_115_);
            leanh::lean_dec_ref_known(v_x_110_, 2);
            v___x_116_ = leanh::lean_apply_2(v_h__1_111_, v_it_114_, v_out_115_);
            return v___x_116_;
        }
        1 => {
            let mut v_it_117_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_118_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_113_);
            leanh::lean_dec(v_h__1_111_);
            v_it_117_ = leanh::lean_ctor_get(v_x_110_, 0);
            leanh::lean_inc(v_it_117_);
            leanh::lean_dec_ref_known(v_x_110_, 1);
            v___x_118_ = leanh::lean_apply_1(v_h__2_112_, v_it_117_);
            return v___x_118_;
        }
        _ => {
            let mut v___x_119_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_120_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_112_);
            leanh::lean_dec(v_h__1_111_);
            v___x_119_ = leanh::lean_box(0);
            v___x_120_ = leanh::lean_apply_1(v_h__3_113_, v___x_119_);
            return v___x_120_;
        }
    }
}
pub unsafe fn l___private_Init_Data_String_Lemmas_Iterate_0__Std_Iter_toArray__eq__match__step_match__1_splitter(
    mut v_00_u03b1_121_: *mut leanh::LeanObject,
    mut v_00_u03b2_122_: *mut leanh::LeanObject,
    mut v_motive_123_: *mut leanh::LeanObject,
    mut v_x_124_: *mut leanh::LeanObject,
    mut v_h__1_125_: *mut leanh::LeanObject,
    mut v_h__2_126_: *mut leanh::LeanObject,
    mut v_h__3_127_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_124_) {
        0 => {
            let mut v_it_128_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_129_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_130_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_127_);
            leanh::lean_dec(v_h__2_126_);
            v_it_128_ = leanh::lean_ctor_get(v_x_124_, 0);
            leanh::lean_inc(v_it_128_);
            v_out_129_ = leanh::lean_ctor_get(v_x_124_, 1);
            leanh::lean_inc(v_out_129_);
            leanh::lean_dec_ref_known(v_x_124_, 2);
            v___x_130_ = leanh::lean_apply_2(v_h__1_125_, v_it_128_, v_out_129_);
            return v___x_130_;
        }
        1 => {
            let mut v_it_131_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_132_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_127_);
            leanh::lean_dec(v_h__1_125_);
            v_it_131_ = leanh::lean_ctor_get(v_x_124_, 0);
            leanh::lean_inc(v_it_131_);
            leanh::lean_dec_ref_known(v_x_124_, 1);
            v___x_132_ = leanh::lean_apply_1(v_h__2_126_, v_it_131_);
            return v___x_132_;
        }
        _ => {
            let mut v___x_133_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_134_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_126_);
            leanh::lean_dec(v_h__1_125_);
            v___x_133_ = leanh::lean_box(0);
            v___x_134_ = leanh::lean_apply_1(v_h__3_127_, v___x_133_);
            return v___x_134_;
        }
    }
}
pub unsafe fn l_String_Slice_Model_revPositionsFrom(
    mut v_s_135_: *mut leanh::LeanObject,
    mut v_p_136_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_138_: u8 = 0;
    v___x_137_ = leanh::lean_unsigned_to_nat(0);
    v___x_138_ = lean_nat_dec_eq(v_p_136_, v___x_137_);
    if v___x_138_ == 0 {
        let mut v___x_139_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_140_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_141_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_142_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_143_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_139_ = leanh::lean_unsigned_to_nat(1);
        v___x_140_ = lean_nat_sub(v_p_136_, v___x_139_);
        v___x_141_ = l_String_Slice_posLE(v_s_135_, v___x_140_);
        v___x_142_ = l_String_Slice_Model_revPositionsFrom(v_s_135_, v___x_141_);
        v___x_143_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_143_, 0, v___x_141_);
        leanh::lean_ctor_set(v___x_143_, 1, v___x_142_);
        return v___x_143_;
    } else {
        let mut v___x_144_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_144_ = leanh::lean_box(0);
        return v___x_144_;
    }
}
pub unsafe fn l_String_Slice_Model_revPositionsFrom___boxed(
    mut v_s_145_: *mut leanh::LeanObject,
    mut v_p_146_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_147_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_147_ = l_String_Slice_Model_revPositionsFrom(v_s_145_, v_p_146_);
    leanh::lean_dec(v_p_146_);
    leanh::lean_dec_ref(v_s_145_);
    return v_res_147_;
}
pub unsafe fn l_String_Model_positionsFrom(
    mut v_s_148_: *mut leanh::LeanObject,
    mut v_p_149_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_151_: u8 = 0;
    v___x_150_ = lean_string_utf8_byte_size(v_s_148_);
    v___x_151_ = lean_nat_dec_eq(v_p_149_, v___x_150_);
    if v___x_151_ == 0 {
        let mut v___x_152_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_153_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_154_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_152_ = lean_string_utf8_next_fast(v_s_148_, v_p_149_);
        v___x_153_ = l_String_Model_positionsFrom(v_s_148_, v___x_152_);
        v___x_154_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_154_, 0, v_p_149_);
        leanh::lean_ctor_set(v___x_154_, 1, v___x_153_);
        return v___x_154_;
    } else {
        let mut v___x_155_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_p_149_);
        v___x_155_ = leanh::lean_box(0);
        return v___x_155_;
    }
}
pub unsafe fn l_String_Model_positionsFrom___boxed(
    mut v_s_156_: *mut leanh::LeanObject,
    mut v_p_157_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_158_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_158_ = l_String_Model_positionsFrom(v_s_156_, v_p_157_);
    leanh::lean_dec_ref(v_s_156_);
    return v_res_158_;
}
pub unsafe fn l___private_Init_Data_String_Lemmas_Iterate_0__String_Internal_ofToSliceWithProof_match__1_splitter___redArg(
    mut v_x_159_: *mut leanh::LeanObject,
    mut v_h__1_160_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_161_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_161_ = leanh::lean_apply_2(v_h__1_160_, v_x_159_, leanh::lean_box(0));
    return v___x_161_;
}
pub unsafe fn l___private_Init_Data_String_Lemmas_Iterate_0__String_Internal_ofToSliceWithProof_match__1_splitter(
    mut v_s_162_: *mut leanh::LeanObject,
    mut v_motive_163_: *mut leanh::LeanObject,
    mut v_x_164_: *mut leanh::LeanObject,
    mut v_h__1_165_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_166_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_166_ = leanh::lean_apply_2(v_h__1_165_, v_x_164_, leanh::lean_box(0));
    return v___x_166_;
}
pub unsafe fn l___private_Init_Data_String_Lemmas_Iterate_0__String_Internal_ofToSliceWithProof_match__1_splitter___boxed(
    mut v_s_167_: *mut leanh::LeanObject,
    mut v_motive_168_: *mut leanh::LeanObject,
    mut v_x_169_: *mut leanh::LeanObject,
    mut v_h__1_170_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_171_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_171_ = l___private_Init_Data_String_Lemmas_Iterate_0__String_Internal_ofToSliceWithProof_match__1_splitter(v_s_167_, v_motive_168_, v_x_169_, v_h__1_170_);
    leanh::lean_dec_ref(v_s_167_);
    return v_res_171_;
}
pub unsafe fn l_String_Model_revPositionsFrom(
    mut v_s_172_: *mut leanh::LeanObject,
    mut v_p_173_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_175_: u8 = 0;
    v___x_174_ = leanh::lean_unsigned_to_nat(0);
    v___x_175_ = lean_nat_dec_eq(v_p_173_, v___x_174_);
    if v___x_175_ == 0 {
        let mut v___x_176_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_177_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_178_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_179_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_180_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_181_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_182_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_176_ = lean_string_utf8_byte_size(v_s_172_);
        leanh::lean_inc_ref(v_s_172_);
        v___x_177_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
        leanh::lean_ctor_set(v___x_177_, 0, v_s_172_);
        leanh::lean_ctor_set(v___x_177_, 1, v___x_174_);
        leanh::lean_ctor_set(v___x_177_, 2, v___x_176_);
        v___x_178_ = leanh::lean_unsigned_to_nat(1);
        v___x_179_ = lean_nat_sub(v_p_173_, v___x_178_);
        v___x_180_ = l_String_Slice_posLE(v___x_177_, v___x_179_);
        leanh::lean_dec_ref_known(v___x_177_, 3);
        v___x_181_ = l_String_Model_revPositionsFrom(v_s_172_, v___x_180_);
        v___x_182_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_182_, 0, v___x_180_);
        leanh::lean_ctor_set(v___x_182_, 1, v___x_181_);
        return v___x_182_;
    } else {
        let mut v___x_183_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_s_172_);
        v___x_183_ = leanh::lean_box(0);
        return v___x_183_;
    }
}
pub unsafe fn l_String_Model_revPositionsFrom___boxed(
    mut v_s_184_: *mut leanh::LeanObject,
    mut v_p_185_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_186_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_186_ = l_String_Model_revPositionsFrom(v_s_184_, v_p_185_);
    leanh::lean_dec(v_p_185_);
    return v_res_186_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_String_Lemmas_Iterate(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_String_Iterate(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Collect(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_Splits(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Iterate(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Termination(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_ByCases(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_Basic(builtin);
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
    res = runtime_initialize_Init_Data_String_OrderInstances(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Subtype_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_String_Lemmas_Iterate(
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
pub unsafe fn initialize_Init_Data_String_Lemmas_Iterate(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_String_Iterate(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers_Collect(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Lemmas_Splits(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Iterate(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Termination(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_ByCases(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Lemmas_Basic(builtin);
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
    res = initialize_Init_Data_String_OrderInstances(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Subtype_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_Iterate(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_String_Lemmas_Iterate(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_String_Lemmas_Iterate(builtin);
}