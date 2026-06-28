// Lean compiler output
// Module: Init.Data.String.Lemmas.Iterate
// Imports: Init.Data.String.Iterate Init.Data.Iterators.Consumers.Collect Init.Data.String.Lemmas.Splits Init.Data.String.Iterate Init.Data.String.Termination Init.Data.Iterators.Lemmas.Consumers.Collect Init.ByCases Init.Data.Iterators.Lemmas.Combinators.FilterMap Init.Data.String.Lemmas.Basic Init.Data.Iterators.Lemmas.Consumers.Loop Init.Data.String.Lemmas.Order Init.Data.String.OrderInstances Init.Data.Subtype.Basic
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
use crate::lean_imports_rs::Init::Data::String::Basic::lean_string_utf8_next_fast;
use crate::lean_imports_rs::Init::Prelude::{
    lean_nat_add, lean_nat_dec_eq, lean_nat_sub, lean_string_utf8_byte_size,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_apply_1, lean_apply_2, lean_box,
    lean_ctor_get, lean_ctor_set, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc,
    lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok, lean_obj_tag,
    lean_unsigned_to_nat,
};
pub unsafe fn l_String_Slice_Model_positionsFrom(
    mut v_s_94_: *mut LeanObject,
    mut v_p_95_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_str_96_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_97_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_98_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_99_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_100_: u8 = 0;
    v_str_96_ = lean_ctor_get(v_s_94_, 0);
    v_startInclusive_97_ = lean_ctor_get(v_s_94_, 1);
    v_endExclusive_98_ = lean_ctor_get(v_s_94_, 2);
    v___x_99_ = lean_nat_sub(v_endExclusive_98_, v_startInclusive_97_);
    v___x_100_ = lean_nat_dec_eq(v_p_95_, v___x_99_);
    lean_dec(v___x_99_);
    if v___x_100_ == 0 {
        let mut v___x_101_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_102_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_103_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_104_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_105_: *mut LeanObject = core::ptr::null_mut();
        v___x_101_ = lean_nat_add(v_startInclusive_97_, v_p_95_);
        v___x_102_ = lean_string_utf8_next_fast(v_str_96_, v___x_101_);
        lean_dec(v___x_101_);
        v___x_103_ = lean_nat_sub(v___x_102_, v_startInclusive_97_);
        v___x_104_ = l_String_Slice_Model_positionsFrom(v_s_94_, v___x_103_);
        v___x_105_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_105_, 0, v_p_95_);
        lean_ctor_set(v___x_105_, 1, v___x_104_);
        return v___x_105_;
    } else {
        let mut v___x_106_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_p_95_);
        v___x_106_ = lean_box(0);
        return v___x_106_;
    }
}
pub unsafe fn l_String_Slice_Model_positionsFrom___boxed(
    mut v_s_107_: *mut LeanObject,
    mut v_p_108_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_109_: *mut LeanObject = core::ptr::null_mut();
    v_res_109_ = l_String_Slice_Model_positionsFrom(v_s_107_, v_p_108_);
    lean_dec_ref(v_s_107_);
    return v_res_109_;
}
pub unsafe fn l___private_Init_Data_String_Lemmas_Iterate_0__Std_Iter_toArray__eq__match__step_match__1_splitter___redArg(
    mut v_x_110_: *mut LeanObject,
    mut v_h__1_111_: *mut LeanObject,
    mut v_h__2_112_: *mut LeanObject,
    mut v_h__3_113_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_110_) {
        0 => {
            let mut v_it_114_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_115_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_116_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_113_);
            lean_dec(v_h__2_112_);
            v_it_114_ = lean_ctor_get(v_x_110_, 0);
            lean_inc(v_it_114_);
            v_out_115_ = lean_ctor_get(v_x_110_, 1);
            lean_inc(v_out_115_);
            lean_dec_ref_known(v_x_110_, 2);
            v___x_116_ = lean_apply_2(v_h__1_111_, v_it_114_, v_out_115_);
            return v___x_116_;
        }
        1 => {
            let mut v_it_117_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_118_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_113_);
            lean_dec(v_h__1_111_);
            v_it_117_ = lean_ctor_get(v_x_110_, 0);
            lean_inc(v_it_117_);
            lean_dec_ref_known(v_x_110_, 1);
            v___x_118_ = lean_apply_1(v_h__2_112_, v_it_117_);
            return v___x_118_;
        }
        _ => {
            let mut v___x_119_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_120_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_112_);
            lean_dec(v_h__1_111_);
            v___x_119_ = lean_box(0);
            v___x_120_ = lean_apply_1(v_h__3_113_, v___x_119_);
            return v___x_120_;
        }
    }
}
pub unsafe fn l___private_Init_Data_String_Lemmas_Iterate_0__Std_Iter_toArray__eq__match__step_match__1_splitter(
    mut v_00_u03b1_121_: *mut LeanObject,
    mut v_00_u03b2_122_: *mut LeanObject,
    mut v_motive_123_: *mut LeanObject,
    mut v_x_124_: *mut LeanObject,
    mut v_h__1_125_: *mut LeanObject,
    mut v_h__2_126_: *mut LeanObject,
    mut v_h__3_127_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_124_) {
        0 => {
            let mut v_it_128_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_129_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_130_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_127_);
            lean_dec(v_h__2_126_);
            v_it_128_ = lean_ctor_get(v_x_124_, 0);
            lean_inc(v_it_128_);
            v_out_129_ = lean_ctor_get(v_x_124_, 1);
            lean_inc(v_out_129_);
            lean_dec_ref_known(v_x_124_, 2);
            v___x_130_ = lean_apply_2(v_h__1_125_, v_it_128_, v_out_129_);
            return v___x_130_;
        }
        1 => {
            let mut v_it_131_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_132_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_127_);
            lean_dec(v_h__1_125_);
            v_it_131_ = lean_ctor_get(v_x_124_, 0);
            lean_inc(v_it_131_);
            lean_dec_ref_known(v_x_124_, 1);
            v___x_132_ = lean_apply_1(v_h__2_126_, v_it_131_);
            return v___x_132_;
        }
        _ => {
            let mut v___x_133_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_134_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_126_);
            lean_dec(v_h__1_125_);
            v___x_133_ = lean_box(0);
            v___x_134_ = lean_apply_1(v_h__3_127_, v___x_133_);
            return v___x_134_;
        }
    }
}
pub unsafe fn l_String_Slice_Model_revPositionsFrom(
    mut v_s_135_: *mut LeanObject,
    mut v_p_136_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_138_: u8 = 0;
    v___x_137_ = lean_unsigned_to_nat(0);
    v___x_138_ = lean_nat_dec_eq(v_p_136_, v___x_137_);
    if v___x_138_ == 0 {
        let mut v___x_139_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_140_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_141_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_142_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_143_: *mut LeanObject = core::ptr::null_mut();
        v___x_139_ = lean_unsigned_to_nat(1);
        v___x_140_ = lean_nat_sub(v_p_136_, v___x_139_);
        v___x_141_ = l_String_Slice_posLE(v_s_135_, v___x_140_);
        v___x_142_ = l_String_Slice_Model_revPositionsFrom(v_s_135_, v___x_141_);
        v___x_143_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_143_, 0, v___x_141_);
        lean_ctor_set(v___x_143_, 1, v___x_142_);
        return v___x_143_;
    } else {
        let mut v___x_144_: *mut LeanObject = core::ptr::null_mut();
        v___x_144_ = lean_box(0);
        return v___x_144_;
    }
}
pub unsafe fn l_String_Slice_Model_revPositionsFrom___boxed(
    mut v_s_145_: *mut LeanObject,
    mut v_p_146_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_147_: *mut LeanObject = core::ptr::null_mut();
    v_res_147_ = l_String_Slice_Model_revPositionsFrom(v_s_145_, v_p_146_);
    lean_dec(v_p_146_);
    lean_dec_ref(v_s_145_);
    return v_res_147_;
}
pub unsafe fn l_String_Model_positionsFrom(
    mut v_s_148_: *mut LeanObject,
    mut v_p_149_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_151_: u8 = 0;
    v___x_150_ = lean_string_utf8_byte_size(v_s_148_);
    v___x_151_ = lean_nat_dec_eq(v_p_149_, v___x_150_);
    if v___x_151_ == 0 {
        let mut v___x_152_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_153_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_154_: *mut LeanObject = core::ptr::null_mut();
        v___x_152_ = lean_string_utf8_next_fast(v_s_148_, v_p_149_);
        v___x_153_ = l_String_Model_positionsFrom(v_s_148_, v___x_152_);
        v___x_154_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_154_, 0, v_p_149_);
        lean_ctor_set(v___x_154_, 1, v___x_153_);
        return v___x_154_;
    } else {
        let mut v___x_155_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_p_149_);
        v___x_155_ = lean_box(0);
        return v___x_155_;
    }
}
pub unsafe fn l_String_Model_positionsFrom___boxed(
    mut v_s_156_: *mut LeanObject,
    mut v_p_157_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_158_: *mut LeanObject = core::ptr::null_mut();
    v_res_158_ = l_String_Model_positionsFrom(v_s_156_, v_p_157_);
    lean_dec_ref(v_s_156_);
    return v_res_158_;
}
pub unsafe fn l___private_Init_Data_String_Lemmas_Iterate_0__String_Internal_ofToSliceWithProof_match__1_splitter___redArg(
    mut v_x_159_: *mut LeanObject,
    mut v_h__1_160_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_161_: *mut LeanObject = core::ptr::null_mut();
    v___x_161_ = lean_apply_2(v_h__1_160_, v_x_159_, lean_box(0));
    return v___x_161_;
}
pub unsafe fn l___private_Init_Data_String_Lemmas_Iterate_0__String_Internal_ofToSliceWithProof_match__1_splitter(
    mut v_s_162_: *mut LeanObject,
    mut v_motive_163_: *mut LeanObject,
    mut v_x_164_: *mut LeanObject,
    mut v_h__1_165_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_166_: *mut LeanObject = core::ptr::null_mut();
    v___x_166_ = lean_apply_2(v_h__1_165_, v_x_164_, lean_box(0));
    return v___x_166_;
}
pub unsafe fn l___private_Init_Data_String_Lemmas_Iterate_0__String_Internal_ofToSliceWithProof_match__1_splitter___boxed(
    mut v_s_167_: *mut LeanObject,
    mut v_motive_168_: *mut LeanObject,
    mut v_x_169_: *mut LeanObject,
    mut v_h__1_170_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_171_: *mut LeanObject = core::ptr::null_mut();
    v_res_171_ = l___private_Init_Data_String_Lemmas_Iterate_0__String_Internal_ofToSliceWithProof_match__1_splitter(v_s_167_, v_motive_168_, v_x_169_, v_h__1_170_);
    lean_dec_ref(v_s_167_);
    return v_res_171_;
}
pub unsafe fn l_String_Model_revPositionsFrom(
    mut v_s_172_: *mut LeanObject,
    mut v_p_173_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_175_: u8 = 0;
    v___x_174_ = lean_unsigned_to_nat(0);
    v___x_175_ = lean_nat_dec_eq(v_p_173_, v___x_174_);
    if v___x_175_ == 0 {
        let mut v___x_176_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_177_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_178_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_179_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_180_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_181_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_182_: *mut LeanObject = core::ptr::null_mut();
        v___x_176_ = lean_string_utf8_byte_size(v_s_172_);
        lean_inc_ref(v_s_172_);
        v___x_177_ = lean_alloc_ctor(0, 3, (0) as u32);
        lean_ctor_set(v___x_177_, 0, v_s_172_);
        lean_ctor_set(v___x_177_, 1, v___x_174_);
        lean_ctor_set(v___x_177_, 2, v___x_176_);
        v___x_178_ = lean_unsigned_to_nat(1);
        v___x_179_ = lean_nat_sub(v_p_173_, v___x_178_);
        v___x_180_ = l_String_Slice_posLE(v___x_177_, v___x_179_);
        lean_dec_ref_known(v___x_177_, 3);
        v___x_181_ = l_String_Model_revPositionsFrom(v_s_172_, v___x_180_);
        v___x_182_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_182_, 0, v___x_180_);
        lean_ctor_set(v___x_182_, 1, v___x_181_);
        return v___x_182_;
    } else {
        let mut v___x_183_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_s_172_);
        v___x_183_ = lean_box(0);
        return v___x_183_;
    }
}
pub unsafe fn l_String_Model_revPositionsFrom___boxed(
    mut v_s_184_: *mut LeanObject,
    mut v_p_185_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_186_: *mut LeanObject = core::ptr::null_mut();
    v_res_186_ = l_String_Model_revPositionsFrom(v_s_184_, v_p_185_);
    lean_dec(v_p_185_);
    return v_res_186_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_String_Lemmas_Iterate(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_String_Iterate(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Collect(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_Splits(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Termination(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_ByCases(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Loop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_Order(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_OrderInstances(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Subtype_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_String_Lemmas_Iterate(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_String_Lemmas_Iterate(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_String_Iterate(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers_Collect(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_String_Lemmas_Splits(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_String_Termination(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_ByCases(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_String_Lemmas_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Consumers_Loop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_String_Lemmas_Order(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_String_OrderInstances(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Subtype_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_Iterate(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_String_Lemmas_Iterate(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_String_Lemmas_Iterate(builtin);
}
