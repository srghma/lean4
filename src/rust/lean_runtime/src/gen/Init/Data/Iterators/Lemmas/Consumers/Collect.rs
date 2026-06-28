// Lean compiler output
// Module: Init.Data.Iterators.Lemmas.Consumers.Collect
// Imports: Init.Data.Iterators.Consumers.Access Init.Data.Iterators.Consumers.Access Init.Data.Iterators.Consumers.Collect Init.Data.Iterators.Consumers.Total Init.Data.Iterators.Consumers.Monadic.Total Init.Data.Iterators.Consumers.Collect Init.Data.Array.Bootstrap Init.Data.Array.Lemmas Init.Data.Iterators.Lemmas.Basic Init.Data.Iterators.Lemmas.Consumers.Monadic.Collect Init.Data.Option.Lemmas
use crate::r#gen::Init::Data::Array::Bootstrap::{
    initialize_Init_Data_Array_Bootstrap, runtime_initialize_Init_Data_Array_Bootstrap,
};
use crate::r#gen::Init::Data::Array::Lemmas::{
    initialize_Init_Data_Array_Lemmas, runtime_initialize_Init_Data_Array_Lemmas,
};
use crate::r#gen::Init::Data::Iterators::Consumers::Access::{
    initialize_Init_Data_Iterators_Consumers_Access,
    runtime_initialize_Init_Data_Iterators_Consumers_Access,
};
use crate::r#gen::Init::Data::Iterators::Consumers::Collect::{
    initialize_Init_Data_Iterators_Consumers_Collect,
    runtime_initialize_Init_Data_Iterators_Consumers_Collect,
};
use crate::r#gen::Init::Data::Iterators::Consumers::Monadic::Total::{
    initialize_Init_Data_Iterators_Consumers_Monadic_Total,
    runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Total,
};
use crate::r#gen::Init::Data::Iterators::Consumers::Total::{
    initialize_Init_Data_Iterators_Consumers_Total,
    runtime_initialize_Init_Data_Iterators_Consumers_Total,
};
use crate::r#gen::Init::Data::Iterators::Lemmas::Basic::{
    initialize_Init_Data_Iterators_Lemmas_Basic,
    runtime_initialize_Init_Data_Iterators_Lemmas_Basic,
};
use crate::r#gen::Init::Data::Iterators::Lemmas::Consumers::Monadic::Collect::{
    initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect,
    runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect,
};
use crate::r#gen::Init::Data::Option::Lemmas::{
    initialize_Init_Data_Option_Lemmas, runtime_initialize_Init_Data_Option_Lemmas,
};
use crate::lean_imports_rs::Init::Prelude::{lean_nat_dec_eq, lean_nat_sub};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_apply_1, lean_apply_2, lean_apply_3, lean_box,
    lean_ctor_get, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_obj_tag, lean_unsigned_to_nat,
};
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Collect_0__Std_Iter_toArray__eq__match__step_match__1_splitter___redArg(
    mut v_x_101_: *mut LeanObject,
    mut v_h__1_102_: *mut LeanObject,
    mut v_h__2_103_: *mut LeanObject,
    mut v_h__3_104_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_101_) {
        0 => {
            let mut v_it_105_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_106_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_107_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_104_);
            lean_dec(v_h__2_103_);
            v_it_105_ = lean_ctor_get(v_x_101_, 0);
            lean_inc(v_it_105_);
            v_out_106_ = lean_ctor_get(v_x_101_, 1);
            lean_inc(v_out_106_);
            lean_dec_ref_known(v_x_101_, 2);
            v___x_107_ = lean_apply_2(v_h__1_102_, v_it_105_, v_out_106_);
            return v___x_107_;
        }
        1 => {
            let mut v_it_108_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_109_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_104_);
            lean_dec(v_h__1_102_);
            v_it_108_ = lean_ctor_get(v_x_101_, 0);
            lean_inc(v_it_108_);
            lean_dec_ref_known(v_x_101_, 1);
            v___x_109_ = lean_apply_1(v_h__2_103_, v_it_108_);
            return v___x_109_;
        }
        _ => {
            let mut v___x_110_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_111_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_103_);
            lean_dec(v_h__1_102_);
            v___x_110_ = lean_box(0);
            v___x_111_ = lean_apply_1(v_h__3_104_, v___x_110_);
            return v___x_111_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Collect_0__Std_Iter_toArray__eq__match__step_match__1_splitter(
    mut v_00_u03b1_112_: *mut LeanObject,
    mut v_00_u03b2_113_: *mut LeanObject,
    mut v_motive_114_: *mut LeanObject,
    mut v_x_115_: *mut LeanObject,
    mut v_h__1_116_: *mut LeanObject,
    mut v_h__2_117_: *mut LeanObject,
    mut v_h__3_118_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_115_) {
        0 => {
            let mut v_it_119_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_120_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_121_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_118_);
            lean_dec(v_h__2_117_);
            v_it_119_ = lean_ctor_get(v_x_115_, 0);
            lean_inc(v_it_119_);
            v_out_120_ = lean_ctor_get(v_x_115_, 1);
            lean_inc(v_out_120_);
            lean_dec_ref_known(v_x_115_, 2);
            v___x_121_ = lean_apply_2(v_h__1_116_, v_it_119_, v_out_120_);
            return v___x_121_;
        }
        1 => {
            let mut v_it_122_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_123_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_118_);
            lean_dec(v_h__1_116_);
            v_it_122_ = lean_ctor_get(v_x_115_, 0);
            lean_inc(v_it_122_);
            lean_dec_ref_known(v_x_115_, 1);
            v___x_123_ = lean_apply_1(v_h__2_117_, v_it_122_);
            return v___x_123_;
        }
        _ => {
            let mut v___x_124_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_125_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_117_);
            lean_dec(v_h__1_116_);
            v___x_124_ = lean_box(0);
            v___x_125_ = lean_apply_1(v_h__3_118_, v___x_124_);
            return v___x_125_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Collect_0__Std_Iter_atIdxSlow_x3f_match__3_splitter___redArg(
    mut v_x_126_: *mut LeanObject,
    mut v_h__1_127_: *mut LeanObject,
    mut v_h__2_128_: *mut LeanObject,
    mut v_h__3_129_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_126_) {
        0 => {
            let mut v_it_130_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_131_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_132_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_129_);
            lean_dec(v_h__2_128_);
            v_it_130_ = lean_ctor_get(v_x_126_, 0);
            lean_inc(v_it_130_);
            v_out_131_ = lean_ctor_get(v_x_126_, 1);
            lean_inc(v_out_131_);
            lean_dec_ref_known(v_x_126_, 2);
            v___x_132_ = lean_apply_3(v_h__1_127_, v_it_130_, v_out_131_, lean_box(0));
            return v___x_132_;
        }
        1 => {
            let mut v_it_133_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_134_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_129_);
            lean_dec(v_h__1_127_);
            v_it_133_ = lean_ctor_get(v_x_126_, 0);
            lean_inc(v_it_133_);
            lean_dec_ref_known(v_x_126_, 1);
            v___x_134_ = lean_apply_2(v_h__2_128_, v_it_133_, lean_box(0));
            return v___x_134_;
        }
        _ => {
            let mut v___x_135_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_128_);
            lean_dec(v_h__1_127_);
            v___x_135_ = lean_apply_1(v_h__3_129_, lean_box(0));
            return v___x_135_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Collect_0__Std_Iter_atIdxSlow_x3f_match__3_splitter(
    mut v_00_u03b1_136_: *mut LeanObject,
    mut v_00_u03b2_137_: *mut LeanObject,
    mut v_inst_138_: *mut LeanObject,
    mut v_it_139_: *mut LeanObject,
    mut v_motive_140_: *mut LeanObject,
    mut v_x_141_: *mut LeanObject,
    mut v_h__1_142_: *mut LeanObject,
    mut v_h__2_143_: *mut LeanObject,
    mut v_h__3_144_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_141_) {
        0 => {
            let mut v_it_145_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_146_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_147_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_144_);
            lean_dec(v_h__2_143_);
            v_it_145_ = lean_ctor_get(v_x_141_, 0);
            lean_inc(v_it_145_);
            v_out_146_ = lean_ctor_get(v_x_141_, 1);
            lean_inc(v_out_146_);
            lean_dec_ref_known(v_x_141_, 2);
            v___x_147_ = lean_apply_3(v_h__1_142_, v_it_145_, v_out_146_, lean_box(0));
            return v___x_147_;
        }
        1 => {
            let mut v_it_148_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_149_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_144_);
            lean_dec(v_h__1_142_);
            v_it_148_ = lean_ctor_get(v_x_141_, 0);
            lean_inc(v_it_148_);
            lean_dec_ref_known(v_x_141_, 1);
            v___x_149_ = lean_apply_2(v_h__2_143_, v_it_148_, lean_box(0));
            return v___x_149_;
        }
        _ => {
            let mut v___x_150_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_143_);
            lean_dec(v_h__1_142_);
            v___x_150_ = lean_apply_1(v_h__3_144_, lean_box(0));
            return v___x_150_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Collect_0__Std_Iter_atIdxSlow_x3f_match__3_splitter___boxed(
    mut v_00_u03b1_151_: *mut LeanObject,
    mut v_00_u03b2_152_: *mut LeanObject,
    mut v_inst_153_: *mut LeanObject,
    mut v_it_154_: *mut LeanObject,
    mut v_motive_155_: *mut LeanObject,
    mut v_x_156_: *mut LeanObject,
    mut v_h__1_157_: *mut LeanObject,
    mut v_h__2_158_: *mut LeanObject,
    mut v_h__3_159_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_160_: *mut LeanObject = core::ptr::null_mut();
    v_res_160_ = l___private_Init_Data_Iterators_Lemmas_Consumers_Collect_0__Std_Iter_atIdxSlow_x3f_match__3_splitter(v_00_u03b1_151_, v_00_u03b2_152_, v_inst_153_, v_it_154_, v_motive_155_, v_x_156_, v_h__1_157_, v_h__2_158_, v_h__3_159_);
    lean_dec(v_it_154_);
    lean_dec(v_inst_153_);
    return v_res_160_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Collect_0__Std_Iter_atIdxSlow_x3f_match__1_splitter___redArg(
    mut v_n_161_: *mut LeanObject,
    mut v_recur_162_: *mut LeanObject,
    mut v_h__1_163_: *mut LeanObject,
    mut v_h__2_164_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_165_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_166_: u8 = 0;
    v_zero_165_ = lean_unsigned_to_nat(0);
    v_isZero_166_ = lean_nat_dec_eq(v_n_161_, v_zero_165_);
    if v_isZero_166_ == 1 {
        let mut v___x_167_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_164_);
        v___x_167_ = lean_apply_1(v_h__1_163_, v_recur_162_);
        return v___x_167_;
    } else {
        let mut v_one_168_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_169_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_170_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_163_);
        v_one_168_ = lean_unsigned_to_nat(1);
        v_n_169_ = lean_nat_sub(v_n_161_, v_one_168_);
        v___x_170_ = lean_apply_2(v_h__2_164_, v_n_169_, v_recur_162_);
        return v___x_170_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Collect_0__Std_Iter_atIdxSlow_x3f_match__1_splitter___redArg___boxed(
    mut v_n_171_: *mut LeanObject,
    mut v_recur_172_: *mut LeanObject,
    mut v_h__1_173_: *mut LeanObject,
    mut v_h__2_174_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_175_: *mut LeanObject = core::ptr::null_mut();
    v_res_175_ = l___private_Init_Data_Iterators_Lemmas_Consumers_Collect_0__Std_Iter_atIdxSlow_x3f_match__1_splitter___redArg(v_n_171_, v_recur_172_, v_h__1_173_, v_h__2_174_);
    lean_dec(v_n_171_);
    return v_res_175_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Collect_0__Std_Iter_atIdxSlow_x3f_match__1_splitter(
    mut v_00_u03b1_176_: *mut LeanObject,
    mut v_00_u03b2_177_: *mut LeanObject,
    mut v_inst_178_: *mut LeanObject,
    mut v_it_179_: *mut LeanObject,
    mut v_motive_180_: *mut LeanObject,
    mut v_n_181_: *mut LeanObject,
    mut v_recur_182_: *mut LeanObject,
    mut v_h__1_183_: *mut LeanObject,
    mut v_h__2_184_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_185_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_186_: u8 = 0;
    v_zero_185_ = lean_unsigned_to_nat(0);
    v_isZero_186_ = lean_nat_dec_eq(v_n_181_, v_zero_185_);
    if v_isZero_186_ == 1 {
        let mut v___x_187_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_184_);
        v___x_187_ = lean_apply_1(v_h__1_183_, v_recur_182_);
        return v___x_187_;
    } else {
        let mut v_one_188_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_189_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_190_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_183_);
        v_one_188_ = lean_unsigned_to_nat(1);
        v_n_189_ = lean_nat_sub(v_n_181_, v_one_188_);
        v___x_190_ = lean_apply_2(v_h__2_184_, v_n_189_, v_recur_182_);
        return v___x_190_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Consumers_Collect_0__Std_Iter_atIdxSlow_x3f_match__1_splitter___boxed(
    mut v_00_u03b1_191_: *mut LeanObject,
    mut v_00_u03b2_192_: *mut LeanObject,
    mut v_inst_193_: *mut LeanObject,
    mut v_it_194_: *mut LeanObject,
    mut v_motive_195_: *mut LeanObject,
    mut v_n_196_: *mut LeanObject,
    mut v_recur_197_: *mut LeanObject,
    mut v_h__1_198_: *mut LeanObject,
    mut v_h__2_199_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_200_: *mut LeanObject = core::ptr::null_mut();
    v_res_200_ = l___private_Init_Data_Iterators_Lemmas_Consumers_Collect_0__Std_Iter_atIdxSlow_x3f_match__1_splitter(v_00_u03b1_191_, v_00_u03b2_192_, v_inst_193_, v_it_194_, v_motive_195_, v_n_196_, v_recur_197_, v_h__1_198_, v_h__2_199_);
    lean_dec(v_n_196_);
    lean_dec(v_it_194_);
    lean_dec(v_inst_193_);
    return v_res_200_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Iterators_Consumers_Access(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Collect(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Total(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Total(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Bootstrap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Iterators_Consumers_Access(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers_Collect(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers_Total(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers_Monadic_Total(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Array_Bootstrap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Array_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Option_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(builtin);
}
