// Lean compiler output
// Module: Init.Data.Iterators.Lemmas.Combinators.Monadic.Append
// Imports: Init.Data.Iterators.Combinators.Monadic.Append Init.Data.Iterators.Consumers.Monadic.Collect Init.Data.Iterators.Lemmas.Consumers.Monadic.Collect Init.Data.Iterators.Lemmas.Monadic.Basic Init.Data.List.Lemmas Init.Data.List.ToArray
use crate::r#gen::Init::Data::Iterators::Combinators::Monadic::Append::{
    initialize_Init_Data_Iterators_Combinators_Monadic_Append,
    runtime_initialize_Init_Data_Iterators_Combinators_Monadic_Append,
};
use crate::r#gen::Init::Data::Iterators::Consumers::Monadic::Collect::{
    initialize_Init_Data_Iterators_Consumers_Monadic_Collect,
    runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Collect,
};
use crate::r#gen::Init::Data::Iterators::Lemmas::Consumers::Monadic::Collect::{
    initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect,
    runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect,
};
use crate::r#gen::Init::Data::Iterators::Lemmas::Monadic::Basic::{
    initialize_Init_Data_Iterators_Lemmas_Monadic_Basic,
    runtime_initialize_Init_Data_Iterators_Lemmas_Monadic_Basic,
};
use crate::r#gen::Init::Data::List::Lemmas::{
    initialize_Init_Data_List_Lemmas, runtime_initialize_Init_Data_List_Lemmas,
};
use crate::r#gen::Init::Data::List::ToArray::{
    initialize_Init_Data_List_ToArray, runtime_initialize_Init_Data_List_ToArray,
};
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Append_0__Std_Iterators_Types_Append_instIterator_match__1_splitter___redArg(
    mut v_x_101_: *mut leanh::LeanObject,
    mut v_h__1_102_: *mut leanh::LeanObject,
    mut v_h__2_103_: *mut leanh::LeanObject,
    mut v_h__3_104_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_101_) {
        0 => {
            let mut v_it_105_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_106_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_107_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_104_);
            leanh::lean_dec(v_h__2_103_);
            v_it_105_ = leanh::lean_ctor_get(v_x_101_, 0);
            leanh::lean_inc(v_it_105_);
            v_out_106_ = leanh::lean_ctor_get(v_x_101_, 1);
            leanh::lean_inc(v_out_106_);
            leanh::lean_dec_ref_known(v_x_101_, 2);
            v___x_107_ = leanh::lean_apply_3(
                v_h__1_102_,
                v_it_105_,
                v_out_106_,
                leanh::lean_box(0),
            );
            return v___x_107_;
        }
        1 => {
            let mut v_it_108_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_109_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_104_);
            leanh::lean_dec(v_h__1_102_);
            v_it_108_ = leanh::lean_ctor_get(v_x_101_, 0);
            leanh::lean_inc(v_it_108_);
            leanh::lean_dec_ref_known(v_x_101_, 1);
            v___x_109_ =
                leanh::lean_apply_2(v_h__2_103_, v_it_108_, leanh::lean_box(0));
            return v___x_109_;
        }
        _ => {
            let mut v___x_110_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_103_);
            leanh::lean_dec(v_h__1_102_);
            v___x_110_ = leanh::lean_apply_1(v_h__3_104_, leanh::lean_box(0));
            return v___x_110_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Append_0__Std_Iterators_Types_Append_instIterator_match__1_splitter(
    mut v_m_111_: *mut leanh::LeanObject,
    mut v_00_u03b2_112_: *mut leanh::LeanObject,
    mut v_00_u03b1_u2081_113_: *mut leanh::LeanObject,
    mut v_inst_114_: *mut leanh::LeanObject,
    mut v_it_u2081_115_: *mut leanh::LeanObject,
    mut v_motive_116_: *mut leanh::LeanObject,
    mut v_x_117_: *mut leanh::LeanObject,
    mut v_h__1_118_: *mut leanh::LeanObject,
    mut v_h__2_119_: *mut leanh::LeanObject,
    mut v_h__3_120_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_117_) {
        0 => {
            let mut v_it_121_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_122_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_123_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_120_);
            leanh::lean_dec(v_h__2_119_);
            v_it_121_ = leanh::lean_ctor_get(v_x_117_, 0);
            leanh::lean_inc(v_it_121_);
            v_out_122_ = leanh::lean_ctor_get(v_x_117_, 1);
            leanh::lean_inc(v_out_122_);
            leanh::lean_dec_ref_known(v_x_117_, 2);
            v___x_123_ = leanh::lean_apply_3(
                v_h__1_118_,
                v_it_121_,
                v_out_122_,
                leanh::lean_box(0),
            );
            return v___x_123_;
        }
        1 => {
            let mut v_it_124_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_125_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_120_);
            leanh::lean_dec(v_h__1_118_);
            v_it_124_ = leanh::lean_ctor_get(v_x_117_, 0);
            leanh::lean_inc(v_it_124_);
            leanh::lean_dec_ref_known(v_x_117_, 1);
            v___x_125_ =
                leanh::lean_apply_2(v_h__2_119_, v_it_124_, leanh::lean_box(0));
            return v___x_125_;
        }
        _ => {
            let mut v___x_126_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_119_);
            leanh::lean_dec(v_h__1_118_);
            v___x_126_ = leanh::lean_apply_1(v_h__3_120_, leanh::lean_box(0));
            return v___x_126_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Append_0__Std_Iterators_Types_Append_instIterator_match__1_splitter___boxed(
    mut v_m_127_: *mut leanh::LeanObject,
    mut v_00_u03b2_128_: *mut leanh::LeanObject,
    mut v_00_u03b1_u2081_129_: *mut leanh::LeanObject,
    mut v_inst_130_: *mut leanh::LeanObject,
    mut v_it_u2081_131_: *mut leanh::LeanObject,
    mut v_motive_132_: *mut leanh::LeanObject,
    mut v_x_133_: *mut leanh::LeanObject,
    mut v_h__1_134_: *mut leanh::LeanObject,
    mut v_h__2_135_: *mut leanh::LeanObject,
    mut v_h__3_136_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_137_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_137_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Append_0__Std_Iterators_Types_Append_instIterator_match__1_splitter(v_m_127_, v_00_u03b2_128_, v_00_u03b1_u2081_129_, v_inst_130_, v_it_u2081_131_, v_motive_132_, v_x_133_, v_h__1_134_, v_h__2_135_, v_h__3_136_);
    leanh::lean_dec(v_it_u2081_131_);
    leanh::lean_dec(v_inst_130_);
    return v_res_137_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Append_0__Std_IterM_step__append_match__1_splitter___redArg(
    mut v_x_138_: *mut leanh::LeanObject,
    mut v_h__1_139_: *mut leanh::LeanObject,
    mut v_h__2_140_: *mut leanh::LeanObject,
    mut v_h__3_141_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_138_) {
        0 => {
            let mut v_it_142_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_143_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_144_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_141_);
            leanh::lean_dec(v_h__2_140_);
            v_it_142_ = leanh::lean_ctor_get(v_x_138_, 0);
            leanh::lean_inc(v_it_142_);
            v_out_143_ = leanh::lean_ctor_get(v_x_138_, 1);
            leanh::lean_inc(v_out_143_);
            leanh::lean_dec_ref_known(v_x_138_, 2);
            v___x_144_ = leanh::lean_apply_3(
                v_h__1_139_,
                v_it_142_,
                v_out_143_,
                leanh::lean_box(0),
            );
            return v___x_144_;
        }
        1 => {
            let mut v_it_145_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_146_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_141_);
            leanh::lean_dec(v_h__1_139_);
            v_it_145_ = leanh::lean_ctor_get(v_x_138_, 0);
            leanh::lean_inc(v_it_145_);
            leanh::lean_dec_ref_known(v_x_138_, 1);
            v___x_146_ =
                leanh::lean_apply_2(v_h__2_140_, v_it_145_, leanh::lean_box(0));
            return v___x_146_;
        }
        _ => {
            let mut v___x_147_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_140_);
            leanh::lean_dec(v_h__1_139_);
            v___x_147_ = leanh::lean_apply_1(v_h__3_141_, leanh::lean_box(0));
            return v___x_147_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Append_0__Std_IterM_step__append_match__1_splitter(
    mut v_00_u03b1_u2081_148_: *mut leanh::LeanObject,
    mut v_00_u03b2_149_: *mut leanh::LeanObject,
    mut v_m_150_: *mut leanh::LeanObject,
    mut v_inst_151_: *mut leanh::LeanObject,
    mut v_it_u2081_152_: *mut leanh::LeanObject,
    mut v_motive_153_: *mut leanh::LeanObject,
    mut v_x_154_: *mut leanh::LeanObject,
    mut v_h__1_155_: *mut leanh::LeanObject,
    mut v_h__2_156_: *mut leanh::LeanObject,
    mut v_h__3_157_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_154_) {
        0 => {
            let mut v_it_158_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_159_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_160_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_157_);
            leanh::lean_dec(v_h__2_156_);
            v_it_158_ = leanh::lean_ctor_get(v_x_154_, 0);
            leanh::lean_inc(v_it_158_);
            v_out_159_ = leanh::lean_ctor_get(v_x_154_, 1);
            leanh::lean_inc(v_out_159_);
            leanh::lean_dec_ref_known(v_x_154_, 2);
            v___x_160_ = leanh::lean_apply_3(
                v_h__1_155_,
                v_it_158_,
                v_out_159_,
                leanh::lean_box(0),
            );
            return v___x_160_;
        }
        1 => {
            let mut v_it_161_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_162_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_157_);
            leanh::lean_dec(v_h__1_155_);
            v_it_161_ = leanh::lean_ctor_get(v_x_154_, 0);
            leanh::lean_inc(v_it_161_);
            leanh::lean_dec_ref_known(v_x_154_, 1);
            v___x_162_ =
                leanh::lean_apply_2(v_h__2_156_, v_it_161_, leanh::lean_box(0));
            return v___x_162_;
        }
        _ => {
            let mut v___x_163_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_156_);
            leanh::lean_dec(v_h__1_155_);
            v___x_163_ = leanh::lean_apply_1(v_h__3_157_, leanh::lean_box(0));
            return v___x_163_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Append_0__Std_IterM_step__append_match__1_splitter___boxed(
    mut v_00_u03b1_u2081_164_: *mut leanh::LeanObject,
    mut v_00_u03b2_165_: *mut leanh::LeanObject,
    mut v_m_166_: *mut leanh::LeanObject,
    mut v_inst_167_: *mut leanh::LeanObject,
    mut v_it_u2081_168_: *mut leanh::LeanObject,
    mut v_motive_169_: *mut leanh::LeanObject,
    mut v_x_170_: *mut leanh::LeanObject,
    mut v_h__1_171_: *mut leanh::LeanObject,
    mut v_h__2_172_: *mut leanh::LeanObject,
    mut v_h__3_173_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_174_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_174_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Append_0__Std_IterM_step__append_match__1_splitter(v_00_u03b1_u2081_164_, v_00_u03b2_165_, v_m_166_, v_inst_167_, v_it_u2081_168_, v_motive_169_, v_x_170_, v_h__1_171_, v_h__2_172_, v_h__3_173_);
    leanh::lean_dec(v_it_u2081_168_);
    leanh::lean_dec(v_inst_167_);
    return v_res_174_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Append_0__Std_IterM_toArray__eq__match__step_match__1_splitter___redArg(
    mut v_x_175_: *mut leanh::LeanObject,
    mut v_h__1_176_: *mut leanh::LeanObject,
    mut v_h__2_177_: *mut leanh::LeanObject,
    mut v_h__3_178_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_175_) {
        0 => {
            let mut v_it_179_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_180_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_181_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_178_);
            leanh::lean_dec(v_h__2_177_);
            v_it_179_ = leanh::lean_ctor_get(v_x_175_, 0);
            leanh::lean_inc(v_it_179_);
            v_out_180_ = leanh::lean_ctor_get(v_x_175_, 1);
            leanh::lean_inc(v_out_180_);
            leanh::lean_dec_ref_known(v_x_175_, 2);
            v___x_181_ = leanh::lean_apply_2(v_h__1_176_, v_it_179_, v_out_180_);
            return v___x_181_;
        }
        1 => {
            let mut v_it_182_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_183_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_178_);
            leanh::lean_dec(v_h__1_176_);
            v_it_182_ = leanh::lean_ctor_get(v_x_175_, 0);
            leanh::lean_inc(v_it_182_);
            leanh::lean_dec_ref_known(v_x_175_, 1);
            v___x_183_ = leanh::lean_apply_1(v_h__2_177_, v_it_182_);
            return v___x_183_;
        }
        _ => {
            let mut v___x_184_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_185_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_177_);
            leanh::lean_dec(v_h__1_176_);
            v___x_184_ = leanh::lean_box(0);
            v___x_185_ = leanh::lean_apply_1(v_h__3_178_, v___x_184_);
            return v___x_185_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Append_0__Std_IterM_toArray__eq__match__step_match__1_splitter(
    mut v_00_u03b1_186_: *mut leanh::LeanObject,
    mut v_00_u03b2_187_: *mut leanh::LeanObject,
    mut v_m_188_: *mut leanh::LeanObject,
    mut v_motive_189_: *mut leanh::LeanObject,
    mut v_x_190_: *mut leanh::LeanObject,
    mut v_h__1_191_: *mut leanh::LeanObject,
    mut v_h__2_192_: *mut leanh::LeanObject,
    mut v_h__3_193_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_190_) {
        0 => {
            let mut v_it_194_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_195_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_196_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_193_);
            leanh::lean_dec(v_h__2_192_);
            v_it_194_ = leanh::lean_ctor_get(v_x_190_, 0);
            leanh::lean_inc(v_it_194_);
            v_out_195_ = leanh::lean_ctor_get(v_x_190_, 1);
            leanh::lean_inc(v_out_195_);
            leanh::lean_dec_ref_known(v_x_190_, 2);
            v___x_196_ = leanh::lean_apply_2(v_h__1_191_, v_it_194_, v_out_195_);
            return v___x_196_;
        }
        1 => {
            let mut v_it_197_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_198_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_193_);
            leanh::lean_dec(v_h__1_191_);
            v_it_197_ = leanh::lean_ctor_get(v_x_190_, 0);
            leanh::lean_inc(v_it_197_);
            leanh::lean_dec_ref_known(v_x_190_, 1);
            v___x_198_ = leanh::lean_apply_1(v_h__2_192_, v_it_197_);
            return v___x_198_;
        }
        _ => {
            let mut v___x_199_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_200_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_192_);
            leanh::lean_dec(v_h__1_191_);
            v___x_199_ = leanh::lean_box(0);
            v___x_200_ = leanh::lean_apply_1(v_h__3_193_, v___x_199_);
            return v___x_200_;
        }
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_Append(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Iterators_Combinators_Monadic_Append(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Collect(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Monadic_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_ToArray(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_Append(
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
pub unsafe fn initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_Append(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Iterators_Combinators_Monadic_Append(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers_Monadic_Collect(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Monadic_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_ToArray(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_Append(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_Append(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_Append(builtin);
}