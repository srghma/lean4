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
    mut v_x_101_: *mut crate::leanh::LeanObject,
    mut v_h__1_102_: *mut crate::leanh::LeanObject,
    mut v_h__2_103_: *mut crate::leanh::LeanObject,
    mut v_h__3_104_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_101_) {
        0 => {
            let mut v_it_105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_104_);
            crate::leanh::lean_dec(v_h__2_103_);
            v_it_105_ = crate::leanh::lean_ctor_get(v_x_101_, 0);
            crate::leanh::lean_inc(v_it_105_);
            v_out_106_ = crate::leanh::lean_ctor_get(v_x_101_, 1);
            crate::leanh::lean_inc(v_out_106_);
            crate::leanh::lean_dec_ref_known(v_x_101_, 2);
            v___x_107_ = crate::leanh::lean_apply_3(
                v_h__1_102_,
                v_it_105_,
                v_out_106_,
                crate::leanh::lean_box(0),
            );
            return v___x_107_;
        }
        1 => {
            let mut v_it_108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_104_);
            crate::leanh::lean_dec(v_h__1_102_);
            v_it_108_ = crate::leanh::lean_ctor_get(v_x_101_, 0);
            crate::leanh::lean_inc(v_it_108_);
            crate::leanh::lean_dec_ref_known(v_x_101_, 1);
            v___x_109_ =
                crate::leanh::lean_apply_2(v_h__2_103_, v_it_108_, crate::leanh::lean_box(0));
            return v___x_109_;
        }
        _ => {
            let mut v___x_110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_103_);
            crate::leanh::lean_dec(v_h__1_102_);
            v___x_110_ = crate::leanh::lean_apply_1(v_h__3_104_, crate::leanh::lean_box(0));
            return v___x_110_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Append_0__Std_Iterators_Types_Append_instIterator_match__1_splitter(
    mut v_m_111_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_112_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_u2081_113_: *mut crate::leanh::LeanObject,
    mut v_inst_114_: *mut crate::leanh::LeanObject,
    mut v_it_u2081_115_: *mut crate::leanh::LeanObject,
    mut v_motive_116_: *mut crate::leanh::LeanObject,
    mut v_x_117_: *mut crate::leanh::LeanObject,
    mut v_h__1_118_: *mut crate::leanh::LeanObject,
    mut v_h__2_119_: *mut crate::leanh::LeanObject,
    mut v_h__3_120_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_117_) {
        0 => {
            let mut v_it_121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_120_);
            crate::leanh::lean_dec(v_h__2_119_);
            v_it_121_ = crate::leanh::lean_ctor_get(v_x_117_, 0);
            crate::leanh::lean_inc(v_it_121_);
            v_out_122_ = crate::leanh::lean_ctor_get(v_x_117_, 1);
            crate::leanh::lean_inc(v_out_122_);
            crate::leanh::lean_dec_ref_known(v_x_117_, 2);
            v___x_123_ = crate::leanh::lean_apply_3(
                v_h__1_118_,
                v_it_121_,
                v_out_122_,
                crate::leanh::lean_box(0),
            );
            return v___x_123_;
        }
        1 => {
            let mut v_it_124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_120_);
            crate::leanh::lean_dec(v_h__1_118_);
            v_it_124_ = crate::leanh::lean_ctor_get(v_x_117_, 0);
            crate::leanh::lean_inc(v_it_124_);
            crate::leanh::lean_dec_ref_known(v_x_117_, 1);
            v___x_125_ =
                crate::leanh::lean_apply_2(v_h__2_119_, v_it_124_, crate::leanh::lean_box(0));
            return v___x_125_;
        }
        _ => {
            let mut v___x_126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_119_);
            crate::leanh::lean_dec(v_h__1_118_);
            v___x_126_ = crate::leanh::lean_apply_1(v_h__3_120_, crate::leanh::lean_box(0));
            return v___x_126_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Append_0__Std_Iterators_Types_Append_instIterator_match__1_splitter___boxed(
    mut v_m_127_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_128_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_u2081_129_: *mut crate::leanh::LeanObject,
    mut v_inst_130_: *mut crate::leanh::LeanObject,
    mut v_it_u2081_131_: *mut crate::leanh::LeanObject,
    mut v_motive_132_: *mut crate::leanh::LeanObject,
    mut v_x_133_: *mut crate::leanh::LeanObject,
    mut v_h__1_134_: *mut crate::leanh::LeanObject,
    mut v_h__2_135_: *mut crate::leanh::LeanObject,
    mut v_h__3_136_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_137_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Append_0__Std_Iterators_Types_Append_instIterator_match__1_splitter(v_m_127_, v_00_u03b2_128_, v_00_u03b1_u2081_129_, v_inst_130_, v_it_u2081_131_, v_motive_132_, v_x_133_, v_h__1_134_, v_h__2_135_, v_h__3_136_);
    crate::leanh::lean_dec(v_it_u2081_131_);
    crate::leanh::lean_dec(v_inst_130_);
    return v_res_137_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Append_0__Std_IterM_step__append_match__1_splitter___redArg(
    mut v_x_138_: *mut crate::leanh::LeanObject,
    mut v_h__1_139_: *mut crate::leanh::LeanObject,
    mut v_h__2_140_: *mut crate::leanh::LeanObject,
    mut v_h__3_141_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_138_) {
        0 => {
            let mut v_it_142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_141_);
            crate::leanh::lean_dec(v_h__2_140_);
            v_it_142_ = crate::leanh::lean_ctor_get(v_x_138_, 0);
            crate::leanh::lean_inc(v_it_142_);
            v_out_143_ = crate::leanh::lean_ctor_get(v_x_138_, 1);
            crate::leanh::lean_inc(v_out_143_);
            crate::leanh::lean_dec_ref_known(v_x_138_, 2);
            v___x_144_ = crate::leanh::lean_apply_3(
                v_h__1_139_,
                v_it_142_,
                v_out_143_,
                crate::leanh::lean_box(0),
            );
            return v___x_144_;
        }
        1 => {
            let mut v_it_145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_141_);
            crate::leanh::lean_dec(v_h__1_139_);
            v_it_145_ = crate::leanh::lean_ctor_get(v_x_138_, 0);
            crate::leanh::lean_inc(v_it_145_);
            crate::leanh::lean_dec_ref_known(v_x_138_, 1);
            v___x_146_ =
                crate::leanh::lean_apply_2(v_h__2_140_, v_it_145_, crate::leanh::lean_box(0));
            return v___x_146_;
        }
        _ => {
            let mut v___x_147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_140_);
            crate::leanh::lean_dec(v_h__1_139_);
            v___x_147_ = crate::leanh::lean_apply_1(v_h__3_141_, crate::leanh::lean_box(0));
            return v___x_147_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Append_0__Std_IterM_step__append_match__1_splitter(
    mut v_00_u03b1_u2081_148_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_149_: *mut crate::leanh::LeanObject,
    mut v_m_150_: *mut crate::leanh::LeanObject,
    mut v_inst_151_: *mut crate::leanh::LeanObject,
    mut v_it_u2081_152_: *mut crate::leanh::LeanObject,
    mut v_motive_153_: *mut crate::leanh::LeanObject,
    mut v_x_154_: *mut crate::leanh::LeanObject,
    mut v_h__1_155_: *mut crate::leanh::LeanObject,
    mut v_h__2_156_: *mut crate::leanh::LeanObject,
    mut v_h__3_157_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_154_) {
        0 => {
            let mut v_it_158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_157_);
            crate::leanh::lean_dec(v_h__2_156_);
            v_it_158_ = crate::leanh::lean_ctor_get(v_x_154_, 0);
            crate::leanh::lean_inc(v_it_158_);
            v_out_159_ = crate::leanh::lean_ctor_get(v_x_154_, 1);
            crate::leanh::lean_inc(v_out_159_);
            crate::leanh::lean_dec_ref_known(v_x_154_, 2);
            v___x_160_ = crate::leanh::lean_apply_3(
                v_h__1_155_,
                v_it_158_,
                v_out_159_,
                crate::leanh::lean_box(0),
            );
            return v___x_160_;
        }
        1 => {
            let mut v_it_161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_157_);
            crate::leanh::lean_dec(v_h__1_155_);
            v_it_161_ = crate::leanh::lean_ctor_get(v_x_154_, 0);
            crate::leanh::lean_inc(v_it_161_);
            crate::leanh::lean_dec_ref_known(v_x_154_, 1);
            v___x_162_ =
                crate::leanh::lean_apply_2(v_h__2_156_, v_it_161_, crate::leanh::lean_box(0));
            return v___x_162_;
        }
        _ => {
            let mut v___x_163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_156_);
            crate::leanh::lean_dec(v_h__1_155_);
            v___x_163_ = crate::leanh::lean_apply_1(v_h__3_157_, crate::leanh::lean_box(0));
            return v___x_163_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Append_0__Std_IterM_step__append_match__1_splitter___boxed(
    mut v_00_u03b1_u2081_164_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_165_: *mut crate::leanh::LeanObject,
    mut v_m_166_: *mut crate::leanh::LeanObject,
    mut v_inst_167_: *mut crate::leanh::LeanObject,
    mut v_it_u2081_168_: *mut crate::leanh::LeanObject,
    mut v_motive_169_: *mut crate::leanh::LeanObject,
    mut v_x_170_: *mut crate::leanh::LeanObject,
    mut v_h__1_171_: *mut crate::leanh::LeanObject,
    mut v_h__2_172_: *mut crate::leanh::LeanObject,
    mut v_h__3_173_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_174_ = l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Append_0__Std_IterM_step__append_match__1_splitter(v_00_u03b1_u2081_164_, v_00_u03b2_165_, v_m_166_, v_inst_167_, v_it_u2081_168_, v_motive_169_, v_x_170_, v_h__1_171_, v_h__2_172_, v_h__3_173_);
    crate::leanh::lean_dec(v_it_u2081_168_);
    crate::leanh::lean_dec(v_inst_167_);
    return v_res_174_;
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Append_0__Std_IterM_toArray__eq__match__step_match__1_splitter___redArg(
    mut v_x_175_: *mut crate::leanh::LeanObject,
    mut v_h__1_176_: *mut crate::leanh::LeanObject,
    mut v_h__2_177_: *mut crate::leanh::LeanObject,
    mut v_h__3_178_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_175_) {
        0 => {
            let mut v_it_179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_178_);
            crate::leanh::lean_dec(v_h__2_177_);
            v_it_179_ = crate::leanh::lean_ctor_get(v_x_175_, 0);
            crate::leanh::lean_inc(v_it_179_);
            v_out_180_ = crate::leanh::lean_ctor_get(v_x_175_, 1);
            crate::leanh::lean_inc(v_out_180_);
            crate::leanh::lean_dec_ref_known(v_x_175_, 2);
            v___x_181_ = crate::leanh::lean_apply_2(v_h__1_176_, v_it_179_, v_out_180_);
            return v___x_181_;
        }
        1 => {
            let mut v_it_182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_178_);
            crate::leanh::lean_dec(v_h__1_176_);
            v_it_182_ = crate::leanh::lean_ctor_get(v_x_175_, 0);
            crate::leanh::lean_inc(v_it_182_);
            crate::leanh::lean_dec_ref_known(v_x_175_, 1);
            v___x_183_ = crate::leanh::lean_apply_1(v_h__2_177_, v_it_182_);
            return v___x_183_;
        }
        _ => {
            let mut v___x_184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_177_);
            crate::leanh::lean_dec(v_h__1_176_);
            v___x_184_ = crate::leanh::lean_box(0);
            v___x_185_ = crate::leanh::lean_apply_1(v_h__3_178_, v___x_184_);
            return v___x_185_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Lemmas_Combinators_Monadic_Append_0__Std_IterM_toArray__eq__match__step_match__1_splitter(
    mut v_00_u03b1_186_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_187_: *mut crate::leanh::LeanObject,
    mut v_m_188_: *mut crate::leanh::LeanObject,
    mut v_motive_189_: *mut crate::leanh::LeanObject,
    mut v_x_190_: *mut crate::leanh::LeanObject,
    mut v_h__1_191_: *mut crate::leanh::LeanObject,
    mut v_h__2_192_: *mut crate::leanh::LeanObject,
    mut v_h__3_193_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_190_) {
        0 => {
            let mut v_it_194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_193_);
            crate::leanh::lean_dec(v_h__2_192_);
            v_it_194_ = crate::leanh::lean_ctor_get(v_x_190_, 0);
            crate::leanh::lean_inc(v_it_194_);
            v_out_195_ = crate::leanh::lean_ctor_get(v_x_190_, 1);
            crate::leanh::lean_inc(v_out_195_);
            crate::leanh::lean_dec_ref_known(v_x_190_, 2);
            v___x_196_ = crate::leanh::lean_apply_2(v_h__1_191_, v_it_194_, v_out_195_);
            return v___x_196_;
        }
        1 => {
            let mut v_it_197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_193_);
            crate::leanh::lean_dec(v_h__1_191_);
            v_it_197_ = crate::leanh::lean_ctor_get(v_x_190_, 0);
            crate::leanh::lean_inc(v_it_197_);
            crate::leanh::lean_dec_ref_known(v_x_190_, 1);
            v___x_198_ = crate::leanh::lean_apply_1(v_h__2_192_, v_it_197_);
            return v___x_198_;
        }
        _ => {
            let mut v___x_199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_192_);
            crate::leanh::lean_dec(v_h__1_191_);
            v___x_199_ = crate::leanh::lean_box(0);
            v___x_200_ = crate::leanh::lean_apply_1(v_h__3_193_, v___x_199_);
            return v___x_200_;
        }
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_Append(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Iterators_Combinators_Monadic_Append(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Collect(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Monadic_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_ToArray(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_Append(
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
pub unsafe fn initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_Append(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Iterators_Combinators_Monadic_Append(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers_Monadic_Collect(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Monadic_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_ToArray(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_Append(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_Append(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_Append(builtin);
}
