// Lean compiler output
// Module: Init.Data.String.Lemmas.Pattern.String.ForwardSearcher
// Imports: Init.Data.String.Lemmas.Pattern.String.Basic Init.Data.String.Pattern.String Init.Data.String.Slice Init.Data.String.Search Init.Data.String.Slice Init.Data.String.Search Init.Data.String.Pattern.String Init.Data.String.Lemmas.IsEmpty Init.Data.Vector.Lemmas Init.Data.Iterators.Lemmas.Basic Init.Data.Iterators.Lemmas.Consumers.Collect Init.Data.String.Lemmas.Basic Init.Data.String.OrderInstances
use crate::ffi::{
    lean_byte_array_fget, lean_byte_array_size, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le,
    lean_nat_sub, lean_uint8_dec_eq,
};
use crate::r#gen::Init::Data::Iterators::Lemmas::Basic::{
    initialize_Init_Data_Iterators_Lemmas_Basic,
    runtime_initialize_Init_Data_Iterators_Lemmas_Basic,
};
use crate::r#gen::Init::Data::Iterators::Lemmas::Consumers::Collect::{
    initialize_Init_Data_Iterators_Lemmas_Consumers_Collect,
    runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Collect,
};
use crate::r#gen::Init::Data::Nat::Lemmas::l_Nat_decidableBallLT___redArg;
use crate::r#gen::Init::Data::String::Lemmas::Basic::{
    initialize_Init_Data_String_Lemmas_Basic, runtime_initialize_Init_Data_String_Lemmas_Basic,
};
use crate::r#gen::Init::Data::String::Lemmas::IsEmpty::{
    initialize_Init_Data_String_Lemmas_IsEmpty, runtime_initialize_Init_Data_String_Lemmas_IsEmpty,
};
use crate::r#gen::Init::Data::String::Lemmas::Pattern::String::Basic::{
    initialize_Init_Data_String_Lemmas_Pattern_String_Basic,
    runtime_initialize_Init_Data_String_Lemmas_Pattern_String_Basic,
};
use crate::r#gen::Init::Data::String::OrderInstances::{
    initialize_Init_Data_String_OrderInstances, runtime_initialize_Init_Data_String_OrderInstances,
};
use crate::r#gen::Init::Data::String::Pattern::String::{
    initialize_Init_Data_String_Pattern_String, runtime_initialize_Init_Data_String_Pattern_String,
};
use crate::r#gen::Init::Data::String::Search::{
    initialize_Init_Data_String_Search, runtime_initialize_Init_Data_String_Search,
};
use crate::r#gen::Init::Data::String::Slice::{
    initialize_Init_Data_String_Slice, runtime_initialize_Init_Data_String_Slice,
};
use crate::r#gen::Init::Data::Vector::Lemmas::{
    initialize_Init_Data_Vector_Lemmas, runtime_initialize_Init_Data_Vector_Lemmas,
};
pub unsafe fn l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_instDecidablePartialMatch___lam__0(
    mut v_pat_114_: *mut leanh::LeanObject,
    mut v_stackPos_115_: *mut leanh::LeanObject,
    mut v_needlePos_116_: *mut leanh::LeanObject,
    mut v_s_117_: *mut leanh::LeanObject,
    mut v_n_118_: *mut leanh::LeanObject,
    mut v_h_119_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_120_: u8 = 0;
    let mut v___x_121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_123_: u8 = 0;
    let mut v___x_124_: u8 = 0;
    v___x_120_ = lean_byte_array_fget(v_pat_114_, v_n_118_);
    v___x_121_ = lean_nat_sub(v_stackPos_115_, v_needlePos_116_);
    v___x_122_ = lean_nat_add(v___x_121_, v_n_118_);
    leanh::lean_dec(v___x_121_);
    v___x_123_ = lean_byte_array_fget(v_s_117_, v___x_122_);
    leanh::lean_dec(v___x_122_);
    v___x_124_ = lean_uint8_dec_eq(v___x_120_, v___x_123_);
    return v___x_124_;
}
pub unsafe fn l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_instDecidablePartialMatch___lam__0___boxed(
    mut v_pat_125_: *mut leanh::LeanObject,
    mut v_stackPos_126_: *mut leanh::LeanObject,
    mut v_needlePos_127_: *mut leanh::LeanObject,
    mut v_s_128_: *mut leanh::LeanObject,
    mut v_n_129_: *mut leanh::LeanObject,
    mut v_h_130_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_131_: u8 = 0;
    let mut v_r_132_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_131_ = l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_instDecidablePartialMatch___lam__0(v_pat_125_, v_stackPos_126_, v_needlePos_127_, v_s_128_, v_n_129_, v_h_130_);
    leanh::lean_dec(v_n_129_);
    leanh::lean_dec_ref(v_s_128_);
    leanh::lean_dec(v_needlePos_127_);
    leanh::lean_dec(v_stackPos_126_);
    leanh::lean_dec_ref(v_pat_125_);
    v_r_132_ = leanh::lean_box((v_res_131_) as usize);
    return v_r_132_;
}
pub unsafe fn l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_instDecidablePartialMatch(
    mut v_pat_133_: *mut leanh::LeanObject,
    mut v_s_134_: *mut leanh::LeanObject,
    mut v_needlePos_135_: *mut leanh::LeanObject,
    mut v_stackPos_136_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_138_: u8 = 0;
    v___x_137_ = lean_byte_array_size(v_s_134_);
    v___x_138_ = lean_nat_dec_le(v_stackPos_136_, v___x_137_);
    if v___x_138_ == 0 {
        leanh::lean_dec(v_stackPos_136_);
        leanh::lean_dec(v_needlePos_135_);
        leanh::lean_dec_ref(v_s_134_);
        leanh::lean_dec_ref(v_pat_133_);
        return v___x_138_;
    } else {
        let mut v___x_139_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_140_: u8 = 0;
        v___x_139_ = lean_byte_array_size(v_pat_133_);
        v___x_140_ = lean_nat_dec_le(v_needlePos_135_, v___x_139_);
        if v___x_140_ == 0 {
            leanh::lean_dec(v_stackPos_136_);
            leanh::lean_dec(v_needlePos_135_);
            leanh::lean_dec_ref(v_s_134_);
            leanh::lean_dec_ref(v_pat_133_);
            return v___x_140_;
        } else {
            let mut v___x_141_: u8 = 0;
            v___x_141_ = lean_nat_dec_le(v_needlePos_135_, v_stackPos_136_);
            if v___x_141_ == 0 {
                leanh::lean_dec(v_stackPos_136_);
                leanh::lean_dec(v_needlePos_135_);
                leanh::lean_dec_ref(v_s_134_);
                leanh::lean_dec_ref(v_pat_133_);
                return v___x_141_;
            } else {
                let mut v___f_142_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_143_: u8 = 0;
                leanh::lean_inc(v_needlePos_135_);
                v___f_142_ = leanh::lean_alloc_closure(l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_instDecidablePartialMatch___lam__0___boxed as *mut core::ffi::c_void, 6, 4);
                leanh::lean_closure_set(v___f_142_, 0, v_pat_133_);
                leanh::lean_closure_set(v___f_142_, 1, v_stackPos_136_);
                leanh::lean_closure_set(v___f_142_, 2, v_needlePos_135_);
                leanh::lean_closure_set(v___f_142_, 3, v_s_134_);
                v___x_143_ = l_Nat_decidableBallLT___redArg(v_needlePos_135_, v___f_142_);
                leanh::lean_dec(v_needlePos_135_);
                return v___x_143_;
            }
        }
    }
}
pub unsafe fn l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_instDecidablePartialMatch___boxed(
    mut v_pat_144_: *mut leanh::LeanObject,
    mut v_s_145_: *mut leanh::LeanObject,
    mut v_needlePos_146_: *mut leanh::LeanObject,
    mut v_stackPos_147_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_148_: u8 = 0;
    let mut v_r_149_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_148_ = l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_instDecidablePartialMatch(v_pat_144_, v_s_145_, v_needlePos_146_, v_stackPos_147_);
    v_r_149_ = leanh::lean_box((v_res_148_) as usize);
    return v_r_149_;
}
pub unsafe fn l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunction_go___redArg(
    mut v_pat_150_: *mut leanh::LeanObject,
    mut v_stackPos_151_: *mut leanh::LeanObject,
    mut v_k_152_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_155_: u8 = 0;
    let mut v___x_156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_153_ = leanh::lean_unsigned_to_nat(1);
                v___x_154_ = lean_nat_add(v_stackPos_151_, v___x_153_);
                leanh::lean_inc(v_k_152_);
                leanh::lean_inc_ref_n(v_pat_150_, 2);
                v___x_155_ = l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_instDecidablePartialMatch(v_pat_150_, v_pat_150_, v_k_152_, v___x_154_);
                if v___x_155_ == 0 {
                    v___x_156_ = lean_nat_sub(v_k_152_, v___x_153_);
                    leanh::lean_dec(v_k_152_);
                    v_k_152_ = v___x_156_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec_ref(v_pat_150_);
                    return v_k_152_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunction_go___redArg___boxed(
    mut v_pat_158_: *mut leanh::LeanObject,
    mut v_stackPos_159_: *mut leanh::LeanObject,
    mut v_k_160_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_161_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_161_ = l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunction_go___redArg(v_pat_158_, v_stackPos_159_, v_k_160_);
    leanh::lean_dec(v_stackPos_159_);
    return v_res_161_;
}
pub unsafe fn l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunction_go(
    mut v_pat_162_: *mut leanh::LeanObject,
    mut v_stackPos_163_: *mut leanh::LeanObject,
    mut v_hst_164_: *mut leanh::LeanObject,
    mut v_k_165_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_166_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_166_ = l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunction_go___redArg(v_pat_162_, v_stackPos_163_, v_k_165_);
    return v___x_166_;
}
pub unsafe fn l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunction_go___boxed(
    mut v_pat_167_: *mut leanh::LeanObject,
    mut v_stackPos_168_: *mut leanh::LeanObject,
    mut v_hst_169_: *mut leanh::LeanObject,
    mut v_k_170_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_171_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_171_ = l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunction_go(v_pat_167_, v_stackPos_168_, v_hst_169_, v_k_170_);
    leanh::lean_dec(v_stackPos_168_);
    return v_res_171_;
}
pub unsafe fn l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunction___redArg(
    mut v_pat_172_: *mut leanh::LeanObject,
    mut v_stackPos_173_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_174_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_stackPos_173_);
    v___x_174_ = l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunction_go___redArg(v_pat_172_, v_stackPos_173_, v_stackPos_173_);
    leanh::lean_dec(v_stackPos_173_);
    return v___x_174_;
}
pub unsafe fn l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunction(
    mut v_pat_175_: *mut leanh::LeanObject,
    mut v_stackPos_176_: *mut leanh::LeanObject,
    mut v_hst_177_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_178_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_stackPos_176_);
    v___x_178_ = l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunction_go___redArg(v_pat_175_, v_stackPos_176_, v_stackPos_176_);
    leanh::lean_dec(v_stackPos_176_);
    return v___x_178_;
}
pub unsafe fn l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunctionRecurrence___redArg(
    mut v_pat_179_: *mut leanh::LeanObject,
    mut v_stackPos_180_: *mut leanh::LeanObject,
    mut v_guess_181_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_182_: u8 = 0;
    let mut v___x_183_: u8 = 0;
    let mut v___x_184_: u8 = 0;
    let mut v___x_185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_186_: u8 = 0;
    let mut v___x_187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_182_ = lean_byte_array_fget(v_pat_179_, v_guess_181_);
                v___x_183_ = lean_byte_array_fget(v_pat_179_, v_stackPos_180_);
                v___x_184_ = lean_uint8_dec_eq(v___x_182_, v___x_183_);
                if v___x_184_ == 0 {
                    v___x_185_ = leanh::lean_unsigned_to_nat(0);
                    v___x_186_ = lean_nat_dec_eq(v_guess_181_, v___x_185_);
                    if v___x_186_ == 0 {
                        v___x_187_ = leanh::lean_unsigned_to_nat(1);
                        v___x_188_ = lean_nat_sub(v_guess_181_, v___x_187_);
                        leanh::lean_dec(v_guess_181_);
                        leanh::lean_inc(v___x_188_);
                        leanh::lean_inc_ref(v_pat_179_);
                        v___x_189_ = l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunction_go___redArg(v_pat_179_, v___x_188_, v___x_188_);
                        leanh::lean_dec(v___x_188_);
                        v_guess_181_ = v___x_189_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_guess_181_);
                        leanh::lean_dec_ref(v_pat_179_);
                        return v___x_185_;
                    }
                } else {
                    leanh::lean_dec_ref(v_pat_179_);
                    v___x_191_ = leanh::lean_unsigned_to_nat(1);
                    v___x_192_ = lean_nat_add(v_guess_181_, v___x_191_);
                    leanh::lean_dec(v_guess_181_);
                    return v___x_192_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunctionRecurrence___redArg___boxed(
    mut v_pat_193_: *mut leanh::LeanObject,
    mut v_stackPos_194_: *mut leanh::LeanObject,
    mut v_guess_195_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_196_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_196_ = l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunctionRecurrence___redArg(v_pat_193_, v_stackPos_194_, v_guess_195_);
    leanh::lean_dec(v_stackPos_194_);
    return v_res_196_;
}
pub unsafe fn l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunctionRecurrence(
    mut v_pat_197_: *mut leanh::LeanObject,
    mut v_stackPos_198_: *mut leanh::LeanObject,
    mut v_hst_199_: *mut leanh::LeanObject,
    mut v_guess_200_: *mut leanh::LeanObject,
    mut v_hg_201_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_202_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_202_ = l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunctionRecurrence___redArg(v_pat_197_, v_stackPos_198_, v_guess_200_);
    return v___x_202_;
}
pub unsafe fn l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunctionRecurrence___boxed(
    mut v_pat_203_: *mut leanh::LeanObject,
    mut v_stackPos_204_: *mut leanh::LeanObject,
    mut v_hst_205_: *mut leanh::LeanObject,
    mut v_guess_206_: *mut leanh::LeanObject,
    mut v_hg_207_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_208_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_208_ = l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_prefixFunctionRecurrence(v_pat_203_, v_stackPos_204_, v_hst_205_, v_guess_206_, v_hg_207_);
    leanh::lean_dec(v_stackPos_204_);
    return v_res_208_;
}
pub unsafe fn l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_Invariants_base___redArg(
    mut v_needlePos_209_: *mut leanh::LeanObject,
    mut v_stackPos_210_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_211_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_211_ = lean_nat_sub(v_stackPos_210_, v_needlePos_209_);
    return v___x_211_;
}
pub unsafe fn l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_Invariants_base___redArg___boxed(
    mut v_needlePos_212_: *mut leanh::LeanObject,
    mut v_stackPos_213_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_214_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_214_ = l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_Invariants_base___redArg(v_needlePos_212_, v_stackPos_213_);
    leanh::lean_dec(v_stackPos_213_);
    leanh::lean_dec(v_needlePos_212_);
    return v_res_214_;
}
pub unsafe fn l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_Invariants_base(
    mut v_pat_215_: *mut leanh::LeanObject,
    mut v_s_216_: *mut leanh::LeanObject,
    mut v_needlePos_217_: *mut leanh::LeanObject,
    mut v_stackPos_218_: *mut leanh::LeanObject,
    mut v_h_219_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_220_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_220_ = lean_nat_sub(v_stackPos_218_, v_needlePos_217_);
    return v___x_220_;
}
pub unsafe fn l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_Invariants_base___boxed(
    mut v_pat_221_: *mut leanh::LeanObject,
    mut v_s_222_: *mut leanh::LeanObject,
    mut v_needlePos_223_: *mut leanh::LeanObject,
    mut v_stackPos_224_: *mut leanh::LeanObject,
    mut v_h_225_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_226_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_226_ = l___private_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher_0__String_Slice_Pattern_Model_ForwardSliceSearcher_Invariants_base(v_pat_221_, v_s_222_, v_needlePos_223_, v_stackPos_224_, v_h_225_);
    leanh::lean_dec(v_stackPos_224_);
    leanh::lean_dec(v_needlePos_223_);
    leanh::lean_dec_ref(v_s_222_);
    leanh::lean_dec_ref(v_pat_221_);
    return v_res_226_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_String_Lemmas_Pattern_String_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Pattern_String(builtin);
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
    res = runtime_initialize_Init_Data_String_Pattern_String(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_IsEmpty(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Vector_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(builtin);
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
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher(
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
pub unsafe fn initialize_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_String_Lemmas_Pattern_String_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Pattern_String(builtin);
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
    res = initialize_Init_Data_String_Pattern_String(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Lemmas_IsEmpty(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Vector_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(builtin);
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
    res = runtime_initialize_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_String_Lemmas_Pattern_String_ForwardSearcher(builtin);
}