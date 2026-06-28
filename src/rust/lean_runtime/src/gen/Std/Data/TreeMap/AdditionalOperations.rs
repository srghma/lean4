// Lean compiler output
// Module: Std.Data.TreeMap.AdditionalOperations
// Imports: Std.Data.TreeMap.Basic Std.Data.TreeMap.Raw.Basic Std.Data.DTreeMap.AdditionalOperations
use crate::r#gen::Std::Data::DTreeMap::AdditionalOperations::{
    initialize_Std_Data_DTreeMap_AdditionalOperations,
    runtime_initialize_Std_Data_DTreeMap_AdditionalOperations,
};
use crate::r#gen::Std::Data::DTreeMap::Internal::Operations::{
    l_Std_DTreeMap_Internal_Impl_filterMap___redArg, l_Std_DTreeMap_Internal_Impl_map___redArg,
};
use crate::r#gen::Std::Data::DTreeMap::Internal::Queries::{
    l_Std_DTreeMap_Internal_Impl_Const_getEntryGE___redArg,
    l_Std_DTreeMap_Internal_Impl_Const_getEntryGT___redArg,
    l_Std_DTreeMap_Internal_Impl_Const_getEntryLE___redArg,
    l_Std_DTreeMap_Internal_Impl_Const_getEntryLT___redArg,
    l_Std_DTreeMap_Internal_Impl_getKeyGE___redArg, l_Std_DTreeMap_Internal_Impl_getKeyGT___redArg,
    l_Std_DTreeMap_Internal_Impl_getKeyLE___redArg, l_Std_DTreeMap_Internal_Impl_getKeyLT___redArg,
};
use crate::r#gen::Std::Data::TreeMap::Basic::{
    initialize_Std_Data_TreeMap_Basic, runtime_initialize_Std_Data_TreeMap_Basic,
};
use crate::r#gen::Std::Data::TreeMap::Raw::Basic::{
    initialize_Std_Data_TreeMap_Raw_Basic, runtime_initialize_Std_Data_TreeMap_Raw_Basic,
};
pub unsafe fn l_Std_TreeMap_filterMap___redArg(
    mut v_f_131_: *mut crate::leanh::LeanObject,
    mut v_m_132_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_133_ = l_Std_DTreeMap_Internal_Impl_filterMap___redArg(v_f_131_, v_m_132_);
    return v___x_133_;
}
pub unsafe fn l_Std_TreeMap_filterMap(
    mut v_00_u03b1_134_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_135_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_136_: *mut crate::leanh::LeanObject,
    mut v_cmp_137_: *mut crate::leanh::LeanObject,
    mut v_f_138_: *mut crate::leanh::LeanObject,
    mut v_m_139_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_140_ = l_Std_DTreeMap_Internal_Impl_filterMap___redArg(v_f_138_, v_m_139_);
    return v___x_140_;
}
pub unsafe fn l_Std_TreeMap_filterMap___boxed(
    mut v_00_u03b1_141_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_142_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_143_: *mut crate::leanh::LeanObject,
    mut v_cmp_144_: *mut crate::leanh::LeanObject,
    mut v_f_145_: *mut crate::leanh::LeanObject,
    mut v_m_146_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_147_ = l_Std_TreeMap_filterMap(
        v_00_u03b1_141_,
        v_00_u03b2_142_,
        v_00_u03b3_143_,
        v_cmp_144_,
        v_f_145_,
        v_m_146_,
    );
    crate::leanh::lean_dec_ref(v_cmp_144_);
    return v_res_147_;
}
pub unsafe fn l_Std_TreeMap_map___redArg(
    mut v_f_148_: *mut crate::leanh::LeanObject,
    mut v_t_149_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_150_ = l_Std_DTreeMap_Internal_Impl_map___redArg(v_f_148_, v_t_149_);
    return v___x_150_;
}
pub unsafe fn l_Std_TreeMap_map(
    mut v_00_u03b1_151_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_152_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_153_: *mut crate::leanh::LeanObject,
    mut v_cmp_154_: *mut crate::leanh::LeanObject,
    mut v_f_155_: *mut crate::leanh::LeanObject,
    mut v_t_156_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_157_ = l_Std_DTreeMap_Internal_Impl_map___redArg(v_f_155_, v_t_156_);
    return v___x_157_;
}
pub unsafe fn l_Std_TreeMap_map___boxed(
    mut v_00_u03b1_158_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_159_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_160_: *mut crate::leanh::LeanObject,
    mut v_cmp_161_: *mut crate::leanh::LeanObject,
    mut v_f_162_: *mut crate::leanh::LeanObject,
    mut v_t_163_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_164_ = l_Std_TreeMap_map(
        v_00_u03b1_158_,
        v_00_u03b2_159_,
        v_00_u03b3_160_,
        v_cmp_161_,
        v_f_162_,
        v_t_163_,
    );
    crate::leanh::lean_dec_ref(v_cmp_161_);
    return v_res_164_;
}
pub unsafe fn l_Std_TreeMap_getEntryGE___redArg(
    mut v_cmp_165_: *mut crate::leanh::LeanObject,
    mut v_t_166_: *mut crate::leanh::LeanObject,
    mut v_k_167_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_168_ =
        l_Std_DTreeMap_Internal_Impl_Const_getEntryGE___redArg(v_cmp_165_, v_k_167_, v_t_166_);
    return v___x_168_;
}
pub unsafe fn l_Std_TreeMap_getEntryGE(
    mut v_00_u03b1_169_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_170_: *mut crate::leanh::LeanObject,
    mut v_cmp_171_: *mut crate::leanh::LeanObject,
    mut v_inst_172_: *mut crate::leanh::LeanObject,
    mut v_t_173_: *mut crate::leanh::LeanObject,
    mut v_k_174_: *mut crate::leanh::LeanObject,
    mut v_h_175_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_176_ =
        l_Std_DTreeMap_Internal_Impl_Const_getEntryGE___redArg(v_cmp_171_, v_k_174_, v_t_173_);
    return v___x_176_;
}
pub unsafe fn l_Std_TreeMap_getEntryGT___redArg(
    mut v_cmp_177_: *mut crate::leanh::LeanObject,
    mut v_t_178_: *mut crate::leanh::LeanObject,
    mut v_k_179_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_180_ =
        l_Std_DTreeMap_Internal_Impl_Const_getEntryGT___redArg(v_cmp_177_, v_k_179_, v_t_178_);
    return v___x_180_;
}
pub unsafe fn l_Std_TreeMap_getEntryGT(
    mut v_00_u03b1_181_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_182_: *mut crate::leanh::LeanObject,
    mut v_cmp_183_: *mut crate::leanh::LeanObject,
    mut v_inst_184_: *mut crate::leanh::LeanObject,
    mut v_t_185_: *mut crate::leanh::LeanObject,
    mut v_k_186_: *mut crate::leanh::LeanObject,
    mut v_h_187_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_188_ =
        l_Std_DTreeMap_Internal_Impl_Const_getEntryGT___redArg(v_cmp_183_, v_k_186_, v_t_185_);
    return v___x_188_;
}
pub unsafe fn l_Std_TreeMap_getEntryLE___redArg(
    mut v_cmp_189_: *mut crate::leanh::LeanObject,
    mut v_t_190_: *mut crate::leanh::LeanObject,
    mut v_k_191_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_192_ =
        l_Std_DTreeMap_Internal_Impl_Const_getEntryLE___redArg(v_cmp_189_, v_k_191_, v_t_190_);
    return v___x_192_;
}
pub unsafe fn l_Std_TreeMap_getEntryLE(
    mut v_00_u03b1_193_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_194_: *mut crate::leanh::LeanObject,
    mut v_cmp_195_: *mut crate::leanh::LeanObject,
    mut v_inst_196_: *mut crate::leanh::LeanObject,
    mut v_t_197_: *mut crate::leanh::LeanObject,
    mut v_k_198_: *mut crate::leanh::LeanObject,
    mut v_h_199_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_200_ =
        l_Std_DTreeMap_Internal_Impl_Const_getEntryLE___redArg(v_cmp_195_, v_k_198_, v_t_197_);
    return v___x_200_;
}
pub unsafe fn l_Std_TreeMap_getEntryLT___redArg(
    mut v_cmp_201_: *mut crate::leanh::LeanObject,
    mut v_t_202_: *mut crate::leanh::LeanObject,
    mut v_k_203_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_204_ =
        l_Std_DTreeMap_Internal_Impl_Const_getEntryLT___redArg(v_cmp_201_, v_k_203_, v_t_202_);
    return v___x_204_;
}
pub unsafe fn l_Std_TreeMap_getEntryLT(
    mut v_00_u03b1_205_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_206_: *mut crate::leanh::LeanObject,
    mut v_cmp_207_: *mut crate::leanh::LeanObject,
    mut v_inst_208_: *mut crate::leanh::LeanObject,
    mut v_t_209_: *mut crate::leanh::LeanObject,
    mut v_k_210_: *mut crate::leanh::LeanObject,
    mut v_h_211_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_212_ =
        l_Std_DTreeMap_Internal_Impl_Const_getEntryLT___redArg(v_cmp_207_, v_k_210_, v_t_209_);
    return v___x_212_;
}
pub unsafe fn l_Std_TreeMap_getKeyGE___redArg(
    mut v_cmp_213_: *mut crate::leanh::LeanObject,
    mut v_t_214_: *mut crate::leanh::LeanObject,
    mut v_k_215_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_216_ = l_Std_DTreeMap_Internal_Impl_getKeyGE___redArg(v_cmp_213_, v_k_215_, v_t_214_);
    return v___x_216_;
}
pub unsafe fn l_Std_TreeMap_getKeyGE(
    mut v_00_u03b1_217_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_218_: *mut crate::leanh::LeanObject,
    mut v_cmp_219_: *mut crate::leanh::LeanObject,
    mut v_inst_220_: *mut crate::leanh::LeanObject,
    mut v_t_221_: *mut crate::leanh::LeanObject,
    mut v_k_222_: *mut crate::leanh::LeanObject,
    mut v_h_223_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_224_ = l_Std_DTreeMap_Internal_Impl_getKeyGE___redArg(v_cmp_219_, v_k_222_, v_t_221_);
    return v___x_224_;
}
pub unsafe fn l_Std_TreeMap_getKeyGT___redArg(
    mut v_cmp_225_: *mut crate::leanh::LeanObject,
    mut v_t_226_: *mut crate::leanh::LeanObject,
    mut v_k_227_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_228_ = l_Std_DTreeMap_Internal_Impl_getKeyGT___redArg(v_cmp_225_, v_k_227_, v_t_226_);
    return v___x_228_;
}
pub unsafe fn l_Std_TreeMap_getKeyGT(
    mut v_00_u03b1_229_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_230_: *mut crate::leanh::LeanObject,
    mut v_cmp_231_: *mut crate::leanh::LeanObject,
    mut v_inst_232_: *mut crate::leanh::LeanObject,
    mut v_t_233_: *mut crate::leanh::LeanObject,
    mut v_k_234_: *mut crate::leanh::LeanObject,
    mut v_h_235_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_236_ = l_Std_DTreeMap_Internal_Impl_getKeyGT___redArg(v_cmp_231_, v_k_234_, v_t_233_);
    return v___x_236_;
}
pub unsafe fn l_Std_TreeMap_getKeyLE___redArg(
    mut v_cmp_237_: *mut crate::leanh::LeanObject,
    mut v_t_238_: *mut crate::leanh::LeanObject,
    mut v_k_239_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_240_ = l_Std_DTreeMap_Internal_Impl_getKeyLE___redArg(v_cmp_237_, v_k_239_, v_t_238_);
    return v___x_240_;
}
pub unsafe fn l_Std_TreeMap_getKeyLE(
    mut v_00_u03b1_241_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_242_: *mut crate::leanh::LeanObject,
    mut v_cmp_243_: *mut crate::leanh::LeanObject,
    mut v_inst_244_: *mut crate::leanh::LeanObject,
    mut v_t_245_: *mut crate::leanh::LeanObject,
    mut v_k_246_: *mut crate::leanh::LeanObject,
    mut v_h_247_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_248_ = l_Std_DTreeMap_Internal_Impl_getKeyLE___redArg(v_cmp_243_, v_k_246_, v_t_245_);
    return v___x_248_;
}
pub unsafe fn l_Std_TreeMap_getKeyLT___redArg(
    mut v_cmp_249_: *mut crate::leanh::LeanObject,
    mut v_t_250_: *mut crate::leanh::LeanObject,
    mut v_k_251_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_252_ = l_Std_DTreeMap_Internal_Impl_getKeyLT___redArg(v_cmp_249_, v_k_251_, v_t_250_);
    return v___x_252_;
}
pub unsafe fn l_Std_TreeMap_getKeyLT(
    mut v_00_u03b1_253_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_254_: *mut crate::leanh::LeanObject,
    mut v_cmp_255_: *mut crate::leanh::LeanObject,
    mut v_inst_256_: *mut crate::leanh::LeanObject,
    mut v_t_257_: *mut crate::leanh::LeanObject,
    mut v_k_258_: *mut crate::leanh::LeanObject,
    mut v_h_259_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_260_ = l_Std_DTreeMap_Internal_Impl_getKeyLT___redArg(v_cmp_255_, v_k_258_, v_t_257_);
    return v___x_260_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_TreeMap_AdditionalOperations(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_TreeMap_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_TreeMap_Raw_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_DTreeMap_AdditionalOperations(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_TreeMap_AdditionalOperations(
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
pub unsafe fn initialize_Std_Data_TreeMap_AdditionalOperations(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_TreeMap_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Data_TreeMap_Raw_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Data_DTreeMap_AdditionalOperations(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_TreeMap_AdditionalOperations(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Data_TreeMap_AdditionalOperations(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Data_TreeMap_AdditionalOperations(builtin);
}
