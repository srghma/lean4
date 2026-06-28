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
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_box, lean_dec_ref, lean_io_result_is_error,
    lean_io_result_mk_ok,
};
pub unsafe fn l_Std_TreeMap_filterMap___redArg(
    mut v_f_131_: *mut LeanObject,
    mut v_m_132_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_133_: *mut LeanObject = core::ptr::null_mut();
    v___x_133_ = l_Std_DTreeMap_Internal_Impl_filterMap___redArg(v_f_131_, v_m_132_);
    return v___x_133_;
}
pub unsafe fn l_Std_TreeMap_filterMap(
    mut v_00_u03b1_134_: *mut LeanObject,
    mut v_00_u03b2_135_: *mut LeanObject,
    mut v_00_u03b3_136_: *mut LeanObject,
    mut v_cmp_137_: *mut LeanObject,
    mut v_f_138_: *mut LeanObject,
    mut v_m_139_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_140_: *mut LeanObject = core::ptr::null_mut();
    v___x_140_ = l_Std_DTreeMap_Internal_Impl_filterMap___redArg(v_f_138_, v_m_139_);
    return v___x_140_;
}
pub unsafe fn l_Std_TreeMap_filterMap___boxed(
    mut v_00_u03b1_141_: *mut LeanObject,
    mut v_00_u03b2_142_: *mut LeanObject,
    mut v_00_u03b3_143_: *mut LeanObject,
    mut v_cmp_144_: *mut LeanObject,
    mut v_f_145_: *mut LeanObject,
    mut v_m_146_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_147_: *mut LeanObject = core::ptr::null_mut();
    v_res_147_ = l_Std_TreeMap_filterMap(
        v_00_u03b1_141_,
        v_00_u03b2_142_,
        v_00_u03b3_143_,
        v_cmp_144_,
        v_f_145_,
        v_m_146_,
    );
    lean_dec_ref(v_cmp_144_);
    return v_res_147_;
}
pub unsafe fn l_Std_TreeMap_map___redArg(
    mut v_f_148_: *mut LeanObject,
    mut v_t_149_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_150_: *mut LeanObject = core::ptr::null_mut();
    v___x_150_ = l_Std_DTreeMap_Internal_Impl_map___redArg(v_f_148_, v_t_149_);
    return v___x_150_;
}
pub unsafe fn l_Std_TreeMap_map(
    mut v_00_u03b1_151_: *mut LeanObject,
    mut v_00_u03b2_152_: *mut LeanObject,
    mut v_00_u03b3_153_: *mut LeanObject,
    mut v_cmp_154_: *mut LeanObject,
    mut v_f_155_: *mut LeanObject,
    mut v_t_156_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_157_: *mut LeanObject = core::ptr::null_mut();
    v___x_157_ = l_Std_DTreeMap_Internal_Impl_map___redArg(v_f_155_, v_t_156_);
    return v___x_157_;
}
pub unsafe fn l_Std_TreeMap_map___boxed(
    mut v_00_u03b1_158_: *mut LeanObject,
    mut v_00_u03b2_159_: *mut LeanObject,
    mut v_00_u03b3_160_: *mut LeanObject,
    mut v_cmp_161_: *mut LeanObject,
    mut v_f_162_: *mut LeanObject,
    mut v_t_163_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_164_: *mut LeanObject = core::ptr::null_mut();
    v_res_164_ = l_Std_TreeMap_map(
        v_00_u03b1_158_,
        v_00_u03b2_159_,
        v_00_u03b3_160_,
        v_cmp_161_,
        v_f_162_,
        v_t_163_,
    );
    lean_dec_ref(v_cmp_161_);
    return v_res_164_;
}
pub unsafe fn l_Std_TreeMap_getEntryGE___redArg(
    mut v_cmp_165_: *mut LeanObject,
    mut v_t_166_: *mut LeanObject,
    mut v_k_167_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_168_: *mut LeanObject = core::ptr::null_mut();
    v___x_168_ =
        l_Std_DTreeMap_Internal_Impl_Const_getEntryGE___redArg(v_cmp_165_, v_k_167_, v_t_166_);
    return v___x_168_;
}
pub unsafe fn l_Std_TreeMap_getEntryGE(
    mut v_00_u03b1_169_: *mut LeanObject,
    mut v_00_u03b2_170_: *mut LeanObject,
    mut v_cmp_171_: *mut LeanObject,
    mut v_inst_172_: *mut LeanObject,
    mut v_t_173_: *mut LeanObject,
    mut v_k_174_: *mut LeanObject,
    mut v_h_175_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_176_: *mut LeanObject = core::ptr::null_mut();
    v___x_176_ =
        l_Std_DTreeMap_Internal_Impl_Const_getEntryGE___redArg(v_cmp_171_, v_k_174_, v_t_173_);
    return v___x_176_;
}
pub unsafe fn l_Std_TreeMap_getEntryGT___redArg(
    mut v_cmp_177_: *mut LeanObject,
    mut v_t_178_: *mut LeanObject,
    mut v_k_179_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_180_: *mut LeanObject = core::ptr::null_mut();
    v___x_180_ =
        l_Std_DTreeMap_Internal_Impl_Const_getEntryGT___redArg(v_cmp_177_, v_k_179_, v_t_178_);
    return v___x_180_;
}
pub unsafe fn l_Std_TreeMap_getEntryGT(
    mut v_00_u03b1_181_: *mut LeanObject,
    mut v_00_u03b2_182_: *mut LeanObject,
    mut v_cmp_183_: *mut LeanObject,
    mut v_inst_184_: *mut LeanObject,
    mut v_t_185_: *mut LeanObject,
    mut v_k_186_: *mut LeanObject,
    mut v_h_187_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_188_: *mut LeanObject = core::ptr::null_mut();
    v___x_188_ =
        l_Std_DTreeMap_Internal_Impl_Const_getEntryGT___redArg(v_cmp_183_, v_k_186_, v_t_185_);
    return v___x_188_;
}
pub unsafe fn l_Std_TreeMap_getEntryLE___redArg(
    mut v_cmp_189_: *mut LeanObject,
    mut v_t_190_: *mut LeanObject,
    mut v_k_191_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_192_: *mut LeanObject = core::ptr::null_mut();
    v___x_192_ =
        l_Std_DTreeMap_Internal_Impl_Const_getEntryLE___redArg(v_cmp_189_, v_k_191_, v_t_190_);
    return v___x_192_;
}
pub unsafe fn l_Std_TreeMap_getEntryLE(
    mut v_00_u03b1_193_: *mut LeanObject,
    mut v_00_u03b2_194_: *mut LeanObject,
    mut v_cmp_195_: *mut LeanObject,
    mut v_inst_196_: *mut LeanObject,
    mut v_t_197_: *mut LeanObject,
    mut v_k_198_: *mut LeanObject,
    mut v_h_199_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_200_: *mut LeanObject = core::ptr::null_mut();
    v___x_200_ =
        l_Std_DTreeMap_Internal_Impl_Const_getEntryLE___redArg(v_cmp_195_, v_k_198_, v_t_197_);
    return v___x_200_;
}
pub unsafe fn l_Std_TreeMap_getEntryLT___redArg(
    mut v_cmp_201_: *mut LeanObject,
    mut v_t_202_: *mut LeanObject,
    mut v_k_203_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_204_: *mut LeanObject = core::ptr::null_mut();
    v___x_204_ =
        l_Std_DTreeMap_Internal_Impl_Const_getEntryLT___redArg(v_cmp_201_, v_k_203_, v_t_202_);
    return v___x_204_;
}
pub unsafe fn l_Std_TreeMap_getEntryLT(
    mut v_00_u03b1_205_: *mut LeanObject,
    mut v_00_u03b2_206_: *mut LeanObject,
    mut v_cmp_207_: *mut LeanObject,
    mut v_inst_208_: *mut LeanObject,
    mut v_t_209_: *mut LeanObject,
    mut v_k_210_: *mut LeanObject,
    mut v_h_211_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_212_: *mut LeanObject = core::ptr::null_mut();
    v___x_212_ =
        l_Std_DTreeMap_Internal_Impl_Const_getEntryLT___redArg(v_cmp_207_, v_k_210_, v_t_209_);
    return v___x_212_;
}
pub unsafe fn l_Std_TreeMap_getKeyGE___redArg(
    mut v_cmp_213_: *mut LeanObject,
    mut v_t_214_: *mut LeanObject,
    mut v_k_215_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_216_: *mut LeanObject = core::ptr::null_mut();
    v___x_216_ = l_Std_DTreeMap_Internal_Impl_getKeyGE___redArg(v_cmp_213_, v_k_215_, v_t_214_);
    return v___x_216_;
}
pub unsafe fn l_Std_TreeMap_getKeyGE(
    mut v_00_u03b1_217_: *mut LeanObject,
    mut v_00_u03b2_218_: *mut LeanObject,
    mut v_cmp_219_: *mut LeanObject,
    mut v_inst_220_: *mut LeanObject,
    mut v_t_221_: *mut LeanObject,
    mut v_k_222_: *mut LeanObject,
    mut v_h_223_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_224_: *mut LeanObject = core::ptr::null_mut();
    v___x_224_ = l_Std_DTreeMap_Internal_Impl_getKeyGE___redArg(v_cmp_219_, v_k_222_, v_t_221_);
    return v___x_224_;
}
pub unsafe fn l_Std_TreeMap_getKeyGT___redArg(
    mut v_cmp_225_: *mut LeanObject,
    mut v_t_226_: *mut LeanObject,
    mut v_k_227_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_228_: *mut LeanObject = core::ptr::null_mut();
    v___x_228_ = l_Std_DTreeMap_Internal_Impl_getKeyGT___redArg(v_cmp_225_, v_k_227_, v_t_226_);
    return v___x_228_;
}
pub unsafe fn l_Std_TreeMap_getKeyGT(
    mut v_00_u03b1_229_: *mut LeanObject,
    mut v_00_u03b2_230_: *mut LeanObject,
    mut v_cmp_231_: *mut LeanObject,
    mut v_inst_232_: *mut LeanObject,
    mut v_t_233_: *mut LeanObject,
    mut v_k_234_: *mut LeanObject,
    mut v_h_235_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_236_: *mut LeanObject = core::ptr::null_mut();
    v___x_236_ = l_Std_DTreeMap_Internal_Impl_getKeyGT___redArg(v_cmp_231_, v_k_234_, v_t_233_);
    return v___x_236_;
}
pub unsafe fn l_Std_TreeMap_getKeyLE___redArg(
    mut v_cmp_237_: *mut LeanObject,
    mut v_t_238_: *mut LeanObject,
    mut v_k_239_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_240_: *mut LeanObject = core::ptr::null_mut();
    v___x_240_ = l_Std_DTreeMap_Internal_Impl_getKeyLE___redArg(v_cmp_237_, v_k_239_, v_t_238_);
    return v___x_240_;
}
pub unsafe fn l_Std_TreeMap_getKeyLE(
    mut v_00_u03b1_241_: *mut LeanObject,
    mut v_00_u03b2_242_: *mut LeanObject,
    mut v_cmp_243_: *mut LeanObject,
    mut v_inst_244_: *mut LeanObject,
    mut v_t_245_: *mut LeanObject,
    mut v_k_246_: *mut LeanObject,
    mut v_h_247_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_248_: *mut LeanObject = core::ptr::null_mut();
    v___x_248_ = l_Std_DTreeMap_Internal_Impl_getKeyLE___redArg(v_cmp_243_, v_k_246_, v_t_245_);
    return v___x_248_;
}
pub unsafe fn l_Std_TreeMap_getKeyLT___redArg(
    mut v_cmp_249_: *mut LeanObject,
    mut v_t_250_: *mut LeanObject,
    mut v_k_251_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_252_: *mut LeanObject = core::ptr::null_mut();
    v___x_252_ = l_Std_DTreeMap_Internal_Impl_getKeyLT___redArg(v_cmp_249_, v_k_251_, v_t_250_);
    return v___x_252_;
}
pub unsafe fn l_Std_TreeMap_getKeyLT(
    mut v_00_u03b1_253_: *mut LeanObject,
    mut v_00_u03b2_254_: *mut LeanObject,
    mut v_cmp_255_: *mut LeanObject,
    mut v_inst_256_: *mut LeanObject,
    mut v_t_257_: *mut LeanObject,
    mut v_k_258_: *mut LeanObject,
    mut v_h_259_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_260_: *mut LeanObject = core::ptr::null_mut();
    v___x_260_ = l_Std_DTreeMap_Internal_Impl_getKeyLT___redArg(v_cmp_255_, v_k_258_, v_t_257_);
    return v___x_260_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_TreeMap_AdditionalOperations(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_TreeMap_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_TreeMap_Raw_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_DTreeMap_AdditionalOperations(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_TreeMap_AdditionalOperations(
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
pub unsafe fn initialize_Std_Data_TreeMap_AdditionalOperations(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_TreeMap_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Data_TreeMap_Raw_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Data_DTreeMap_AdditionalOperations(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_TreeMap_AdditionalOperations(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Data_TreeMap_AdditionalOperations(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Data_TreeMap_AdditionalOperations(builtin);
}
