// Lean compiler output
// Module: Lean.Elab.BuiltinDo.Basic
// Imports: Lean.Elab.Do.Basic Lean.Parser.Do
use crate::r#gen::Init::Meta::Defs::{l_Lean_TSyntax_getId, l_Lean_mkHole};
use crate::r#gen::Init::Prelude::l_Lean_replaceRef;
use crate::r#gen::Lean::Elab::Binders::l_Lean_Elab_Term_addLocalVarInfo;
use crate::r#gen::Lean::Elab::Do::Basic::{
    initialize_Lean_Elab_Do_Basic, l_Lean_Elab_Do_elabDoElem,
    l_Lean_Elab_Do_withLCtxKeepingMutVarDefs___redArg, runtime_initialize_Lean_Elab_Do_Basic,
};
use crate::r#gen::Lean::Elab::Term::TermElabM::l_Lean_Elab_Term_elabType;
use crate::r#gen::Lean::Meta::Basic::l_Lean_Meta_getFVarFromUserName;
use crate::r#gen::Lean::Parser::Do::{
    initialize_Lean_Parser_Do, runtime_initialize_Lean_Parser_Do,
};
pub unsafe fn l_Lean_Elab_Do_elabDoIdDecl___lam__0(
    mut v___x_125_: *mut crate::leanh::LeanObject,
    mut v_x_126_: *mut crate::leanh::LeanObject,
    mut v_k_127_: *mut crate::leanh::LeanObject,
    mut v___y_128_: *mut crate::leanh::LeanObject,
    mut v___y_129_: *mut crate::leanh::LeanObject,
    mut v___y_130_: *mut crate::leanh::LeanObject,
    mut v___y_131_: *mut crate::leanh::LeanObject,
    mut v___y_132_: *mut crate::leanh::LeanObject,
    mut v___y_133_: *mut crate::leanh::LeanObject,
    mut v___y_134_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_143_: u8 = 0;
    let mut v___x_145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_147_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_136_ = l_Lean_Meta_getFVarFromUserName(
                    v___x_125_, v___y_131_, v___y_132_, v___y_133_, v___y_134_,
                );
                if crate::leanh::lean_obj_tag(v___x_136_) == 0 {
                    v_a_137_ = crate::leanh::lean_ctor_get(v___x_136_, 0);
                    crate::leanh::lean_inc(v_a_137_);
                    crate::leanh::lean_dec_ref_known(v___x_136_, 1);
                    v___x_138_ = l_Lean_Elab_Term_addLocalVarInfo(
                        v_x_126_, v_a_137_, v___y_129_, v___y_130_, v___y_131_, v___y_132_,
                        v___y_133_, v___y_134_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_138_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_138_, 1);
                        crate::leanh::lean_inc(v___y_134_);
                        crate::leanh::lean_inc_ref(v___y_133_);
                        crate::leanh::lean_inc(v___y_132_);
                        crate::leanh::lean_inc_ref(v___y_131_);
                        crate::leanh::lean_inc(v___y_130_);
                        crate::leanh::lean_inc_ref(v___y_129_);
                        crate::leanh::lean_inc_ref(v___y_128_);
                        v___x_139_ = crate::leanh::lean_apply_8(
                            v_k_127_,
                            v___y_128_,
                            v___y_129_,
                            v___y_130_,
                            v___y_131_,
                            v___y_132_,
                            v___y_133_,
                            v___y_134_,
                            crate::leanh::lean_box(0),
                        );
                        return v___x_139_;
                    } else {
                        crate::leanh::lean_dec_ref(v_k_127_);
                        v_a_140_ = crate::leanh::lean_ctor_get(v___x_138_, 0);
                        v_isSharedCheck_147_ = (!crate::leanh::lean_is_exclusive(v___x_138_)) as u8;
                        if v_isSharedCheck_147_ == 0 {
                            v___x_142_ = v___x_138_;
                            v_isShared_143_ = v_isSharedCheck_147_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_140_);
                            crate::leanh::lean_dec(v___x_138_);
                            v___x_142_ = crate::leanh::lean_box(0);
                            v_isShared_143_ = v_isSharedCheck_147_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_k_127_);
                    crate::leanh::lean_dec(v_x_126_);
                    return v___x_136_;
                }
            }
            1 => {
                if v_isShared_143_ == 0 {
                    v___x_145_ = v___x_142_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_146_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_146_, 0, v_a_140_);
                    v___x_145_ = v_reuseFailAlloc_146_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_145_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Do_elabDoIdDecl___lam__0___boxed(
    mut v___x_148_: *mut crate::leanh::LeanObject,
    mut v_x_149_: *mut crate::leanh::LeanObject,
    mut v_k_150_: *mut crate::leanh::LeanObject,
    mut v___y_151_: *mut crate::leanh::LeanObject,
    mut v___y_152_: *mut crate::leanh::LeanObject,
    mut v___y_153_: *mut crate::leanh::LeanObject,
    mut v___y_154_: *mut crate::leanh::LeanObject,
    mut v___y_155_: *mut crate::leanh::LeanObject,
    mut v___y_156_: *mut crate::leanh::LeanObject,
    mut v___y_157_: *mut crate::leanh::LeanObject,
    mut v___y_158_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_159_ = l_Lean_Elab_Do_elabDoIdDecl___lam__0(
        v___x_148_, v_x_149_, v_k_150_, v___y_151_, v___y_152_, v___y_153_, v___y_154_, v___y_155_,
        v___y_156_, v___y_157_,
    );
    crate::leanh::lean_dec(v___y_157_);
    crate::leanh::lean_dec_ref(v___y_156_);
    crate::leanh::lean_dec(v___y_155_);
    crate::leanh::lean_dec_ref(v___y_154_);
    crate::leanh::lean_dec(v___y_153_);
    crate::leanh::lean_dec_ref(v___y_152_);
    crate::leanh::lean_dec_ref(v___y_151_);
    return v_res_159_;
}
pub unsafe fn l_Lean_Elab_Do_elabDoIdDecl___lam__1(
    mut v_ref_160_: *mut crate::leanh::LeanObject,
    mut v_lctx_161_: *mut crate::leanh::LeanObject,
    mut v_a_162_: *mut crate::leanh::LeanObject,
    mut v___x_163_: *mut crate::leanh::LeanObject,
    mut v___f_164_: *mut crate::leanh::LeanObject,
    mut v___y_165_: *mut crate::leanh::LeanObject,
    mut v___y_166_: *mut crate::leanh::LeanObject,
    mut v___y_167_: *mut crate::leanh::LeanObject,
    mut v___y_168_: *mut crate::leanh::LeanObject,
    mut v___y_169_: *mut crate::leanh::LeanObject,
    mut v___y_170_: *mut crate::leanh::LeanObject,
    mut v___y_171_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fileName_173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_185_: u8 = 0;
    let mut v_cancelTk_x3f_186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_187_: u8 = 0;
    let mut v_inheritedTraceOptions_188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fileName_173_ = crate::leanh::lean_ctor_get(v___y_170_, 0);
    v_fileMap_174_ = crate::leanh::lean_ctor_get(v___y_170_, 1);
    v_options_175_ = crate::leanh::lean_ctor_get(v___y_170_, 2);
    v_currRecDepth_176_ = crate::leanh::lean_ctor_get(v___y_170_, 3);
    v_maxRecDepth_177_ = crate::leanh::lean_ctor_get(v___y_170_, 4);
    v_ref_178_ = crate::leanh::lean_ctor_get(v___y_170_, 5);
    v_currNamespace_179_ = crate::leanh::lean_ctor_get(v___y_170_, 6);
    v_openDecls_180_ = crate::leanh::lean_ctor_get(v___y_170_, 7);
    v_initHeartbeats_181_ = crate::leanh::lean_ctor_get(v___y_170_, 8);
    v_maxHeartbeats_182_ = crate::leanh::lean_ctor_get(v___y_170_, 9);
    v_quotContext_183_ = crate::leanh::lean_ctor_get(v___y_170_, 10);
    v_currMacroScope_184_ = crate::leanh::lean_ctor_get(v___y_170_, 11);
    v_diag_185_ = crate::leanh::lean_ctor_get_uint8(
        v___y_170_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_186_ = crate::leanh::lean_ctor_get(v___y_170_, 12);
    v_suppressElabErrors_187_ = crate::leanh::lean_ctor_get_uint8(
        v___y_170_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_188_ = crate::leanh::lean_ctor_get(v___y_170_, 13);
    v_ref_189_ = l_Lean_replaceRef(v_ref_160_, v_ref_178_);
    crate::leanh::lean_inc_ref(v_inheritedTraceOptions_188_);
    crate::leanh::lean_inc(v_cancelTk_x3f_186_);
    crate::leanh::lean_inc(v_currMacroScope_184_);
    crate::leanh::lean_inc(v_quotContext_183_);
    crate::leanh::lean_inc(v_maxHeartbeats_182_);
    crate::leanh::lean_inc(v_initHeartbeats_181_);
    crate::leanh::lean_inc(v_openDecls_180_);
    crate::leanh::lean_inc(v_currNamespace_179_);
    crate::leanh::lean_inc(v_maxRecDepth_177_);
    crate::leanh::lean_inc(v_currRecDepth_176_);
    crate::leanh::lean_inc_ref(v_options_175_);
    crate::leanh::lean_inc_ref(v_fileMap_174_);
    crate::leanh::lean_inc_ref(v_fileName_173_);
    v___x_190_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
    crate::leanh::lean_ctor_set(v___x_190_, 0, v_fileName_173_);
    crate::leanh::lean_ctor_set(v___x_190_, 1, v_fileMap_174_);
    crate::leanh::lean_ctor_set(v___x_190_, 2, v_options_175_);
    crate::leanh::lean_ctor_set(v___x_190_, 3, v_currRecDepth_176_);
    crate::leanh::lean_ctor_set(v___x_190_, 4, v_maxRecDepth_177_);
    crate::leanh::lean_ctor_set(v___x_190_, 5, v_ref_189_);
    crate::leanh::lean_ctor_set(v___x_190_, 6, v_currNamespace_179_);
    crate::leanh::lean_ctor_set(v___x_190_, 7, v_openDecls_180_);
    crate::leanh::lean_ctor_set(v___x_190_, 8, v_initHeartbeats_181_);
    crate::leanh::lean_ctor_set(v___x_190_, 9, v_maxHeartbeats_182_);
    crate::leanh::lean_ctor_set(v___x_190_, 10, v_quotContext_183_);
    crate::leanh::lean_ctor_set(v___x_190_, 11, v_currMacroScope_184_);
    crate::leanh::lean_ctor_set(v___x_190_, 12, v_cancelTk_x3f_186_);
    crate::leanh::lean_ctor_set(v___x_190_, 13, v_inheritedTraceOptions_188_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_190_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
        v_diag_185_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_190_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_187_,
    );
    crate::leanh::lean_inc_ref(v_a_162_);
    v___x_191_ = l_Lean_Elab_Do_withLCtxKeepingMutVarDefs___redArg(
        v_lctx_161_,
        v_a_162_,
        v___x_163_,
        v___f_164_,
        v___y_165_,
        v___y_166_,
        v___y_167_,
        v___y_168_,
        v___y_169_,
        v___x_190_,
        v___y_171_,
    );
    crate::leanh::lean_dec_ref_known(v___x_190_, 14);
    return v___x_191_;
}
pub unsafe fn l_Lean_Elab_Do_elabDoIdDecl___lam__1___boxed(
    mut v_ref_192_: *mut crate::leanh::LeanObject,
    mut v_lctx_193_: *mut crate::leanh::LeanObject,
    mut v_a_194_: *mut crate::leanh::LeanObject,
    mut v___x_195_: *mut crate::leanh::LeanObject,
    mut v___f_196_: *mut crate::leanh::LeanObject,
    mut v___y_197_: *mut crate::leanh::LeanObject,
    mut v___y_198_: *mut crate::leanh::LeanObject,
    mut v___y_199_: *mut crate::leanh::LeanObject,
    mut v___y_200_: *mut crate::leanh::LeanObject,
    mut v___y_201_: *mut crate::leanh::LeanObject,
    mut v___y_202_: *mut crate::leanh::LeanObject,
    mut v___y_203_: *mut crate::leanh::LeanObject,
    mut v___y_204_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_205_ = l_Lean_Elab_Do_elabDoIdDecl___lam__1(
        v_ref_192_,
        v_lctx_193_,
        v_a_194_,
        v___x_195_,
        v___f_196_,
        v___y_197_,
        v___y_198_,
        v___y_199_,
        v___y_200_,
        v___y_201_,
        v___y_202_,
        v___y_203_,
    );
    crate::leanh::lean_dec(v___y_203_);
    crate::leanh::lean_dec_ref(v___y_202_);
    crate::leanh::lean_dec(v___y_201_);
    crate::leanh::lean_dec_ref(v___y_200_);
    crate::leanh::lean_dec(v___y_199_);
    crate::leanh::lean_dec_ref(v___y_198_);
    crate::leanh::lean_dec_ref(v___y_197_);
    crate::leanh::lean_dec_ref(v_a_194_);
    crate::leanh::lean_dec(v_ref_192_);
    return v_res_205_;
}
pub unsafe fn l_Lean_Elab_Do_elabDoIdDecl(
    mut v_x_206_: *mut crate::leanh::LeanObject,
    mut v_xType_x3f_207_: *mut crate::leanh::LeanObject,
    mut v_rhs_208_: *mut crate::leanh::LeanObject,
    mut v_k_209_: *mut crate::leanh::LeanObject,
    mut v_kind_210_: u8,
    mut v_a_211_: *mut crate::leanh::LeanObject,
    mut v_a_212_: *mut crate::leanh::LeanObject,
    mut v_a_213_: *mut crate::leanh::LeanObject,
    mut v_a_214_: *mut crate::leanh::LeanObject,
    mut v_a_215_: *mut crate::leanh::LeanObject,
    mut v_a_216_: *mut crate::leanh::LeanObject,
    mut v_a_217_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_229_: u8 = 0;
    let mut v___x_230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_231_: u8 = 0;
    let mut v___x_232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_xType_x3f_207_) == 0 {
                    v___x_231_ = 0;
                    v___x_232_ = l_Lean_mkHole(v_x_206_, v___x_231_);
                    v___y_220_ = v___x_232_;
                    state = 1;
                    continue;
                } else {
                    v_val_233_ = crate::leanh::lean_ctor_get(v_xType_x3f_207_, 0);
                    crate::leanh::lean_inc(v_val_233_);
                    crate::leanh::lean_dec_ref_known(v_xType_x3f_207_, 1);
                    v___y_220_ = v_val_233_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_221_ = l_Lean_Elab_Term_elabType(
                    v___y_220_, v_a_212_, v_a_213_, v_a_214_, v_a_215_, v_a_216_, v_a_217_,
                );
                if crate::leanh::lean_obj_tag(v___x_221_) == 0 {
                    v_a_222_ = crate::leanh::lean_ctor_get(v___x_221_, 0);
                    crate::leanh::lean_inc(v_a_222_);
                    crate::leanh::lean_dec_ref_known(v___x_221_, 1);
                    v_lctx_223_ = crate::leanh::lean_ctor_get(v_a_214_, 2);
                    v_ref_224_ = crate::leanh::lean_ctor_get(v_a_216_, 5);
                    v___x_225_ = l_Lean_TSyntax_getId(v_x_206_);
                    crate::leanh::lean_inc_n(v___x_225_, 2);
                    v___f_226_ = crate::leanh::lean_alloc_closure(
                        l_Lean_Elab_Do_elabDoIdDecl___lam__0___boxed as *mut core::ffi::c_void,
                        11,
                        3,
                    );
                    crate::leanh::lean_closure_set(v___f_226_, 0, v___x_225_);
                    crate::leanh::lean_closure_set(v___f_226_, 1, v_x_206_);
                    crate::leanh::lean_closure_set(v___f_226_, 2, v_k_209_);
                    crate::leanh::lean_inc_ref(v_a_211_);
                    crate::leanh::lean_inc_ref(v_lctx_223_);
                    crate::leanh::lean_inc(v_ref_224_);
                    v___f_227_ = crate::leanh::lean_alloc_closure(
                        l_Lean_Elab_Do_elabDoIdDecl___lam__1___boxed as *mut core::ffi::c_void,
                        13,
                        5,
                    );
                    crate::leanh::lean_closure_set(v___f_227_, 0, v_ref_224_);
                    crate::leanh::lean_closure_set(v___f_227_, 1, v_lctx_223_);
                    crate::leanh::lean_closure_set(v___f_227_, 2, v_a_211_);
                    crate::leanh::lean_closure_set(v___f_227_, 3, v___x_225_);
                    crate::leanh::lean_closure_set(v___f_227_, 4, v___f_226_);
                    v___x_228_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_228_, 0, v___x_225_);
                    crate::leanh::lean_ctor_set(v___x_228_, 1, v_a_222_);
                    crate::leanh::lean_ctor_set(v___x_228_, 2, v___f_227_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_228_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_kind_210_,
                    );
                    v___x_229_ = 1;
                    v___x_230_ = l_Lean_Elab_Do_elabDoElem(
                        v_rhs_208_, v___x_228_, v___x_229_, v_a_211_, v_a_212_, v_a_213_, v_a_214_,
                        v_a_215_, v_a_216_, v_a_217_,
                    );
                    return v___x_230_;
                } else {
                    crate::leanh::lean_dec_ref(v_k_209_);
                    crate::leanh::lean_dec(v_rhs_208_);
                    crate::leanh::lean_dec(v_x_206_);
                    return v___x_221_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Do_elabDoIdDecl___boxed(
    mut v_x_234_: *mut crate::leanh::LeanObject,
    mut v_xType_x3f_235_: *mut crate::leanh::LeanObject,
    mut v_rhs_236_: *mut crate::leanh::LeanObject,
    mut v_k_237_: *mut crate::leanh::LeanObject,
    mut v_kind_238_: *mut crate::leanh::LeanObject,
    mut v_a_239_: *mut crate::leanh::LeanObject,
    mut v_a_240_: *mut crate::leanh::LeanObject,
    mut v_a_241_: *mut crate::leanh::LeanObject,
    mut v_a_242_: *mut crate::leanh::LeanObject,
    mut v_a_243_: *mut crate::leanh::LeanObject,
    mut v_a_244_: *mut crate::leanh::LeanObject,
    mut v_a_245_: *mut crate::leanh::LeanObject,
    mut v_a_246_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_kind_boxed_247_: u8 = 0;
    let mut v_res_248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_kind_boxed_247_ = (crate::leanh::lean_unbox(v_kind_238_) as u8);
    v_res_248_ = l_Lean_Elab_Do_elabDoIdDecl(
        v_x_234_,
        v_xType_x3f_235_,
        v_rhs_236_,
        v_k_237_,
        v_kind_boxed_247_,
        v_a_239_,
        v_a_240_,
        v_a_241_,
        v_a_242_,
        v_a_243_,
        v_a_244_,
        v_a_245_,
    );
    crate::leanh::lean_dec(v_a_245_);
    crate::leanh::lean_dec_ref(v_a_244_);
    crate::leanh::lean_dec(v_a_243_);
    crate::leanh::lean_dec_ref(v_a_242_);
    crate::leanh::lean_dec(v_a_241_);
    crate::leanh::lean_dec_ref(v_a_240_);
    crate::leanh::lean_dec_ref(v_a_239_);
    return v_res_248_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_BuiltinDo_Basic(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Do_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_BuiltinDo_Basic(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    res = runtime_initialize_Lean_Parser_Do(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_BuiltinDo_Basic(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Do_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Parser_Do(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_BuiltinDo_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_BuiltinDo_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_BuiltinDo_Basic(builtin);
}
