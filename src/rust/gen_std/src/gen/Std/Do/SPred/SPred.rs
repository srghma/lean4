// Lean compiler output
// Module: Std.Do.SPred.SPred
// Imports: Init.Ext Std.Do.SPred.SVal Init.NotationExtra
use crate::r#gen::Init::Ext::{initialize_Init_Ext, runtime_initialize_Init_Ext};
use crate::r#gen::Init::NotationExtra::{
    initialize_Init_NotationExtra, runtime_initialize_Init_NotationExtra,
};
use crate::r#gen::Std::Do::SPred::SVal::{
    initialize_Std_Do_SPred_SVal, runtime_initialize_Std_Do_SPred_SVal,
};
pub unsafe fn l_Std_Do_SPred_pure___redArg___lam__0___boxed(
    mut v_tail_139_: *mut leanh::LeanObject,
    mut v___y_140_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_141_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_141_ = l_Std_Do_SPred_pure___redArg___lam__0(v_tail_139_, v___y_140_);
    leanh::lean_dec(v___y_140_);
    return v_res_141_;
}
pub unsafe fn l_Std_Do_SPred_pure___redArg(
    mut v_00_u03c3s_142_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_00_u03c3s_142_) == 0 {
        let mut v___x_143_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_143_ = leanh::lean_box(0);
        return v___x_143_;
    } else {
        let mut v_tail_144_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_145_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_tail_144_ = leanh::lean_ctor_get(v_00_u03c3s_142_, 1);
        leanh::lean_inc(v_tail_144_);
        leanh::lean_dec_ref_known(v_00_u03c3s_142_, 2);
        v___f_145_ = leanh::lean_alloc_closure(
            l_Std_Do_SPred_pure___redArg___lam__0___boxed as *mut core::ffi::c_void,
            2,
            1,
        );
        leanh::lean_closure_set(v___f_145_, 0, v_tail_144_);
        return v___f_145_;
    }
}
pub unsafe fn l_Std_Do_SPred_pure___redArg___lam__0(
    mut v_tail_146_: *mut leanh::LeanObject,
    mut v___y_147_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_148_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_148_ = l_Std_Do_SPred_pure___redArg(v_tail_146_);
    return v___x_148_;
}
pub unsafe fn l_Std_Do_SPred_pure(
    mut v_00_u03c3s_149_: *mut leanh::LeanObject,
    mut v_P_150_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_151_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_151_ = l_Std_Do_SPred_pure___redArg(v_00_u03c3s_149_);
    return v___x_151_;
}
pub unsafe fn l_Std_Do_SPred_and(
    mut v_00_u03c3s_152_: *mut leanh::LeanObject,
    mut v_P_153_: *mut leanh::LeanObject,
    mut v_Q_154_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_00_u03c3s_152_) == 0 {
        let mut v___x_155_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_Q_154_);
        leanh::lean_dec(v_P_153_);
        v___x_155_ = leanh::lean_box(0);
        return v___x_155_;
    } else {
        let mut v_tail_156_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_157_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_tail_156_ = leanh::lean_ctor_get(v_00_u03c3s_152_, 1);
        leanh::lean_inc(v_tail_156_);
        leanh::lean_dec_ref_known(v_00_u03c3s_152_, 2);
        v___f_157_ = leanh::lean_alloc_closure(
            l_Std_Do_SPred_and___lam__0 as *mut core::ffi::c_void,
            4,
            3,
        );
        leanh::lean_closure_set(v___f_157_, 0, v_P_153_);
        leanh::lean_closure_set(v___f_157_, 1, v_Q_154_);
        leanh::lean_closure_set(v___f_157_, 2, v_tail_156_);
        return v___f_157_;
    }
}
pub unsafe fn l_Std_Do_SPred_and___lam__0(
    mut v_P_158_: *mut leanh::LeanObject,
    mut v_Q_159_: *mut leanh::LeanObject,
    mut v_tail_160_: *mut leanh::LeanObject,
    mut v___y_161_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_164_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v___y_161_);
    v___x_162_ = leanh::lean_apply_1(v_P_158_, v___y_161_);
    v___x_163_ = leanh::lean_apply_1(v_Q_159_, v___y_161_);
    v___x_164_ = l_Std_Do_SPred_and(v_tail_160_, v___x_162_, v___x_163_);
    return v___x_164_;
}
pub unsafe fn l_Std_Do_SPred_or(
    mut v_00_u03c3s_165_: *mut leanh::LeanObject,
    mut v_P_166_: *mut leanh::LeanObject,
    mut v_Q_167_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_00_u03c3s_165_) == 0 {
        let mut v___x_168_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_Q_167_);
        leanh::lean_dec(v_P_166_);
        v___x_168_ = leanh::lean_box(0);
        return v___x_168_;
    } else {
        let mut v_tail_169_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_170_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_tail_169_ = leanh::lean_ctor_get(v_00_u03c3s_165_, 1);
        leanh::lean_inc(v_tail_169_);
        leanh::lean_dec_ref_known(v_00_u03c3s_165_, 2);
        v___f_170_ = leanh::lean_alloc_closure(
            l_Std_Do_SPred_or___lam__0 as *mut core::ffi::c_void,
            4,
            3,
        );
        leanh::lean_closure_set(v___f_170_, 0, v_P_166_);
        leanh::lean_closure_set(v___f_170_, 1, v_Q_167_);
        leanh::lean_closure_set(v___f_170_, 2, v_tail_169_);
        return v___f_170_;
    }
}
pub unsafe fn l_Std_Do_SPred_or___lam__0(
    mut v_P_171_: *mut leanh::LeanObject,
    mut v_Q_172_: *mut leanh::LeanObject,
    mut v_tail_173_: *mut leanh::LeanObject,
    mut v___y_174_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_177_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v___y_174_);
    v___x_175_ = leanh::lean_apply_1(v_P_171_, v___y_174_);
    v___x_176_ = leanh::lean_apply_1(v_Q_172_, v___y_174_);
    v___x_177_ = l_Std_Do_SPred_or(v_tail_173_, v___x_175_, v___x_176_);
    return v___x_177_;
}
pub unsafe fn l_Std_Do_SPred_not(
    mut v_00_u03c3s_178_: *mut leanh::LeanObject,
    mut v_P_179_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_00_u03c3s_178_) == 0 {
        let mut v___x_180_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_P_179_);
        v___x_180_ = leanh::lean_box(0);
        return v___x_180_;
    } else {
        let mut v_tail_181_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_182_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_tail_181_ = leanh::lean_ctor_get(v_00_u03c3s_178_, 1);
        leanh::lean_inc(v_tail_181_);
        leanh::lean_dec_ref_known(v_00_u03c3s_178_, 2);
        v___f_182_ = leanh::lean_alloc_closure(
            l_Std_Do_SPred_not___lam__0 as *mut core::ffi::c_void,
            3,
            2,
        );
        leanh::lean_closure_set(v___f_182_, 0, v_P_179_);
        leanh::lean_closure_set(v___f_182_, 1, v_tail_181_);
        return v___f_182_;
    }
}
pub unsafe fn l_Std_Do_SPred_not___lam__0(
    mut v_P_183_: *mut leanh::LeanObject,
    mut v_tail_184_: *mut leanh::LeanObject,
    mut v___y_185_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_187_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_186_ = leanh::lean_apply_1(v_P_183_, v___y_185_);
    v___x_187_ = l_Std_Do_SPred_not(v_tail_184_, v___x_186_);
    return v___x_187_;
}
pub unsafe fn l_Std_Do_SPred_imp(
    mut v_00_u03c3s_188_: *mut leanh::LeanObject,
    mut v_P_189_: *mut leanh::LeanObject,
    mut v_Q_190_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_00_u03c3s_188_) == 0 {
        let mut v___x_191_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_Q_190_);
        leanh::lean_dec(v_P_189_);
        v___x_191_ = leanh::lean_box(0);
        return v___x_191_;
    } else {
        let mut v_tail_192_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_193_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_tail_192_ = leanh::lean_ctor_get(v_00_u03c3s_188_, 1);
        leanh::lean_inc(v_tail_192_);
        leanh::lean_dec_ref_known(v_00_u03c3s_188_, 2);
        v___f_193_ = leanh::lean_alloc_closure(
            l_Std_Do_SPred_imp___lam__0 as *mut core::ffi::c_void,
            4,
            3,
        );
        leanh::lean_closure_set(v___f_193_, 0, v_P_189_);
        leanh::lean_closure_set(v___f_193_, 1, v_Q_190_);
        leanh::lean_closure_set(v___f_193_, 2, v_tail_192_);
        return v___f_193_;
    }
}
pub unsafe fn l_Std_Do_SPred_imp___lam__0(
    mut v_P_194_: *mut leanh::LeanObject,
    mut v_Q_195_: *mut leanh::LeanObject,
    mut v_tail_196_: *mut leanh::LeanObject,
    mut v___y_197_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_200_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v___y_197_);
    v___x_198_ = leanh::lean_apply_1(v_P_194_, v___y_197_);
    v___x_199_ = leanh::lean_apply_1(v_Q_195_, v___y_197_);
    v___x_200_ = l_Std_Do_SPred_imp(v_tail_196_, v___x_198_, v___x_199_);
    return v___x_200_;
}
pub unsafe fn l_Std_Do_SPred_iff(
    mut v_00_u03c3s_201_: *mut leanh::LeanObject,
    mut v_P_202_: *mut leanh::LeanObject,
    mut v_Q_203_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_00_u03c3s_201_) == 0 {
        let mut v___x_204_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_Q_203_);
        leanh::lean_dec(v_P_202_);
        v___x_204_ = leanh::lean_box(0);
        return v___x_204_;
    } else {
        let mut v_tail_205_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_206_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_tail_205_ = leanh::lean_ctor_get(v_00_u03c3s_201_, 1);
        leanh::lean_inc(v_tail_205_);
        leanh::lean_dec_ref_known(v_00_u03c3s_201_, 2);
        v___f_206_ = leanh::lean_alloc_closure(
            l_Std_Do_SPred_iff___lam__0 as *mut core::ffi::c_void,
            4,
            3,
        );
        leanh::lean_closure_set(v___f_206_, 0, v_P_202_);
        leanh::lean_closure_set(v___f_206_, 1, v_Q_203_);
        leanh::lean_closure_set(v___f_206_, 2, v_tail_205_);
        return v___f_206_;
    }
}
pub unsafe fn l_Std_Do_SPred_iff___lam__0(
    mut v_P_207_: *mut leanh::LeanObject,
    mut v_Q_208_: *mut leanh::LeanObject,
    mut v_tail_209_: *mut leanh::LeanObject,
    mut v___y_210_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_213_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v___y_210_);
    v___x_211_ = leanh::lean_apply_1(v_P_207_, v___y_210_);
    v___x_212_ = leanh::lean_apply_1(v_Q_208_, v___y_210_);
    v___x_213_ = l_Std_Do_SPred_iff(v_tail_209_, v___x_211_, v___x_212_);
    return v___x_213_;
}
pub unsafe fn l_Std_Do_SPred_exists___redArg___lam__0(
    mut v_P_214_: *mut leanh::LeanObject,
    mut v___y_215_: *mut leanh::LeanObject,
    mut v_a_216_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_217_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_217_ = leanh::lean_apply_2(v_P_214_, v_a_216_, v___y_215_);
    return v___x_217_;
}
pub unsafe fn l_Std_Do_SPred_exists___redArg(
    mut v_00_u03c3s_218_: *mut leanh::LeanObject,
    mut v_P_219_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_00_u03c3s_218_) == 0 {
        let mut v___x_220_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_P_219_);
        v___x_220_ = leanh::lean_box(0);
        return v___x_220_;
    } else {
        let mut v_tail_221_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_222_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_tail_221_ = leanh::lean_ctor_get(v_00_u03c3s_218_, 1);
        leanh::lean_inc(v_tail_221_);
        leanh::lean_dec_ref_known(v_00_u03c3s_218_, 2);
        v___f_222_ = leanh::lean_alloc_closure(
            l_Std_Do_SPred_exists___redArg___lam__1 as *mut core::ffi::c_void,
            3,
            2,
        );
        leanh::lean_closure_set(v___f_222_, 0, v_P_219_);
        leanh::lean_closure_set(v___f_222_, 1, v_tail_221_);
        return v___f_222_;
    }
}
pub unsafe fn l_Std_Do_SPred_exists___redArg___lam__1(
    mut v_P_223_: *mut leanh::LeanObject,
    mut v_tail_224_: *mut leanh::LeanObject,
    mut v___y_225_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_227_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_226_ = leanh::lean_alloc_closure(
        l_Std_Do_SPred_exists___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_226_, 0, v_P_223_);
    leanh::lean_closure_set(v___f_226_, 1, v___y_225_);
    v___x_227_ = l_Std_Do_SPred_exists___redArg(v_tail_224_, v___f_226_);
    return v___x_227_;
}
pub unsafe fn l_Std_Do_SPred_exists(
    mut v_00_u03b1_228_: *mut leanh::LeanObject,
    mut v_00_u03c3s_229_: *mut leanh::LeanObject,
    mut v_P_230_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_231_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_231_ = l_Std_Do_SPred_exists___redArg(v_00_u03c3s_229_, v_P_230_);
    return v___x_231_;
}
pub unsafe fn l_Std_Do_SPred_forall___redArg(
    mut v_00_u03c3s_232_: *mut leanh::LeanObject,
    mut v_P_233_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_00_u03c3s_232_) == 0 {
        let mut v___x_234_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_P_233_);
        v___x_234_ = leanh::lean_box(0);
        return v___x_234_;
    } else {
        let mut v_tail_235_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_236_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_tail_235_ = leanh::lean_ctor_get(v_00_u03c3s_232_, 1);
        leanh::lean_inc(v_tail_235_);
        leanh::lean_dec_ref_known(v_00_u03c3s_232_, 2);
        v___f_236_ = leanh::lean_alloc_closure(
            l_Std_Do_SPred_forall___redArg___lam__1 as *mut core::ffi::c_void,
            3,
            2,
        );
        leanh::lean_closure_set(v___f_236_, 0, v_P_233_);
        leanh::lean_closure_set(v___f_236_, 1, v_tail_235_);
        return v___f_236_;
    }
}
pub unsafe fn l_Std_Do_SPred_forall___redArg___lam__1(
    mut v_P_237_: *mut leanh::LeanObject,
    mut v_tail_238_: *mut leanh::LeanObject,
    mut v___y_239_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_241_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_240_ = leanh::lean_alloc_closure(
        l_Std_Do_SPred_exists___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_240_, 0, v_P_237_);
    leanh::lean_closure_set(v___f_240_, 1, v___y_239_);
    v___x_241_ = l_Std_Do_SPred_forall___redArg(v_tail_238_, v___f_240_);
    return v___x_241_;
}
pub unsafe fn l_Std_Do_SPred_forall(
    mut v_00_u03b1_242_: *mut leanh::LeanObject,
    mut v_00_u03c3s_243_: *mut leanh::LeanObject,
    mut v_P_244_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_245_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_245_ = l_Std_Do_SPred_forall___redArg(v_00_u03c3s_243_, v_P_244_);
    return v___x_245_;
}
pub unsafe fn l_Std_Do_SPred_conjunction(
    mut v_00_u03c3s_246_: *mut leanh::LeanObject,
    mut v_env_247_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_env_247_) == 0 {
        let mut v___x_248_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_248_ = l_Std_Do_SPred_pure___redArg(v_00_u03c3s_246_);
        return v___x_248_;
    } else {
        let mut v_head_249_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_250_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_251_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_252_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_head_249_ = leanh::lean_ctor_get(v_env_247_, 0);
        leanh::lean_inc(v_head_249_);
        v_tail_250_ = leanh::lean_ctor_get(v_env_247_, 1);
        leanh::lean_inc(v_tail_250_);
        leanh::lean_dec_ref_known(v_env_247_, 2);
        leanh::lean_inc(v_00_u03c3s_246_);
        v___x_251_ = l_Std_Do_SPred_conjunction(v_00_u03c3s_246_, v_tail_250_);
        v___x_252_ = l_Std_Do_SPred_and(v_00_u03c3s_246_, v_head_249_, v___x_251_);
        return v___x_252_;
    }
}
pub unsafe fn l___private_Std_Do_SPred_SPred_0__Std_Do_SPred_conjunction_match__1_splitter___redArg(
    mut v_env_253_: *mut leanh::LeanObject,
    mut v_h__1_254_: *mut leanh::LeanObject,
    mut v_h__2_255_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_env_253_) == 0 {
        let mut v___x_256_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_257_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_255_);
        v___x_256_ = leanh::lean_box(0);
        v___x_257_ = leanh::lean_apply_1(v_h__1_254_, v___x_256_);
        return v___x_257_;
    } else {
        let mut v_head_258_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_259_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_260_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_254_);
        v_head_258_ = leanh::lean_ctor_get(v_env_253_, 0);
        leanh::lean_inc(v_head_258_);
        v_tail_259_ = leanh::lean_ctor_get(v_env_253_, 1);
        leanh::lean_inc(v_tail_259_);
        leanh::lean_dec_ref_known(v_env_253_, 2);
        v___x_260_ = leanh::lean_apply_2(v_h__2_255_, v_head_258_, v_tail_259_);
        return v___x_260_;
    }
}
pub unsafe fn l___private_Std_Do_SPred_SPred_0__Std_Do_SPred_conjunction_match__1_splitter(
    mut v_00_u03c3s_261_: *mut leanh::LeanObject,
    mut v_motive_262_: *mut leanh::LeanObject,
    mut v_env_263_: *mut leanh::LeanObject,
    mut v_h__1_264_: *mut leanh::LeanObject,
    mut v_h__2_265_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_env_263_) == 0 {
        let mut v___x_266_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_267_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_265_);
        v___x_266_ = leanh::lean_box(0);
        v___x_267_ = leanh::lean_apply_1(v_h__1_264_, v___x_266_);
        return v___x_267_;
    } else {
        let mut v_head_268_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_269_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_270_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_264_);
        v_head_268_ = leanh::lean_ctor_get(v_env_263_, 0);
        leanh::lean_inc(v_head_268_);
        v_tail_269_ = leanh::lean_ctor_get(v_env_263_, 1);
        leanh::lean_inc(v_tail_269_);
        leanh::lean_dec_ref_known(v_env_263_, 2);
        v___x_270_ = leanh::lean_apply_2(v_h__2_265_, v_head_268_, v_tail_269_);
        return v___x_270_;
    }
}
pub unsafe fn l___private_Std_Do_SPred_SPred_0__Std_Do_SPred_conjunction_match__1_splitter___boxed(
    mut v_00_u03c3s_271_: *mut leanh::LeanObject,
    mut v_motive_272_: *mut leanh::LeanObject,
    mut v_env_273_: *mut leanh::LeanObject,
    mut v_h__1_274_: *mut leanh::LeanObject,
    mut v_h__2_275_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_276_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_276_ = l___private_Std_Do_SPred_SPred_0__Std_Do_SPred_conjunction_match__1_splitter(
        v_00_u03c3s_271_,
        v_motive_272_,
        v_env_273_,
        v_h__1_274_,
        v_h__2_275_,
    );
    leanh::lean_dec(v_00_u03c3s_271_);
    return v_res_276_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Do_SPred_SPred(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Ext(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Do_SPred_SVal(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_NotationExtra(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Do_SPred_SPred(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Do_SPred_SPred(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Ext(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Do_SPred_SVal(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_NotationExtra(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Do_SPred_SPred(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Do_SPred_SPred(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Do_SPred_SPred(builtin);
}