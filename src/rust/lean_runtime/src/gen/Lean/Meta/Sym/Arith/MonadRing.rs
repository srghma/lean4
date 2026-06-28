// Lean compiler output
// Module: Lean.Meta.Sym.Arith.MonadRing
// Imports: Lean.Meta.Sym.Arith.MonadCanon
use crate::r#gen::Lean::Meta::Sym::Arith::MonadCanon::{
    initialize_Lean_Meta_Sym_Arith_MonadCanon, runtime_initialize_Lean_Meta_Sym_Arith_MonadCanon,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_4, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_set, lean_dec,
    lean_dec_ref, lean_inc, lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_is_exclusive,
};
pub unsafe fn l_Lean_Meta_Sym_Arith_instMonadRingOfMonadLift___redArg___lam__0(
    mut v_modifyRing_127_: *mut LeanObject,
    mut v_inst_128_: *mut LeanObject,
    mut v_f_129_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_131_: *mut LeanObject = core::ptr::null_mut();
    v___x_130_ = lean_apply_1(v_modifyRing_127_, v_f_129_);
    v___x_131_ = lean_apply_2(v_inst_128_, lean_box(0), v___x_130_);
    return v___x_131_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_instMonadRingOfMonadLift___redArg(
    mut v_inst_132_: *mut LeanObject,
    mut v_inst_133_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_getRing_134_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modifyRing_135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_137_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_138_: u8 = 0;
    let mut v___f_139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_142_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_143_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_144_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_getRing_134_ = lean_ctor_get(v_inst_133_, 0);
                v_modifyRing_135_ = lean_ctor_get(v_inst_133_, 1);
                v_isSharedCheck_144_ = (!lean_is_exclusive(v_inst_133_)) as u8;
                if v_isSharedCheck_144_ == 0 {
                    v___x_137_ = v_inst_133_;
                    v_isShared_138_ = v_isSharedCheck_144_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_modifyRing_135_);
                    lean_inc(v_getRing_134_);
                    lean_dec(v_inst_133_);
                    v___x_137_ = lean_box(0);
                    v_isShared_138_ = v_isSharedCheck_144_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_inst_132_);
                v___f_139_ = lean_alloc_closure(
                    l_Lean_Meta_Sym_Arith_instMonadRingOfMonadLift___redArg___lam__0
                        as *mut core::ffi::c_void,
                    3,
                    2,
                );
                lean_closure_set(v___f_139_, 0, v_modifyRing_135_);
                lean_closure_set(v___f_139_, 1, v_inst_132_);
                v___x_140_ = lean_apply_2(v_inst_132_, lean_box(0), v_getRing_134_);
                if v_isShared_138_ == 0 {
                    lean_ctor_set(v___x_137_, 1, v___f_139_);
                    lean_ctor_set(v___x_137_, 0, v___x_140_);
                    v___x_142_ = v___x_137_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_143_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_143_, 0, v___x_140_);
                    lean_ctor_set(v_reuseFailAlloc_143_, 1, v___f_139_);
                    v___x_142_ = v_reuseFailAlloc_143_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_142_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Arith_instMonadRingOfMonadLift(
    mut v_m_145_: *mut LeanObject,
    mut v_n_146_: *mut LeanObject,
    mut v_inst_147_: *mut LeanObject,
    mut v_inst_148_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_getRing_149_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modifyRing_150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_152_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_153_: u8 = 0;
    let mut v___f_154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_157_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_158_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_159_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_getRing_149_ = lean_ctor_get(v_inst_148_, 0);
                v_modifyRing_150_ = lean_ctor_get(v_inst_148_, 1);
                v_isSharedCheck_159_ = (!lean_is_exclusive(v_inst_148_)) as u8;
                if v_isSharedCheck_159_ == 0 {
                    v___x_152_ = v_inst_148_;
                    v_isShared_153_ = v_isSharedCheck_159_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_modifyRing_150_);
                    lean_inc(v_getRing_149_);
                    lean_dec(v_inst_148_);
                    v___x_152_ = lean_box(0);
                    v_isShared_153_ = v_isSharedCheck_159_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_inst_147_);
                v___f_154_ = lean_alloc_closure(
                    l_Lean_Meta_Sym_Arith_instMonadRingOfMonadLift___redArg___lam__0
                        as *mut core::ffi::c_void,
                    3,
                    2,
                );
                lean_closure_set(v___f_154_, 0, v_modifyRing_150_);
                lean_closure_set(v___f_154_, 1, v_inst_147_);
                v___x_155_ = lean_apply_2(v_inst_147_, lean_box(0), v_getRing_149_);
                if v_isShared_153_ == 0 {
                    lean_ctor_set(v___x_152_, 1, v___f_154_);
                    lean_ctor_set(v___x_152_, 0, v___x_155_);
                    v___x_157_ = v___x_152_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_158_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_158_, 0, v___x_155_);
                    lean_ctor_set(v_reuseFailAlloc_158_, 1, v___f_154_);
                    v___x_157_ = v_reuseFailAlloc_158_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_157_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Arith_instMonadCommRingOfMonadLift___redArg___lam__0(
    mut v_modifyCommRing_160_: *mut LeanObject,
    mut v_inst_161_: *mut LeanObject,
    mut v_f_162_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_164_: *mut LeanObject = core::ptr::null_mut();
    v___x_163_ = lean_apply_1(v_modifyCommRing_160_, v_f_162_);
    v___x_164_ = lean_apply_2(v_inst_161_, lean_box(0), v___x_163_);
    return v___x_164_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_instMonadCommRingOfMonadLift___redArg(
    mut v_inst_165_: *mut LeanObject,
    mut v_inst_166_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_getCommRing_167_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modifyCommRing_168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_170_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_171_: u8 = 0;
    let mut v___f_172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_176_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_177_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_getCommRing_167_ = lean_ctor_get(v_inst_166_, 0);
                v_modifyCommRing_168_ = lean_ctor_get(v_inst_166_, 1);
                v_isSharedCheck_177_ = (!lean_is_exclusive(v_inst_166_)) as u8;
                if v_isSharedCheck_177_ == 0 {
                    v___x_170_ = v_inst_166_;
                    v_isShared_171_ = v_isSharedCheck_177_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_modifyCommRing_168_);
                    lean_inc(v_getCommRing_167_);
                    lean_dec(v_inst_166_);
                    v___x_170_ = lean_box(0);
                    v_isShared_171_ = v_isSharedCheck_177_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_inst_165_);
                v___f_172_ = lean_alloc_closure(
                    l_Lean_Meta_Sym_Arith_instMonadCommRingOfMonadLift___redArg___lam__0
                        as *mut core::ffi::c_void,
                    3,
                    2,
                );
                lean_closure_set(v___f_172_, 0, v_modifyCommRing_168_);
                lean_closure_set(v___f_172_, 1, v_inst_165_);
                v___x_173_ = lean_apply_2(v_inst_165_, lean_box(0), v_getCommRing_167_);
                if v_isShared_171_ == 0 {
                    lean_ctor_set(v___x_170_, 1, v___f_172_);
                    lean_ctor_set(v___x_170_, 0, v___x_173_);
                    v___x_175_ = v___x_170_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_176_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_176_, 0, v___x_173_);
                    lean_ctor_set(v_reuseFailAlloc_176_, 1, v___f_172_);
                    v___x_175_ = v_reuseFailAlloc_176_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_175_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Arith_instMonadCommRingOfMonadLift(
    mut v_m_178_: *mut LeanObject,
    mut v_n_179_: *mut LeanObject,
    mut v_inst_180_: *mut LeanObject,
    mut v_inst_181_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_getCommRing_182_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modifyCommRing_183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_185_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_186_: u8 = 0;
    let mut v___f_187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_191_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_192_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_getCommRing_182_ = lean_ctor_get(v_inst_181_, 0);
                v_modifyCommRing_183_ = lean_ctor_get(v_inst_181_, 1);
                v_isSharedCheck_192_ = (!lean_is_exclusive(v_inst_181_)) as u8;
                if v_isSharedCheck_192_ == 0 {
                    v___x_185_ = v_inst_181_;
                    v_isShared_186_ = v_isSharedCheck_192_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_modifyCommRing_183_);
                    lean_inc(v_getCommRing_182_);
                    lean_dec(v_inst_181_);
                    v___x_185_ = lean_box(0);
                    v_isShared_186_ = v_isSharedCheck_192_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_inst_180_);
                v___f_187_ = lean_alloc_closure(
                    l_Lean_Meta_Sym_Arith_instMonadCommRingOfMonadLift___redArg___lam__0
                        as *mut core::ffi::c_void,
                    3,
                    2,
                );
                lean_closure_set(v___f_187_, 0, v_modifyCommRing_183_);
                lean_closure_set(v___f_187_, 1, v_inst_180_);
                v___x_188_ = lean_apply_2(v_inst_180_, lean_box(0), v_getCommRing_182_);
                if v_isShared_186_ == 0 {
                    lean_ctor_set(v___x_185_, 1, v___f_187_);
                    lean_ctor_set(v___x_185_, 0, v___x_188_);
                    v___x_190_ = v___x_185_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_191_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_191_, 0, v___x_188_);
                    lean_ctor_set(v_reuseFailAlloc_191_, 1, v___f_187_);
                    v___x_190_ = v_reuseFailAlloc_191_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_190_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Arith_instMonadRingOfMonadOfMonadCommRing___redArg___lam__0(
    mut v_f_193_: *mut LeanObject,
    mut v_s_194_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toRing_195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_invFn_x3f_196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_semiringId_x3f_197_: *mut LeanObject = core::ptr::null_mut();
    let mut v_commSemiringInst_198_: *mut LeanObject = core::ptr::null_mut();
    let mut v_commRingInst_199_: *mut LeanObject = core::ptr::null_mut();
    let mut v_noZeroDivInst_x3f_200_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fieldInst_x3f_201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_203_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_204_: u8 = 0;
    let mut v___x_205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_207_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_208_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_209_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toRing_195_ = lean_ctor_get(v_s_194_, 0);
                v_invFn_x3f_196_ = lean_ctor_get(v_s_194_, 1);
                v_semiringId_x3f_197_ = lean_ctor_get(v_s_194_, 2);
                v_commSemiringInst_198_ = lean_ctor_get(v_s_194_, 3);
                v_commRingInst_199_ = lean_ctor_get(v_s_194_, 4);
                v_noZeroDivInst_x3f_200_ = lean_ctor_get(v_s_194_, 5);
                v_fieldInst_x3f_201_ = lean_ctor_get(v_s_194_, 6);
                v_isSharedCheck_209_ = (!lean_is_exclusive(v_s_194_)) as u8;
                if v_isSharedCheck_209_ == 0 {
                    v___x_203_ = v_s_194_;
                    v_isShared_204_ = v_isSharedCheck_209_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_fieldInst_x3f_201_);
                    lean_inc(v_noZeroDivInst_x3f_200_);
                    lean_inc(v_commRingInst_199_);
                    lean_inc(v_commSemiringInst_198_);
                    lean_inc(v_semiringId_x3f_197_);
                    lean_inc(v_invFn_x3f_196_);
                    lean_inc(v_toRing_195_);
                    lean_dec(v_s_194_);
                    v___x_203_ = lean_box(0);
                    v_isShared_204_ = v_isSharedCheck_209_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_205_ = lean_apply_1(v_f_193_, v_toRing_195_);
                if v_isShared_204_ == 0 {
                    lean_ctor_set(v___x_203_, 0, v___x_205_);
                    v___x_207_ = v___x_203_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_208_ = lean_alloc_ctor(0, 7, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_208_, 0, v___x_205_);
                    lean_ctor_set(v_reuseFailAlloc_208_, 1, v_invFn_x3f_196_);
                    lean_ctor_set(v_reuseFailAlloc_208_, 2, v_semiringId_x3f_197_);
                    lean_ctor_set(v_reuseFailAlloc_208_, 3, v_commSemiringInst_198_);
                    lean_ctor_set(v_reuseFailAlloc_208_, 4, v_commRingInst_199_);
                    lean_ctor_set(v_reuseFailAlloc_208_, 5, v_noZeroDivInst_x3f_200_);
                    lean_ctor_set(v_reuseFailAlloc_208_, 6, v_fieldInst_x3f_201_);
                    v___x_207_ = v_reuseFailAlloc_208_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_207_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Arith_instMonadRingOfMonadOfMonadCommRing___redArg___lam__1(
    mut v_modifyCommRing_210_: *mut LeanObject,
    mut v_f_211_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_213_: *mut LeanObject = core::ptr::null_mut();
    v___f_212_ = lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_instMonadRingOfMonadOfMonadCommRing___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_212_, 0, v_f_211_);
    v___x_213_ = lean_apply_1(v_modifyCommRing_210_, v___f_212_);
    return v___x_213_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_instMonadRingOfMonadOfMonadCommRing___redArg___lam__2(
    mut v_toPure_214_: *mut LeanObject,
    mut v_____do__lift_215_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toRing_216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_217_: *mut LeanObject = core::ptr::null_mut();
    v_toRing_216_ = lean_ctor_get(v_____do__lift_215_, 0);
    lean_inc_ref(v_toRing_216_);
    lean_dec_ref(v_____do__lift_215_);
    v___x_217_ = lean_apply_2(v_toPure_214_, lean_box(0), v_toRing_216_);
    return v___x_217_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_instMonadRingOfMonadOfMonadCommRing___redArg(
    mut v_inst_218_: *mut LeanObject,
    mut v_inst_219_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getCommRing_222_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modifyCommRing_223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_226_: u8 = 0;
    let mut v_toPure_227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_232_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_233_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_234_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_220_ = lean_ctor_get(v_inst_218_, 0);
                lean_inc_ref(v_toApplicative_220_);
                v_toBind_221_ = lean_ctor_get(v_inst_218_, 1);
                lean_inc(v_toBind_221_);
                lean_dec_ref(v_inst_218_);
                v_getCommRing_222_ = lean_ctor_get(v_inst_219_, 0);
                v_modifyCommRing_223_ = lean_ctor_get(v_inst_219_, 1);
                v_isSharedCheck_234_ = (!lean_is_exclusive(v_inst_219_)) as u8;
                if v_isSharedCheck_234_ == 0 {
                    v___x_225_ = v_inst_219_;
                    v_isShared_226_ = v_isSharedCheck_234_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_modifyCommRing_223_);
                    lean_inc(v_getCommRing_222_);
                    lean_dec(v_inst_219_);
                    v___x_225_ = lean_box(0);
                    v_isShared_226_ = v_isSharedCheck_234_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toPure_227_ = lean_ctor_get(v_toApplicative_220_, 1);
                lean_inc(v_toPure_227_);
                lean_dec_ref(v_toApplicative_220_);
                v___f_228_ = lean_alloc_closure(
                    l_Lean_Meta_Sym_Arith_instMonadRingOfMonadOfMonadCommRing___redArg___lam__1
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___f_228_, 0, v_modifyCommRing_223_);
                v___f_229_ = lean_alloc_closure(
                    l_Lean_Meta_Sym_Arith_instMonadRingOfMonadOfMonadCommRing___redArg___lam__2
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___f_229_, 0, v_toPure_227_);
                v___x_230_ = lean_apply_4(
                    v_toBind_221_,
                    lean_box(0),
                    lean_box(0),
                    v_getCommRing_222_,
                    v___f_229_,
                );
                if v_isShared_226_ == 0 {
                    lean_ctor_set(v___x_225_, 1, v___f_228_);
                    lean_ctor_set(v___x_225_, 0, v___x_230_);
                    v___x_232_ = v___x_225_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_233_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_233_, 0, v___x_230_);
                    lean_ctor_set(v_reuseFailAlloc_233_, 1, v___f_228_);
                    v___x_232_ = v_reuseFailAlloc_233_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_232_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Arith_instMonadRingOfMonadOfMonadCommRing(
    mut v_m_235_: *mut LeanObject,
    mut v_inst_236_: *mut LeanObject,
    mut v_inst_237_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_238_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getCommRing_240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modifyCommRing_241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_244_: u8 = 0;
    let mut v_toPure_245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_250_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_251_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_252_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_238_ = lean_ctor_get(v_inst_236_, 0);
                lean_inc_ref(v_toApplicative_238_);
                v_toBind_239_ = lean_ctor_get(v_inst_236_, 1);
                lean_inc(v_toBind_239_);
                lean_dec_ref(v_inst_236_);
                v_getCommRing_240_ = lean_ctor_get(v_inst_237_, 0);
                v_modifyCommRing_241_ = lean_ctor_get(v_inst_237_, 1);
                v_isSharedCheck_252_ = (!lean_is_exclusive(v_inst_237_)) as u8;
                if v_isSharedCheck_252_ == 0 {
                    v___x_243_ = v_inst_237_;
                    v_isShared_244_ = v_isSharedCheck_252_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_modifyCommRing_241_);
                    lean_inc(v_getCommRing_240_);
                    lean_dec(v_inst_237_);
                    v___x_243_ = lean_box(0);
                    v_isShared_244_ = v_isSharedCheck_252_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toPure_245_ = lean_ctor_get(v_toApplicative_238_, 1);
                lean_inc(v_toPure_245_);
                lean_dec_ref(v_toApplicative_238_);
                v___f_246_ = lean_alloc_closure(
                    l_Lean_Meta_Sym_Arith_instMonadRingOfMonadOfMonadCommRing___redArg___lam__1
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___f_246_, 0, v_modifyCommRing_241_);
                v___f_247_ = lean_alloc_closure(
                    l_Lean_Meta_Sym_Arith_instMonadRingOfMonadOfMonadCommRing___redArg___lam__2
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___f_247_, 0, v_toPure_245_);
                v___x_248_ = lean_apply_4(
                    v_toBind_239_,
                    lean_box(0),
                    lean_box(0),
                    v_getCommRing_240_,
                    v___f_247_,
                );
                if v_isShared_244_ == 0 {
                    lean_ctor_set(v___x_243_, 1, v___f_246_);
                    lean_ctor_set(v___x_243_, 0, v___x_248_);
                    v___x_250_ = v___x_243_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_251_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_251_, 0, v___x_248_);
                    lean_ctor_set(v_reuseFailAlloc_251_, 1, v___f_246_);
                    v___x_250_ = v_reuseFailAlloc_251_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_250_;
            }
            _ => {}
        }
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Sym_Arith_MonadRing(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Sym_Arith_MonadCanon(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Sym_Arith_MonadRing(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Sym_Arith_MonadRing(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Sym_Arith_MonadCanon(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Arith_MonadRing(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Sym_Arith_MonadRing(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Sym_Arith_MonadRing(builtin);
}
