// Lean compiler output
// Module: Lean.Meta.Sym.Arith.MonadRing
// Imports: Lean.Meta.Sym.Arith.MonadCanon
use crate::r#gen::Lean::Meta::Sym::Arith::MonadCanon::{
    initialize_Lean_Meta_Sym_Arith_MonadCanon, runtime_initialize_Lean_Meta_Sym_Arith_MonadCanon,
};
pub unsafe fn l_Lean_Meta_Sym_Arith_instMonadRingOfMonadLift___redArg___lam__0(
    mut v_modifyRing_127_: *mut crate::leanh::LeanObject,
    mut v_inst_128_: *mut crate::leanh::LeanObject,
    mut v_f_129_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_130_ = crate::leanh::lean_apply_1(v_modifyRing_127_, v_f_129_);
    v___x_131_ = crate::leanh::lean_apply_2(v_inst_128_, crate::leanh::lean_box(0), v___x_130_);
    return v___x_131_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_instMonadRingOfMonadLift___redArg(
    mut v_inst_132_: *mut crate::leanh::LeanObject,
    mut v_inst_133_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_getRing_134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifyRing_135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_138_: u8 = 0;
    let mut v___f_139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_144_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_getRing_134_ = crate::leanh::lean_ctor_get(v_inst_133_, 0);
                v_modifyRing_135_ = crate::leanh::lean_ctor_get(v_inst_133_, 1);
                v_isSharedCheck_144_ = (!crate::leanh::lean_is_exclusive(v_inst_133_)) as u8;
                if v_isSharedCheck_144_ == 0 {
                    v___x_137_ = v_inst_133_;
                    v_isShared_138_ = v_isSharedCheck_144_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_modifyRing_135_);
                    crate::leanh::lean_inc(v_getRing_134_);
                    crate::leanh::lean_dec(v_inst_133_);
                    v___x_137_ = crate::leanh::lean_box(0);
                    v_isShared_138_ = v_isSharedCheck_144_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_inst_132_);
                v___f_139_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Meta_Sym_Arith_instMonadRingOfMonadLift___redArg___lam__0
                        as *mut core::ffi::c_void,
                    3,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_139_, 0, v_modifyRing_135_);
                crate::leanh::lean_closure_set(v___f_139_, 1, v_inst_132_);
                v___x_140_ = crate::leanh::lean_apply_2(
                    v_inst_132_,
                    crate::leanh::lean_box(0),
                    v_getRing_134_,
                );
                if v_isShared_138_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_137_, 1, v___f_139_);
                    crate::leanh::lean_ctor_set(v___x_137_, 0, v___x_140_);
                    v___x_142_ = v___x_137_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_143_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_143_, 0, v___x_140_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_143_, 1, v___f_139_);
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
    mut v_m_145_: *mut crate::leanh::LeanObject,
    mut v_n_146_: *mut crate::leanh::LeanObject,
    mut v_inst_147_: *mut crate::leanh::LeanObject,
    mut v_inst_148_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_getRing_149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifyRing_150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_153_: u8 = 0;
    let mut v___f_154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_159_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_getRing_149_ = crate::leanh::lean_ctor_get(v_inst_148_, 0);
                v_modifyRing_150_ = crate::leanh::lean_ctor_get(v_inst_148_, 1);
                v_isSharedCheck_159_ = (!crate::leanh::lean_is_exclusive(v_inst_148_)) as u8;
                if v_isSharedCheck_159_ == 0 {
                    v___x_152_ = v_inst_148_;
                    v_isShared_153_ = v_isSharedCheck_159_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_modifyRing_150_);
                    crate::leanh::lean_inc(v_getRing_149_);
                    crate::leanh::lean_dec(v_inst_148_);
                    v___x_152_ = crate::leanh::lean_box(0);
                    v_isShared_153_ = v_isSharedCheck_159_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_inst_147_);
                v___f_154_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Meta_Sym_Arith_instMonadRingOfMonadLift___redArg___lam__0
                        as *mut core::ffi::c_void,
                    3,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_154_, 0, v_modifyRing_150_);
                crate::leanh::lean_closure_set(v___f_154_, 1, v_inst_147_);
                v___x_155_ = crate::leanh::lean_apply_2(
                    v_inst_147_,
                    crate::leanh::lean_box(0),
                    v_getRing_149_,
                );
                if v_isShared_153_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_152_, 1, v___f_154_);
                    crate::leanh::lean_ctor_set(v___x_152_, 0, v___x_155_);
                    v___x_157_ = v___x_152_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_158_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_158_, 0, v___x_155_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_158_, 1, v___f_154_);
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
    mut v_modifyCommRing_160_: *mut crate::leanh::LeanObject,
    mut v_inst_161_: *mut crate::leanh::LeanObject,
    mut v_f_162_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_163_ = crate::leanh::lean_apply_1(v_modifyCommRing_160_, v_f_162_);
    v___x_164_ = crate::leanh::lean_apply_2(v_inst_161_, crate::leanh::lean_box(0), v___x_163_);
    return v___x_164_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_instMonadCommRingOfMonadLift___redArg(
    mut v_inst_165_: *mut crate::leanh::LeanObject,
    mut v_inst_166_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_getCommRing_167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifyCommRing_168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_171_: u8 = 0;
    let mut v___f_172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_177_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_getCommRing_167_ = crate::leanh::lean_ctor_get(v_inst_166_, 0);
                v_modifyCommRing_168_ = crate::leanh::lean_ctor_get(v_inst_166_, 1);
                v_isSharedCheck_177_ = (!crate::leanh::lean_is_exclusive(v_inst_166_)) as u8;
                if v_isSharedCheck_177_ == 0 {
                    v___x_170_ = v_inst_166_;
                    v_isShared_171_ = v_isSharedCheck_177_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_modifyCommRing_168_);
                    crate::leanh::lean_inc(v_getCommRing_167_);
                    crate::leanh::lean_dec(v_inst_166_);
                    v___x_170_ = crate::leanh::lean_box(0);
                    v_isShared_171_ = v_isSharedCheck_177_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_inst_165_);
                v___f_172_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Meta_Sym_Arith_instMonadCommRingOfMonadLift___redArg___lam__0
                        as *mut core::ffi::c_void,
                    3,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_172_, 0, v_modifyCommRing_168_);
                crate::leanh::lean_closure_set(v___f_172_, 1, v_inst_165_);
                v___x_173_ = crate::leanh::lean_apply_2(
                    v_inst_165_,
                    crate::leanh::lean_box(0),
                    v_getCommRing_167_,
                );
                if v_isShared_171_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_170_, 1, v___f_172_);
                    crate::leanh::lean_ctor_set(v___x_170_, 0, v___x_173_);
                    v___x_175_ = v___x_170_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_176_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_176_, 0, v___x_173_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_176_, 1, v___f_172_);
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
    mut v_m_178_: *mut crate::leanh::LeanObject,
    mut v_n_179_: *mut crate::leanh::LeanObject,
    mut v_inst_180_: *mut crate::leanh::LeanObject,
    mut v_inst_181_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_getCommRing_182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifyCommRing_183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_186_: u8 = 0;
    let mut v___f_187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_192_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_getCommRing_182_ = crate::leanh::lean_ctor_get(v_inst_181_, 0);
                v_modifyCommRing_183_ = crate::leanh::lean_ctor_get(v_inst_181_, 1);
                v_isSharedCheck_192_ = (!crate::leanh::lean_is_exclusive(v_inst_181_)) as u8;
                if v_isSharedCheck_192_ == 0 {
                    v___x_185_ = v_inst_181_;
                    v_isShared_186_ = v_isSharedCheck_192_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_modifyCommRing_183_);
                    crate::leanh::lean_inc(v_getCommRing_182_);
                    crate::leanh::lean_dec(v_inst_181_);
                    v___x_185_ = crate::leanh::lean_box(0);
                    v_isShared_186_ = v_isSharedCheck_192_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_inst_180_);
                v___f_187_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Meta_Sym_Arith_instMonadCommRingOfMonadLift___redArg___lam__0
                        as *mut core::ffi::c_void,
                    3,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_187_, 0, v_modifyCommRing_183_);
                crate::leanh::lean_closure_set(v___f_187_, 1, v_inst_180_);
                v___x_188_ = crate::leanh::lean_apply_2(
                    v_inst_180_,
                    crate::leanh::lean_box(0),
                    v_getCommRing_182_,
                );
                if v_isShared_186_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_185_, 1, v___f_187_);
                    crate::leanh::lean_ctor_set(v___x_185_, 0, v___x_188_);
                    v___x_190_ = v___x_185_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_191_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_191_, 0, v___x_188_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_191_, 1, v___f_187_);
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
    mut v_f_193_: *mut crate::leanh::LeanObject,
    mut v_s_194_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toRing_195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invFn_x3f_196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringId_x3f_197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_commSemiringInst_198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_commRingInst_199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_noZeroDivInst_x3f_200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fieldInst_x3f_201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_204_: u8 = 0;
    let mut v___x_205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_209_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toRing_195_ = crate::leanh::lean_ctor_get(v_s_194_, 0);
                v_invFn_x3f_196_ = crate::leanh::lean_ctor_get(v_s_194_, 1);
                v_semiringId_x3f_197_ = crate::leanh::lean_ctor_get(v_s_194_, 2);
                v_commSemiringInst_198_ = crate::leanh::lean_ctor_get(v_s_194_, 3);
                v_commRingInst_199_ = crate::leanh::lean_ctor_get(v_s_194_, 4);
                v_noZeroDivInst_x3f_200_ = crate::leanh::lean_ctor_get(v_s_194_, 5);
                v_fieldInst_x3f_201_ = crate::leanh::lean_ctor_get(v_s_194_, 6);
                v_isSharedCheck_209_ = (!crate::leanh::lean_is_exclusive(v_s_194_)) as u8;
                if v_isSharedCheck_209_ == 0 {
                    v___x_203_ = v_s_194_;
                    v_isShared_204_ = v_isSharedCheck_209_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_fieldInst_x3f_201_);
                    crate::leanh::lean_inc(v_noZeroDivInst_x3f_200_);
                    crate::leanh::lean_inc(v_commRingInst_199_);
                    crate::leanh::lean_inc(v_commSemiringInst_198_);
                    crate::leanh::lean_inc(v_semiringId_x3f_197_);
                    crate::leanh::lean_inc(v_invFn_x3f_196_);
                    crate::leanh::lean_inc(v_toRing_195_);
                    crate::leanh::lean_dec(v_s_194_);
                    v___x_203_ = crate::leanh::lean_box(0);
                    v_isShared_204_ = v_isSharedCheck_209_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_205_ = crate::leanh::lean_apply_1(v_f_193_, v_toRing_195_);
                if v_isShared_204_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_203_, 0, v___x_205_);
                    v___x_207_ = v___x_203_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_208_ = crate::leanh::lean_alloc_ctor(0, 7, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_208_, 0, v___x_205_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_208_, 1, v_invFn_x3f_196_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_208_, 2, v_semiringId_x3f_197_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_208_, 3, v_commSemiringInst_198_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_208_, 4, v_commRingInst_199_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_208_, 5, v_noZeroDivInst_x3f_200_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_208_, 6, v_fieldInst_x3f_201_);
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
    mut v_modifyCommRing_210_: *mut crate::leanh::LeanObject,
    mut v_f_211_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_212_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_instMonadRingOfMonadOfMonadCommRing___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_212_, 0, v_f_211_);
    v___x_213_ = crate::leanh::lean_apply_1(v_modifyCommRing_210_, v___f_212_);
    return v___x_213_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_instMonadRingOfMonadOfMonadCommRing___redArg___lam__2(
    mut v_toPure_214_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_215_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toRing_216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toRing_216_ = crate::leanh::lean_ctor_get(v_____do__lift_215_, 0);
    crate::leanh::lean_inc_ref(v_toRing_216_);
    crate::leanh::lean_dec_ref(v_____do__lift_215_);
    v___x_217_ =
        crate::leanh::lean_apply_2(v_toPure_214_, crate::leanh::lean_box(0), v_toRing_216_);
    return v___x_217_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_instMonadRingOfMonadOfMonadCommRing___redArg(
    mut v_inst_218_: *mut crate::leanh::LeanObject,
    mut v_inst_219_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getCommRing_222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifyCommRing_223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_226_: u8 = 0;
    let mut v_toPure_227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_234_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_220_ = crate::leanh::lean_ctor_get(v_inst_218_, 0);
                crate::leanh::lean_inc_ref(v_toApplicative_220_);
                v_toBind_221_ = crate::leanh::lean_ctor_get(v_inst_218_, 1);
                crate::leanh::lean_inc(v_toBind_221_);
                crate::leanh::lean_dec_ref(v_inst_218_);
                v_getCommRing_222_ = crate::leanh::lean_ctor_get(v_inst_219_, 0);
                v_modifyCommRing_223_ = crate::leanh::lean_ctor_get(v_inst_219_, 1);
                v_isSharedCheck_234_ = (!crate::leanh::lean_is_exclusive(v_inst_219_)) as u8;
                if v_isSharedCheck_234_ == 0 {
                    v___x_225_ = v_inst_219_;
                    v_isShared_226_ = v_isSharedCheck_234_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_modifyCommRing_223_);
                    crate::leanh::lean_inc(v_getCommRing_222_);
                    crate::leanh::lean_dec(v_inst_219_);
                    v___x_225_ = crate::leanh::lean_box(0);
                    v_isShared_226_ = v_isSharedCheck_234_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toPure_227_ = crate::leanh::lean_ctor_get(v_toApplicative_220_, 1);
                crate::leanh::lean_inc(v_toPure_227_);
                crate::leanh::lean_dec_ref(v_toApplicative_220_);
                v___f_228_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Meta_Sym_Arith_instMonadRingOfMonadOfMonadCommRing___redArg___lam__1
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_228_, 0, v_modifyCommRing_223_);
                v___f_229_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Meta_Sym_Arith_instMonadRingOfMonadOfMonadCommRing___redArg___lam__2
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_229_, 0, v_toPure_227_);
                v___x_230_ = crate::leanh::lean_apply_4(
                    v_toBind_221_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v_getCommRing_222_,
                    v___f_229_,
                );
                if v_isShared_226_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_225_, 1, v___f_228_);
                    crate::leanh::lean_ctor_set(v___x_225_, 0, v___x_230_);
                    v___x_232_ = v___x_225_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_233_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_233_, 0, v___x_230_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_233_, 1, v___f_228_);
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
    mut v_m_235_: *mut crate::leanh::LeanObject,
    mut v_inst_236_: *mut crate::leanh::LeanObject,
    mut v_inst_237_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getCommRing_240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifyCommRing_241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_244_: u8 = 0;
    let mut v_toPure_245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_252_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_238_ = crate::leanh::lean_ctor_get(v_inst_236_, 0);
                crate::leanh::lean_inc_ref(v_toApplicative_238_);
                v_toBind_239_ = crate::leanh::lean_ctor_get(v_inst_236_, 1);
                crate::leanh::lean_inc(v_toBind_239_);
                crate::leanh::lean_dec_ref(v_inst_236_);
                v_getCommRing_240_ = crate::leanh::lean_ctor_get(v_inst_237_, 0);
                v_modifyCommRing_241_ = crate::leanh::lean_ctor_get(v_inst_237_, 1);
                v_isSharedCheck_252_ = (!crate::leanh::lean_is_exclusive(v_inst_237_)) as u8;
                if v_isSharedCheck_252_ == 0 {
                    v___x_243_ = v_inst_237_;
                    v_isShared_244_ = v_isSharedCheck_252_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_modifyCommRing_241_);
                    crate::leanh::lean_inc(v_getCommRing_240_);
                    crate::leanh::lean_dec(v_inst_237_);
                    v___x_243_ = crate::leanh::lean_box(0);
                    v_isShared_244_ = v_isSharedCheck_252_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toPure_245_ = crate::leanh::lean_ctor_get(v_toApplicative_238_, 1);
                crate::leanh::lean_inc(v_toPure_245_);
                crate::leanh::lean_dec_ref(v_toApplicative_238_);
                v___f_246_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Meta_Sym_Arith_instMonadRingOfMonadOfMonadCommRing___redArg___lam__1
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_246_, 0, v_modifyCommRing_241_);
                v___f_247_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Meta_Sym_Arith_instMonadRingOfMonadOfMonadCommRing___redArg___lam__2
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_247_, 0, v_toPure_245_);
                v___x_248_ = crate::leanh::lean_apply_4(
                    v_toBind_239_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v_getCommRing_240_,
                    v___f_247_,
                );
                if v_isShared_244_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_243_, 1, v___f_246_);
                    crate::leanh::lean_ctor_set(v___x_243_, 0, v___x_248_);
                    v___x_250_ = v___x_243_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_251_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_251_, 0, v___x_248_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_251_, 1, v___f_246_);
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
pub unsafe fn runtime_initialize_Lean_Meta_Sym_Arith_MonadRing(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Sym_Arith_MonadCanon(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Sym_Arith_MonadRing(
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
pub unsafe fn initialize_Lean_Meta_Sym_Arith_MonadRing(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Sym_Arith_MonadCanon(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Arith_MonadRing(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Sym_Arith_MonadRing(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Sym_Arith_MonadRing(builtin);
}
