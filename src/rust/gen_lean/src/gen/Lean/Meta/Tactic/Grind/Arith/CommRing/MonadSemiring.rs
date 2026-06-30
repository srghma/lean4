// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.CommRing.MonadSemiring
// Imports: Lean.Meta.Sym.Arith.MonadCanon Lean.Meta.Tactic.Grind.Arith.CommRing.Types
use crate::r#gen::Lean::Meta::Sym::Arith::MonadCanon::{
    initialize_Lean_Meta_Sym_Arith_MonadCanon, runtime_initialize_Lean_Meta_Sym_Arith_MonadCanon,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::CommRing::Types::{
    initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Types,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Types,
};
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringOfMonadLift___redArg___lam__0(
    mut v_modifySemiring_125_: *mut leanh::LeanObject,
    mut v_inst_126_: *mut leanh::LeanObject,
    mut v_f_127_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_129_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_128_ = leanh::lean_apply_1(v_modifySemiring_125_, v_f_127_);
    v___x_129_ = leanh::lean_apply_2(v_inst_126_, leanh::lean_box(0), v___x_128_);
    return v___x_129_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringOfMonadLift___redArg(
    mut v_inst_130_: *mut leanh::LeanObject,
    mut v_inst_131_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_getSemiring_132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifySemiring_133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_136_: u8 = 0;
    let mut v___f_137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_142_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_getSemiring_132_ = leanh::lean_ctor_get(v_inst_131_, 0);
                v_modifySemiring_133_ = leanh::lean_ctor_get(v_inst_131_, 1);
                v_isSharedCheck_142_ = (!leanh::lean_is_exclusive(v_inst_131_)) as u8;
                if v_isSharedCheck_142_ == 0 {
                    v___x_135_ = v_inst_131_;
                    v_isShared_136_ = v_isSharedCheck_142_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_modifySemiring_133_);
                    leanh::lean_inc(v_getSemiring_132_);
                    leanh::lean_dec(v_inst_131_);
                    v___x_135_ = leanh::lean_box(0);
                    v_isShared_136_ = v_isSharedCheck_142_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_inst_130_);
                v___f_137_ = leanh::lean_alloc_closure(
                    l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringOfMonadLift___redArg___lam__0
                        as *mut core::ffi::c_void,
                    3,
                    2,
                );
                leanh::lean_closure_set(v___f_137_, 0, v_modifySemiring_133_);
                leanh::lean_closure_set(v___f_137_, 1, v_inst_130_);
                v___x_138_ = leanh::lean_apply_2(
                    v_inst_130_,
                    leanh::lean_box(0),
                    v_getSemiring_132_,
                );
                if v_isShared_136_ == 0 {
                    leanh::lean_ctor_set(v___x_135_, 1, v___f_137_);
                    leanh::lean_ctor_set(v___x_135_, 0, v___x_138_);
                    v___x_140_ = v___x_135_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_141_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_141_, 0, v___x_138_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_141_, 1, v___f_137_);
                    v___x_140_ = v_reuseFailAlloc_141_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_140_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringOfMonadLift(
    mut v_m_143_: *mut leanh::LeanObject,
    mut v_n_144_: *mut leanh::LeanObject,
    mut v_inst_145_: *mut leanh::LeanObject,
    mut v_inst_146_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_getSemiring_147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifySemiring_148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_151_: u8 = 0;
    let mut v___f_152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_157_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_getSemiring_147_ = leanh::lean_ctor_get(v_inst_146_, 0);
                v_modifySemiring_148_ = leanh::lean_ctor_get(v_inst_146_, 1);
                v_isSharedCheck_157_ = (!leanh::lean_is_exclusive(v_inst_146_)) as u8;
                if v_isSharedCheck_157_ == 0 {
                    v___x_150_ = v_inst_146_;
                    v_isShared_151_ = v_isSharedCheck_157_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_modifySemiring_148_);
                    leanh::lean_inc(v_getSemiring_147_);
                    leanh::lean_dec(v_inst_146_);
                    v___x_150_ = leanh::lean_box(0);
                    v_isShared_151_ = v_isSharedCheck_157_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_inst_145_);
                v___f_152_ = leanh::lean_alloc_closure(
                    l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringOfMonadLift___redArg___lam__0
                        as *mut core::ffi::c_void,
                    3,
                    2,
                );
                leanh::lean_closure_set(v___f_152_, 0, v_modifySemiring_148_);
                leanh::lean_closure_set(v___f_152_, 1, v_inst_145_);
                v___x_153_ = leanh::lean_apply_2(
                    v_inst_145_,
                    leanh::lean_box(0),
                    v_getSemiring_147_,
                );
                if v_isShared_151_ == 0 {
                    leanh::lean_ctor_set(v___x_150_, 1, v___f_152_);
                    leanh::lean_ctor_set(v___x_150_, 0, v___x_153_);
                    v___x_155_ = v___x_150_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_156_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_156_, 0, v___x_153_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_156_, 1, v___f_152_);
                    v___x_155_ = v_reuseFailAlloc_156_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_155_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_instMonadCommSemiringOfMonadLift___redArg___lam__0(
    mut v_modifyCommSemiring_158_: *mut leanh::LeanObject,
    mut v_inst_159_: *mut leanh::LeanObject,
    mut v_f_160_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_162_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_161_ = leanh::lean_apply_1(v_modifyCommSemiring_158_, v_f_160_);
    v___x_162_ = leanh::lean_apply_2(v_inst_159_, leanh::lean_box(0), v___x_161_);
    return v___x_162_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_instMonadCommSemiringOfMonadLift___redArg(
    mut v_inst_163_: *mut leanh::LeanObject,
    mut v_inst_164_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_getCommSemiring_165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifyCommSemiring_166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_169_: u8 = 0;
    let mut v___f_170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_175_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_getCommSemiring_165_ = leanh::lean_ctor_get(v_inst_164_, 0);
                v_modifyCommSemiring_166_ = leanh::lean_ctor_get(v_inst_164_, 1);
                v_isSharedCheck_175_ = (!leanh::lean_is_exclusive(v_inst_164_)) as u8;
                if v_isSharedCheck_175_ == 0 {
                    v___x_168_ = v_inst_164_;
                    v_isShared_169_ = v_isSharedCheck_175_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_modifyCommSemiring_166_);
                    leanh::lean_inc(v_getCommSemiring_165_);
                    leanh::lean_dec(v_inst_164_);
                    v___x_168_ = leanh::lean_box(0);
                    v_isShared_169_ = v_isSharedCheck_175_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_inst_163_);
                v___f_170_ = leanh::lean_alloc_closure(l_Lean_Meta_Grind_Arith_CommRing_instMonadCommSemiringOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void, 3, 2);
                leanh::lean_closure_set(v___f_170_, 0, v_modifyCommSemiring_166_);
                leanh::lean_closure_set(v___f_170_, 1, v_inst_163_);
                v___x_171_ = leanh::lean_apply_2(
                    v_inst_163_,
                    leanh::lean_box(0),
                    v_getCommSemiring_165_,
                );
                if v_isShared_169_ == 0 {
                    leanh::lean_ctor_set(v___x_168_, 1, v___f_170_);
                    leanh::lean_ctor_set(v___x_168_, 0, v___x_171_);
                    v___x_173_ = v___x_168_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_174_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_174_, 0, v___x_171_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_174_, 1, v___f_170_);
                    v___x_173_ = v_reuseFailAlloc_174_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_173_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_instMonadCommSemiringOfMonadLift(
    mut v_m_176_: *mut leanh::LeanObject,
    mut v_n_177_: *mut leanh::LeanObject,
    mut v_inst_178_: *mut leanh::LeanObject,
    mut v_inst_179_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_getCommSemiring_180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifyCommSemiring_181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_184_: u8 = 0;
    let mut v___f_185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_190_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_getCommSemiring_180_ = leanh::lean_ctor_get(v_inst_179_, 0);
                v_modifyCommSemiring_181_ = leanh::lean_ctor_get(v_inst_179_, 1);
                v_isSharedCheck_190_ = (!leanh::lean_is_exclusive(v_inst_179_)) as u8;
                if v_isSharedCheck_190_ == 0 {
                    v___x_183_ = v_inst_179_;
                    v_isShared_184_ = v_isSharedCheck_190_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_modifyCommSemiring_181_);
                    leanh::lean_inc(v_getCommSemiring_180_);
                    leanh::lean_dec(v_inst_179_);
                    v___x_183_ = leanh::lean_box(0);
                    v_isShared_184_ = v_isSharedCheck_190_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_inst_178_);
                v___f_185_ = leanh::lean_alloc_closure(l_Lean_Meta_Grind_Arith_CommRing_instMonadCommSemiringOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void, 3, 2);
                leanh::lean_closure_set(v___f_185_, 0, v_modifyCommSemiring_181_);
                leanh::lean_closure_set(v___f_185_, 1, v_inst_178_);
                v___x_186_ = leanh::lean_apply_2(
                    v_inst_178_,
                    leanh::lean_box(0),
                    v_getCommSemiring_180_,
                );
                if v_isShared_184_ == 0 {
                    leanh::lean_ctor_set(v___x_183_, 1, v___f_185_);
                    leanh::lean_ctor_set(v___x_183_, 0, v___x_186_);
                    v___x_188_ = v___x_183_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_189_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_189_, 0, v___x_186_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_189_, 1, v___f_185_);
                    v___x_188_ = v_reuseFailAlloc_189_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_188_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringOfMonadOfMonadCommSemiring___redArg___lam__0(
    mut v_f_191_: *mut leanh::LeanObject,
    mut v_s_192_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toSemiring_193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ringId_194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_commSemiringInst_195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_addRightCancelInst_x3f_196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toQFn_x3f_197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_200_: u8 = 0;
    let mut v___x_201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_205_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toSemiring_193_ = leanh::lean_ctor_get(v_s_192_, 0);
                v_ringId_194_ = leanh::lean_ctor_get(v_s_192_, 1);
                v_commSemiringInst_195_ = leanh::lean_ctor_get(v_s_192_, 2);
                v_addRightCancelInst_x3f_196_ = leanh::lean_ctor_get(v_s_192_, 3);
                v_toQFn_x3f_197_ = leanh::lean_ctor_get(v_s_192_, 4);
                v_isSharedCheck_205_ = (!leanh::lean_is_exclusive(v_s_192_)) as u8;
                if v_isSharedCheck_205_ == 0 {
                    v___x_199_ = v_s_192_;
                    v_isShared_200_ = v_isSharedCheck_205_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_toQFn_x3f_197_);
                    leanh::lean_inc(v_addRightCancelInst_x3f_196_);
                    leanh::lean_inc(v_commSemiringInst_195_);
                    leanh::lean_inc(v_ringId_194_);
                    leanh::lean_inc(v_toSemiring_193_);
                    leanh::lean_dec(v_s_192_);
                    v___x_199_ = leanh::lean_box(0);
                    v_isShared_200_ = v_isSharedCheck_205_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_201_ = leanh::lean_apply_1(v_f_191_, v_toSemiring_193_);
                if v_isShared_200_ == 0 {
                    leanh::lean_ctor_set(v___x_199_, 0, v___x_201_);
                    v___x_203_ = v___x_199_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_204_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_204_, 0, v___x_201_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_204_, 1, v_ringId_194_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_204_, 2, v_commSemiringInst_195_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_204_,
                        3,
                        v_addRightCancelInst_x3f_196_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_204_, 4, v_toQFn_x3f_197_);
                    v___x_203_ = v_reuseFailAlloc_204_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_203_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringOfMonadOfMonadCommSemiring___redArg___lam__1(
    mut v_modifyCommSemiring_206_: *mut leanh::LeanObject,
    mut v_f_207_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_209_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_208_ = leanh::lean_alloc_closure(l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringOfMonadOfMonadCommSemiring___redArg___lam__0 as *mut core::ffi::c_void, 2, 1);
    leanh::lean_closure_set(v___f_208_, 0, v_f_207_);
    v___x_209_ = leanh::lean_apply_1(v_modifyCommSemiring_206_, v___f_208_);
    return v___x_209_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringOfMonadOfMonadCommSemiring___redArg___lam__2(
    mut v_toPure_210_: *mut leanh::LeanObject,
    mut v_____do__lift_211_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toSemiring_212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_213_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toSemiring_212_ = leanh::lean_ctor_get(v_____do__lift_211_, 0);
    leanh::lean_inc_ref(v_toSemiring_212_);
    leanh::lean_dec_ref(v_____do__lift_211_);
    v___x_213_ =
        leanh::lean_apply_2(v_toPure_210_, leanh::lean_box(0), v_toSemiring_212_);
    return v___x_213_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringOfMonadOfMonadCommSemiring___redArg(
    mut v_inst_214_: *mut leanh::LeanObject,
    mut v_inst_215_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getCommSemiring_218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifyCommSemiring_219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_222_: u8 = 0;
    let mut v_toPure_223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_230_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_216_ = leanh::lean_ctor_get(v_inst_214_, 0);
                leanh::lean_inc_ref(v_toApplicative_216_);
                v_toBind_217_ = leanh::lean_ctor_get(v_inst_214_, 1);
                leanh::lean_inc(v_toBind_217_);
                leanh::lean_dec_ref(v_inst_214_);
                v_getCommSemiring_218_ = leanh::lean_ctor_get(v_inst_215_, 0);
                v_modifyCommSemiring_219_ = leanh::lean_ctor_get(v_inst_215_, 1);
                v_isSharedCheck_230_ = (!leanh::lean_is_exclusive(v_inst_215_)) as u8;
                if v_isSharedCheck_230_ == 0 {
                    v___x_221_ = v_inst_215_;
                    v_isShared_222_ = v_isSharedCheck_230_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_modifyCommSemiring_219_);
                    leanh::lean_inc(v_getCommSemiring_218_);
                    leanh::lean_dec(v_inst_215_);
                    v___x_221_ = leanh::lean_box(0);
                    v_isShared_222_ = v_isSharedCheck_230_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toPure_223_ = leanh::lean_ctor_get(v_toApplicative_216_, 1);
                leanh::lean_inc(v_toPure_223_);
                leanh::lean_dec_ref(v_toApplicative_216_);
                v___f_224_ = leanh::lean_alloc_closure(l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringOfMonadOfMonadCommSemiring___redArg___lam__1 as *mut core::ffi::c_void, 2, 1);
                leanh::lean_closure_set(v___f_224_, 0, v_modifyCommSemiring_219_);
                v___f_225_ = leanh::lean_alloc_closure(l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringOfMonadOfMonadCommSemiring___redArg___lam__2 as *mut core::ffi::c_void, 2, 1);
                leanh::lean_closure_set(v___f_225_, 0, v_toPure_223_);
                v___x_226_ = leanh::lean_apply_4(
                    v_toBind_217_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v_getCommSemiring_218_,
                    v___f_225_,
                );
                if v_isShared_222_ == 0 {
                    leanh::lean_ctor_set(v___x_221_, 1, v___f_224_);
                    leanh::lean_ctor_set(v___x_221_, 0, v___x_226_);
                    v___x_228_ = v___x_221_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_229_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_229_, 0, v___x_226_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_229_, 1, v___f_224_);
                    v___x_228_ = v_reuseFailAlloc_229_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_228_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringOfMonadOfMonadCommSemiring(
    mut v_m_231_: *mut leanh::LeanObject,
    mut v_inst_232_: *mut leanh::LeanObject,
    mut v_inst_233_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getCommSemiring_236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifyCommSemiring_237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_240_: u8 = 0;
    let mut v_toPure_241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_248_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_234_ = leanh::lean_ctor_get(v_inst_232_, 0);
                leanh::lean_inc_ref(v_toApplicative_234_);
                v_toBind_235_ = leanh::lean_ctor_get(v_inst_232_, 1);
                leanh::lean_inc(v_toBind_235_);
                leanh::lean_dec_ref(v_inst_232_);
                v_getCommSemiring_236_ = leanh::lean_ctor_get(v_inst_233_, 0);
                v_modifyCommSemiring_237_ = leanh::lean_ctor_get(v_inst_233_, 1);
                v_isSharedCheck_248_ = (!leanh::lean_is_exclusive(v_inst_233_)) as u8;
                if v_isSharedCheck_248_ == 0 {
                    v___x_239_ = v_inst_233_;
                    v_isShared_240_ = v_isSharedCheck_248_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_modifyCommSemiring_237_);
                    leanh::lean_inc(v_getCommSemiring_236_);
                    leanh::lean_dec(v_inst_233_);
                    v___x_239_ = leanh::lean_box(0);
                    v_isShared_240_ = v_isSharedCheck_248_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toPure_241_ = leanh::lean_ctor_get(v_toApplicative_234_, 1);
                leanh::lean_inc(v_toPure_241_);
                leanh::lean_dec_ref(v_toApplicative_234_);
                v___f_242_ = leanh::lean_alloc_closure(l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringOfMonadOfMonadCommSemiring___redArg___lam__1 as *mut core::ffi::c_void, 2, 1);
                leanh::lean_closure_set(v___f_242_, 0, v_modifyCommSemiring_237_);
                v___f_243_ = leanh::lean_alloc_closure(l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringOfMonadOfMonadCommSemiring___redArg___lam__2 as *mut core::ffi::c_void, 2, 1);
                leanh::lean_closure_set(v___f_243_, 0, v_toPure_241_);
                v___x_244_ = leanh::lean_apply_4(
                    v_toBind_235_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v_getCommSemiring_236_,
                    v___f_243_,
                );
                if v_isShared_240_ == 0 {
                    leanh::lean_ctor_set(v___x_239_, 1, v___f_242_);
                    leanh::lean_ctor_set(v___x_239_, 0, v___x_244_);
                    v___x_246_ = v___x_239_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_247_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_247_, 0, v___x_244_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_247_, 1, v___f_242_);
                    v___x_246_ = v_reuseFailAlloc_247_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_246_;
            }
            _ => {}
        }
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_MonadSemiring(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Sym_Arith_MonadCanon(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Types(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_MonadSemiring(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_MonadSemiring(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Sym_Arith_MonadCanon(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Types(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_MonadSemiring(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_MonadSemiring(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_MonadSemiring(builtin);
}