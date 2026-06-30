// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.CommRing.MonadRing
// Imports: Lean.Meta.Sym.Arith.MonadCanon Lean.Meta.Tactic.Grind.Arith.CommRing.Types
use crate::r#gen::Lean::Meta::Sym::Arith::MonadCanon::{
    initialize_Lean_Meta_Sym_Arith_MonadCanon, runtime_initialize_Lean_Meta_Sym_Arith_MonadCanon,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::CommRing::Types::{
    initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Types,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Types,
};
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_instMonadRingOfMonadLift___redArg___lam__0(
    mut v_modifyRing_139_: *mut leanh::LeanObject,
    mut v_inst_140_: *mut leanh::LeanObject,
    mut v_f_141_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_143_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_142_ = leanh::lean_apply_1(v_modifyRing_139_, v_f_141_);
    v___x_143_ = leanh::lean_apply_2(v_inst_140_, leanh::lean_box(0), v___x_142_);
    return v___x_143_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_instMonadRingOfMonadLift___redArg(
    mut v_inst_144_: *mut leanh::LeanObject,
    mut v_inst_145_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_getRing_146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifyRing_147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_150_: u8 = 0;
    let mut v___f_151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_156_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_getRing_146_ = leanh::lean_ctor_get(v_inst_145_, 0);
                v_modifyRing_147_ = leanh::lean_ctor_get(v_inst_145_, 1);
                v_isSharedCheck_156_ = (!leanh::lean_is_exclusive(v_inst_145_)) as u8;
                if v_isSharedCheck_156_ == 0 {
                    v___x_149_ = v_inst_145_;
                    v_isShared_150_ = v_isSharedCheck_156_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_modifyRing_147_);
                    leanh::lean_inc(v_getRing_146_);
                    leanh::lean_dec(v_inst_145_);
                    v___x_149_ = leanh::lean_box(0);
                    v_isShared_150_ = v_isSharedCheck_156_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_inst_144_);
                v___f_151_ = leanh::lean_alloc_closure(
                    l_Lean_Meta_Grind_Arith_CommRing_instMonadRingOfMonadLift___redArg___lam__0
                        as *mut core::ffi::c_void,
                    3,
                    2,
                );
                leanh::lean_closure_set(v___f_151_, 0, v_modifyRing_147_);
                leanh::lean_closure_set(v___f_151_, 1, v_inst_144_);
                v___x_152_ = leanh::lean_apply_2(
                    v_inst_144_,
                    leanh::lean_box(0),
                    v_getRing_146_,
                );
                if v_isShared_150_ == 0 {
                    leanh::lean_ctor_set(v___x_149_, 1, v___f_151_);
                    leanh::lean_ctor_set(v___x_149_, 0, v___x_152_);
                    v___x_154_ = v___x_149_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_155_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_155_, 0, v___x_152_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_155_, 1, v___f_151_);
                    v___x_154_ = v_reuseFailAlloc_155_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_154_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_instMonadRingOfMonadLift(
    mut v_m_157_: *mut leanh::LeanObject,
    mut v_n_158_: *mut leanh::LeanObject,
    mut v_inst_159_: *mut leanh::LeanObject,
    mut v_inst_160_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_getRing_161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifyRing_162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_165_: u8 = 0;
    let mut v___f_166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_171_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_getRing_161_ = leanh::lean_ctor_get(v_inst_160_, 0);
                v_modifyRing_162_ = leanh::lean_ctor_get(v_inst_160_, 1);
                v_isSharedCheck_171_ = (!leanh::lean_is_exclusive(v_inst_160_)) as u8;
                if v_isSharedCheck_171_ == 0 {
                    v___x_164_ = v_inst_160_;
                    v_isShared_165_ = v_isSharedCheck_171_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_modifyRing_162_);
                    leanh::lean_inc(v_getRing_161_);
                    leanh::lean_dec(v_inst_160_);
                    v___x_164_ = leanh::lean_box(0);
                    v_isShared_165_ = v_isSharedCheck_171_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_inst_159_);
                v___f_166_ = leanh::lean_alloc_closure(
                    l_Lean_Meta_Grind_Arith_CommRing_instMonadRingOfMonadLift___redArg___lam__0
                        as *mut core::ffi::c_void,
                    3,
                    2,
                );
                leanh::lean_closure_set(v___f_166_, 0, v_modifyRing_162_);
                leanh::lean_closure_set(v___f_166_, 1, v_inst_159_);
                v___x_167_ = leanh::lean_apply_2(
                    v_inst_159_,
                    leanh::lean_box(0),
                    v_getRing_161_,
                );
                if v_isShared_165_ == 0 {
                    leanh::lean_ctor_set(v___x_164_, 1, v___f_166_);
                    leanh::lean_ctor_set(v___x_164_, 0, v___x_167_);
                    v___x_169_ = v___x_164_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_170_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_170_, 0, v___x_167_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_170_, 1, v___f_166_);
                    v___x_169_ = v_reuseFailAlloc_170_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_169_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingOfMonadLift___redArg___lam__0(
    mut v_modifyCommRing_172_: *mut leanh::LeanObject,
    mut v_inst_173_: *mut leanh::LeanObject,
    mut v_f_174_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_176_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_175_ = leanh::lean_apply_1(v_modifyCommRing_172_, v_f_174_);
    v___x_176_ = leanh::lean_apply_2(v_inst_173_, leanh::lean_box(0), v___x_175_);
    return v___x_176_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingOfMonadLift___redArg(
    mut v_inst_177_: *mut leanh::LeanObject,
    mut v_inst_178_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_getCommRing_179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifyCommRing_180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_183_: u8 = 0;
    let mut v___f_184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_189_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_getCommRing_179_ = leanh::lean_ctor_get(v_inst_178_, 0);
                v_modifyCommRing_180_ = leanh::lean_ctor_get(v_inst_178_, 1);
                v_isSharedCheck_189_ = (!leanh::lean_is_exclusive(v_inst_178_)) as u8;
                if v_isSharedCheck_189_ == 0 {
                    v___x_182_ = v_inst_178_;
                    v_isShared_183_ = v_isSharedCheck_189_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_modifyCommRing_180_);
                    leanh::lean_inc(v_getCommRing_179_);
                    leanh::lean_dec(v_inst_178_);
                    v___x_182_ = leanh::lean_box(0);
                    v_isShared_183_ = v_isSharedCheck_189_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_inst_177_);
                v___f_184_ = leanh::lean_alloc_closure(
                    l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingOfMonadLift___redArg___lam__0
                        as *mut core::ffi::c_void,
                    3,
                    2,
                );
                leanh::lean_closure_set(v___f_184_, 0, v_modifyCommRing_180_);
                leanh::lean_closure_set(v___f_184_, 1, v_inst_177_);
                v___x_185_ = leanh::lean_apply_2(
                    v_inst_177_,
                    leanh::lean_box(0),
                    v_getCommRing_179_,
                );
                if v_isShared_183_ == 0 {
                    leanh::lean_ctor_set(v___x_182_, 1, v___f_184_);
                    leanh::lean_ctor_set(v___x_182_, 0, v___x_185_);
                    v___x_187_ = v___x_182_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_188_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_188_, 0, v___x_185_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_188_, 1, v___f_184_);
                    v___x_187_ = v_reuseFailAlloc_188_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_187_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingOfMonadLift(
    mut v_m_190_: *mut leanh::LeanObject,
    mut v_n_191_: *mut leanh::LeanObject,
    mut v_inst_192_: *mut leanh::LeanObject,
    mut v_inst_193_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_getCommRing_194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifyCommRing_195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_198_: u8 = 0;
    let mut v___f_199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_204_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_getCommRing_194_ = leanh::lean_ctor_get(v_inst_193_, 0);
                v_modifyCommRing_195_ = leanh::lean_ctor_get(v_inst_193_, 1);
                v_isSharedCheck_204_ = (!leanh::lean_is_exclusive(v_inst_193_)) as u8;
                if v_isSharedCheck_204_ == 0 {
                    v___x_197_ = v_inst_193_;
                    v_isShared_198_ = v_isSharedCheck_204_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_modifyCommRing_195_);
                    leanh::lean_inc(v_getCommRing_194_);
                    leanh::lean_dec(v_inst_193_);
                    v___x_197_ = leanh::lean_box(0);
                    v_isShared_198_ = v_isSharedCheck_204_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_inst_192_);
                v___f_199_ = leanh::lean_alloc_closure(
                    l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingOfMonadLift___redArg___lam__0
                        as *mut core::ffi::c_void,
                    3,
                    2,
                );
                leanh::lean_closure_set(v___f_199_, 0, v_modifyCommRing_195_);
                leanh::lean_closure_set(v___f_199_, 1, v_inst_192_);
                v___x_200_ = leanh::lean_apply_2(
                    v_inst_192_,
                    leanh::lean_box(0),
                    v_getCommRing_194_,
                );
                if v_isShared_198_ == 0 {
                    leanh::lean_ctor_set(v___x_197_, 1, v___f_199_);
                    leanh::lean_ctor_set(v___x_197_, 0, v___x_200_);
                    v___x_202_ = v___x_197_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_203_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_203_, 0, v___x_200_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_203_, 1, v___f_199_);
                    v___x_202_ = v_reuseFailAlloc_203_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_202_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_instMonadRingOfMonadOfMonadCommRing___redArg___lam__0(
    mut v_f_205_: *mut leanh::LeanObject,
    mut v_s_206_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toRing_207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_invFn_x3f_208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringId_x3f_209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_commSemiringInst_210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_commRingInst_211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_noZeroDivInst_x3f_212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fieldInst_x3f_213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_powIdentityInst_x3f_214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_denoteEntries_215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextId_216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_steps_217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_queue_218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_basis_219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diseqs_220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_recheck_221_: u8 = 0;
    let mut v_invSet_222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_powIdentityVarCount_223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numEq0_x3f_224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numEq0Updated_225_: u8 = 0;
    let mut v___x_227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_228_: u8 = 0;
    let mut v___x_229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_233_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toRing_207_ = leanh::lean_ctor_get(v_s_206_, 0);
                v_invFn_x3f_208_ = leanh::lean_ctor_get(v_s_206_, 1);
                v_semiringId_x3f_209_ = leanh::lean_ctor_get(v_s_206_, 2);
                v_commSemiringInst_210_ = leanh::lean_ctor_get(v_s_206_, 3);
                v_commRingInst_211_ = leanh::lean_ctor_get(v_s_206_, 4);
                v_noZeroDivInst_x3f_212_ = leanh::lean_ctor_get(v_s_206_, 5);
                v_fieldInst_x3f_213_ = leanh::lean_ctor_get(v_s_206_, 6);
                v_powIdentityInst_x3f_214_ = leanh::lean_ctor_get(v_s_206_, 7);
                v_denoteEntries_215_ = leanh::lean_ctor_get(v_s_206_, 8);
                v_nextId_216_ = leanh::lean_ctor_get(v_s_206_, 9);
                v_steps_217_ = leanh::lean_ctor_get(v_s_206_, 10);
                v_queue_218_ = leanh::lean_ctor_get(v_s_206_, 11);
                v_basis_219_ = leanh::lean_ctor_get(v_s_206_, 12);
                v_diseqs_220_ = leanh::lean_ctor_get(v_s_206_, 13);
                v_recheck_221_ = leanh::lean_ctor_get_uint8(
                    v_s_206_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 17) as u32,
                );
                v_invSet_222_ = leanh::lean_ctor_get(v_s_206_, 14);
                v_powIdentityVarCount_223_ = leanh::lean_ctor_get(v_s_206_, 15);
                v_numEq0_x3f_224_ = leanh::lean_ctor_get(v_s_206_, 16);
                v_numEq0Updated_225_ = leanh::lean_ctor_get_uint8(
                    v_s_206_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 17 + 1) as u32,
                );
                v_isSharedCheck_233_ = (!leanh::lean_is_exclusive(v_s_206_)) as u8;
                if v_isSharedCheck_233_ == 0 {
                    v___x_227_ = v_s_206_;
                    v_isShared_228_ = v_isSharedCheck_233_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_numEq0_x3f_224_);
                    leanh::lean_inc(v_powIdentityVarCount_223_);
                    leanh::lean_inc(v_invSet_222_);
                    leanh::lean_inc(v_diseqs_220_);
                    leanh::lean_inc(v_basis_219_);
                    leanh::lean_inc(v_queue_218_);
                    leanh::lean_inc(v_steps_217_);
                    leanh::lean_inc(v_nextId_216_);
                    leanh::lean_inc(v_denoteEntries_215_);
                    leanh::lean_inc(v_powIdentityInst_x3f_214_);
                    leanh::lean_inc(v_fieldInst_x3f_213_);
                    leanh::lean_inc(v_noZeroDivInst_x3f_212_);
                    leanh::lean_inc(v_commRingInst_211_);
                    leanh::lean_inc(v_commSemiringInst_210_);
                    leanh::lean_inc(v_semiringId_x3f_209_);
                    leanh::lean_inc(v_invFn_x3f_208_);
                    leanh::lean_inc(v_toRing_207_);
                    leanh::lean_dec(v_s_206_);
                    v___x_227_ = leanh::lean_box(0);
                    v_isShared_228_ = v_isSharedCheck_233_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_229_ = leanh::lean_apply_1(v_f_205_, v_toRing_207_);
                if v_isShared_228_ == 0 {
                    leanh::lean_ctor_set(v___x_227_, 0, v___x_229_);
                    v___x_231_ = v___x_227_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_232_ = leanh::lean_alloc_ctor(0, 17, (2) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_232_, 0, v___x_229_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_232_, 1, v_invFn_x3f_208_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_232_, 2, v_semiringId_x3f_209_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_232_, 3, v_commSemiringInst_210_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_232_, 4, v_commRingInst_211_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_232_, 5, v_noZeroDivInst_x3f_212_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_232_, 6, v_fieldInst_x3f_213_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_232_,
                        7,
                        v_powIdentityInst_x3f_214_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_232_, 8, v_denoteEntries_215_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_232_, 9, v_nextId_216_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_232_, 10, v_steps_217_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_232_, 11, v_queue_218_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_232_, 12, v_basis_219_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_232_, 13, v_diseqs_220_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_232_, 14, v_invSet_222_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_232_,
                        15,
                        v_powIdentityVarCount_223_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_232_, 16, v_numEq0_x3f_224_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_232_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 17) as u32,
                        v_recheck_221_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_232_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 17 + 1) as u32,
                        v_numEq0Updated_225_,
                    );
                    v___x_231_ = v_reuseFailAlloc_232_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_231_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_instMonadRingOfMonadOfMonadCommRing___redArg___lam__1(
    mut v_modifyCommRing_234_: *mut leanh::LeanObject,
    mut v_f_235_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_237_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_236_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_instMonadRingOfMonadOfMonadCommRing___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_236_, 0, v_f_235_);
    v___x_237_ = leanh::lean_apply_1(v_modifyCommRing_234_, v___f_236_);
    return v___x_237_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_instMonadRingOfMonadOfMonadCommRing___redArg___lam__2(
    mut v_toPure_238_: *mut leanh::LeanObject,
    mut v_____do__lift_239_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toRing_240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_241_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toRing_240_ = leanh::lean_ctor_get(v_____do__lift_239_, 0);
    leanh::lean_inc_ref(v_toRing_240_);
    leanh::lean_dec_ref(v_____do__lift_239_);
    v___x_241_ =
        leanh::lean_apply_2(v_toPure_238_, leanh::lean_box(0), v_toRing_240_);
    return v___x_241_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_instMonadRingOfMonadOfMonadCommRing___redArg(
    mut v_inst_242_: *mut leanh::LeanObject,
    mut v_inst_243_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getCommRing_246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifyCommRing_247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_250_: u8 = 0;
    let mut v_toPure_251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_258_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_244_ = leanh::lean_ctor_get(v_inst_242_, 0);
                leanh::lean_inc_ref(v_toApplicative_244_);
                v_toBind_245_ = leanh::lean_ctor_get(v_inst_242_, 1);
                leanh::lean_inc(v_toBind_245_);
                leanh::lean_dec_ref(v_inst_242_);
                v_getCommRing_246_ = leanh::lean_ctor_get(v_inst_243_, 0);
                v_modifyCommRing_247_ = leanh::lean_ctor_get(v_inst_243_, 1);
                v_isSharedCheck_258_ = (!leanh::lean_is_exclusive(v_inst_243_)) as u8;
                if v_isSharedCheck_258_ == 0 {
                    v___x_249_ = v_inst_243_;
                    v_isShared_250_ = v_isSharedCheck_258_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_modifyCommRing_247_);
                    leanh::lean_inc(v_getCommRing_246_);
                    leanh::lean_dec(v_inst_243_);
                    v___x_249_ = leanh::lean_box(0);
                    v_isShared_250_ = v_isSharedCheck_258_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toPure_251_ = leanh::lean_ctor_get(v_toApplicative_244_, 1);
                leanh::lean_inc(v_toPure_251_);
                leanh::lean_dec_ref(v_toApplicative_244_);
                v___f_252_ = leanh::lean_alloc_closure(l_Lean_Meta_Grind_Arith_CommRing_instMonadRingOfMonadOfMonadCommRing___redArg___lam__1 as *mut core::ffi::c_void, 2, 1);
                leanh::lean_closure_set(v___f_252_, 0, v_modifyCommRing_247_);
                v___f_253_ = leanh::lean_alloc_closure(l_Lean_Meta_Grind_Arith_CommRing_instMonadRingOfMonadOfMonadCommRing___redArg___lam__2 as *mut core::ffi::c_void, 2, 1);
                leanh::lean_closure_set(v___f_253_, 0, v_toPure_251_);
                v___x_254_ = leanh::lean_apply_4(
                    v_toBind_245_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v_getCommRing_246_,
                    v___f_253_,
                );
                if v_isShared_250_ == 0 {
                    leanh::lean_ctor_set(v___x_249_, 1, v___f_252_);
                    leanh::lean_ctor_set(v___x_249_, 0, v___x_254_);
                    v___x_256_ = v___x_249_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_257_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_257_, 0, v___x_254_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_257_, 1, v___f_252_);
                    v___x_256_ = v_reuseFailAlloc_257_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_256_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_instMonadRingOfMonadOfMonadCommRing(
    mut v_m_259_: *mut leanh::LeanObject,
    mut v_inst_260_: *mut leanh::LeanObject,
    mut v_inst_261_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getCommRing_264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifyCommRing_265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_268_: u8 = 0;
    let mut v_toPure_269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_276_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_262_ = leanh::lean_ctor_get(v_inst_260_, 0);
                leanh::lean_inc_ref(v_toApplicative_262_);
                v_toBind_263_ = leanh::lean_ctor_get(v_inst_260_, 1);
                leanh::lean_inc(v_toBind_263_);
                leanh::lean_dec_ref(v_inst_260_);
                v_getCommRing_264_ = leanh::lean_ctor_get(v_inst_261_, 0);
                v_modifyCommRing_265_ = leanh::lean_ctor_get(v_inst_261_, 1);
                v_isSharedCheck_276_ = (!leanh::lean_is_exclusive(v_inst_261_)) as u8;
                if v_isSharedCheck_276_ == 0 {
                    v___x_267_ = v_inst_261_;
                    v_isShared_268_ = v_isSharedCheck_276_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_modifyCommRing_265_);
                    leanh::lean_inc(v_getCommRing_264_);
                    leanh::lean_dec(v_inst_261_);
                    v___x_267_ = leanh::lean_box(0);
                    v_isShared_268_ = v_isSharedCheck_276_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toPure_269_ = leanh::lean_ctor_get(v_toApplicative_262_, 1);
                leanh::lean_inc(v_toPure_269_);
                leanh::lean_dec_ref(v_toApplicative_262_);
                v___f_270_ = leanh::lean_alloc_closure(l_Lean_Meta_Grind_Arith_CommRing_instMonadRingOfMonadOfMonadCommRing___redArg___lam__1 as *mut core::ffi::c_void, 2, 1);
                leanh::lean_closure_set(v___f_270_, 0, v_modifyCommRing_265_);
                v___f_271_ = leanh::lean_alloc_closure(l_Lean_Meta_Grind_Arith_CommRing_instMonadRingOfMonadOfMonadCommRing___redArg___lam__2 as *mut core::ffi::c_void, 2, 1);
                leanh::lean_closure_set(v___f_271_, 0, v_toPure_269_);
                v___x_272_ = leanh::lean_apply_4(
                    v_toBind_263_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v_getCommRing_264_,
                    v___f_271_,
                );
                if v_isShared_268_ == 0 {
                    leanh::lean_ctor_set(v___x_267_, 1, v___f_270_);
                    leanh::lean_ctor_set(v___x_267_, 0, v___x_272_);
                    v___x_274_ = v___x_267_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_275_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_275_, 0, v___x_272_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_275_, 1, v___f_270_);
                    v___x_274_ = v_reuseFailAlloc_275_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_274_;
            }
            _ => {}
        }
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_MonadRing(
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
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_MonadRing(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_MonadRing(
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
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_MonadRing(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_MonadRing(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_MonadRing(builtin);
}