// Lean compiler output
// Module: Std.Tactic.BVDecide.LRAT.Internal.CompactLRATChecker
// Imports: Std.Tactic.BVDecide.LRAT.Internal.LRATChecker Std.Tactic.BVDecide.LRAT.Internal.Formula.Implementation Std.Tactic.BVDecide.LRAT.Internal.Formula.Instance Std.Tactic.BVDecide.LRAT.Internal.Actions
use crate::ffi::{lean_array_fget_borrowed, lean_array_get_size, lean_nat_add, lean_nat_dec_lt};
use crate::r#gen::Init::Core::l_instBEqProd___redArg___lam__0___boxed;
use crate::r#gen::Init::Data::List::Basic::l_List_elem___redArg;
use crate::r#gen::Init::Prelude::l_instBEqOfDecidableEq___redArg___lam__0___boxed;
use crate::r#gen::Std::Tactic::BVDecide::LRAT::Internal::Actions::{
    initialize_Std_Tactic_BVDecide_LRAT_Internal_Actions,
    l_Std_Tactic_BVDecide_LRAT_Internal_intActionToDefaultClauseAction,
    runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Actions,
};
use crate::r#gen::Std::Tactic::BVDecide::LRAT::Internal::Formula::Implementation::{
    initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Implementation,
    l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_delete,
    l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatAdd,
    l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupAdd,
    runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Implementation,
};
use crate::r#gen::Std::Tactic::BVDecide::LRAT::Internal::Formula::Instance::{
    initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Instance,
    runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Instance,
};
use crate::r#gen::Std::Tactic::BVDecide::LRAT::Internal::LRATChecker::{
    initialize_Std_Tactic_BVDecide_LRAT_Internal_LRATChecker,
    runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_LRATChecker,
};
use crate::r#gen::Std::Tactic::BVDecide::LRAT::Internal::PosFin::l_Std_Tactic_BVDecide_LRAT_Internal_instDecidableEqPosFin___boxed;
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go___lam__0(
    mut v___x_161_: u8,
    mut v___y_162_: u8,
    mut v___y_163_: u8,
) -> u8 {
    if v___y_162_ == 0 {
        if v___y_163_ == 0 {
            return v___x_161_;
        } else {
            return v___y_162_;
        }
    } else {
        return v___y_163_;
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go___lam__0___boxed(
    mut v___x_164_: *mut leanh::LeanObject,
    mut v___y_165_: *mut leanh::LeanObject,
    mut v___y_166_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_429__boxed_167_: u8 = 0;
    let mut v___y_430__boxed_168_: u8 = 0;
    let mut v___y_431__boxed_169_: u8 = 0;
    let mut v_res_170_: u8 = 0;
    let mut v_r_171_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_429__boxed_167_ = (leanh::lean_unbox(v___x_164_) as u8);
    v___y_430__boxed_168_ = (leanh::lean_unbox(v___y_165_) as u8);
    v___y_431__boxed_169_ = (leanh::lean_unbox(v___y_166_) as u8);
    v_res_170_ = l_Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go___lam__0(
        v___x_429__boxed_167_,
        v___y_430__boxed_168_,
        v___y_431__boxed_169_,
    );
    v_r_171_ = leanh::lean_box((v_res_170_) as usize);
    return v_r_171_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go(
    mut v_n_172_: *mut leanh::LeanObject,
    mut v_f_173_: *mut leanh::LeanObject,
    mut v_proof_174_: *mut leanh::LeanObject,
    mut v_idx_175_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_177_: u8 = 0;
    let mut v___x_178_: u8 = 0;
    let mut v___x_179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_step_180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rupHints_185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_189_: u8 = 0;
    let mut v___x_190_: u8 = 0;
    let mut v___x_191_: u8 = 0;
    let mut v_c_192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rupHints_193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_196_: u8 = 0;
    let mut v___x_197_: u8 = 0;
    let mut v_fst_198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pivot_203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rupHints_204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ratHints_205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_212_: u8 = 0;
    let mut v___x_213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_218_: u8 = 0;
    let mut v___x_219_: u8 = 0;
    let mut v_fst_220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ids_224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_176_ = lean_array_get_size(v_proof_174_);
                v___x_177_ = lean_nat_dec_lt(v_idx_175_, v___x_176_);
                if v___x_177_ == 0 {
                    leanh::lean_dec(v_idx_175_);
                    leanh::lean_dec_ref(v_f_173_);
                    leanh::lean_dec(v_n_172_);
                    v___x_178_ = 1;
                    return v___x_178_;
                } else {
                    v___x_179_ = lean_array_fget_borrowed(v_proof_174_, v_idx_175_);
                    leanh::lean_inc(v___x_179_);
                    v_step_180_ =
                        l_Std_Tactic_BVDecide_LRAT_Internal_intActionToDefaultClauseAction(
                            v_n_172_, v___x_179_,
                        );
                    if leanh::lean_obj_tag(v_step_180_) == 0 {
                        v___x_181_ = leanh::lean_unsigned_to_nat(1);
                        v___x_182_ = lean_nat_add(v_idx_175_, v___x_181_);
                        leanh::lean_dec(v_idx_175_);
                        v_idx_175_ = v___x_182_;
                        state = 0;
                        continue;
                    } else {
                        v_val_184_ = leanh::lean_ctor_get(v_step_180_, 0);
                        leanh::lean_inc(v_val_184_);
                        leanh::lean_dec_ref_known(v_step_180_, 1);
                        match leanh::lean_obj_tag(v_val_184_) {
                            0 => {
                                leanh::lean_dec(v_idx_175_);
                                v_rupHints_185_ = leanh::lean_ctor_get(v_val_184_, 1);
                                leanh::lean_inc_ref(v_rupHints_185_);
                                leanh::lean_dec_ref_known(v_val_184_, 2);
                                v___x_186_ = leanh::lean_box(0);
                                v___x_187_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupAdd(v_n_172_, v_f_173_, v___x_186_, v_rupHints_185_);
                                leanh::lean_dec_ref(v_rupHints_185_);
                                leanh::lean_dec(v_n_172_);
                                v_snd_188_ = leanh::lean_ctor_get(v___x_187_, 1);
                                leanh::lean_inc(v_snd_188_);
                                leanh::lean_dec_ref(v___x_187_);
                                v___x_189_ = (leanh::lean_unbox(v_snd_188_) as u8);
                                leanh::lean_dec(v_snd_188_);
                                if v___x_189_ == 0 {
                                    v___x_190_ = 2;
                                    return v___x_190_;
                                } else {
                                    v___x_191_ = 0;
                                    return v___x_191_;
                                }
                            }
                            1 => {
                                v_c_192_ = leanh::lean_ctor_get(v_val_184_, 1);
                                leanh::lean_inc(v_c_192_);
                                v_rupHints_193_ = leanh::lean_ctor_get(v_val_184_, 2);
                                leanh::lean_inc_ref(v_rupHints_193_);
                                leanh::lean_dec_ref_known(v_val_184_, 3);
                                v___x_194_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupAdd(v_n_172_, v_f_173_, v_c_192_, v_rupHints_193_);
                                leanh::lean_dec_ref(v_rupHints_193_);
                                v_snd_195_ = leanh::lean_ctor_get(v___x_194_, 1);
                                leanh::lean_inc(v_snd_195_);
                                v___x_196_ = (leanh::lean_unbox(v_snd_195_) as u8);
                                leanh::lean_dec(v_snd_195_);
                                if v___x_196_ == 0 {
                                    leanh::lean_dec_ref(v___x_194_);
                                    leanh::lean_dec(v_idx_175_);
                                    leanh::lean_dec(v_n_172_);
                                    v___x_197_ = 2;
                                    return v___x_197_;
                                } else {
                                    v_fst_198_ = leanh::lean_ctor_get(v___x_194_, 0);
                                    leanh::lean_inc(v_fst_198_);
                                    leanh::lean_dec_ref(v___x_194_);
                                    v___x_199_ = leanh::lean_unsigned_to_nat(1);
                                    v___x_200_ = lean_nat_add(v_idx_175_, v___x_199_);
                                    leanh::lean_dec(v_idx_175_);
                                    v_f_173_ = v_fst_198_;
                                    v_idx_175_ = v___x_200_;
                                    state = 0;
                                    continue;
                                }
                            }
                            2 => {
                                v_c_202_ = leanh::lean_ctor_get(v_val_184_, 1);
                                leanh::lean_inc_n(v_c_202_, 2);
                                v_pivot_203_ = leanh::lean_ctor_get(v_val_184_, 2);
                                leanh::lean_inc_ref_n(v_pivot_203_, 2);
                                v_rupHints_204_ = leanh::lean_ctor_get(v_val_184_, 3);
                                leanh::lean_inc_ref(v_rupHints_204_);
                                v_ratHints_205_ = leanh::lean_ctor_get(v_val_184_, 4);
                                leanh::lean_inc_ref(v_ratHints_205_);
                                leanh::lean_dec_ref_known(v_val_184_, 5);
                                v___x_206_ = leanh::lean_box((v___x_177_) as usize);
                                v___f_207_ = leanh::lean_alloc_closure(l_Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go___lam__0___boxed as *mut core::ffi::c_void, 3, 1);
                                leanh::lean_closure_set(v___f_207_, 0, v___x_206_);
                                leanh::lean_inc(v_n_172_);
                                v___x_208_ = leanh::lean_alloc_closure(l_Std_Tactic_BVDecide_LRAT_Internal_instDecidableEqPosFin___boxed as *mut core::ffi::c_void, 3, 1);
                                leanh::lean_closure_set(v___x_208_, 0, v_n_172_);
                                v___f_209_ = leanh::lean_alloc_closure(
                                    l_instBEqOfDecidableEq___redArg___lam__0___boxed
                                        as *mut core::ffi::c_void,
                                    3,
                                    1,
                                );
                                leanh::lean_closure_set(v___f_209_, 0, v___x_208_);
                                v___f_210_ = leanh::lean_alloc_closure(
                                    l_instBEqOfDecidableEq___redArg___lam__0___boxed
                                        as *mut core::ffi::c_void,
                                    3,
                                    1,
                                );
                                leanh::lean_closure_set(v___f_210_, 0, v___f_207_);
                                v___f_211_ = leanh::lean_alloc_closure(
                                    l_instBEqProd___redArg___lam__0___boxed
                                        as *mut core::ffi::c_void,
                                    4,
                                    2,
                                );
                                leanh::lean_closure_set(v___f_211_, 0, v___f_209_);
                                leanh::lean_closure_set(v___f_211_, 1, v___f_210_);
                                v___x_212_ =
                                    l_List_elem___redArg(v___f_211_, v_pivot_203_, v_c_202_);
                                if v___x_212_ == 0 {
                                    leanh::lean_dec_ref(v_ratHints_205_);
                                    leanh::lean_dec_ref(v_rupHints_204_);
                                    leanh::lean_dec_ref(v_pivot_203_);
                                    leanh::lean_dec(v_c_202_);
                                    v___x_213_ = leanh::lean_unsigned_to_nat(1);
                                    v___x_214_ = lean_nat_add(v_idx_175_, v___x_213_);
                                    leanh::lean_dec(v_idx_175_);
                                    v_idx_175_ = v___x_214_;
                                    state = 0;
                                    continue;
                                } else {
                                    v___x_216_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatAdd(v_n_172_, v_f_173_, v_c_202_, v_pivot_203_, v_rupHints_204_, v_ratHints_205_);
                                    leanh::lean_dec_ref(v_rupHints_204_);
                                    v_snd_217_ = leanh::lean_ctor_get(v___x_216_, 1);
                                    leanh::lean_inc(v_snd_217_);
                                    v___x_218_ = (leanh::lean_unbox(v_snd_217_) as u8);
                                    leanh::lean_dec(v_snd_217_);
                                    if v___x_218_ == 0 {
                                        leanh::lean_dec_ref(v___x_216_);
                                        leanh::lean_dec(v_idx_175_);
                                        leanh::lean_dec(v_n_172_);
                                        v___x_219_ = 2;
                                        return v___x_219_;
                                    } else {
                                        v_fst_220_ = leanh::lean_ctor_get(v___x_216_, 0);
                                        leanh::lean_inc(v_fst_220_);
                                        leanh::lean_dec_ref(v___x_216_);
                                        v___x_221_ = leanh::lean_unsigned_to_nat(1);
                                        v___x_222_ = lean_nat_add(v_idx_175_, v___x_221_);
                                        leanh::lean_dec(v_idx_175_);
                                        v_f_173_ = v_fst_220_;
                                        v_idx_175_ = v___x_222_;
                                        state = 0;
                                        continue;
                                    }
                                }
                            }
                            _ => {
                                v_ids_224_ = leanh::lean_ctor_get(v_val_184_, 0);
                                leanh::lean_inc_ref(v_ids_224_);
                                leanh::lean_dec_ref_known(v_val_184_, 1);
                                v___x_225_ =
                                    l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_delete(
                                        v_n_172_, v_f_173_, v_ids_224_,
                                    );
                                leanh::lean_dec_ref(v_ids_224_);
                                v___x_226_ = leanh::lean_unsigned_to_nat(1);
                                v___x_227_ = lean_nat_add(v_idx_175_, v___x_226_);
                                leanh::lean_dec(v_idx_175_);
                                v_f_173_ = v___x_225_;
                                v_idx_175_ = v___x_227_;
                                state = 0;
                                continue;
                            }
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go___boxed(
    mut v_n_229_: *mut leanh::LeanObject,
    mut v_f_230_: *mut leanh::LeanObject,
    mut v_proof_231_: *mut leanh::LeanObject,
    mut v_idx_232_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_233_: u8 = 0;
    let mut v_r_234_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_233_ = l_Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go(
        v_n_229_,
        v_f_230_,
        v_proof_231_,
        v_idx_232_,
    );
    leanh::lean_dec_ref(v_proof_231_);
    v_r_234_ = leanh::lean_box((v_res_233_) as usize);
    return v_r_234_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATChecker_0__Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go_match__3_splitter___redArg(
    mut v_step_235_: *mut leanh::LeanObject,
    mut v_h__1_236_: *mut leanh::LeanObject,
    mut v_h__2_237_: *mut leanh::LeanObject,
    mut v_h__3_238_: *mut leanh::LeanObject,
    mut v_h__4_239_: *mut leanh::LeanObject,
    mut v_h__5_240_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_step_235_) == 0 {
        let mut v___x_241_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_242_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__5_240_);
        leanh::lean_dec(v_h__4_239_);
        leanh::lean_dec(v_h__3_238_);
        leanh::lean_dec(v_h__2_237_);
        v___x_241_ = leanh::lean_box(0);
        v___x_242_ = leanh::lean_apply_1(v_h__1_236_, v___x_241_);
        return v___x_242_;
    } else {
        let mut v_val_243_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_236_);
        v_val_243_ = leanh::lean_ctor_get(v_step_235_, 0);
        leanh::lean_inc(v_val_243_);
        leanh::lean_dec_ref_known(v_step_235_, 1);
        match leanh::lean_obj_tag(v_val_243_) {
            0 => {
                let mut v_id_244_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_rupHints_245_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_246_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v_h__5_240_);
                leanh::lean_dec(v_h__4_239_);
                leanh::lean_dec(v_h__3_238_);
                v_id_244_ = leanh::lean_ctor_get(v_val_243_, 0);
                leanh::lean_inc(v_id_244_);
                v_rupHints_245_ = leanh::lean_ctor_get(v_val_243_, 1);
                leanh::lean_inc_ref(v_rupHints_245_);
                leanh::lean_dec_ref_known(v_val_243_, 2);
                v___x_246_ = leanh::lean_apply_2(v_h__2_237_, v_id_244_, v_rupHints_245_);
                return v___x_246_;
            }
            1 => {
                let mut v_id_247_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_c_248_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_rupHints_249_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_250_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v_h__5_240_);
                leanh::lean_dec(v_h__4_239_);
                leanh::lean_dec(v_h__2_237_);
                v_id_247_ = leanh::lean_ctor_get(v_val_243_, 0);
                leanh::lean_inc(v_id_247_);
                v_c_248_ = leanh::lean_ctor_get(v_val_243_, 1);
                leanh::lean_inc(v_c_248_);
                v_rupHints_249_ = leanh::lean_ctor_get(v_val_243_, 2);
                leanh::lean_inc_ref(v_rupHints_249_);
                leanh::lean_dec_ref_known(v_val_243_, 3);
                v___x_250_ =
                    leanh::lean_apply_3(v_h__3_238_, v_id_247_, v_c_248_, v_rupHints_249_);
                return v___x_250_;
            }
            2 => {
                let mut v_id_251_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_c_252_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_pivot_253_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_rupHints_254_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_ratHints_255_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_256_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v_h__5_240_);
                leanh::lean_dec(v_h__3_238_);
                leanh::lean_dec(v_h__2_237_);
                v_id_251_ = leanh::lean_ctor_get(v_val_243_, 0);
                leanh::lean_inc(v_id_251_);
                v_c_252_ = leanh::lean_ctor_get(v_val_243_, 1);
                leanh::lean_inc(v_c_252_);
                v_pivot_253_ = leanh::lean_ctor_get(v_val_243_, 2);
                leanh::lean_inc_ref(v_pivot_253_);
                v_rupHints_254_ = leanh::lean_ctor_get(v_val_243_, 3);
                leanh::lean_inc_ref(v_rupHints_254_);
                v_ratHints_255_ = leanh::lean_ctor_get(v_val_243_, 4);
                leanh::lean_inc_ref(v_ratHints_255_);
                leanh::lean_dec_ref_known(v_val_243_, 5);
                v___x_256_ = leanh::lean_apply_5(
                    v_h__4_239_,
                    v_id_251_,
                    v_c_252_,
                    v_pivot_253_,
                    v_rupHints_254_,
                    v_ratHints_255_,
                );
                return v___x_256_;
            }
            _ => {
                let mut v_ids_257_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_258_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v_h__4_239_);
                leanh::lean_dec(v_h__3_238_);
                leanh::lean_dec(v_h__2_237_);
                v_ids_257_ = leanh::lean_ctor_get(v_val_243_, 0);
                leanh::lean_inc_ref(v_ids_257_);
                leanh::lean_dec_ref_known(v_val_243_, 1);
                v___x_258_ = leanh::lean_apply_1(v_h__5_240_, v_ids_257_);
                return v___x_258_;
            }
        }
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATChecker_0__Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go_match__3_splitter(
    mut v_n_259_: *mut leanh::LeanObject,
    mut v_motive_260_: *mut leanh::LeanObject,
    mut v_step_261_: *mut leanh::LeanObject,
    mut v_h__1_262_: *mut leanh::LeanObject,
    mut v_h__2_263_: *mut leanh::LeanObject,
    mut v_h__3_264_: *mut leanh::LeanObject,
    mut v_h__4_265_: *mut leanh::LeanObject,
    mut v_h__5_266_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_step_261_) == 0 {
        let mut v___x_267_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_268_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__5_266_);
        leanh::lean_dec(v_h__4_265_);
        leanh::lean_dec(v_h__3_264_);
        leanh::lean_dec(v_h__2_263_);
        v___x_267_ = leanh::lean_box(0);
        v___x_268_ = leanh::lean_apply_1(v_h__1_262_, v___x_267_);
        return v___x_268_;
    } else {
        let mut v_val_269_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_262_);
        v_val_269_ = leanh::lean_ctor_get(v_step_261_, 0);
        leanh::lean_inc(v_val_269_);
        leanh::lean_dec_ref_known(v_step_261_, 1);
        match leanh::lean_obj_tag(v_val_269_) {
            0 => {
                let mut v_id_270_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_rupHints_271_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_272_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v_h__5_266_);
                leanh::lean_dec(v_h__4_265_);
                leanh::lean_dec(v_h__3_264_);
                v_id_270_ = leanh::lean_ctor_get(v_val_269_, 0);
                leanh::lean_inc(v_id_270_);
                v_rupHints_271_ = leanh::lean_ctor_get(v_val_269_, 1);
                leanh::lean_inc_ref(v_rupHints_271_);
                leanh::lean_dec_ref_known(v_val_269_, 2);
                v___x_272_ = leanh::lean_apply_2(v_h__2_263_, v_id_270_, v_rupHints_271_);
                return v___x_272_;
            }
            1 => {
                let mut v_id_273_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_c_274_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_rupHints_275_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_276_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v_h__5_266_);
                leanh::lean_dec(v_h__4_265_);
                leanh::lean_dec(v_h__2_263_);
                v_id_273_ = leanh::lean_ctor_get(v_val_269_, 0);
                leanh::lean_inc(v_id_273_);
                v_c_274_ = leanh::lean_ctor_get(v_val_269_, 1);
                leanh::lean_inc(v_c_274_);
                v_rupHints_275_ = leanh::lean_ctor_get(v_val_269_, 2);
                leanh::lean_inc_ref(v_rupHints_275_);
                leanh::lean_dec_ref_known(v_val_269_, 3);
                v___x_276_ =
                    leanh::lean_apply_3(v_h__3_264_, v_id_273_, v_c_274_, v_rupHints_275_);
                return v___x_276_;
            }
            2 => {
                let mut v_id_277_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_c_278_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_pivot_279_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_rupHints_280_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_ratHints_281_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_282_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v_h__5_266_);
                leanh::lean_dec(v_h__3_264_);
                leanh::lean_dec(v_h__2_263_);
                v_id_277_ = leanh::lean_ctor_get(v_val_269_, 0);
                leanh::lean_inc(v_id_277_);
                v_c_278_ = leanh::lean_ctor_get(v_val_269_, 1);
                leanh::lean_inc(v_c_278_);
                v_pivot_279_ = leanh::lean_ctor_get(v_val_269_, 2);
                leanh::lean_inc_ref(v_pivot_279_);
                v_rupHints_280_ = leanh::lean_ctor_get(v_val_269_, 3);
                leanh::lean_inc_ref(v_rupHints_280_);
                v_ratHints_281_ = leanh::lean_ctor_get(v_val_269_, 4);
                leanh::lean_inc_ref(v_ratHints_281_);
                leanh::lean_dec_ref_known(v_val_269_, 5);
                v___x_282_ = leanh::lean_apply_5(
                    v_h__4_265_,
                    v_id_277_,
                    v_c_278_,
                    v_pivot_279_,
                    v_rupHints_280_,
                    v_ratHints_281_,
                );
                return v___x_282_;
            }
            _ => {
                let mut v_ids_283_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_284_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v_h__4_265_);
                leanh::lean_dec(v_h__3_264_);
                leanh::lean_dec(v_h__2_263_);
                v_ids_283_ = leanh::lean_ctor_get(v_val_269_, 0);
                leanh::lean_inc_ref(v_ids_283_);
                leanh::lean_dec_ref_known(v_val_269_, 1);
                v___x_284_ = leanh::lean_apply_1(v_h__5_266_, v_ids_283_);
                return v___x_284_;
            }
        }
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATChecker_0__Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go_match__3_splitter___boxed(
    mut v_n_285_: *mut leanh::LeanObject,
    mut v_motive_286_: *mut leanh::LeanObject,
    mut v_step_287_: *mut leanh::LeanObject,
    mut v_h__1_288_: *mut leanh::LeanObject,
    mut v_h__2_289_: *mut leanh::LeanObject,
    mut v_h__3_290_: *mut leanh::LeanObject,
    mut v_h__4_291_: *mut leanh::LeanObject,
    mut v_h__5_292_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_293_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_293_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATChecker_0__Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go_match__3_splitter(v_n_285_, v_motive_286_, v_step_287_, v_h__1_288_, v_h__2_289_, v_h__3_290_, v_h__4_291_, v_h__5_292_);
    leanh::lean_dec(v_n_285_);
    return v_res_293_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATChecker_0__Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go_match__1_splitter___redArg(
    mut v_x_294_: *mut leanh::LeanObject,
    mut v_h__1_295_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_298_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_296_ = leanh::lean_ctor_get(v_x_294_, 0);
    leanh::lean_inc(v_fst_296_);
    v_snd_297_ = leanh::lean_ctor_get(v_x_294_, 1);
    leanh::lean_inc(v_snd_297_);
    leanh::lean_dec_ref(v_x_294_);
    v___x_298_ = leanh::lean_apply_2(v_h__1_295_, v_fst_296_, v_snd_297_);
    return v___x_298_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATChecker_0__Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go_match__1_splitter(
    mut v_n_299_: *mut leanh::LeanObject,
    mut v_motive_300_: *mut leanh::LeanObject,
    mut v_x_301_: *mut leanh::LeanObject,
    mut v_h__1_302_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_305_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_303_ = leanh::lean_ctor_get(v_x_301_, 0);
    leanh::lean_inc(v_fst_303_);
    v_snd_304_ = leanh::lean_ctor_get(v_x_301_, 1);
    leanh::lean_inc(v_snd_304_);
    leanh::lean_dec_ref(v_x_301_);
    v___x_305_ = leanh::lean_apply_2(v_h__1_302_, v_fst_303_, v_snd_304_);
    return v___x_305_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATChecker_0__Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go_match__1_splitter___boxed(
    mut v_n_306_: *mut leanh::LeanObject,
    mut v_motive_307_: *mut leanh::LeanObject,
    mut v_x_308_: *mut leanh::LeanObject,
    mut v_h__1_309_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_310_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_310_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATChecker_0__Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go_match__1_splitter(v_n_306_, v_motive_307_, v_x_308_, v_h__1_309_);
    leanh::lean_dec(v_n_306_);
    return v_res_310_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker(
    mut v_n_311_: *mut leanh::LeanObject,
    mut v_f_312_: *mut leanh::LeanObject,
    mut v_proof_313_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_315_: u8 = 0;
    v___x_314_ = leanh::lean_unsigned_to_nat(0);
    v___x_315_ = l_Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go(
        v_n_311_,
        v_f_312_,
        v_proof_313_,
        v___x_314_,
    );
    return v___x_315_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker___boxed(
    mut v_n_316_: *mut leanh::LeanObject,
    mut v_f_317_: *mut leanh::LeanObject,
    mut v_proof_318_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_319_: u8 = 0;
    let mut v_r_320_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_319_ =
        l_Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker(v_n_316_, v_f_317_, v_proof_318_);
    leanh::lean_dec_ref(v_proof_318_);
    v_r_320_ = leanh::lean_box((v_res_319_) as usize);
    return v_r_320_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATChecker(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_LRATChecker(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Implementation(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Instance(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Actions(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATChecker(
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
pub unsafe fn initialize_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATChecker(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Tactic_BVDecide_LRAT_Internal_LRATChecker(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Implementation(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Instance(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_LRAT_Internal_Actions(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATChecker(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATChecker(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATChecker(builtin);
}