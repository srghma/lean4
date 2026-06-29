// Lean compiler output
// Module: Std.Tactic.BVDecide.LRAT.Internal.CompactLRATChecker
// Imports: Std.Tactic.BVDecide.LRAT.Internal.LRATChecker Std.Tactic.BVDecide.LRAT.Internal.Formula.Implementation Std.Tactic.BVDecide.LRAT.Internal.Formula.Instance Std.Tactic.BVDecide.LRAT.Internal.Actions
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
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget_borrowed, lean_array_get_size, lean_nat_add, lean_nat_dec_lt,
};
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
    mut v___x_164_: *mut crate::leanh::LeanObject,
    mut v___y_165_: *mut crate::leanh::LeanObject,
    mut v___y_166_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_429__boxed_167_: u8 = 0;
    let mut v___y_430__boxed_168_: u8 = 0;
    let mut v___y_431__boxed_169_: u8 = 0;
    let mut v_res_170_: u8 = 0;
    let mut v_r_171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_429__boxed_167_ = (crate::leanh::lean_unbox(v___x_164_) as u8);
    v___y_430__boxed_168_ = (crate::leanh::lean_unbox(v___y_165_) as u8);
    v___y_431__boxed_169_ = (crate::leanh::lean_unbox(v___y_166_) as u8);
    v_res_170_ = l_Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go___lam__0(
        v___x_429__boxed_167_,
        v___y_430__boxed_168_,
        v___y_431__boxed_169_,
    );
    v_r_171_ = crate::leanh::lean_box((v_res_170_) as usize);
    return v_r_171_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go(
    mut v_n_172_: *mut crate::leanh::LeanObject,
    mut v_f_173_: *mut crate::leanh::LeanObject,
    mut v_proof_174_: *mut crate::leanh::LeanObject,
    mut v_idx_175_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_177_: u8 = 0;
    let mut v___x_178_: u8 = 0;
    let mut v___x_179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_step_180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rupHints_185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_189_: u8 = 0;
    let mut v___x_190_: u8 = 0;
    let mut v___x_191_: u8 = 0;
    let mut v_c_192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rupHints_193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_196_: u8 = 0;
    let mut v___x_197_: u8 = 0;
    let mut v_fst_198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pivot_203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rupHints_204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ratHints_205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_212_: u8 = 0;
    let mut v___x_213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_218_: u8 = 0;
    let mut v___x_219_: u8 = 0;
    let mut v_fst_220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ids_224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_176_ = lean_array_get_size(v_proof_174_);
                v___x_177_ = lean_nat_dec_lt(v_idx_175_, v___x_176_);
                if v___x_177_ == 0 {
                    crate::leanh::lean_dec(v_idx_175_);
                    crate::leanh::lean_dec_ref(v_f_173_);
                    crate::leanh::lean_dec(v_n_172_);
                    v___x_178_ = 1;
                    return v___x_178_;
                } else {
                    v___x_179_ = lean_array_fget_borrowed(v_proof_174_, v_idx_175_);
                    crate::leanh::lean_inc(v___x_179_);
                    v_step_180_ =
                        l_Std_Tactic_BVDecide_LRAT_Internal_intActionToDefaultClauseAction(
                            v_n_172_, v___x_179_,
                        );
                    if crate::leanh::lean_obj_tag(v_step_180_) == 0 {
                        v___x_181_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_182_ = lean_nat_add(v_idx_175_, v___x_181_);
                        crate::leanh::lean_dec(v_idx_175_);
                        v_idx_175_ = v___x_182_;
                        state = 0;
                        continue;
                    } else {
                        v_val_184_ = crate::leanh::lean_ctor_get(v_step_180_, 0);
                        crate::leanh::lean_inc(v_val_184_);
                        crate::leanh::lean_dec_ref_known(v_step_180_, 1);
                        match crate::leanh::lean_obj_tag(v_val_184_) {
                            0 => {
                                crate::leanh::lean_dec(v_idx_175_);
                                v_rupHints_185_ = crate::leanh::lean_ctor_get(v_val_184_, 1);
                                crate::leanh::lean_inc_ref(v_rupHints_185_);
                                crate::leanh::lean_dec_ref_known(v_val_184_, 2);
                                v___x_186_ = crate::leanh::lean_box(0);
                                v___x_187_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupAdd(v_n_172_, v_f_173_, v___x_186_, v_rupHints_185_);
                                crate::leanh::lean_dec_ref(v_rupHints_185_);
                                crate::leanh::lean_dec(v_n_172_);
                                v_snd_188_ = crate::leanh::lean_ctor_get(v___x_187_, 1);
                                crate::leanh::lean_inc(v_snd_188_);
                                crate::leanh::lean_dec_ref(v___x_187_);
                                v___x_189_ = (crate::leanh::lean_unbox(v_snd_188_) as u8);
                                crate::leanh::lean_dec(v_snd_188_);
                                if v___x_189_ == 0 {
                                    v___x_190_ = 2;
                                    return v___x_190_;
                                } else {
                                    v___x_191_ = 0;
                                    return v___x_191_;
                                }
                            }
                            1 => {
                                v_c_192_ = crate::leanh::lean_ctor_get(v_val_184_, 1);
                                crate::leanh::lean_inc(v_c_192_);
                                v_rupHints_193_ = crate::leanh::lean_ctor_get(v_val_184_, 2);
                                crate::leanh::lean_inc_ref(v_rupHints_193_);
                                crate::leanh::lean_dec_ref_known(v_val_184_, 3);
                                v___x_194_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupAdd(v_n_172_, v_f_173_, v_c_192_, v_rupHints_193_);
                                crate::leanh::lean_dec_ref(v_rupHints_193_);
                                v_snd_195_ = crate::leanh::lean_ctor_get(v___x_194_, 1);
                                crate::leanh::lean_inc(v_snd_195_);
                                v___x_196_ = (crate::leanh::lean_unbox(v_snd_195_) as u8);
                                crate::leanh::lean_dec(v_snd_195_);
                                if v___x_196_ == 0 {
                                    crate::leanh::lean_dec_ref(v___x_194_);
                                    crate::leanh::lean_dec(v_idx_175_);
                                    crate::leanh::lean_dec(v_n_172_);
                                    v___x_197_ = 2;
                                    return v___x_197_;
                                } else {
                                    v_fst_198_ = crate::leanh::lean_ctor_get(v___x_194_, 0);
                                    crate::leanh::lean_inc(v_fst_198_);
                                    crate::leanh::lean_dec_ref(v___x_194_);
                                    v___x_199_ = crate::leanh::lean_unsigned_to_nat(1);
                                    v___x_200_ = lean_nat_add(v_idx_175_, v___x_199_);
                                    crate::leanh::lean_dec(v_idx_175_);
                                    v_f_173_ = v_fst_198_;
                                    v_idx_175_ = v___x_200_;
                                    state = 0;
                                    continue;
                                }
                            }
                            2 => {
                                v_c_202_ = crate::leanh::lean_ctor_get(v_val_184_, 1);
                                crate::leanh::lean_inc_n(v_c_202_, 2);
                                v_pivot_203_ = crate::leanh::lean_ctor_get(v_val_184_, 2);
                                crate::leanh::lean_inc_ref_n(v_pivot_203_, 2);
                                v_rupHints_204_ = crate::leanh::lean_ctor_get(v_val_184_, 3);
                                crate::leanh::lean_inc_ref(v_rupHints_204_);
                                v_ratHints_205_ = crate::leanh::lean_ctor_get(v_val_184_, 4);
                                crate::leanh::lean_inc_ref(v_ratHints_205_);
                                crate::leanh::lean_dec_ref_known(v_val_184_, 5);
                                v___x_206_ = crate::leanh::lean_box((v___x_177_) as usize);
                                v___f_207_ = crate::leanh::lean_alloc_closure(l_Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go___lam__0___boxed as *mut core::ffi::c_void, 3, 1);
                                crate::leanh::lean_closure_set(v___f_207_, 0, v___x_206_);
                                crate::leanh::lean_inc(v_n_172_);
                                v___x_208_ = crate::leanh::lean_alloc_closure(l_Std_Tactic_BVDecide_LRAT_Internal_instDecidableEqPosFin___boxed as *mut core::ffi::c_void, 3, 1);
                                crate::leanh::lean_closure_set(v___x_208_, 0, v_n_172_);
                                v___f_209_ = crate::leanh::lean_alloc_closure(
                                    l_instBEqOfDecidableEq___redArg___lam__0___boxed
                                        as *mut core::ffi::c_void,
                                    3,
                                    1,
                                );
                                crate::leanh::lean_closure_set(v___f_209_, 0, v___x_208_);
                                v___f_210_ = crate::leanh::lean_alloc_closure(
                                    l_instBEqOfDecidableEq___redArg___lam__0___boxed
                                        as *mut core::ffi::c_void,
                                    3,
                                    1,
                                );
                                crate::leanh::lean_closure_set(v___f_210_, 0, v___f_207_);
                                v___f_211_ = crate::leanh::lean_alloc_closure(
                                    l_instBEqProd___redArg___lam__0___boxed
                                        as *mut core::ffi::c_void,
                                    4,
                                    2,
                                );
                                crate::leanh::lean_closure_set(v___f_211_, 0, v___f_209_);
                                crate::leanh::lean_closure_set(v___f_211_, 1, v___f_210_);
                                v___x_212_ =
                                    l_List_elem___redArg(v___f_211_, v_pivot_203_, v_c_202_);
                                if v___x_212_ == 0 {
                                    crate::leanh::lean_dec_ref(v_ratHints_205_);
                                    crate::leanh::lean_dec_ref(v_rupHints_204_);
                                    crate::leanh::lean_dec_ref(v_pivot_203_);
                                    crate::leanh::lean_dec(v_c_202_);
                                    v___x_213_ = crate::leanh::lean_unsigned_to_nat(1);
                                    v___x_214_ = lean_nat_add(v_idx_175_, v___x_213_);
                                    crate::leanh::lean_dec(v_idx_175_);
                                    v_idx_175_ = v___x_214_;
                                    state = 0;
                                    continue;
                                } else {
                                    v___x_216_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatAdd(v_n_172_, v_f_173_, v_c_202_, v_pivot_203_, v_rupHints_204_, v_ratHints_205_);
                                    crate::leanh::lean_dec_ref(v_rupHints_204_);
                                    v_snd_217_ = crate::leanh::lean_ctor_get(v___x_216_, 1);
                                    crate::leanh::lean_inc(v_snd_217_);
                                    v___x_218_ = (crate::leanh::lean_unbox(v_snd_217_) as u8);
                                    crate::leanh::lean_dec(v_snd_217_);
                                    if v___x_218_ == 0 {
                                        crate::leanh::lean_dec_ref(v___x_216_);
                                        crate::leanh::lean_dec(v_idx_175_);
                                        crate::leanh::lean_dec(v_n_172_);
                                        v___x_219_ = 2;
                                        return v___x_219_;
                                    } else {
                                        v_fst_220_ = crate::leanh::lean_ctor_get(v___x_216_, 0);
                                        crate::leanh::lean_inc(v_fst_220_);
                                        crate::leanh::lean_dec_ref(v___x_216_);
                                        v___x_221_ = crate::leanh::lean_unsigned_to_nat(1);
                                        v___x_222_ = lean_nat_add(v_idx_175_, v___x_221_);
                                        crate::leanh::lean_dec(v_idx_175_);
                                        v_f_173_ = v_fst_220_;
                                        v_idx_175_ = v___x_222_;
                                        state = 0;
                                        continue;
                                    }
                                }
                            }
                            _ => {
                                v_ids_224_ = crate::leanh::lean_ctor_get(v_val_184_, 0);
                                crate::leanh::lean_inc_ref(v_ids_224_);
                                crate::leanh::lean_dec_ref_known(v_val_184_, 1);
                                v___x_225_ =
                                    l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_delete(
                                        v_n_172_, v_f_173_, v_ids_224_,
                                    );
                                crate::leanh::lean_dec_ref(v_ids_224_);
                                v___x_226_ = crate::leanh::lean_unsigned_to_nat(1);
                                v___x_227_ = lean_nat_add(v_idx_175_, v___x_226_);
                                crate::leanh::lean_dec(v_idx_175_);
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
    mut v_n_229_: *mut crate::leanh::LeanObject,
    mut v_f_230_: *mut crate::leanh::LeanObject,
    mut v_proof_231_: *mut crate::leanh::LeanObject,
    mut v_idx_232_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_233_: u8 = 0;
    let mut v_r_234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_233_ = l_Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go(
        v_n_229_,
        v_f_230_,
        v_proof_231_,
        v_idx_232_,
    );
    crate::leanh::lean_dec_ref(v_proof_231_);
    v_r_234_ = crate::leanh::lean_box((v_res_233_) as usize);
    return v_r_234_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATChecker_0__Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go_match__3_splitter___redArg(
    mut v_step_235_: *mut crate::leanh::LeanObject,
    mut v_h__1_236_: *mut crate::leanh::LeanObject,
    mut v_h__2_237_: *mut crate::leanh::LeanObject,
    mut v_h__3_238_: *mut crate::leanh::LeanObject,
    mut v_h__4_239_: *mut crate::leanh::LeanObject,
    mut v_h__5_240_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_step_235_) == 0 {
        let mut v___x_241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__5_240_);
        crate::leanh::lean_dec(v_h__4_239_);
        crate::leanh::lean_dec(v_h__3_238_);
        crate::leanh::lean_dec(v_h__2_237_);
        v___x_241_ = crate::leanh::lean_box(0);
        v___x_242_ = crate::leanh::lean_apply_1(v_h__1_236_, v___x_241_);
        return v___x_242_;
    } else {
        let mut v_val_243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_236_);
        v_val_243_ = crate::leanh::lean_ctor_get(v_step_235_, 0);
        crate::leanh::lean_inc(v_val_243_);
        crate::leanh::lean_dec_ref_known(v_step_235_, 1);
        match crate::leanh::lean_obj_tag(v_val_243_) {
            0 => {
                let mut v_id_244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_rupHints_245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_h__5_240_);
                crate::leanh::lean_dec(v_h__4_239_);
                crate::leanh::lean_dec(v_h__3_238_);
                v_id_244_ = crate::leanh::lean_ctor_get(v_val_243_, 0);
                crate::leanh::lean_inc(v_id_244_);
                v_rupHints_245_ = crate::leanh::lean_ctor_get(v_val_243_, 1);
                crate::leanh::lean_inc_ref(v_rupHints_245_);
                crate::leanh::lean_dec_ref_known(v_val_243_, 2);
                v___x_246_ = crate::leanh::lean_apply_2(v_h__2_237_, v_id_244_, v_rupHints_245_);
                return v___x_246_;
            }
            1 => {
                let mut v_id_247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_c_248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_rupHints_249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_h__5_240_);
                crate::leanh::lean_dec(v_h__4_239_);
                crate::leanh::lean_dec(v_h__2_237_);
                v_id_247_ = crate::leanh::lean_ctor_get(v_val_243_, 0);
                crate::leanh::lean_inc(v_id_247_);
                v_c_248_ = crate::leanh::lean_ctor_get(v_val_243_, 1);
                crate::leanh::lean_inc(v_c_248_);
                v_rupHints_249_ = crate::leanh::lean_ctor_get(v_val_243_, 2);
                crate::leanh::lean_inc_ref(v_rupHints_249_);
                crate::leanh::lean_dec_ref_known(v_val_243_, 3);
                v___x_250_ =
                    crate::leanh::lean_apply_3(v_h__3_238_, v_id_247_, v_c_248_, v_rupHints_249_);
                return v___x_250_;
            }
            2 => {
                let mut v_id_251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_c_252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_pivot_253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_rupHints_254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_ratHints_255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_h__5_240_);
                crate::leanh::lean_dec(v_h__3_238_);
                crate::leanh::lean_dec(v_h__2_237_);
                v_id_251_ = crate::leanh::lean_ctor_get(v_val_243_, 0);
                crate::leanh::lean_inc(v_id_251_);
                v_c_252_ = crate::leanh::lean_ctor_get(v_val_243_, 1);
                crate::leanh::lean_inc(v_c_252_);
                v_pivot_253_ = crate::leanh::lean_ctor_get(v_val_243_, 2);
                crate::leanh::lean_inc_ref(v_pivot_253_);
                v_rupHints_254_ = crate::leanh::lean_ctor_get(v_val_243_, 3);
                crate::leanh::lean_inc_ref(v_rupHints_254_);
                v_ratHints_255_ = crate::leanh::lean_ctor_get(v_val_243_, 4);
                crate::leanh::lean_inc_ref(v_ratHints_255_);
                crate::leanh::lean_dec_ref_known(v_val_243_, 5);
                v___x_256_ = crate::leanh::lean_apply_5(
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
                let mut v_ids_257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_h__4_239_);
                crate::leanh::lean_dec(v_h__3_238_);
                crate::leanh::lean_dec(v_h__2_237_);
                v_ids_257_ = crate::leanh::lean_ctor_get(v_val_243_, 0);
                crate::leanh::lean_inc_ref(v_ids_257_);
                crate::leanh::lean_dec_ref_known(v_val_243_, 1);
                v___x_258_ = crate::leanh::lean_apply_1(v_h__5_240_, v_ids_257_);
                return v___x_258_;
            }
        }
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATChecker_0__Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go_match__3_splitter(
    mut v_n_259_: *mut crate::leanh::LeanObject,
    mut v_motive_260_: *mut crate::leanh::LeanObject,
    mut v_step_261_: *mut crate::leanh::LeanObject,
    mut v_h__1_262_: *mut crate::leanh::LeanObject,
    mut v_h__2_263_: *mut crate::leanh::LeanObject,
    mut v_h__3_264_: *mut crate::leanh::LeanObject,
    mut v_h__4_265_: *mut crate::leanh::LeanObject,
    mut v_h__5_266_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_step_261_) == 0 {
        let mut v___x_267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__5_266_);
        crate::leanh::lean_dec(v_h__4_265_);
        crate::leanh::lean_dec(v_h__3_264_);
        crate::leanh::lean_dec(v_h__2_263_);
        v___x_267_ = crate::leanh::lean_box(0);
        v___x_268_ = crate::leanh::lean_apply_1(v_h__1_262_, v___x_267_);
        return v___x_268_;
    } else {
        let mut v_val_269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_262_);
        v_val_269_ = crate::leanh::lean_ctor_get(v_step_261_, 0);
        crate::leanh::lean_inc(v_val_269_);
        crate::leanh::lean_dec_ref_known(v_step_261_, 1);
        match crate::leanh::lean_obj_tag(v_val_269_) {
            0 => {
                let mut v_id_270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_rupHints_271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_h__5_266_);
                crate::leanh::lean_dec(v_h__4_265_);
                crate::leanh::lean_dec(v_h__3_264_);
                v_id_270_ = crate::leanh::lean_ctor_get(v_val_269_, 0);
                crate::leanh::lean_inc(v_id_270_);
                v_rupHints_271_ = crate::leanh::lean_ctor_get(v_val_269_, 1);
                crate::leanh::lean_inc_ref(v_rupHints_271_);
                crate::leanh::lean_dec_ref_known(v_val_269_, 2);
                v___x_272_ = crate::leanh::lean_apply_2(v_h__2_263_, v_id_270_, v_rupHints_271_);
                return v___x_272_;
            }
            1 => {
                let mut v_id_273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_c_274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_rupHints_275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_h__5_266_);
                crate::leanh::lean_dec(v_h__4_265_);
                crate::leanh::lean_dec(v_h__2_263_);
                v_id_273_ = crate::leanh::lean_ctor_get(v_val_269_, 0);
                crate::leanh::lean_inc(v_id_273_);
                v_c_274_ = crate::leanh::lean_ctor_get(v_val_269_, 1);
                crate::leanh::lean_inc(v_c_274_);
                v_rupHints_275_ = crate::leanh::lean_ctor_get(v_val_269_, 2);
                crate::leanh::lean_inc_ref(v_rupHints_275_);
                crate::leanh::lean_dec_ref_known(v_val_269_, 3);
                v___x_276_ =
                    crate::leanh::lean_apply_3(v_h__3_264_, v_id_273_, v_c_274_, v_rupHints_275_);
                return v___x_276_;
            }
            2 => {
                let mut v_id_277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_c_278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_pivot_279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_rupHints_280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_ratHints_281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_h__5_266_);
                crate::leanh::lean_dec(v_h__3_264_);
                crate::leanh::lean_dec(v_h__2_263_);
                v_id_277_ = crate::leanh::lean_ctor_get(v_val_269_, 0);
                crate::leanh::lean_inc(v_id_277_);
                v_c_278_ = crate::leanh::lean_ctor_get(v_val_269_, 1);
                crate::leanh::lean_inc(v_c_278_);
                v_pivot_279_ = crate::leanh::lean_ctor_get(v_val_269_, 2);
                crate::leanh::lean_inc_ref(v_pivot_279_);
                v_rupHints_280_ = crate::leanh::lean_ctor_get(v_val_269_, 3);
                crate::leanh::lean_inc_ref(v_rupHints_280_);
                v_ratHints_281_ = crate::leanh::lean_ctor_get(v_val_269_, 4);
                crate::leanh::lean_inc_ref(v_ratHints_281_);
                crate::leanh::lean_dec_ref_known(v_val_269_, 5);
                v___x_282_ = crate::leanh::lean_apply_5(
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
                let mut v_ids_283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_h__4_265_);
                crate::leanh::lean_dec(v_h__3_264_);
                crate::leanh::lean_dec(v_h__2_263_);
                v_ids_283_ = crate::leanh::lean_ctor_get(v_val_269_, 0);
                crate::leanh::lean_inc_ref(v_ids_283_);
                crate::leanh::lean_dec_ref_known(v_val_269_, 1);
                v___x_284_ = crate::leanh::lean_apply_1(v_h__5_266_, v_ids_283_);
                return v___x_284_;
            }
        }
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATChecker_0__Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go_match__3_splitter___boxed(
    mut v_n_285_: *mut crate::leanh::LeanObject,
    mut v_motive_286_: *mut crate::leanh::LeanObject,
    mut v_step_287_: *mut crate::leanh::LeanObject,
    mut v_h__1_288_: *mut crate::leanh::LeanObject,
    mut v_h__2_289_: *mut crate::leanh::LeanObject,
    mut v_h__3_290_: *mut crate::leanh::LeanObject,
    mut v_h__4_291_: *mut crate::leanh::LeanObject,
    mut v_h__5_292_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_293_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATChecker_0__Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go_match__3_splitter(v_n_285_, v_motive_286_, v_step_287_, v_h__1_288_, v_h__2_289_, v_h__3_290_, v_h__4_291_, v_h__5_292_);
    crate::leanh::lean_dec(v_n_285_);
    return v_res_293_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATChecker_0__Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go_match__1_splitter___redArg(
    mut v_x_294_: *mut crate::leanh::LeanObject,
    mut v_h__1_295_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_296_ = crate::leanh::lean_ctor_get(v_x_294_, 0);
    crate::leanh::lean_inc(v_fst_296_);
    v_snd_297_ = crate::leanh::lean_ctor_get(v_x_294_, 1);
    crate::leanh::lean_inc(v_snd_297_);
    crate::leanh::lean_dec_ref(v_x_294_);
    v___x_298_ = crate::leanh::lean_apply_2(v_h__1_295_, v_fst_296_, v_snd_297_);
    return v___x_298_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATChecker_0__Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go_match__1_splitter(
    mut v_n_299_: *mut crate::leanh::LeanObject,
    mut v_motive_300_: *mut crate::leanh::LeanObject,
    mut v_x_301_: *mut crate::leanh::LeanObject,
    mut v_h__1_302_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_303_ = crate::leanh::lean_ctor_get(v_x_301_, 0);
    crate::leanh::lean_inc(v_fst_303_);
    v_snd_304_ = crate::leanh::lean_ctor_get(v_x_301_, 1);
    crate::leanh::lean_inc(v_snd_304_);
    crate::leanh::lean_dec_ref(v_x_301_);
    v___x_305_ = crate::leanh::lean_apply_2(v_h__1_302_, v_fst_303_, v_snd_304_);
    return v___x_305_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATChecker_0__Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go_match__1_splitter___boxed(
    mut v_n_306_: *mut crate::leanh::LeanObject,
    mut v_motive_307_: *mut crate::leanh::LeanObject,
    mut v_x_308_: *mut crate::leanh::LeanObject,
    mut v_h__1_309_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_310_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATChecker_0__Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go_match__1_splitter(v_n_306_, v_motive_307_, v_x_308_, v_h__1_309_);
    crate::leanh::lean_dec(v_n_306_);
    return v_res_310_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker(
    mut v_n_311_: *mut crate::leanh::LeanObject,
    mut v_f_312_: *mut crate::leanh::LeanObject,
    mut v_proof_313_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_315_: u8 = 0;
    v___x_314_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_315_ = l_Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go(
        v_n_311_,
        v_f_312_,
        v_proof_313_,
        v___x_314_,
    );
    return v___x_315_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker___boxed(
    mut v_n_316_: *mut crate::leanh::LeanObject,
    mut v_f_317_: *mut crate::leanh::LeanObject,
    mut v_proof_318_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_319_: u8 = 0;
    let mut v_r_320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_319_ =
        l_Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker(v_n_316_, v_f_317_, v_proof_318_);
    crate::leanh::lean_dec_ref(v_proof_318_);
    v_r_320_ = crate::leanh::lean_box((v_res_319_) as usize);
    return v_r_320_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATChecker(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_LRATChecker(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Implementation(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Instance(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Actions(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATChecker(
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
pub unsafe fn initialize_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATChecker(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Tactic_BVDecide_LRAT_Internal_LRATChecker(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Implementation(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Instance(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_LRAT_Internal_Actions(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATChecker(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATChecker(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATChecker(builtin);
}
