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
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_apply_1, lean_apply_2, lean_apply_3,
    lean_apply_5, lean_box, lean_closure_set, lean_ctor_get, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_inc, lean_inc_n, lean_inc_ref, lean_inc_ref_n,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_obj_tag, lean_unbox, lean_unsigned_to_nat,
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
    mut v___x_164_: *mut LeanObject,
    mut v___y_165_: *mut LeanObject,
    mut v___y_166_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_429__boxed_167_: u8 = 0;
    let mut v___y_430__boxed_168_: u8 = 0;
    let mut v___y_431__boxed_169_: u8 = 0;
    let mut v_res_170_: u8 = 0;
    let mut v_r_171_: *mut LeanObject = core::ptr::null_mut();
    v___x_429__boxed_167_ = (lean_unbox(v___x_164_) as u8);
    v___y_430__boxed_168_ = (lean_unbox(v___y_165_) as u8);
    v___y_431__boxed_169_ = (lean_unbox(v___y_166_) as u8);
    v_res_170_ = l_Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go___lam__0(
        v___x_429__boxed_167_,
        v___y_430__boxed_168_,
        v___y_431__boxed_169_,
    );
    v_r_171_ = lean_box((v_res_170_) as usize);
    return v_r_171_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go(
    mut v_n_172_: *mut LeanObject,
    mut v_f_173_: *mut LeanObject,
    mut v_proof_174_: *mut LeanObject,
    mut v_idx_175_: *mut LeanObject,
) -> u8 {
    let mut v___x_176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_177_: u8 = 0;
    let mut v___x_178_: u8 = 0;
    let mut v___x_179_: *mut LeanObject = core::ptr::null_mut();
    let mut v_step_180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_182_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_184_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rupHints_185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_187_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_189_: u8 = 0;
    let mut v___x_190_: u8 = 0;
    let mut v___x_191_: u8 = 0;
    let mut v_c_192_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rupHints_193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_194_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_196_: u8 = 0;
    let mut v___x_197_: u8 = 0;
    let mut v_fst_198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_200_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_202_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pivot_203_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rupHints_204_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ratHints_205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_212_: u8 = 0;
    let mut v___x_213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_218_: u8 = 0;
    let mut v___x_219_: u8 = 0;
    let mut v_fst_220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_222_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ids_224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_227_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_176_ = lean_array_get_size(v_proof_174_);
                v___x_177_ = lean_nat_dec_lt(v_idx_175_, v___x_176_);
                if v___x_177_ == 0 {
                    lean_dec(v_idx_175_);
                    lean_dec_ref(v_f_173_);
                    lean_dec(v_n_172_);
                    v___x_178_ = 1;
                    return v___x_178_;
                } else {
                    v___x_179_ = lean_array_fget_borrowed(v_proof_174_, v_idx_175_);
                    lean_inc(v___x_179_);
                    v_step_180_ =
                        l_Std_Tactic_BVDecide_LRAT_Internal_intActionToDefaultClauseAction(
                            v_n_172_, v___x_179_,
                        );
                    if lean_obj_tag(v_step_180_) == 0 {
                        v___x_181_ = lean_unsigned_to_nat(1);
                        v___x_182_ = lean_nat_add(v_idx_175_, v___x_181_);
                        lean_dec(v_idx_175_);
                        v_idx_175_ = v___x_182_;
                        state = 0;
                        continue;
                    } else {
                        v_val_184_ = lean_ctor_get(v_step_180_, 0);
                        lean_inc(v_val_184_);
                        lean_dec_ref_known(v_step_180_, 1);
                        match lean_obj_tag(v_val_184_) {
                            0 => {
                                lean_dec(v_idx_175_);
                                v_rupHints_185_ = lean_ctor_get(v_val_184_, 1);
                                lean_inc_ref(v_rupHints_185_);
                                lean_dec_ref_known(v_val_184_, 2);
                                v___x_186_ = lean_box(0);
                                v___x_187_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupAdd(v_n_172_, v_f_173_, v___x_186_, v_rupHints_185_);
                                lean_dec_ref(v_rupHints_185_);
                                lean_dec(v_n_172_);
                                v_snd_188_ = lean_ctor_get(v___x_187_, 1);
                                lean_inc(v_snd_188_);
                                lean_dec_ref(v___x_187_);
                                v___x_189_ = (lean_unbox(v_snd_188_) as u8);
                                lean_dec(v_snd_188_);
                                if v___x_189_ == 0 {
                                    v___x_190_ = 2;
                                    return v___x_190_;
                                } else {
                                    v___x_191_ = 0;
                                    return v___x_191_;
                                }
                            }
                            1 => {
                                v_c_192_ = lean_ctor_get(v_val_184_, 1);
                                lean_inc(v_c_192_);
                                v_rupHints_193_ = lean_ctor_get(v_val_184_, 2);
                                lean_inc_ref(v_rupHints_193_);
                                lean_dec_ref_known(v_val_184_, 3);
                                v___x_194_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupAdd(v_n_172_, v_f_173_, v_c_192_, v_rupHints_193_);
                                lean_dec_ref(v_rupHints_193_);
                                v_snd_195_ = lean_ctor_get(v___x_194_, 1);
                                lean_inc(v_snd_195_);
                                v___x_196_ = (lean_unbox(v_snd_195_) as u8);
                                lean_dec(v_snd_195_);
                                if v___x_196_ == 0 {
                                    lean_dec_ref(v___x_194_);
                                    lean_dec(v_idx_175_);
                                    lean_dec(v_n_172_);
                                    v___x_197_ = 2;
                                    return v___x_197_;
                                } else {
                                    v_fst_198_ = lean_ctor_get(v___x_194_, 0);
                                    lean_inc(v_fst_198_);
                                    lean_dec_ref(v___x_194_);
                                    v___x_199_ = lean_unsigned_to_nat(1);
                                    v___x_200_ = lean_nat_add(v_idx_175_, v___x_199_);
                                    lean_dec(v_idx_175_);
                                    v_f_173_ = v_fst_198_;
                                    v_idx_175_ = v___x_200_;
                                    state = 0;
                                    continue;
                                }
                            }
                            2 => {
                                v_c_202_ = lean_ctor_get(v_val_184_, 1);
                                lean_inc_n(v_c_202_, 2);
                                v_pivot_203_ = lean_ctor_get(v_val_184_, 2);
                                lean_inc_ref_n(v_pivot_203_, 2);
                                v_rupHints_204_ = lean_ctor_get(v_val_184_, 3);
                                lean_inc_ref(v_rupHints_204_);
                                v_ratHints_205_ = lean_ctor_get(v_val_184_, 4);
                                lean_inc_ref(v_ratHints_205_);
                                lean_dec_ref_known(v_val_184_, 5);
                                v___x_206_ = lean_box((v___x_177_) as usize);
                                v___f_207_ = lean_alloc_closure(l_Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go___lam__0___boxed as *mut core::ffi::c_void, 3, 1);
                                lean_closure_set(v___f_207_, 0, v___x_206_);
                                lean_inc(v_n_172_);
                                v___x_208_ = lean_alloc_closure(l_Std_Tactic_BVDecide_LRAT_Internal_instDecidableEqPosFin___boxed as *mut core::ffi::c_void, 3, 1);
                                lean_closure_set(v___x_208_, 0, v_n_172_);
                                v___f_209_ = lean_alloc_closure(
                                    l_instBEqOfDecidableEq___redArg___lam__0___boxed
                                        as *mut core::ffi::c_void,
                                    3,
                                    1,
                                );
                                lean_closure_set(v___f_209_, 0, v___x_208_);
                                v___f_210_ = lean_alloc_closure(
                                    l_instBEqOfDecidableEq___redArg___lam__0___boxed
                                        as *mut core::ffi::c_void,
                                    3,
                                    1,
                                );
                                lean_closure_set(v___f_210_, 0, v___f_207_);
                                v___f_211_ = lean_alloc_closure(
                                    l_instBEqProd___redArg___lam__0___boxed
                                        as *mut core::ffi::c_void,
                                    4,
                                    2,
                                );
                                lean_closure_set(v___f_211_, 0, v___f_209_);
                                lean_closure_set(v___f_211_, 1, v___f_210_);
                                v___x_212_ =
                                    l_List_elem___redArg(v___f_211_, v_pivot_203_, v_c_202_);
                                if v___x_212_ == 0 {
                                    lean_dec_ref(v_ratHints_205_);
                                    lean_dec_ref(v_rupHints_204_);
                                    lean_dec_ref(v_pivot_203_);
                                    lean_dec(v_c_202_);
                                    v___x_213_ = lean_unsigned_to_nat(1);
                                    v___x_214_ = lean_nat_add(v_idx_175_, v___x_213_);
                                    lean_dec(v_idx_175_);
                                    v_idx_175_ = v___x_214_;
                                    state = 0;
                                    continue;
                                } else {
                                    v___x_216_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatAdd(v_n_172_, v_f_173_, v_c_202_, v_pivot_203_, v_rupHints_204_, v_ratHints_205_);
                                    lean_dec_ref(v_rupHints_204_);
                                    v_snd_217_ = lean_ctor_get(v___x_216_, 1);
                                    lean_inc(v_snd_217_);
                                    v___x_218_ = (lean_unbox(v_snd_217_) as u8);
                                    lean_dec(v_snd_217_);
                                    if v___x_218_ == 0 {
                                        lean_dec_ref(v___x_216_);
                                        lean_dec(v_idx_175_);
                                        lean_dec(v_n_172_);
                                        v___x_219_ = 2;
                                        return v___x_219_;
                                    } else {
                                        v_fst_220_ = lean_ctor_get(v___x_216_, 0);
                                        lean_inc(v_fst_220_);
                                        lean_dec_ref(v___x_216_);
                                        v___x_221_ = lean_unsigned_to_nat(1);
                                        v___x_222_ = lean_nat_add(v_idx_175_, v___x_221_);
                                        lean_dec(v_idx_175_);
                                        v_f_173_ = v_fst_220_;
                                        v_idx_175_ = v___x_222_;
                                        state = 0;
                                        continue;
                                    }
                                }
                            }
                            _ => {
                                v_ids_224_ = lean_ctor_get(v_val_184_, 0);
                                lean_inc_ref(v_ids_224_);
                                lean_dec_ref_known(v_val_184_, 1);
                                v___x_225_ =
                                    l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_delete(
                                        v_n_172_, v_f_173_, v_ids_224_,
                                    );
                                lean_dec_ref(v_ids_224_);
                                v___x_226_ = lean_unsigned_to_nat(1);
                                v___x_227_ = lean_nat_add(v_idx_175_, v___x_226_);
                                lean_dec(v_idx_175_);
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
    mut v_n_229_: *mut LeanObject,
    mut v_f_230_: *mut LeanObject,
    mut v_proof_231_: *mut LeanObject,
    mut v_idx_232_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_233_: u8 = 0;
    let mut v_r_234_: *mut LeanObject = core::ptr::null_mut();
    v_res_233_ = l_Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go(
        v_n_229_,
        v_f_230_,
        v_proof_231_,
        v_idx_232_,
    );
    lean_dec_ref(v_proof_231_);
    v_r_234_ = lean_box((v_res_233_) as usize);
    return v_r_234_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATChecker_0__Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go_match__3_splitter___redArg(
    mut v_step_235_: *mut LeanObject,
    mut v_h__1_236_: *mut LeanObject,
    mut v_h__2_237_: *mut LeanObject,
    mut v_h__3_238_: *mut LeanObject,
    mut v_h__4_239_: *mut LeanObject,
    mut v_h__5_240_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_step_235_) == 0 {
        let mut v___x_241_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_242_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__5_240_);
        lean_dec(v_h__4_239_);
        lean_dec(v_h__3_238_);
        lean_dec(v_h__2_237_);
        v___x_241_ = lean_box(0);
        v___x_242_ = lean_apply_1(v_h__1_236_, v___x_241_);
        return v___x_242_;
    } else {
        let mut v_val_243_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_236_);
        v_val_243_ = lean_ctor_get(v_step_235_, 0);
        lean_inc(v_val_243_);
        lean_dec_ref_known(v_step_235_, 1);
        match lean_obj_tag(v_val_243_) {
            0 => {
                let mut v_id_244_: *mut LeanObject = core::ptr::null_mut();
                let mut v_rupHints_245_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_246_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v_h__5_240_);
                lean_dec(v_h__4_239_);
                lean_dec(v_h__3_238_);
                v_id_244_ = lean_ctor_get(v_val_243_, 0);
                lean_inc(v_id_244_);
                v_rupHints_245_ = lean_ctor_get(v_val_243_, 1);
                lean_inc_ref(v_rupHints_245_);
                lean_dec_ref_known(v_val_243_, 2);
                v___x_246_ = lean_apply_2(v_h__2_237_, v_id_244_, v_rupHints_245_);
                return v___x_246_;
            }
            1 => {
                let mut v_id_247_: *mut LeanObject = core::ptr::null_mut();
                let mut v_c_248_: *mut LeanObject = core::ptr::null_mut();
                let mut v_rupHints_249_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_250_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v_h__5_240_);
                lean_dec(v_h__4_239_);
                lean_dec(v_h__2_237_);
                v_id_247_ = lean_ctor_get(v_val_243_, 0);
                lean_inc(v_id_247_);
                v_c_248_ = lean_ctor_get(v_val_243_, 1);
                lean_inc(v_c_248_);
                v_rupHints_249_ = lean_ctor_get(v_val_243_, 2);
                lean_inc_ref(v_rupHints_249_);
                lean_dec_ref_known(v_val_243_, 3);
                v___x_250_ = lean_apply_3(v_h__3_238_, v_id_247_, v_c_248_, v_rupHints_249_);
                return v___x_250_;
            }
            2 => {
                let mut v_id_251_: *mut LeanObject = core::ptr::null_mut();
                let mut v_c_252_: *mut LeanObject = core::ptr::null_mut();
                let mut v_pivot_253_: *mut LeanObject = core::ptr::null_mut();
                let mut v_rupHints_254_: *mut LeanObject = core::ptr::null_mut();
                let mut v_ratHints_255_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_256_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v_h__5_240_);
                lean_dec(v_h__3_238_);
                lean_dec(v_h__2_237_);
                v_id_251_ = lean_ctor_get(v_val_243_, 0);
                lean_inc(v_id_251_);
                v_c_252_ = lean_ctor_get(v_val_243_, 1);
                lean_inc(v_c_252_);
                v_pivot_253_ = lean_ctor_get(v_val_243_, 2);
                lean_inc_ref(v_pivot_253_);
                v_rupHints_254_ = lean_ctor_get(v_val_243_, 3);
                lean_inc_ref(v_rupHints_254_);
                v_ratHints_255_ = lean_ctor_get(v_val_243_, 4);
                lean_inc_ref(v_ratHints_255_);
                lean_dec_ref_known(v_val_243_, 5);
                v___x_256_ = lean_apply_5(
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
                let mut v_ids_257_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_258_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v_h__4_239_);
                lean_dec(v_h__3_238_);
                lean_dec(v_h__2_237_);
                v_ids_257_ = lean_ctor_get(v_val_243_, 0);
                lean_inc_ref(v_ids_257_);
                lean_dec_ref_known(v_val_243_, 1);
                v___x_258_ = lean_apply_1(v_h__5_240_, v_ids_257_);
                return v___x_258_;
            }
        }
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATChecker_0__Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go_match__3_splitter(
    mut v_n_259_: *mut LeanObject,
    mut v_motive_260_: *mut LeanObject,
    mut v_step_261_: *mut LeanObject,
    mut v_h__1_262_: *mut LeanObject,
    mut v_h__2_263_: *mut LeanObject,
    mut v_h__3_264_: *mut LeanObject,
    mut v_h__4_265_: *mut LeanObject,
    mut v_h__5_266_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_step_261_) == 0 {
        let mut v___x_267_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_268_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__5_266_);
        lean_dec(v_h__4_265_);
        lean_dec(v_h__3_264_);
        lean_dec(v_h__2_263_);
        v___x_267_ = lean_box(0);
        v___x_268_ = lean_apply_1(v_h__1_262_, v___x_267_);
        return v___x_268_;
    } else {
        let mut v_val_269_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_262_);
        v_val_269_ = lean_ctor_get(v_step_261_, 0);
        lean_inc(v_val_269_);
        lean_dec_ref_known(v_step_261_, 1);
        match lean_obj_tag(v_val_269_) {
            0 => {
                let mut v_id_270_: *mut LeanObject = core::ptr::null_mut();
                let mut v_rupHints_271_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_272_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v_h__5_266_);
                lean_dec(v_h__4_265_);
                lean_dec(v_h__3_264_);
                v_id_270_ = lean_ctor_get(v_val_269_, 0);
                lean_inc(v_id_270_);
                v_rupHints_271_ = lean_ctor_get(v_val_269_, 1);
                lean_inc_ref(v_rupHints_271_);
                lean_dec_ref_known(v_val_269_, 2);
                v___x_272_ = lean_apply_2(v_h__2_263_, v_id_270_, v_rupHints_271_);
                return v___x_272_;
            }
            1 => {
                let mut v_id_273_: *mut LeanObject = core::ptr::null_mut();
                let mut v_c_274_: *mut LeanObject = core::ptr::null_mut();
                let mut v_rupHints_275_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_276_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v_h__5_266_);
                lean_dec(v_h__4_265_);
                lean_dec(v_h__2_263_);
                v_id_273_ = lean_ctor_get(v_val_269_, 0);
                lean_inc(v_id_273_);
                v_c_274_ = lean_ctor_get(v_val_269_, 1);
                lean_inc(v_c_274_);
                v_rupHints_275_ = lean_ctor_get(v_val_269_, 2);
                lean_inc_ref(v_rupHints_275_);
                lean_dec_ref_known(v_val_269_, 3);
                v___x_276_ = lean_apply_3(v_h__3_264_, v_id_273_, v_c_274_, v_rupHints_275_);
                return v___x_276_;
            }
            2 => {
                let mut v_id_277_: *mut LeanObject = core::ptr::null_mut();
                let mut v_c_278_: *mut LeanObject = core::ptr::null_mut();
                let mut v_pivot_279_: *mut LeanObject = core::ptr::null_mut();
                let mut v_rupHints_280_: *mut LeanObject = core::ptr::null_mut();
                let mut v_ratHints_281_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_282_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v_h__5_266_);
                lean_dec(v_h__3_264_);
                lean_dec(v_h__2_263_);
                v_id_277_ = lean_ctor_get(v_val_269_, 0);
                lean_inc(v_id_277_);
                v_c_278_ = lean_ctor_get(v_val_269_, 1);
                lean_inc(v_c_278_);
                v_pivot_279_ = lean_ctor_get(v_val_269_, 2);
                lean_inc_ref(v_pivot_279_);
                v_rupHints_280_ = lean_ctor_get(v_val_269_, 3);
                lean_inc_ref(v_rupHints_280_);
                v_ratHints_281_ = lean_ctor_get(v_val_269_, 4);
                lean_inc_ref(v_ratHints_281_);
                lean_dec_ref_known(v_val_269_, 5);
                v___x_282_ = lean_apply_5(
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
                let mut v_ids_283_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_284_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v_h__4_265_);
                lean_dec(v_h__3_264_);
                lean_dec(v_h__2_263_);
                v_ids_283_ = lean_ctor_get(v_val_269_, 0);
                lean_inc_ref(v_ids_283_);
                lean_dec_ref_known(v_val_269_, 1);
                v___x_284_ = lean_apply_1(v_h__5_266_, v_ids_283_);
                return v___x_284_;
            }
        }
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATChecker_0__Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go_match__3_splitter___boxed(
    mut v_n_285_: *mut LeanObject,
    mut v_motive_286_: *mut LeanObject,
    mut v_step_287_: *mut LeanObject,
    mut v_h__1_288_: *mut LeanObject,
    mut v_h__2_289_: *mut LeanObject,
    mut v_h__3_290_: *mut LeanObject,
    mut v_h__4_291_: *mut LeanObject,
    mut v_h__5_292_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_293_: *mut LeanObject = core::ptr::null_mut();
    v_res_293_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATChecker_0__Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go_match__3_splitter(v_n_285_, v_motive_286_, v_step_287_, v_h__1_288_, v_h__2_289_, v_h__3_290_, v_h__4_291_, v_h__5_292_);
    lean_dec(v_n_285_);
    return v_res_293_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATChecker_0__Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go_match__1_splitter___redArg(
    mut v_x_294_: *mut LeanObject,
    mut v_h__1_295_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_296_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_298_: *mut LeanObject = core::ptr::null_mut();
    v_fst_296_ = lean_ctor_get(v_x_294_, 0);
    lean_inc(v_fst_296_);
    v_snd_297_ = lean_ctor_get(v_x_294_, 1);
    lean_inc(v_snd_297_);
    lean_dec_ref(v_x_294_);
    v___x_298_ = lean_apply_2(v_h__1_295_, v_fst_296_, v_snd_297_);
    return v___x_298_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATChecker_0__Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go_match__1_splitter(
    mut v_n_299_: *mut LeanObject,
    mut v_motive_300_: *mut LeanObject,
    mut v_x_301_: *mut LeanObject,
    mut v_h__1_302_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_303_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_305_: *mut LeanObject = core::ptr::null_mut();
    v_fst_303_ = lean_ctor_get(v_x_301_, 0);
    lean_inc(v_fst_303_);
    v_snd_304_ = lean_ctor_get(v_x_301_, 1);
    lean_inc(v_snd_304_);
    lean_dec_ref(v_x_301_);
    v___x_305_ = lean_apply_2(v_h__1_302_, v_fst_303_, v_snd_304_);
    return v___x_305_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATChecker_0__Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go_match__1_splitter___boxed(
    mut v_n_306_: *mut LeanObject,
    mut v_motive_307_: *mut LeanObject,
    mut v_x_308_: *mut LeanObject,
    mut v_h__1_309_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_310_: *mut LeanObject = core::ptr::null_mut();
    v_res_310_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATChecker_0__Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go_match__1_splitter(v_n_306_, v_motive_307_, v_x_308_, v_h__1_309_);
    lean_dec(v_n_306_);
    return v_res_310_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker(
    mut v_n_311_: *mut LeanObject,
    mut v_f_312_: *mut LeanObject,
    mut v_proof_313_: *mut LeanObject,
) -> u8 {
    let mut v___x_314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_315_: u8 = 0;
    v___x_314_ = lean_unsigned_to_nat(0);
    v___x_315_ = l_Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go(
        v_n_311_,
        v_f_312_,
        v_proof_313_,
        v___x_314_,
    );
    return v___x_315_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker___boxed(
    mut v_n_316_: *mut LeanObject,
    mut v_f_317_: *mut LeanObject,
    mut v_proof_318_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_319_: u8 = 0;
    let mut v_r_320_: *mut LeanObject = core::ptr::null_mut();
    v_res_319_ =
        l_Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker(v_n_316_, v_f_317_, v_proof_318_);
    lean_dec_ref(v_proof_318_);
    v_r_320_ = lean_box((v_res_319_) as usize);
    return v_r_320_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATChecker(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_LRATChecker(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Implementation(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Instance(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Actions(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATChecker(
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
pub unsafe fn initialize_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATChecker(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Tactic_BVDecide_LRAT_Internal_LRATChecker(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Implementation(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Instance(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_LRAT_Internal_Actions(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATChecker(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATChecker(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATChecker(builtin);
}
